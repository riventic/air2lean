import ZigLean.Mem.Basic
import ZigLean.Float.Value

/-!
# Memory encodings

`Zig.Enc` instances for the types whose layout does not depend on the program: integers,
`bool`, floats, pointers and optionals. All values are little-endian, and the sizes and
alignments are the ones of the reference target (x86_64). `Check.lean` compares them with the
exporter's `abi_size`/`abi_align` of each type, so a wrong rule here stops the translation.
The translator writes the instances of structs and enums (`Emit.lean`), from the offsets that
the exporter writes.
-/

namespace Zig

/-- The alignment of `uN`/`iN` on x86_64: the byte count rounded up to a power of 2, at most
16. -/
def intAlign (n : Nat) : Nat :=
  let bytes := (n + 7) / 8
  if bytes ≤ 1 then 1 else if bytes ≤ 2 then 2 else if bytes ≤ 4 then 4
  else if bytes ≤ 8 then 8 else 16

/-- The ABI size of `uN`/`iN`: the byte count rounded up to the alignment. -/
def intSize (n : Nat) : Nat := alignUp ((n + 7) / 8) (intAlign n)

/-- The value bytes of `v`, little-endian. In a partly used last byte (`n % 8 ≠ 0`), only the
low bits are defined (`Byte.part`): Zig stores a `uN` as its integer type, and the bits above
are padding. -/
def intBytes {n : Nat} (v : BitVec n) : Array Byte :=
  (Array.range ((n + 7) / 8)).map fun i =>
    let x := (v.toNat >>> (8 * i)) % 256 |> BitVec.ofNat 8
    if n - 8 * i < 8 then .part (n - 8 * i) x else .int x

/-- Byte `i` of an `n`-bit integer: `.int`, or `.part m` if its `m` defined bits hold all of
the integer's bits in this byte. -/
def byteBits (n i : Nat) : Byte → Option (BitVec 8)
  | .int x => some x
  | .part m x => if n - 8 * i ≤ m then some x else none
  | _ => none

/-- The integer in the first `(n + 7) / 8` bytes. An undefined bit, a pointer byte or an error
byte throws `.unspecified`. -/
def intOfBytes (n : Nat) (bs : Array Byte) : Result (BitVec n) :=
  (bs.extract 0 ((n + 7) / 8)).zipIdx.foldr (init := pure 0) fun (b, i) acc => do
    let hi ← acc
    match byteBits n i b with
    | some x => pure (BitVec.ofNat n (x.toNat + 256 * hi.toNat))
    | none => throw .unspecified

/-- The bytes after the value bytes up to `size` are padding: undefined. -/
def padTo (size : Nat) (bs : Array Byte) : Array Byte :=
  bs ++ Array.replicate (size - bs.size) .undef

instance {n : Nat} : Enc (BitVec n) where
  size := intSize n
  align := intAlign n
  encode v := padTo (intSize n) (intBytes v)
  decode := intOfBytes n

/-- A byte other than 0 or 1 is not a `bool`: illegal behaviour. -/
instance : Enc Bool where
  size := 1
  align := 1
  encode b := #[.int (if b then 1 else 0)]
  decode bs := match (bs[0]? : Option Byte) with
    | some (.int x) => if x = 0 then pure false else if x = 1 then pure true else throw .illegal
    | _ => throw .unspecified

/-- The float's bits as an integer of the same width: `f80` (10 bytes) has size 16. -/
instance {fmt : FloatFmt} : Enc (Float fmt) where
  size := intSize fmt.width
  align := intAlign fmt.width
  encode v := Enc.encode v.bits
  decode bs := do pure ⟨← intOfBytes fmt.width bs⟩

instance : Enc Unit where
  size := 0
  align := 1
  encode _ := #[]
  decode _ := pure ()

/-- A pointer: 8 bytes that each remember the pointer. Integer bytes are not a pointer until
`@ptrFromInt` is in the model: `.unspecified`. -/
instance : Enc Ptr where
  size := 8
  align := 8
  encode p := (Array.finRange 8).map (.ptrFrag p)
  decode bs := match (bs[0]? : Option Byte) with
    | some (.ptrFrag p _) =>
      if bs.extract 0 8 == (Array.finRange 8).map (.ptrFrag p) then pure p else throw .unspecified
    | _ => throw .unspecified

/-- `?*T`: `null` is address 0, 8 zero bytes. -/
instance (priority := high) : Enc (Option Ptr) where
  size := 8
  align := 8
  encode
    | none => Array.replicate 8 (.int 0)
    | some p => Enc.encode p
  decode bs :=
    if bs.extract 0 8 == Array.replicate 8 (.int 0) then pure none else some <$> Enc.decode bs

/-- `?T` for a `T` that is not a pointer: the payload at offset 0, then a flag byte (1 =
non-null), then padding to the alignment of `T`. -/
instance {α : Type} [Enc α] : Enc (Option α) where
  size := alignUp (Enc.size α + 1) (Enc.align α)
  align := Enc.align α
  encode v :=
    let size := alignUp (Enc.size α + 1) (Enc.align α)
    match v with
    | none => padTo size (Array.replicate (Enc.size α) .undef ++ #[.int 0])
    | some x => padTo size (Enc.encode x ++ #[.int 1])
  decode bs :=
    match (bs[Enc.size α]? : Option Byte) with
    | some (.int 0) => pure none
    | some (.int 1) => some <$> Enc.decode bs
    | some (.int _) => throw .illegal
    | _ => throw .unspecified

/-- A slice: the pointer at offset 0, the length at offset 8. -/
instance : Enc Slice where
  size := 16
  align := 8
  encode s := Enc.encode s.ptr ++ Enc.encode s.len
  decode bs := do
    pure ⟨← Enc.decode (bs.extract 0 8), ← Enc.decode (bs.extract 8 16)⟩

/-- `?[]T`: `null` is a pointer with address 0; the length bytes are undefined. -/
instance (priority := high) : Enc (Option Slice) where
  size := 16
  align := 8
  encode
    | none => Array.replicate 8 (.int 0) ++ Array.replicate 8 .undef
    | some s => Enc.encode s
  decode bs :=
    if bs.extract 0 8 == Array.replicate 8 (.int 0) then pure none else some <$> Enc.decode bs

/-- `[n]T`: the items one after the other, each `Enc.size α` bytes. -/
instance {α : Type} {n : Nat} [Enc α] : Enc (Vector α n) where
  size := n * Enc.size α
  align := Enc.align α
  encode v := (v.toArray.map Enc.encode).flatten
  decode bs := do
    let xs ← (Array.range n).mapM fun i =>
      (Enc.decode (bs.extract (i * Enc.size α) ((i + 1) * Enc.size α)) : Result α)
    if h : xs.size = n then pure ⟨xs, h⟩ else throw .unspecified

/-! ## Error unions -/

/-- The 2 bytes of an error code (`anyerror` is `u16`): 0 for no error, else the name's
`errFrag` bytes. -/
def errBytes : Option ErrName → Array Byte
  | none => #[.int 0, .int 0]
  | some e => #[.errFrag e 0, .errFrag e 1]

/-- The error of the 2 bytes of an error code: `none` for 0. A code that is not 0 and not an
error of the model (e.g. bytes of a test input) throws `.unspecified`. -/
def errOfBytes (bs : Array Byte) : Result (Option ErrName) :=
  match (bs[0]? : Option Byte), (bs[1]? : Option Byte) with
  | some (.int a), some (.int b) => if a = 0 ∧ b = 0 then pure none else throw .unspecified
  | some (.errFrag e _), _ => if bs.extract 0 2 == errBytes (some e) then pure (some e) else throw .unspecified
  | _, _ => throw .unspecified

/-- The offsets of the error code and the payload in `E!T`, from the size and alignment of
`T` (the compiler's rule): the payload first only if its alignment is more than 2. -/
def errUnionOffsets (size align : Nat) : Nat × Nat :=
  if align > 2 then (alignUp size 2, 0) else (0, alignUp 2 align)

def errUnionSize (size align : Nat) : Nat :=
  let (eo, po) := errUnionOffsets size align
  alignUp (Nat.max (eo + 2) (po + size)) (Nat.max align 2)

/-- `E!T`: the error code and the payload at `errUnionOffsets`. -/
instance {α : Type} [Enc α] : Enc (Except ErrName α) where
  size := errUnionSize (Enc.size α) (Enc.align α)
  align := Nat.max (Enc.align α) 2
  encode v :=
    let (eo, po) := errUnionOffsets (Enc.size α) (Enc.align α)
    let size := errUnionSize (Enc.size α) (Enc.align α)
    match v with
    | .ok x => writeBytes (writeBytes (Array.replicate size .undef) eo (errBytes none)) po (Enc.encode x)
    | .error e => writeBytes (Array.replicate size .undef) eo (errBytes (some e))
  decode bs := do
    let (eo, po) := errUnionOffsets (Enc.size α) (Enc.align α)
    match ← errOfBytes (bs.extract eo (eo + 2)) with
    | none => .ok <$> Enc.decode (bs.extract po (po + Enc.size α))
    | some e => pure (.error e)

/-- `is_err_ptr`: does the error union `E!α` at `p` (alignment `align`) hold an error? -/
def errIsErrAt (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM Bool := do
  let (eo, _) := errUnionOffsets (Enc.size α) (Enc.align α)
  pure (← errOfBytes (← loadBytes (p.add eo) 2 (Nat.min align 2))).isSome

/-- `unwrap_errunion_err_ptr`: the error of the error union `E!α` at `p` (alignment `align`). Sema checks for an
error first. -/
def errCodeAt (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM ErrName := do
  let (eo, _) := errUnionOffsets (Enc.size α) (Enc.align α)
  match ← errOfBytes (← loadBytes (p.add eo) 2 (Nat.min align 2)) with
  | some e => pure e
  | none => throw .unspecified

/-- `unwrap_errunion_payload_ptr`: the pointer to the payload of the error union `E!α` at `p`. -/
def errPayloadPtr (α : Type) [Enc α] (p : Ptr) : Ptr :=
  p.add (errUnionOffsets (Enc.size α) (Enc.align α)).2

/-- `errunion_payload_ptr_set`: set the error code to 0 (no error), then the payload pointer. -/
def errSetOk (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM Ptr := do
  let (eo, po) := errUnionOffsets (Enc.size α) (Enc.align α)
  storeBytes (p.add eo) (Nat.min align 2) (errBytes none)
  pure (p.add po)

/-! ## Structs: helpers for the generated instances -/

/-- `size` bytes: each part at its offset, the rest (padding) undefined. -/
def Enc.fields (size : Nat) (parts : List (Nat × Array Byte)) : Array Byte :=
  parts.foldl (fun acc (o, bs) => writeBytes acc o bs) (Array.replicate size .undef)

/-- The value at offset `o` of `bs`. -/
def Enc.decodeAt {α : Type} [Enc α] (bs : Array Byte) (o : Nat) : Result α :=
  Enc.decode (bs.extract o (o + Enc.size α))

end Zig
