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

/-- The value bytes of `v`, little-endian; a partly used last byte has zero high bits. -/
def intBytes {n : Nat} (v : BitVec n) : Array Byte :=
  (Array.range ((n + 7) / 8)).map fun i => .int ((v.toNat >>> (8 * i)) % 256 |> BitVec.ofNat 8)

/-- The integer in the first `(n + 7) / 8` bytes. An undefined byte or a pointer byte throws
`.unspecified`. -/
def intOfBytes (n : Nat) (bs : Array Byte) : Result (BitVec n) :=
  (bs.extract 0 ((n + 7) / 8)).foldr (init := pure 0) fun b acc => do
    let hi ← acc
    match b with
    | .int x => pure (BitVec.ofNat n (x.toNat + 256 * hi.toNat))
    | _ => throw .unspecified

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

/-! ## Structs: helpers for the generated instances -/

/-- `size` bytes: each part at its offset, the rest (padding) undefined. -/
def Enc.fields (size : Nat) (parts : List (Nat × Array Byte)) : Array Byte :=
  parts.foldl (fun acc (o, bs) => writeBytes acc o bs) (Array.replicate size .undef)

/-- The value at offset `o` of `bs`. -/
def Enc.decodeAt {α : Type} [Enc α] (bs : Array Byte) (o : Nat) : Result α :=
  Enc.decode (bs.extract o (o + Enc.size α))

end Zig
