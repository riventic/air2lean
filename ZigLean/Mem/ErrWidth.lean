import ZigLean.Mem.Enc

/-!
# Error codes of every `--error-limit` width

Zig stores an error as an unsigned integer whose width depends on the compilation:
`Zcu.errorSetBits` is `0` for `--error-limit 0` and `log2(limit) + 1` otherwise, and the
default limit `maxInt(u16) - 1` gives 16 bits. Size and alignment follow the target's integer
rules (`std.zig.target.intByteSize`/`intAlignment`), which on the modelled x86_64 and aarch64
targets are `intSize`/`intAlign`: 1, 2 or 4 bytes for 1 to 32 bits.

This module is the width-parameterized form of the 16-bit error storage in `Enc.lean`. Every
definition takes the profile's `error_set_bits` (`bits`); at `bits = 16` it coincides with the
existing definitions (`ZigLean/Mem/ErrWidthLemmas.lean`, `errOfBytesW_sixteen` & co.), which
the translator keeps emitting for the default configuration. Stored errors keep their symbolic
name (`Byte.errFrag`), never a compiler ordinal.

Integer/error casts need the compilation's numbering, which AIR does not export. `ErrorTable`
makes it an explicit parameter: `intFromErrorW`/`errorFromIntW` are stated over any table that
fits the width, and an out-of-range code is an explicit error, never a wrapped value.
-/

namespace Zig

/-! ## Width selection -/

/-- `Zcu.errorSetBits` (Zig 0.16, `src/Zcu.zig`) for a non-SPIR-V target. -/
def errorLimitBits (limit : Nat) : Nat := if limit = 0 then 0 else Nat.log2 limit + 1

/-- The default `--error-limit`: `maxInt(u16) - 1` (`src/Compilation.zig`). -/
def defaultErrorLimit : Nat := 65534

/-- The widths with error storage in the model: `--error-limit` 1 to `maxInt(u32)`.
Width 0 (`--error-limit 0`) has no error value and no storage; the translator rejects it. -/
def ValidErrBits (bits : Nat) : Prop := 0 < bits ∧ bits ≤ 32

instance (bits : Nat) : Decidable (ValidErrBits bits) := inferInstanceAs (Decidable (_ ∧ _))

/-- Bytes of the error integer (`std.zig.target.intByteSize` on x86_64/aarch64). -/
def errCodeSize (bits : Nat) : Nat := intSize bits

/-- Alignment of the error integer (`std.zig.target.intAlignment` on x86_64/aarch64). -/
def errCodeAlign (bits : Nat) : Nat := intAlign bits

/-- Nonzero codes of a `bits`-bit error integer: the most errors one compilation can name. -/
def errCapacity (bits : Nat) : Nat := 2 ^ bits - 1

/-! ## Code bytes -/

/-- The `errCodeSize bits` bytes of an error code: zeros for no error, else the name's
fragments. -/
def errBytesW (bits : Nat) : Option ErrName → Array Byte
  | none => Array.replicate (errCodeSize bits) (.int 0)
  | some e => Array.ofFn (n := errCodeSize bits) fun i =>
      if h : i.val < 4 then .errFrag e ⟨i.val, h⟩ else .undef

/-- The error of the first `errCodeSize bits` bytes: `none` for the zero code. Any other
content (mixed, partial, swapped or foreign fragments, integer bytes) throws `.unspecified`. -/
def errOfBytesW (bits : Nat) (bs : Array Byte) : Result (Option ErrName) :=
  let code := bs.extract 0 (errCodeSize bits)
  if 4 < errCodeSize bits then throw .unspecified
  else if code = errBytesW bits none then pure none
  else match (code[0]? : Option Byte) with
    | some (.errFrag e _) => if code = errBytesW bits (some e) then pure (some e) else throw .unspecified
    | _ => throw .unspecified

/-! ## Declared finite domains -/

/-- `E` at width `bits`: a foreign name stores undefined bytes and never reloads as `E`. -/
def errorEncW (bits : Nat) (d : ErrorDomain) : Enc ErrName where
  size := errCodeSize bits
  align := errCodeAlign bits
  encode e := if d.names.contains e then errBytesW bits (some e)
    else Array.replicate (errCodeSize bits) .undef
  decode bs := do
    match ← errOfBytesW bits bs with
    | some e => if d.names.contains e then pure e else throw .unspecified
    | none => throw .unspecified

/-- `?E` at width `bits`: `null` is the zero code. -/
def optionalErrorEncW (bits : Nat) (d : ErrorDomain) : Enc (Option ErrName) where
  size := errCodeSize bits
  align := errCodeAlign bits
  encode
    | none => errBytesW bits none
    | some e => (errorEncW bits d).encode e
  decode bs := do
    match ← errOfBytesW bits bs with
    | none => pure none
    | some e => if d.names.contains e then pure (some e) else throw .unspecified

/-- The members of `d`, stored with `bits`-bit codes. A separate type from `FiniteError d`, so
that the two widths never share an instance. -/
def FiniteErrorW (_bits : Nat) (d : ErrorDomain) : Type := FiniteError d

instance (bits : Nat) (d : ErrorDomain) : Enc (FiniteErrorW bits d) where
  size := errCodeSize bits
  align := errCodeAlign bits
  encode e := errBytesW bits (some e.val)
  decode bs := do
    match ← errOfBytesW bits bs with
    | some e => if h : d.names.contains e = true then pure ⟨e, h⟩ else throw .unspecified
    | none => throw .unspecified

/-! ## Error unions -/

/-- `codegen.errUnionErrorOffset`/`errUnionPayloadOffset` with a `bits`-bit error integer. -/
def errUnionOffsetsW (bits size align : Nat) : Nat × Nat :=
  if size = 0 then (0, 0)
  else if align ≥ errCodeAlign bits then (alignUp size (errCodeAlign bits), 0)
  else (0, alignUp (errCodeSize bits) align)

def errUnionSizeW (bits size align : Nat) : Nat :=
  let (eo, po) := errUnionOffsetsW bits size align
  alignUp (Nat.max (eo + errCodeSize bits) (po + size)) (Nat.max align (errCodeAlign bits))

/-- `E!T` at width `bits`, with an explicit payload dictionary. -/
def Enc.errorUnionWithW {α : Type} (bits : Nat) (payload : Enc α) : Enc (Except ErrName α) where
  size := errUnionSizeW bits payload.size payload.align
  align := Nat.max payload.align (errCodeAlign bits)
  encode v :=
    let (eo, po) := errUnionOffsetsW bits payload.size payload.align
    let size := errUnionSizeW bits payload.size payload.align
    match v with
    | .ok x => writeBytes (writeBytes (Array.replicate size .undef) eo (errBytesW bits none)) po
        (payload.encode x)
    | .error e => writeBytes (Array.replicate size .undef) eo (errBytesW bits (some e))
  decode bs := do
    let (eo, po) := errUnionOffsetsW bits payload.size payload.align
    match ← errOfBytesW bits (bs.extract eo (eo + errCodeSize bits)) with
    | none => .ok <$> payload.decode (bs.extract po (po + payload.size))
    | some e => pure (.error e)

/-- A declared finite error union at width `bits`: foreign errors store undefined bytes and
fail on load. -/
def errorUnionEncW {α : Type} (bits : Nat) (d : ErrorDomain) (payload : Enc α) :
    Enc (Except ErrName α) :=
  let base := Enc.errorUnionWithW bits payload
  { base with
    encode := fun v => match v with
      | .ok _ => base.encode v
      | .error e => if d.names.contains e then base.encode v else Array.replicate base.size .undef
    decode := fun bs => do
      let v ← base.decode bs
      match v with
      | .ok _ => pure v
      | .error e => if d.names.contains e then pure v else throw .unspecified }

/-! ## Pointer-form operations at width `bits` -/

def optionalErrorIsSomeW (bits : Nat) (d : ErrorDomain) (align : Nat) (p : Ptr) : MemM Bool := do
  pure (← (optionalErrorEncW bits d).decode
    (← loadBytes p (errCodeSize bits) align)).isSome

private def errCodeBytesAt (bits : Nat) (α : Type) [Enc α] (align : Nat) (p : Ptr) :
    MemM (Option ErrName) := do
  let (eo, _) := errUnionOffsetsW bits (Enc.size α) (Enc.align α)
  errOfBytesW bits (← loadBytes (p.add eo) (errCodeSize bits) (Nat.min align (errCodeAlign bits)))

def errIsErrAtW (bits : Nat) (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM Bool := do
  pure (← errCodeBytesAt bits α align p).isSome

def errCodeAtW (bits : Nat) (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM ErrName := do
  match ← errCodeBytesAt bits α align p with
  | some e => pure e
  | none => throw .unspecified

def errPayloadPtrW (bits : Nat) (α : Type) [Enc α] (p : Ptr) : Ptr :=
  p.add (errUnionOffsetsW bits (Enc.size α) (Enc.align α)).2

def tryPayloadPtrW (bits : Nat) (α : Type) [Enc α] (align : Nat) (p : Ptr) :
    MemM (Except ErrName Ptr) := do
  match ← errCodeBytesAt bits α align p with
  | some e => pure (.error e)
  | none => pure (.ok (errPayloadPtrW bits α p))

def errSetOkW (bits : Nat) (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM Ptr := do
  let (eo, po) := errUnionOffsetsW bits (Enc.size α) (Enc.align α)
  storeBytes (p.add eo) (Nat.min align (errCodeAlign bits)) (errBytesW bits none)
  pure (p.add po)

def finiteErrIsErrAtW (bits : Nat) (d : ErrorDomain) (α : Type) [Enc α] (align : Nat) (p : Ptr) :
    MemM Bool := do
  match ← errCodeBytesAt bits α align p with
  | some e => do let _ ← requireError d e; pure true
  | none => pure false

def finiteErrCodeAtW (bits : Nat) (d : ErrorDomain) (α : Type) [Enc α] (align : Nat) (p : Ptr) :
    MemM ErrName := do
  requireError d (← errCodeAtW bits α align p)

def finiteTryPayloadPtrW (bits : Nat) (d : ErrorDomain) (α : Type) [Enc α] (align : Nat) (p : Ptr) :
    MemM (Except ErrName Ptr) := do
  requireErrorUnion d (← tryPayloadPtrW bits α align p)

/-! ## Integer/error casts over an explicit numbering -/

/-- A compilation's numbering of its global error set: code `i + 1` is `names[i]`. Zig
assigns it per compilation and AIR does not export it, so it is a parameter, never guessed. -/
structure ErrorTable where
  names : Array ErrName
  unique : names.toList.Nodup

/-- The compiler rejects a compilation whose error count exceeds `--error-limit`
("ZCU used more errors than possible"), so every real table fits its width. -/
def ErrorTable.fits (t : ErrorTable) (bits : Nat) : Prop := t.names.size ≤ errCapacity bits

/-- The table of `names` at width `bits`; duplicates or too many names are explicit errors. -/
def ErrorTable.check (names : Array ErrName) (bits : Nat) : Except String ErrorTable :=
  if h : names.toList.Nodup then
    if names.size ≤ errCapacity bits then .ok ⟨names, h⟩
    else .error s!"{names.size} errors exceed the {errCapacity bits} codes of a {bits}-bit error integer"
  else .error "an error table names an error twice"

/-- The position of `e` in `l`. -/
def errIndex (e : ErrName) : List ErrName → Option Nat
  | [] => none
  | x :: xs => if x = e then some 0 else (errIndex e xs).map (· + 1)

/-- `@intFromError`: the code of `e`. A name outside the numbering has no code. -/
def intFromErrorW (bits : Nat) (t : ErrorTable) (e : ErrName) : Result (BitVec bits) :=
  match errIndex e t.names.toList with
  | some i => if i + 1 ≤ errCapacity bits then pure (BitVec.ofNat bits (i + 1)) else throw .unspecified
  | none => throw .unspecified

/-- `@errorFromInt`: code 0 and codes without an error are the safety panic
`invalid error code`. -/
def errorFromIntW (bits : Nat) (t : ErrorTable) (c : BitVec bits) : Result ErrName :=
  if h : 0 < c.toNat ∧ c.toNat ≤ t.names.size then
    pure t.names[c.toNat - 1]
  else throw .panic

/-- An integer converted to the error integer (`@intCast` to `u<bits>`): a value that does
not fit the narrower width is the safety panic `integer overflow`, not a truncated code. -/
def errorCodeOfNat (bits x : Nat) : Result (BitVec bits) :=
  if x < 2 ^ bits then pure (BitVec.ofNat bits x) else throw .overflow

/-- `@errorCast` to the finite set `d`: an error outside `d` is the safety panic
`invalid error code`. The name, not a code, is the identity, so no width is involved. -/
def errorCastW (d : ErrorDomain) (e : ErrName) : Result ErrName :=
  if d.names.contains e then pure e else throw .panic

end Zig
