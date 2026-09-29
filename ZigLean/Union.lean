import ZigLean.Packed

/-!
# `extern` and `packed` unions

An `extern` or `packed` union has no tag: its value is its `n` bytes (`n` = its size), and
every field starts at byte 0. `Emit.lean` writes a `structure` with the one field
`bytes : Vector Byte n`, its `Zig.Enc` instance (the bytes), and `get_f`/`modify_f` for each
field `f`. A bare union is not here: in `ReleaseSafe` it has a hidden tag, and the translator
makes it a tagged union.

- `extern`: a field is its `Zig.Enc` encoding. A read decodes the first `Enc.size α` bytes: an
  undefined byte throws `.unspecified`.
- `packed`: a field is its `Zig.Packed` bits at bit 0 of the backing integer. A read takes the
  field's `w` bits from the first `(w + 7) / 8` bytes. A write or `union_init` makes the bits
  above the field in its last byte undefined (`intBytes`, `Byte.part`).
-/

namespace Zig

/-- The first `n` bytes of `bs`; undefined bytes after its end. -/
def Raw.ofArray (n : Nat) (bs : Array Byte) : Vector Byte n :=
  Vector.ofFn fun i => bs.getD i.1 .undef

/-! ## `extern` -/

/-- `union_init` of an `extern` union: the field's bytes, then undefined bytes. -/
def Raw.init {α : Type} [Enc α] (n : Nat) (v : α) : Vector Byte n := Raw.ofArray n (Enc.encode v)

/-- A field read of an `extern` union. -/
def Raw.get (α : Type) [Enc α] {n : Nat} (u : Vector Byte n) : Result α :=
  Enc.decode (u.toArray.extract 0 (Enc.size α))

/-- A field write of an `extern` union: the bytes after the field do not change. -/
def Raw.set {α : Type} [Enc α] {n : Nat} (u : Vector Byte n) (v : α) : Vector Byte n :=
  Raw.ofArray n (writeBytes u.toArray 0 (Enc.encode v))

/-! ## `packed` -/

/-- `union_init` of a `packed` union: the field's bits, then undefined bits. -/
def PackedU.init {α : Type} {w : Nat} [Packed α w] (n : Nat) (v : α) : Vector Byte n :=
  Raw.ofArray n (intBytes (Packed.toBits v))

/-- A field read of a `packed` union: the low `w` bits of the backing integer (`trunc`). -/
def PackedU.get (α : Type) {w : Nat} [Packed α w] {n : Nat} (u : Vector Byte n) : Result α := do
  Packed.ofBits? (← intOfBytes w u.toArray (trunc := true))

/-- A field write of a `packed` union: the bytes after the field do not change. -/
def PackedU.set {α : Type} {w : Nat} [Packed α w] {n : Nat} (u : Vector Byte n) (v : α) :
    Vector Byte n :=
  Raw.ofArray n (writeBytes u.toArray 0 (intBytes (Packed.toBits v)))

/-- The value of a field for `modify_f`: `default` if the bytes are not a value (Zig: the
field is undefined), as `modify_f` of a tagged union does for a field that is not active. -/
def Raw.getD {α : Type} [Inhabited α] (r : Result α) : α :=
  match r.run with
  | some (.ok x) => x
  | _ => default

end Zig
