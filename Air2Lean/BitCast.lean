import Air2Lean.Memory

/-!
# Version-keyed `@bitCast` semantics

Zig ≤0.16 defines `@bitCast` on the in-memory representation; Zig 0.17.0 defines it on the
*logical* bit representation (`docs/bitcast-semantics.md`): an array or vector is its elements'
bits concatenated, element 0 in the lowest bits, with no padding, and an enum with an explicit
tag type is its tag integer. `Check.lean` and `Emit.lean` share the classification here.

The function's `Dialect.bitCast` selects the semantics (`ZigVersion.bitCast`). For a 0.17 input,
a `bitcast` whose operand and result types differ and where either side is an
array, a vector, an enum or `void` goes through `bitShape?`: the source becomes its logical bits, then
the bits become the destination (`ZigLean/BitCast.lean`). A type that has no shape here is
rejected for 0.17 with a stable diagnostic (`logicalBitCastFailure`) instead of being translated
with the ≤0.16 rules. ≤0.16 inputs keep the existing `bitcast` rules unchanged.
-/

namespace Air2Lean

/-- How a type in a 0.17 `@bitCast` becomes, and is made from, its logical bits. -/
inductive BitShape where
  | int (bits : Nat)
  | bool
  | float (bits : Nat)
  /-- A packed struct: its backing integer (`Zig.Packed`). -/
  | packed (bits : Nat)
  /-- An enum: its tag integer of `bits` bits, `signed` for an `iN` tag type. -/
  | enum (bits : Nat) (signed : Bool)
  /-- `[len]uW`/`[len]iW` (`vector = false`) or `@Vector(len, uW)`: `Zig.BitCast.ofLanes`. -/
  | intLanes (vector : Bool) (len lane : Nat)
  /-- `[len]bool` or `@Vector(len, bool)`: `Zig.BitCast.ofBools`. -/
  | boolLanes (vector : Bool) (len : Nat)
  /-- Any other type with a logical bit representation, through its `Zig.Packed` instance
  (`ZigLean/PackedRepr.lean`): a packed union, and an array or vector (at any nesting depth) of
  floats, enums, packed structs or unions. -/
  | value (bits : Nat)
  deriving Repr, BEq

/-- `@bitSizeOf` of the shape in Zig 0.17 (arrays and vectors: `len * @bitSizeOf(E)`). -/
def BitShape.bits : BitShape → Nat
  | .int b | .float b | .packed b | .enum b _ | .value b => b
  | .bool => 1
  | .intLanes _ n w => n * w
  | .boolLanes _ n => n

/-- A type whose 0.17 `@bitCast` takes the logical-order path: an array, a vector or an enum
(and `void`, which 0.17 newly accepts and the model rejects). Packed structs and unions, floats
and `bool` without one of these on the other side keep the existing rules, which are the same
bits (`packedScalarCast`). -/
def logicalBitCastTy (types : Array Ty) (id : TyId) : Bool :=
  match types[id]? with
  | some (.array ..) | some (.vector ..) | some (.enum ..) | some .void => true
  | _ => false

/-- A `bitcast` from `src` to `dst` under the `bitCast` semantics takes the logical-order path. -/
def logicalBitCastApplies (bitCast : ZigVersion.BitCast) (types : Array Ty) (src dst : TyId) : Bool :=
  bitCast == .logical && src != dst &&
    (logicalBitCastTy types src || logicalBitCastTy types dst)

/-- The stable diagnostic of a 0.17 `@bitCast` the model does not translate. -/
def logicalBitCastFailure (what : String) : String :=
  s!"a Zig 0.17 `@bitCast` {what} is outside the subset (logical bit order, docs/bitcast-semantics.md)"

/-- Zig 0.17's `@bitSizeOf` of a type with a logical bit representation (`hasBitRepresentation`)
that the model has: a packable type (`packedBits`), or an array (no sentinel) or vector of such
types at any depth, `len * @bitSizeOf(E)` bits. -/
partial def logicalBits (types : Array Ty) (id : TyId) : Option Nat :=
  match types[id]? with
  | some (.array len c false) | some (.vector len c) => (len * ·) <$> logicalBits types c
  | _ => packedBits types id

/-- The shape of `id` in a 0.17 `@bitCast`, or the diagnostic's description of why not. -/
def bitShape? (types : Array Ty) (id : TyId) : Except String BitShape :=
  let lanes (vector : Bool) (len : Nat) (child : TyId) : Except String BitShape :=
    match types[child]? with
    | some (.int _ w) => pure (.intLanes vector len w)
    | some .bool => pure (.boolLanes vector len)
    | _ => match logicalBits types child with
      | some w => pure (.value (len * w))
      | none => throw s!"of an array or vector whose element has no logical bit representation \
          in the model (type {child}: a pointer, optional, sentinel-terminated array or `void`)"
  match types[id]? with
  | some (.int _ b) => pure (.int b)
  | some .bool => pure .bool
  | some (.float b) => pure (.float b)
  | some (.struct _ "packed" _) =>
    match packedBits types id with
    | some b => pure (.packed b)
    | none => throw s!"of a packed struct without a modelled backing integer (type {id})"
  | some (.enum _ tag _ _) =>
    match types[tag]? with
    | some (.int s b) => pure (.enum b s)
    | _ => throw s!"of an enum without an integer tag type (type {id})"
  | some (.union _ "packed" none _) =>
    match packedBits types id with
    | some b => pure (.value b)
    | none => throw s!"of a packed union without a modelled backing integer (type {id})"
  | some (.array len child false) => lanes false len child
  | some (.array ..) => throw s!"of a sentinel-terminated array (type {id})"
  | some (.vector len child) => lanes true len child
  | _ => throw s!"to or from a type other than an integer, `bool`, float, packed struct or \
      union, enum, or an array or vector of these (type {id}; an `auto` or `extern` struct, \
      tuple, tagged or `extern` union, pointer, optional or error type has no logical bit \
      representation: Sema rejects its `@bitCast`)"

/-- Both shapes of a 0.17 logical-order `@bitCast` from `src` to `dst`, with equal bit sizes. -/
def logicalBitCastShapes (types : Array Ty) (src dst : TyId) :
    Except String (BitShape × BitShape) := do
  let s ← (bitShape? types src).mapError logicalBitCastFailure
  let d ← (bitShape? types dst).mapError logicalBitCastFailure
  unless s.bits == d.bits do
    throw (logicalBitCastFailure
      s!"between types of {s.bits} and {d.bits} logical bits (types {src} and {dst})")
  pure (s, d)

end Air2Lean
