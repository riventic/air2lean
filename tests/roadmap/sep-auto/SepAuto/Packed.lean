import ZigLean.Sep.Full.Auto

/-!
# A packed value's bits read back (`ZigLean/PackedLayout.lean`, ledger #packed-roundtrip)

`Packed.toBits (Packed.ofBits b : T) = b` for valid bits `b` of every packed type the translator
generates (`LawfulPacked`, derived by `lawfulPackedOf?` from the generated instance, and the
`fsym_arith` rewrite `packedRoundTrip`): packed structs of `bool`, integer and enum fields
(exhaustive, signed, non-exhaustive), nested packed structs, a float field (whose bits the
`mask` names), and a struct without fields. A store of `fromInt(b)` (`Packed.ofBits b`) to a word
leaves the word `b` (the arena's `reset` storing a node's size). Arrays and vectors have each
direction of their lanes' law, for every lane type and width (the generic instances). A packed
union has the bits direction only (`PackedU.bitsOf_intBytes`), and so has a struct with a union
field (its value direction fails closed; ledger #packed-lawful-split); a struct with a vector
field, next to fields of any other kind (a union, a float, an enum), and a vector of enum lanes
get their laws derived too. The types are written as the
translator writes them (`tests/golden/0.17.1/layout/Gen.lean`).
-/

namespace SepAuto.Packed

open Zig Zig.Full Zig.Full.FAssn

inductive Mode where
  | off
  | low
  | high
  deriving Repr, Inhabited, DecidableEq

def Mode.toBits : Mode → BitVec 2
  | .off => (0 : BitVec 2)
  | .low => (1 : BitVec 2)
  | .high => (2 : BitVec 2)

def Mode.ofInt? (v : Int) : Option Mode :=
  if v = 0 then Option.some .off else if v = 1 then Option.some .low else if v = 2 then Option.some .high else Option.none

instance : Zig.Packed Mode 2 where
  toBits := Mode.toBits
  ofBits b := (Mode.ofInt? (Zig.val false b)).getD default
  valid b := (Mode.ofInt? (Zig.val false b)).isSome

inductive Sgn where
  | neg
  | zero
  deriving Repr, Inhabited, DecidableEq

def Sgn.toBits : Sgn → BitVec 2
  | .neg => (-1 : BitVec 2)
  | .zero => (0 : BitVec 2)

def Sgn.ofInt? (v : Int) : Option Sgn :=
  if v = -1 then Option.some .neg else if v = 0 then Option.some .zero else Option.none

instance : Zig.Packed Sgn 2 where
  toBits := Sgn.toBits
  ofBits b := (Sgn.ofInt? (Zig.val true b)).getD default
  valid b := (Sgn.ofInt? (Zig.val true b)).isSome

/-- A non-exhaustive enum: its bits. -/
structure Open where
  bits : BitVec 3
  deriving Repr, Inhabited, DecidableEq

def Open.toBits (e : Open) : BitVec 3 := e.bits

instance : Zig.Packed Open 3 where
  toBits := Open.toBits
  ofBits b := ⟨b⟩

structure Flags where
  ready : Bool
  mode : Mode
  count : BitVec 4
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Flags 7 where
  toBits v := ((Zig.Packed.toBits v.ready).setWidth 7 <<< 0) ||| ((Zig.Packed.toBits v.mode).setWidth 7 <<< 1) ||| ((Zig.Packed.toBits v.count).setWidth 7 <<< 3)
  ofBits b := { ready := Zig.Packed.get b 0, mode := Zig.Packed.get b 1, count := Zig.Packed.get b 3 }
  valid b := Zig.Packed.validAt (Mode) b 1

/-- The arena's `Node.Size`. -/
structure Size where
  resizing : Bool
  «_» : BitVec 63
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Size 64 where
  toBits v := ((Zig.Packed.toBits v.resizing).setWidth 64 <<< 0) ||| ((Zig.Packed.toBits v.«_»).setWidth 64 <<< 1)
  ofBits b := { resizing := Zig.Packed.get b 0, «_» := Zig.Packed.get b 1 }

instance : Zig.Enc Size where
  size := 8
  align := 8
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 64 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

structure Two where
  a : Mode
  s : Sgn
  o : Open
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Two 7 where
  toBits v := ((Zig.Packed.toBits v.a).setWidth 7 <<< 0) ||| ((Zig.Packed.toBits v.s).setWidth 7 <<< 2) ||| ((Zig.Packed.toBits v.o).setWidth 7 <<< 4)
  ofBits b := { a := Zig.Packed.get b 0, s := Zig.Packed.get b 2, o := Zig.Packed.get b 4 }
  valid b := Zig.Packed.validAt (Mode) b 0 && Zig.Packed.validAt (Sgn) b 2

/-- A packed struct of packed structs. -/
structure Outer where
  a : Flags
  b : Size
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Outer 71 where
  toBits v := ((Zig.Packed.toBits v.a).setWidth 71 <<< 0) ||| ((Zig.Packed.toBits v.b).setWidth 71 <<< 7)
  ofBits b := { a := Zig.Packed.get b 0, b := Zig.Packed.get b 7 }
  valid b := Zig.Packed.validAt (Flags) b 0

/-- A float field: the struct's `mask` is its fields'. -/
structure Fl where
  x : Float .f32
  on : Bool
  deriving Inhabited

instance : Zig.Packed Fl 33 where
  toBits v := ((Zig.Packed.toBits v.x).setWidth 33 <<< 0) ||| ((Zig.Packed.toBits v.on).setWidth 33 <<< 32)
  ofBits b := { x := Zig.Packed.get b 0, on := Zig.Packed.get b 32 }
  mask v := ((Zig.Packed.mask v.x).setWidth 33 <<< 0) ||| ((BitVec.allOnes 1).setWidth 33 <<< 32)

structure Empty0 where
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Empty0 0 where
  toBits _ := (0 : BitVec 0)
  ofBits _ := {  }

/-- A packed union (its bytes). -/
structure Reg where
  bytes : Vector Zig.Byte 1
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Reg 8 where
  toBits u := Zig.PackedU.bitsOf 8 u.bytes.toArray
  ofBits b := ⟨Zig.Raw.ofArray 1 (Zig.intBytes b)⟩
  mask u := Zig.PackedU.maskOf 8 u.bytes.toArray

structure Wrap where
  r : Reg
  on : Bool
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Wrap 9 where
  toBits v := ((Zig.Packed.toBits v.r).setWidth 9 <<< 0) ||| ((Zig.Packed.toBits v.on).setWidth 9 <<< 8)
  ofBits b := { r := Zig.Packed.get b 0, on := Zig.Packed.get b 8 }
  mask v := ((Zig.Packed.mask v.r).setWidth 9 <<< 0) ||| ((BitVec.allOnes 1).setWidth 9 <<< 8)

/-- A `bool` and an integer field: every bit pattern is a value. -/
theorem size_bits (x : BitVec 64) : Packed.toBits (Packed.ofBits x : Size) = x := by
  fsym_arith

/-- The arena's `fromInt` of a size with the `resizing` bit cleared: the cleared size. -/
theorem size_cleared (x : BitVec 64) :
    (Packed.toBits (Packed.ofBits (x &&& 18446744073709551614#64) : Size)).toNat = x.toNat - x.toNat % 2 := by
  fsym_arith

/-- An exhaustive enum field: valid bits. -/
theorem flags_bits (x : BitVec 7) (h : Packed.valid (α := Flags) x = true) :
    Packed.toBits (Packed.ofBits x : Flags) = x := by
  fsym_arith

/-- A signed enum, an unsigned one and a non-exhaustive one. -/
theorem two_bits (x : BitVec 7) (h : Packed.valid (α := Two) x = true) :
    Packed.toBits (Packed.ofBits x : Two) = x := by
  fsym_arith

/-- A packed struct of packed structs. -/
theorem outer_bits (x : BitVec 71) (h : Packed.valid (α := Outer) x = true) :
    Packed.toBits (Packed.ofBits x : Outer) = x := by
  fsym_arith

/-- A float field. -/
theorem fl_bits (x : BitVec 33) : Packed.toBits (Packed.ofBits x : Fl) = x := by
  fsym_arith

/-- No field. -/
theorem empty_bits (x : BitVec 0) : Packed.toBits (Packed.ofBits x : Empty0) = x := by
  fsym_arith

/-! The other direction (`packedValRoundTrip`, `packedValidToBits`): a value with every bit
determined is the value of its bits, which are valid. -/

/-- An exhaustive enum field. -/
theorem flags_val (v : Flags) : (Packed.ofBits (Packed.toBits v) : Flags) = v := by
  fsym_arith

theorem flags_valid (v : Flags) : Packed.valid (α := Flags) (Packed.toBits v) = true := by
  fsym_arith

/-- An exhaustive enum. -/
theorem mode_val (v : Mode) : (Packed.ofBits (Packed.toBits v) : Mode) = v := by
  fsym_arith

theorem mode_valid (v : Mode) : Packed.valid (α := Mode) (Packed.toBits v) = true := by
  fsym_arith

/-- A packed struct of packed structs. -/
theorem outer_val (v : Outer) : (Packed.ofBits (Packed.toBits v) : Outer) = v := by
  fsym_arith

/-- A float field: only with every bit determined (a NaN has none). -/
theorem fl_val (v : Fl) (h : Packed.mask v = BitVec.allOnes 33) :
    (Packed.ofBits (Packed.toBits v) : Fl) = v := by
  fsym_arith

/-- A store of `fromInt(b)` to a word leaves the word `b`. -/
theorem store_fromInt (p : Ptr) (v x : BitVec 64) :
    FTotalTriple (wpts p v) (store 8 p (Packed.ofBits x : Size)) (fun _ => wpts p x) := by
  fsym

/-! ## Arrays and vectors: each direction of the lanes' law (one generic instance per direction) -/

/-- A vector of integer lanes. -/
theorem vec_bits (x : BitVec (3 * 4)) (h : Packed.valid (α := Vec (BitVec 4) 3) x = true) :
    Packed.toBits (Packed.ofBits x : Vec (BitVec 4) 3) = x := by
  fsym_arith

theorem vec_val (v : Vec (BitVec 4) 3) (h : Packed.mask v = BitVec.allOnes (3 * 4)) :
    (Packed.ofBits (Packed.toBits v) : Vec (BitVec 4) 3) = v := by
  fsym_arith

/-- An array of float lanes: only with every bit determined (a NaN lane has none). -/
theorem floats_val (v : Vector (Float .f16) 2)
    (h : Packed.mask v = BitVec.allOnes (2 * FloatFmt.f16.width)) :
    (Packed.ofBits (Packed.toBits v) : Vector (Float .f16) 2) = v := by
  fsym_arith

/-- Lanes of any lawful type and width, any number of them, nested. -/
theorem generic_lanes_bits {T : Type} {n k j : Nat} [Zig.Packed T n] [LawfulPacked T n]
    (x : BitVec (j * (k * n))) (h : Packed.valid (α := Vector (Vec T k) j) x = true) :
    Packed.toBits (Packed.ofBits x : Vector (Vec T k) j) = x := by
  fsym_arith

theorem generic_lanes_val {T : Type} {n k : Nat} [Zig.Packed T n] [LawfulPacked T n]
    (v : Vec T k) (h : Packed.mask v = BitVec.allOnes (k * n)) :
    (Packed.ofBits (Packed.toBits v) : Vec T k) = v := by
  fsym_arith

/-- One direction of the lanes' law gives that direction of the vector's. -/
example {T : Type} {n k : Nat} [Zig.Packed T n] [LawfulPackedBits T n] :
    LawfulPackedBits (Vec T k) (k * n) := inferInstance

example {T : Type} {n k : Nat} [Zig.Packed T n] [LawfulPackedVal T n] :
    LawfulPackedVal (Vector T k) (k * n) := inferInstance

/-! ## Packed unions: the bits direction only -/

/-- A packed union's bits direction, for every union (`PackedU.bitsOf_intBytes`). -/
theorem reg_bits (x : BitVec 8) : Packed.toBits (Packed.ofBits x : Reg) = x :=
  PackedU.bitsOf_intBytes x (by decide)

/-- No value direction: a byte whose bits are all determined in a form other than `.int` (here
`.mask 0xFF 0`, which `Byte.ofDefBits` never makes) reads back as `.int`. So do the padding bytes
of a union wider than its bits: `ofBits` makes them undefined, whatever they held. -/
theorem reg_no_val : ∃ u : Reg, Packed.mask u = BitVec.allOnes 8 ∧
    (Packed.ofBits (Packed.toBits u) : Reg) ≠ u :=
  ⟨⟨#v[.mask 0xFF 0]⟩, by decide, by decide +kernel⟩

/-- A struct with a packed union field has the bits direction (its fields', derived by direction,
ledger #packed-lawful-split)... -/
theorem wrap_bits (x : BitVec 9) : Packed.toBits (Packed.ofBits x : Wrap) = x := by
  fsym_arith

set_option linter.unusedVariables false in
/-- ... and not the value direction (fail closed: the union has none, `reg_no_val`). -/
example (v : Wrap) (h : Packed.mask v = BitVec.allOnes 9) : True := by
  fail_if_success have : (Packed.ofBits (Packed.toBits v) : Wrap) = v := by fsym_arith
  trivial

/-- A type without a law of a direction (a packed union field, the value direction) is left
alone, and its failed derivation logs no error into the proof that meets it (at the top level,
with error recovery on). -/
theorem wrap_left (v : Wrap) (h : (Packed.ofBits (Packed.toBits v) : Wrap) = v) :
    (Packed.ofBits (Packed.toBits v) : Wrap) = v := by
  fsym_arith

/-! ## Array and vector fields, lanes of a derived law -/

/-- A packed struct with a vector field (Zig 0.15.2 `VectorFields`, `VF`): the field's validity
and determined bits from its lanes' (`Packed.valid_vec_of`, `Packed.mask_vec_of`). -/
structure VF where
  t : BitVec 4
  v : Zig.Vec (BitVec 4) 3
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed VF 16 where
  toBits v := ((Zig.Packed.toBits v.t).setWidth 16 <<< 0) ||| ((Zig.Packed.toBits v.v).setWidth 16 <<< 4)
  ofBits b := { t := Zig.Packed.get b 0, v := Zig.Packed.get b 4 }

theorem vf_bits (x : BitVec 16) : Packed.toBits (Packed.ofBits x : VF) = x := by
  fsym_arith

theorem vf_val (v : VF) : (Packed.ofBits (Packed.toBits v) : VF) = v := by
  fsym_arith

/-- Lanes of an enum: the lane's law derived first (no instance), then the vector's. -/
theorem vec_enum_bits (x : BitVec (2 * 2)) (h : Packed.valid (α := Vector Mode 2) x = true) :
    Packed.toBits (Packed.ofBits x : Vector Mode 2) = x := by
  fsym_arith

theorem vec_enum_val (v : Vec Mode 2) (h : Packed.mask v = BitVec.allOnes (2 * 2)) :
    (Packed.ofBits (Packed.toBits v) : Vec Mode 2) = v := by
  fsym_arith

/-! A vector field next to a field of any other kind: the instance's `mask` then names every
field (all ones for the vector's, `PackedLayout.mask_full_of`), and its `valid` the enum fields
only (the vector's bits are all valid, by its lanes'). -/

/-- Next to a packed union (Zig 0.14.1/0.15.2 `packed struct { r: Reg, v: @Vector(3, u4) }`):
the bits direction... -/
structure VR where
  r : Reg
  v : Zig.Vec (BitVec 4) 3
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed VR 20 where
  toBits v := ((Zig.Packed.toBits v.r).setWidth 20 <<< 0) ||| ((Zig.Packed.toBits v.v).setWidth 20 <<< 8)
  ofBits b := { r := Zig.Packed.get b 0, v := Zig.Packed.get b 8 }
  mask v := ((Zig.Packed.mask v.r).setWidth 20 <<< 0) ||| ((BitVec.allOnes 12).setWidth 20 <<< 8)

theorem vr_bits (x : BitVec 20) : Packed.toBits (Packed.ofBits x : VR) = x := by
  fsym_arith

set_option linter.unusedVariables false in
/-- ... and not the value direction (fail closed: the union has none). -/
example (v : VR) (h : Packed.mask v = BitVec.allOnes 20) : True := by
  fail_if_success have : (Packed.ofBits (Packed.toBits v) : VR) = v := by fsym_arith
  trivial

/-- Next to a float (`packed struct { f: f32, v: @Vector(3, u4) }`). -/
structure FV where
  f : Float .f32
  v : Zig.Vec (BitVec 4) 3
  deriving Inhabited

instance : Zig.Packed FV 44 where
  toBits v := ((Zig.Packed.toBits v.f).setWidth 44 <<< 0) ||| ((Zig.Packed.toBits v.v).setWidth 44 <<< 32)
  ofBits b := { f := Zig.Packed.get b 0, v := Zig.Packed.get b 32 }
  mask v := ((Zig.Packed.mask v.f).setWidth 44 <<< 0) ||| ((BitVec.allOnes 12).setWidth 44 <<< 32)

theorem fv_bits (x : BitVec 44) : Packed.toBits (Packed.ofBits x : FV) = x := by
  fsym_arith

theorem fv_val (v : FV) (h : Packed.mask v = BitVec.allOnes 44) :
    (Packed.ofBits (Packed.toBits v) : FV) = v := by
  fsym_arith

/-- Next to an exhaustive enum (`packed struct { m: Mode, v: @Vector(3, u4) }`). -/
structure MV where
  m : Mode
  v : Zig.Vec (BitVec 4) 3
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed MV 14 where
  toBits v := ((Zig.Packed.toBits v.m).setWidth 14 <<< 0) ||| ((Zig.Packed.toBits v.v).setWidth 14 <<< 2)
  ofBits b := { m := Zig.Packed.get b 0, v := Zig.Packed.get b 2 }
  valid b := Zig.Packed.validAt (Mode) b 0

theorem mv_bits (x : BitVec 14) (h : Packed.valid (α := MV) x = true) :
    Packed.toBits (Packed.ofBits x : MV) = x := by
  fsym_arith

theorem mv_val (v : MV) : (Packed.ofBits (Packed.toBits v) : MV) = v := by
  fsym_arith

/-- Every kind at once: an enum, a vector of integers, a float, a vector of floats (its `mask`
its lanes'), lanes of an enum (their validity in `valid`) and a `bool`. -/
structure Mix where
  m : Mode
  v : Zig.Vec (BitVec 4) 3
  f : Float .f32
  w : Zig.Vec (Float .f16) 2
  e : Vector Mode 2
  on : Bool
  deriving Inhabited

instance : Zig.Packed Mix 83 where
  toBits v := ((Zig.Packed.toBits v.m).setWidth 83 <<< 0) ||| ((Zig.Packed.toBits v.v).setWidth 83 <<< 2) ||| ((Zig.Packed.toBits v.f).setWidth 83 <<< 14) ||| ((Zig.Packed.toBits v.w).setWidth 83 <<< 46) ||| ((Zig.Packed.toBits v.e).setWidth 83 <<< 78) ||| ((Zig.Packed.toBits v.on).setWidth 83 <<< 82)
  ofBits b := { m := Zig.Packed.get b 0, v := Zig.Packed.get b 2, f := Zig.Packed.get b 14, w := Zig.Packed.get b 46, e := Zig.Packed.get b 78, on := Zig.Packed.get b 82 }
  valid b := Zig.Packed.validAt (Mode) b 0 && Zig.Packed.validAt (Vector Mode 2) b 78
  mask v := ((BitVec.allOnes 2).setWidth 83 <<< 0) ||| ((BitVec.allOnes 12).setWidth 83 <<< 2) ||| ((Zig.Packed.mask v.f).setWidth 83 <<< 14) ||| ((Zig.Packed.mask v.w).setWidth 83 <<< 46) ||| ((BitVec.allOnes 4).setWidth 83 <<< 78) ||| ((BitVec.allOnes 1).setWidth 83 <<< 82)

theorem mix_bits (x : BitVec 83) (h : Packed.valid (α := Mix) x = true) :
    Packed.toBits (Packed.ofBits x : Mix) = x := by
  fsym_arith

theorem mix_val (v : Mix) (h : Packed.mask v = BitVec.allOnes 83) :
    (Packed.ofBits (Packed.toBits v) : Mix) = v := by
  fsym_arith

/-- Lanes of lanes: the field's facts from its lanes', in any depth. -/
structure VN where
  t : BitVec 4
  a : Vector (Zig.Vec (BitVec 4) 3) 2
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed VN 28 where
  toBits v := ((Zig.Packed.toBits v.t).setWidth 28 <<< 0) ||| ((Zig.Packed.toBits v.a).setWidth 28 <<< 4)
  ofBits b := { t := Zig.Packed.get b 0, a := Zig.Packed.get b 4 }

theorem vn_bits (x : BitVec 28) : Packed.toBits (Packed.ofBits x : VN) = x := by
  fsym_arith

theorem vn_val (v : VN) : (Packed.ofBits (Packed.toBits v) : VN) = v := by
  fsym_arith

/-- A `mask` that writes all ones for a float field (a NaN's bits are not determined): no law
(fail closed, `PackedLayout.mask_full_of`'s `hf`). -/
structure BadMask where
  f : Float .f32
  on : Bool
  deriving Inhabited

instance : Zig.Packed BadMask 33 where
  toBits v := ((Zig.Packed.toBits v.f).setWidth 33 <<< 0) ||| ((Zig.Packed.toBits v.on).setWidth 33 <<< 32)
  ofBits b := { f := Zig.Packed.get b 0, on := Zig.Packed.get b 32 }
  mask _ := ((BitVec.allOnes 32).setWidth 33 <<< 0) ||| ((BitVec.allOnes 1).setWidth 33 <<< 32)

set_option linter.unusedVariables false in
example (x : BitVec 33) : True := by
  fail_if_success have : Packed.toBits (Packed.ofBits x : BadMask) = x := by fsym_arith
  trivial

/-! ## Generic clients and the nesting budget -/

/-- **A generic client** over any packed type with a law: the context's `LawfulPacked`. -/
theorem generic_bits {T : Type} {n : Nat} [Zig.Packed T n] [LawfulPacked T n] (x : BitVec n)
    (h : Packed.valid (α := T) x = true) : Packed.toBits (Packed.ofBits x : T) = x := by
  fsym_arith

theorem generic_val {T : Type} {n : Nat} [Zig.Packed T n] [LawfulPacked T n] (v : T)
    (h : Packed.mask v = BitVec.allOnes n) : (Packed.ofBits (Packed.toBits v) : T) = v := by
  fsym_arith

/-- Four packed structs nested around an enum: the outer one is past the nesting budget of the
derivation (`lawfulPackedOf?`, 4). -/
structure P1 where
  m : Mode
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed P1 2 where
  toBits v := ((Zig.Packed.toBits v.m).setWidth 2 <<< 0)
  ofBits b := { m := Zig.Packed.get b 0 }
  valid b := Zig.Packed.validAt (Mode) b 0

structure P2 where
  p : P1
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed P2 2 where
  toBits v := ((Zig.Packed.toBits v.p).setWidth 2 <<< 0)
  ofBits b := { p := Zig.Packed.get b 0 }
  valid b := Zig.Packed.validAt (P1) b 0

structure P3 where
  p : P2
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed P3 2 where
  toBits v := ((Zig.Packed.toBits v.p).setWidth 2 <<< 0)
  ofBits b := { p := Zig.Packed.get b 0 }
  valid b := Zig.Packed.validAt (P2) b 0

structure P4 where
  p : P3
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed P4 2 where
  toBits v := ((Zig.Packed.toBits v.p).setWidth 2 <<< 0)
  ofBits b := { p := Zig.Packed.get b 0 }
  valid b := Zig.Packed.validAt (P3) b 0

set_option linter.unusedVariables false in
/-- **No failure cached under the nesting budget**: the hypothesis about `P4` (normalized first)
asks for `P4`'s law, which is past the budget; `P2`'s, asked next in the same run, is derived. -/
theorem nested_inner_after_outer (x : BitVec 2) (y : BitVec 2)
    (h4 : Packed.toBits (Packed.ofBits x : P4) = x) (h : Packed.valid (α := P2) y = true) :
    Packed.toBits (Packed.ofBits y : P2) = y := by
  fsym_arith

end SepAuto.Packed
