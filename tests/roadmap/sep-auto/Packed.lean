import ZigLean.Sep.Full.Auto

/-!
# A packed value's bits read back (`ZigLean/PackedLayout.lean`, ledger #packed-roundtrip)

`Packed.toBits (Packed.ofBits b : T) = b` for valid bits `b` of every packed type the translator
generates (`LawfulPacked`, derived by `lawfulPackedOf?` from the generated instance, and the
`fsym_arith` rewrite `packedRoundTrip`): packed structs of `bool`, integer and enum fields
(exhaustive, signed, non-exhaustive), nested packed structs, a float field (whose bits the
`mask` names), and a struct without fields. A store of `fromInt(b)` (`Packed.ofBits b`) to a word
leaves the word `b` (the arena's `reset` storing a node's size). A packed union field has no
round trip law here (fail closed). The types are written as the translator writes them
(`tests/golden/0.17.0/layout/Gen.lean`).
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

/-- A store of `fromInt(b)` to a word leaves the word `b`. -/
theorem store_fromInt (p : Ptr) (v x : BitVec 64) :
    FTotalTriple (wpts p v) (store 8 p (Packed.ofBits x : Size)) (fun _ => wpts p x) := by
  fsym

set_option linter.unusedVariables false in
/-- A packed union field: no round trip law (fail closed). -/
example (x : BitVec 9) : True := by
  fail_if_success have : Packed.toBits (Packed.ofBits x : Wrap) = x := by fsym_arith
  trivial

/-- A type without a law (a packed union field) is left alone, and its failed derivation logs no
error into the proof that meets it (at the top level, with error recovery on). -/
theorem wrap_left (x : BitVec 9) (h : Packed.toBits (Packed.ofBits x : Wrap) = x) :
    Packed.toBits (Packed.ofBits x : Wrap) = x := by
  fsym_arith

end SepAuto.Packed
