import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Auto

/-!
# Typed values in the full-state logic (`ZigLean/Sep/Full/Typed.lean`), library-only

A struct `Pt` laid out like a generated one (`x` at 0, `y` at 2): `fsym` reads and writes its
fields with the field rules, the field values given; a write through the bytes view; the payload
of an error union through its payload pointer (`@[fsym]`, nothing given); a read-only field of a
`const` value.
-/

namespace OneLogic.Typed

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

structure Pt where
  x : BitVec 16
  y : BitVec 16

instance : Enc Pt where
  size := 4
  align := 2
  encode v := Enc.fields 4 [(0, Enc.encode v.x), (2, Enc.encode v.y)]
  decode bs := do pure { x := ← Enc.decodeAt bs 0, y := ← Enc.decodeAt bs 2 }

/-- The fields of the bytes of a `Pt`. -/
theorem Pt.decode_fields {bs : Array Byte} {s : Pt} (h : Enc.decode bs = pure s) :
    Enc.decodeAt bs 0 = pure s.x ∧ Enc.decodeAt bs 2 = pure s.y := by
  obtain ⟨x, hx, h⟩ := result_bind_eq_pure h
  obtain ⟨y, hy, h⟩ := result_bind_eq_pure h
  have e : (⟨x, y⟩ : Pt) = s := by
    have := congrArg (fun r : Result Pt => r.run) h
    simpa [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using this
  subst e
  exact ⟨hx, hy⟩

/-- `p.y` -/
def getY (p : Ptr) : MemM (BitVec 16) := Zig.load (BitVec 16) 2 (p.add 2)

theorem getY_spec (p : Ptr) (s : Pt) :
    FTotalTriple (up (pts p 2 s)) (getY p) (fun r => ⟪r = s.y⟫ ⋆ up (pts p 2 s)) := by
  unfold getY
  fsym [FTotalTriple.field_load (T := Pt) (k := 2) (s := s) (v := s.y)
    (hv := fun _ _ h => (Pt.decode_fields h).2)]

/-- The bytes of a `Pt` with a new `x`. -/
theorem Pt.decode_setX {bs : Array Byte} {s : Pt} (hs : bs.size = Enc.size Pt)
    (h : Enc.decode bs = pure s) (x : BitVec 16) :
    Enc.decode (writeBytes bs 0 (Enc.encode x)) = pure (Pt.mk x s.y) := by
  have hw : (Enc.encode x).size = 2 := LawfulEnc.size_encode _
  have hs4 : bs.size = 4 := hs
  have e0 := extract_writeBytes bs 0 (Enc.encode x) (by omega)
  have e2 := extract_writeBytes_disjoint bs 0 (Enc.encode x) 2 2 (by omega) (by omega) (by omega)
  rw [hw] at e0
  have h2 := (Pt.decode_fields h).2
  show (do pure { x := ← Enc.decodeAt _ 0, y := ← Enc.decodeAt _ 2 } : Result Pt) = _
  simp only [Enc.decodeAt] at h2 ⊢
  rw [show (0 : Nat) + Enc.size (BitVec 16) = 0 + 2 from rfl, e0,
    show (2 : Nat) + Enc.size (BitVec 16) = 2 + 2 from rfl, e2, LawfulEnc.decode_encode]
  rw [show (2 : Nat) + Enc.size (BitVec 16) = 2 + 2 from rfl] at h2
  rw [h2]; rfl

/-- `p.x = p.y` -/
def copyYX (p : Ptr) : MemM Unit := do
  let v ← Zig.load (BitVec 16) 2 (p.add 2)
  Zig.store 2 p v

theorem copyYX_spec (p : Ptr) (s : Pt) :
    FTotalTriple (up (pts p 2 s)) (copyYX p) (fun _ => up (pts p 2 (Pt.mk s.y s.y))) := by
  unfold copyYX
  fsym [FTotalTriple.field_load (T := Pt) (k := 2) (s := s) (v := s.y)
      (hv := fun _ _ h => (Pt.decode_fields h).2),
    FTotalTriple.field_store0 (T := Pt) (s := s) (s' := Pt.mk s.y s.y) s.y
      (hw := fun _ hs h => Pt.decode_setX hs h s.y)]

/-- The bytes view: a write of both fields, whatever the bytes held before. -/
def setPt (p : Ptr) (x y : BitVec 16) : MemM Unit := do
  Zig.store 2 (p.add 2) y
  Zig.store 2 p x

theorem setPt_spec (p : Ptr) (bs : Array Byte) (x y : BitVec 16) (hs : bs.size = 4) :
    FTotalTriple (up (region p 2 bs)) (setPt p x y)
      (fun _ => up (region p 2 (writeBytes (writeBytes bs 2 (Enc.encode y)) 0 (Enc.encode x)))) := by
  unfold setPt
  fsym

/-- The payload of an error union that holds a value, through its payload pointer. -/
def bumpOk (p : Ptr) : MemM Unit := do
  let v ← Zig.load (BitVec 8) 1 (errPayloadPtr (BitVec 8) p)
  Zig.store 1 (errPayloadPtr (BitVec 8) p) (v + 1)

theorem bumpOk_spec (p : Ptr) (x : BitVec 8) :
    FTotalTriple (up (pts p 2 (Except.ok x : Except ErrName (BitVec 8)))) (bumpOk p)
      (fun _ => up (pts p 2 (Except.ok (x + 1) : Except ErrName (BitVec 8)))) := by
  unfold bumpOk
  fsym

/-- A field of a read-only `Pt`. -/
theorem cgetY_spec (p : Ptr) (s : Pt) :
    FTotalTriple (cpts p 2 s) (getY p) (fun r => ⟪r = s.y⟫ ⋆ cpts p 2 s) := by
  unfold getY
  fsym [FTotalTriple.cfield_load (T := Pt) (k := 2) (s := s) (v := s.y)
    (hv := fun _ _ h => (Pt.decode_fields h).2)]

end OneLogic.Typed
