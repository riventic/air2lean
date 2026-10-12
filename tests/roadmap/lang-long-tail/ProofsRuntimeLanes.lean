import LangLongTail.RuntimeLanes
import ZigLean.VecMem

/-!
# L09: runtime-index lane stores, on the retained translation

`LangLongTail.RuntimeLanes` is the translation of `air/runtime_lanes/0.15.2` (Zig 0.14.1 and
0.15.2 lower `v[i] = x` with a runtime `i` to `vector_store_elem`; 0.16.0 rejects the source).
For every index, the translated store is the safety check and then the store through the
comptime lane pointer of lane `i` (`Zig.storeLane` at bit `9 i`), so the lane theorems of
`ZigLean/VecMem.lean` (`Vec.storeLane_vec`, `Vec.load_storeLane_vec`: lane `i` becomes `x`,
every other lane and the padding keep their bits) hold for it.
-/

open RuntimeLanes Zig

namespace RuntimeLanesClients

/-- For an index inside the vector, the translated store runs as the lane store at bit `9 i`. -/
theorem setU9_run (p : Ptr) (i : BitVec 64) (x : BitVec 9) (m : Mem) (h : i.toNat < 4) :
    (setU9 p i x).run m = (storeLane 5 8 (i.toNat * 9) p x).run m := by
  have hl : Zig.lt false i (4 : BitVec 64) = true := by simp [Zig.lt, BitVec.ult, h]
  simp only [setU9, hl, storeLaneAt_lt (w := 9) x h, zig_unfold]
  simp only [bind, StateT.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure,
    StateT.pure, ExceptT.pure, StateT.lift, ite_true]
  rcases hs : storeLane 5 8 (i.toNat * 9) p x m with _ | ⟨_ | ⟨⟨⟩, m'⟩⟩ <;> rfl

/-- An index past the lanes is the `outOfBounds` safety panic; memory is not touched. -/
theorem setU9_oob (p : Ptr) (i : BitVec 64) (x : BitVec 9) (m : Mem) (h : 4 ≤ i.toNat) :
    (setU9 p i x).run m = some (.error .outOfBounds) := by
  have hl : Zig.lt false i (4 : BitVec 64) = false := by simp [Zig.lt, BitVec.ult]; omega
  simp only [setU9, hl, zig_unfold]
  rfl

end RuntimeLanesClients
