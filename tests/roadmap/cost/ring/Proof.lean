import Ring.Gen
import ZigLean.Sep.CostRuns
import ZigLean.Range

/-!
# A queue-operation bound (P06): draining a ring buffer

`ring.zig` is a ring-buffer queue of `u32` with capacity 8: the buffer `buf`, the index `head` of
the oldest item and the item count `len`. `Ring/Gen.lean` is its retained Zig 0.17.0
translation. `drain` pops every item and returns their sum, one loop iteration per item.

* `step`: the loop body as a `LoopTemplate` (P03) with the ghost measure `len`, proved by
  `sep_unfold`/`sep_steps` on the generated body. The module supplies the invariant (the
  remaining items and the running sum) and the facts of the checked operations.
* `drain_within`: under the capacity premises `head < 8` and `len ≤ 8`, the loop exits within
  `len + 1` body runs (`TotalTripleWithin`, the unit of `LoopRuns`), and so within `cap + 1 = 9`
  for every queue (`drain_within_cap`). The capacity premise also rules out the overflow of the
  sum: at most 8 items of `u32` (`ringSum_lt`).
* `drain_fails`: a corrupted queue (`head ≥ 8`, `len ≠ 0`) fails with `.outOfBounds` at the first
  body run (`FailsWithin 1`), walked by `sep_steps` on the same generated body, and has no
  bounded triple at all (`drain_corrupt_not_within`).

The counts are model counts (SEM-05), not time.
-/

open Zig Assn

namespace RingCost

/-- The sum of the `l` items of the ring `xs` from index `h`. -/
def ringSum (xs : List (BitVec 32)) (h : Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => (xs[h % 8]?.getD 0).toNat + ringSum xs ((h + 1) % 8) l

theorem ringSum_le (xs : List (BitVec 32)) : ∀ (l h : Nat), ringSum xs h l ≤ l * (2 ^ 32 - 1)
  | 0, _ => by simp [ringSum]
  | l + 1, h => by
    have := ringSum_le xs l ((h + 1) % 8)
    have hx : (xs[h % 8]?.getD 0).toNat < 2 ^ 32 := BitVec.isLt _
    simp only [ringSum]
    rw [Nat.succ_mul]; omega

/-- At most 8 items of `u32`: the sum fits in 40 bits. -/
theorem ringSum_lt (xs : List (BitVec 32)) (h l : Nat) (hl : l ≤ 8) : ringSum xs h l < 2 ^ 40 := by
  have := ringSum_le xs l h
  have : l * (2 ^ 32 - 1) ≤ 8 * (2 ^ 32 - 1) := Nat.mul_le_mul_right _ hl
  omega

/-- The invariant at the ghost measure `n = len`: the sum so far plus the items left is `T`. -/
def inv (p0 p1 p2 : Ptr) (xs : List (BitVec 32)) (T : Nat) (s : Ring.drainLocals) (n : Nat) : Assn :=
  Assn.ex fun (h : BitVec 32) => Assn.ex fun (l : BitVec 32) =>
    ⌜n = l.toNat ∧ h.toNat < 8 ∧ l.toNat ≤ 8 ∧ s.sum.toNat + ringSum xs h.toNat l.toNat = T ∧ T < 2 ^ 40⌝ ∗
      (arr p0 xs ∗ (pts p1 4 h ∗ pts p2 4 l))

/-- The exit: the queue is empty and the sum is `T`. -/
def post (p0 p1 p2 : Ptr) (xs : List (BitVec 32)) (T : Nat) (e : Ring.drainExit) (s : Ring.drainLocals) : Assn :=
  Assn.ex fun (h : BitVec 32) =>
    ⌜e = .br5 ∧ s.sum.toNat = T⌝ ∗ (arr p0 xs ∗ (pts p1 4 h ∗ pts p2 4 (0 : BitVec 32)))

theorem step (p0 p1 p2 : Ptr) (xs : List (BitVec 32)) (hxs : xs.length = 8) (T : Nat) :
    LoopTemplate (Ring.drain.loop6 p0 p1 p2) Ring.drain.again6 (inv p0 p1 p2 xs T) (post p0 p1 p2 xs T) := by
  constructor
  intro s n
  unfold inv
  sep_intro h l hfacts
  obtain ⟨rfl, hh, hl, hsum, hT⟩ := hfacts
  sep_unfold [Ring.drain.loop6]
  sep_step
  have hw : (h.setWidth 64).toNat = h.toNat := Zig.toNat_setWidth_of_le (by decide)
  by_cases hl0 : l = 0
  · -- The queue is empty: the loop exits.
    subst hl0
    sep_unfold
    sep_ret
    intro hp hpre
    refine loopNext_exit rfl ⟨h, ?_⟩
    sep_close hpre
  · have hl0' : (l != 0) = true := by simpa using hl0
    have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl0 (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hidx : (h.setWidth 64).toNat < xs.length := by rw [hw, hxs]; exact hh
    have hlt : (h.setWidth 64).toNat < 8 := by rw [hw]; exact hh
    -- The facts of the checked operations of one iteration.
    have hT' : s.sum.toNat + ringSum xs h.toNat l.toNat < 2 ^ 40 := by omega
    have hring : ringSum xs h.toNat l.toNat =
        (xs[h.toNat % 8]?.getD 0).toNat + ringSum xs ((h.toNat + 1) % 8) (l.toNat - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by omega⟩
      rw [hk]; rfl
    have hget : (xs[h.toNat % 8]?.getD 0) = xs[(h.setWidth 64).toNat]'hidx := by
      rw [Nat.mod_eq_of_lt hh]; simp [hw, List.getElem?_eq_getElem (show h.toNat < xs.length by omega)]
    have hxw : ((xs[(h.setWidth 64).toNat]'hidx).setWidth 64).toNat = (xs[(h.setWidth 64).toNat]'hidx).toNat :=
      Zig.toNat_setWidth_of_le (by decide)
    have hadd : Zig.add false s.sum ((xs[(h.setWidth 64).toNat]'hidx).setWidth 64) =
        pure (s.sum + (xs[(h.setWidth 64).toNat]'hidx).setWidth 64) :=
      Zig.add_unsigned_of_lt (by rw [hxw, ← hget]; omega)
    have hadd1 : Zig.add false h 1 = pure (h + 1) := Zig.add_unsigned_of_lt (by simp; omega)
    have hrem : Zig.rem false (h + 1) 8 = pure ((h + 1).umod 8) := by simp [Zig.rem]
    have hsub : Zig.sub false l 1 = pure (l - 1) := Zig.sub_unsigned_of_le (by simp; omega)
    sep_unfold [hl0']
    sep_steps [hl0', Zig.intCast_unsigned_widen h 64 (by decide), hlt, Zig.intCast_unsigned_widen (xs[(h.setWidth 64).toNat]'hidx) 64 (by decide), hadd, hadd1, hrem, hsub]
    sep_ret
    intro hp hpre
    have hl1 : (l - 1).toNat = l.toNat - 1 := Zig.toNat_sub_one l hl0
    refine loopNext_repeat rfl (n' := (l - 1).toNat) (by rw [hl1]; omega) ⟨(h + 1).umod 8, l - 1, ?_⟩
    have hh1 : ((h + 1).umod 8).toNat = (h.toNat + 1) % 8 := by
      show ((h + 1) % 8).toNat = _; rw [BitVec.toNat_umod, Zig.toNat_add_of_lt (by simp; omega)]; simp
    sep_close hpre
    · exact ⟨rfl, by rw [hh1]; omega, by rw [hl1]; omega, by
        rw [hh1, hl1, Zig.toNat_add_of_lt (by rw [hxw, ← hget]; omega), hxw, ← hget]; omega, hT⟩
/-- Under the capacity premises the loop exits within `len + 1` body runs with the sum of the
queue's items. -/
theorem drain_within (p0 p1 p2 : Ptr) (xs : List (BitVec 32)) (hxs : xs.length = 8)
    (h l : BitVec 32) (hh : h.toNat < 8) (hl : l.toNat ≤ 8) :
    TotalTripleWithin (l.toNat + 1) (arr p0 xs ∗ (pts p1 4 h ∗ pts p2 4 l))
      (Ring.drain.loop6 p0 p1 p2) Ring.drain.again6 { sum := 0 }
      (post p0 p1 p2 xs (ringSum xs h.toNat l.toNat)) :=
  (TotalTripleWithin.of_template (step p0 p1 p2 xs hxs _) _ _).conseq
    (fun hp hpre => ⟨h, l, sep_lift.mpr ⟨⟨rfl, hh, hl, by simp, ringSum_lt xs _ _ hl⟩, hpre⟩⟩)
    (fun _ _ _ hq => hq)

/-- The capacity bound: every queue drains within `cap + 1 = 9` body runs. -/
theorem drain_within_cap (p0 p1 p2 : Ptr) (xs : List (BitVec 32)) (hxs : xs.length = 8)
    (h l : BitVec 32) (hh : h.toNat < 8) (hl : l.toNat ≤ 8) :
    TotalTripleWithin 9 (arr p0 xs ∗ (pts p1 4 h ∗ pts p2 4 l))
      (Ring.drain.loop6 p0 p1 p2) Ring.drain.again6 { sum := 0 }
      (post p0 p1 p2 xs (ringSum xs h.toNat l.toNat)) :=
  (drain_within p0 p1 p2 xs hxs h l hh hl).mono (by omega)

/-- A corrupted queue, `head ≥ 8` with an item, fails its bounds check in the first body run. -/
theorem drain_fails (p0 p1 p2 : Ptr) (xs : List (BitVec 32)) (h l : BitVec 32) (hh : 8 ≤ h.toNat)
    (hl : l ≠ 0) (s : Ring.drainLocals) :
    FailsWithin 1 (pts p2 4 l ∗ (pts p1 4 h ∗ arr p0 xs)) (Ring.drain.loop6 p0 p1 p2)
      Ring.drain.again6 s (· = .outOfBounds) := by
  refine FailsWithin.of_fails (e := .outOfBounds) ?_ rfl
  have hl0 : (l != 0) = true := by simpa using hl
  have hw : ¬ (h.setWidth 64).toNat < 8 := by
    rw [Zig.toNat_setWidth_of_le (by decide)]; omega
  sep_unfold [Ring.drain.loop6]
  sep_steps [hl0, Zig.intCast_unsigned_widen h 64 (by decide), hw]
  exact Fails.throw_bind _

/-- So it has no bounded triple, for any bound. -/
theorem drain_corrupt_not_within (p0 p1 p2 : Ptr) (xs : List (BitVec 32)) (h l : BitVec 32)
    (hh : 8 ≤ h.toNat) (hl : l ≠ 0) (s : Ring.drainLocals) {B : Nat} {Q : Ring.drainExit → Ring.drainLocals → Assn}
    {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF)
    (hp : (pts p2 4 l ∗ (pts p1 4 h ∗ arr p0 xs)) hP) (hs : m.Seq) :
    ¬ TotalTripleWithin B (pts p2 4 l ∗ (pts p1 4 h ∗ arr p0 xs)) (Ring.drain.loop6 p0 p1 p2)
      Ring.drain.again6 s Q :=
  (drain_fails p0 p1 p2 xs h l hh hl s).not_within hd hm hp hs

end RingCost

/-! ## A diverging loop: no bound of any size -/

namespace RingCost

/-- A body that always repeats: the loop never ends. -/
def spin : MM Unit Bool := pure true

theorem spin_not_within {B : Nat} {Q : Bool → Unit → Assn} {m : Mem} {hP hF : Heap}
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hs : m.Seq) :
    ¬ TotalTripleWithin B (fun _ => True) spin id () Q :=
  forever_not_within (fun _ _ => True) (fun s m _ => ⟨true, s, m, rfl, rfl, trivial⟩) hd hm trivial hs trivial

end RingCost

/-- info: 'RingCost.drain_within_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RingCost.drain_within_cap

/-- info: 'RingCost.drain_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RingCost.drain_fails
