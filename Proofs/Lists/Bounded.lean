import Proofs.Lists.Cost
import ZigLean.Sep.Bounded

/-!
# Resource-bounded total correctness for `examples/lists/lists.zig` (P05)

`sum_loop_within`: the generated loop of `sum` over a list of `xs.length` items exits within
`xs.length + 1` body runs (`TotalTripleWithin`, counted by P06's `LoopRuns`) with the sum in its
locals and the list unchanged. `sum_loop_total` is the total triple it implies.
`sum_loop_not_within` shows the bound is tight: the bound `xs.length` is refuted by any list
satisfying the precondition. `sum_total` is the function-level total triple for `sum`.

The bound counts loop-body runs of the model; it is not CPU time.
-/

namespace Lists
open Zig Assn

/-- `sum`'s translated loop exits within `xs.length + 1` body runs, with the sum. -/
theorem sum_loop_within (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) :
    TotalTripleWithin (xs.length + 1) (list hd xs) sum.loop6 sum.again6 (sumStart hd)
      (fun e s => ⌜e = .br5 ∧ s.s = BitVec.ofNat 64 (xs.map BitVec.toNat).sum⌝ ∗ list hd xs) := by
  intro m h hF hdj hm hl hst
  obtain ⟨e, s', m', hrun, he, hs, hH, hst', -⟩ :=
    loopRuns_exact sum.loop6 sum.again6 (sumInv m (xs.map BitVec.toNat).sum)
      (fun e s m' => e = .br5 ∧ s.s.toNat = (xs.map BitVec.toNat).sum ∧ m'.heap = m.heap ∧
        m'.Seq ∧ m.SameAllocs m')
      (sum_count_step m _ htot) (sumStart hd) m xs.length
      ⟨rfl, hst, .refl m, xs, h, hF, rfl, hdj, hm, hl, by simp⟩
  refine ⟨xs.length + 1, e, s', m', h, Nat.le_refl _, hrun, hdj, by rw [hH, hm],
    sep_lift.mpr ⟨⟨he, ?_⟩, hl⟩, hst'⟩
  apply BitVec.eq_of_toNat_eq
  rw [hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htot]

/-- Bounded implies total: the loop returns, with the sum. -/
theorem sum_loop_total (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) :
    TotalTriple (list hd xs) ((Zig.loop sum.loop6 sum.again6).run (sumStart hd))
      (fun r => ⌜r.1 = .br5 ∧ r.2.s = BitVec.ofNat 64 (xs.map BitVec.toNat).sum⌝ ∗ list hd xs) :=
  (sum_loop_within hd xs htot).toTotal

/-- The bound is tight: from any list satisfying the precondition, `xs.length` body runs do not
suffice, whatever the postcondition. -/
theorem sum_loop_not_within (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) {m : Mem} {h hF : Heap} (hl : list hd xs h)
    (hm : m.heap = h ∪ hF) (hdj : Heap.Disjoint h hF) (hst : m.Seq) (Q : sumExit → sumLocals → Assn) :
    ¬ TotalTripleWithin xs.length (list hd xs) sum.loop6 sum.again6 (sumStart hd) Q := by
  obtain ⟨k, e, s', m', _, -, hk, -⟩ := sum_loop_within hd xs htot m h hF hdj hm hl hst
  have := sum_count_unique hd xs hl hm hdj hst htot hk
  exact TotalTripleWithin.not_within_of_count hdj hm hl hst hk (by omega)

/-- `sum` returns the sum and leaves the list unchanged. -/
theorem sum_total (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) :
    TotalTriple (list hd xs) (sum hd)
      (fun r => ⌜r = BitVec.ofNat 64 (xs.map BitVec.toNat).sum⌝ ∗ list hd xs) := by
  intro m h hF hdj hm hl hst
  obtain ⟨_, m', -, hr, -, hH, hst'⟩ := sum_cost hd xs hl hm hdj hst htot
  exact ⟨_, m', h, hr, hdj, by rw [hH, hm], sep_lift.mpr ⟨rfl, hl⟩, hst'⟩

end Lists
