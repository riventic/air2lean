import Proofs.Lists.Linked

/-!
# A queue traversal: an instance of `Proofs/Lists/Linked.lean`

The queue is the singly linked list of `examples/lists/lists.zig` with nodes of bare fields:
`Lists.Linked.list` at `X := fun _ => emp`. The generated `Lists.Open.sum` walks it from its head and
adds each `u32` item to a `u64` total with overflow checking. The loop proof is the generic one
(`Lists.Linked.sum_total`, `FTotalTriple.loop_ghost` walked by `fsym`); this file only
instantiates it and discharges its overflow premise from a capacity premise.

* `sum_total`: under the explicit capacity premise `xs.length ≤ 2 ^ 32`, `sum` returns (no
  overflow panic, no divergence) the exact sum and leaves the queue unchanged.

The legacy statement of the same triple on every `Mem.FSeq` memory is in
`tests/roadmap/strength-log/ProofsLists.lean`.
-/

namespace Lists.Queue
open Zig Zig.Full Zig.Full.FAssn Lists.Open

/-- The queue from `hd` holds `xs`: a list of bare nodes. -/
abbrev list (hd : Option Ptr) (xs : List (BitVec 32)) : FAssn := Linked.list (fun _ => emp) hd xs

/-- `sum` returns the exact sum of the queue's items and leaves the queue unchanged, under the
capacity premise `xs.length ≤ 2 ^ 32` (`length · (2 ^ 32 - 1) < 2 ^ 64`, `sum_toNat_lt`). -/
theorem sum_total (hd : Option Ptr) (xs : List (BitVec 32)) (hlen : xs.length ≤ 2 ^ 32) :
    FTotalTriple (list hd xs ⋆ plain) (sum hd)
      (fun r => ⟪r.toNat = (xs.map BitVec.toNat).sum⟫ ⋆ (list hd xs ⋆ plain)) :=
  have htot := sum_toNat_lt (k := 32) xs hlen
  (Linked.sum_total hd xs htot).post fun _ _ h => by
    obtain ⟨hr, hl⟩ := Full.sep_lift.mp h
    exact Full.sep_lift.mpr ⟨by simp [hr, Nat.mod_eq_of_lt htot], hl⟩

end Lists.Queue

/-! ## Designated mutants (P03, `assurance/mutation-map.json`)

The walk that proves `Lists.Linked.sum_total` (`unfold sum; fsym [listSeg_snoc_upd]`), first as a
control on the queue, then twice mutated; each mutant must be rejected:

* `queue-overflow-premise-dropped`: without the overflow premise the walk does not prove the
  triple: the generated loop's overflow check stays a residual instead of being assumed away;
* `queue-sum-off-by-one`: a postcondition one more than the queue's sum is rejected.

The CI step that elaborates this file records their kills (`scripts/mutation_kill_log.py`). -/

namespace Lists.Queue.Mutants
open Zig Zig.Full Zig.Full.FAssn Lists.Open

set_option linter.unusedVariables false

/-- Control: the generic walk with the overflow premise proves the queue's sum. -/
example (hd : Option Ptr) (xs : List (BitVec 32)) (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) :
    FTotalTriple (list hd xs ⋆ plain) (sum hd)
      (fun r => ⟪r = BitVec.ofNat 64 (xs.map BitVec.toNat).sum⟫ ⋆ (list hd xs ⋆ plain)) := by
  unfold sum
  fsym [listSeg_snoc_upd]

/-- `queue-overflow-premise-dropped`: the same walk without the overflow premise fails. -/
example (hd : Option Ptr) (xs : List (BitVec 32)) : True := by
  fail_if_success
    have : FTotalTriple (list hd xs ⋆ plain) (sum hd)
        (fun r => ⟪r = BitVec.ofNat 64 (xs.map BitVec.toNat).sum⟫ ⋆ (list hd xs ⋆ plain)) := by
      unfold sum
      fsym [listSeg_snoc_upd]
  trivial

/-- `queue-sum-off-by-one`: the same walk does not prove a sum one too large. -/
example (hd : Option Ptr) (xs : List (BitVec 32)) (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) : True := by
  fail_if_success
    have : FTotalTriple (list hd xs ⋆ plain) (sum hd)
        (fun r => ⟪r = BitVec.ofNat 64 ((xs.map BitVec.toNat).sum + 1)⟫ ⋆ (list hd xs ⋆ plain)) := by
      unfold sum
      fsym [listSeg_snoc_upd]
  trivial

end Lists.Queue.Mutants

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'Lists.Queue.sum_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lists.Queue.sum_total
