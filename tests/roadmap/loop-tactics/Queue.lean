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
    FTotalTriple (list hd xs) (sum hd)
      (fun r => ⟪r.toNat = (xs.map BitVec.toNat).sum⟫ ⋆ list hd xs) :=
  have htot := sum_toNat_lt (k := 32) xs hlen
  (Linked.sum_total hd xs htot).post fun _ _ h => by
    obtain ⟨hr, hl⟩ := Full.sep_lift.mp h
    exact Full.sep_lift.mpr ⟨by simp [hr, Nat.mod_eq_of_lt htot], hl⟩

end Lists.Queue

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'Lists.Queue.sum_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lists.Queue.sum_total
