import Proofs.Lists.Linked

/-!
# Step bounds for `examples/lists/lists.zig` (P05)

The translator puts a step (`Zig.tick`) at every run of a loop body, and a step needs a credit or
the plain mode (`docs/sep-full-state.md` §Step ticks). `Lists.Linked.sum_loop_exact` and
`Lists.Linked.sum_exact` state the cost of `sum` exactly: over a list of `xs.length` items it pays
`xs.length + 1` credits (one per node and the final null test) and returns as many receipts.
This file shows that the bound is tight:

* `sum_loop_not_within`, `sum_not_within`: from any credit-free start (`CreditFree`) that holds
  the list, `xs.length` credits do not pay the loop or the function, whatever the postcondition
  (`FTotalTriple.not_fewer_credits`).
* `sum_steps`: the same start runs `sum` to the sum of the items in exactly `xs.length + 1`
  steps, and the final memory's live bytes are the untouched frame and a part that holds the same
  list (`FTotalTriple.ticks_eq_post`).

The bound counts steps of the model, not CPU time. The plain-mode statements of `sum` and its loop
follow from the cost statements (`FTotalTriple.of_credits_plain`).
-/

namespace Lists.Linked
open Zig Zig.Full Zig.Full.FAssn Lists.Open

variable {X : Ptr → FAssn}

/-- **The loop bound is tight**: from any credit-free start that holds the list, `xs.length`
credits do not pay `sum`'s loop, whatever the postcondition. -/
theorem sum_loop_not_within {mb : Lean.Order.MonoBind (MM sumLocals)} (hd : Option Ptr)
    (xs : List (BitVec 32)) (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) (s : sumLocals)
    (hs : s.s = 0) (hp : s.p = hd) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hl : list X hd xs r) (hseq : m.FSeq) (hc : CreditFree r rF) (Q : sumExit × sumLocals → FAssn) :
    ¬ FTotalTriple (list X hd xs ⋆ credits xs.length)
      ((@Zig.loop (MM sumLocals) _ _ mb _ sum.loop6 sum.again6).run s) Q :=
  FTotalTriple.not_fewer_credits (sum_loop_exact hd xs htot s hs hp) (Nat.lt_succ_self _) hh hl
    hseq hc

/-- **The bound of `sum` is tight**: from any credit-free start that holds the list, `xs.length`
credits do not pay `sum`, whatever the postcondition. -/
theorem sum_not_within (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hl : list X hd xs r) (hseq : m.FSeq) (hc : CreditFree r rF) (Q : BitVec 64 → FAssn) :
    ¬ FTotalTriple (list X hd xs ⋆ credits xs.length) (sum hd) Q :=
  FTotalTriple.not_fewer_credits (sum_exact hd xs htot) (Nat.lt_succ_self _) hh hl hseq hc

/-- **`sum` runs exactly `xs.length + 1` steps**: from any credit-free start `m` that holds the
list (`r`) and a frame `rF`, `sum` returns the sum of the items after exactly that many steps, and
the live bytes of its final memory are the frame's and a part `r'` that holds the same list
(`FMatch`: the frame's bytes are untouched). -/
theorem sum_steps (hd : Option Ptr) (xs : List (BitVec 32))
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hl : list X hd xs r) (hseq : m.FSeq) (hc : CreditFree r rF) :
    ∃ m', (sum hd).run m = pure (BitVec.ofNat 64 (xs.map BitVec.toNat).sum, m') ∧
      m'.ticks = m.ticks + (xs.length + 1) ∧ ∃ r', FHeap.Disjoint r'.heap rF.heap ∧
        SMatch m' (r'.heap ∪ rF.heap) (r'.gh.add rF.gh).share ∧ list X hd xs r' ∧ m'.FSeq := by
  obtain ⟨v, m', hr, ht, r', hd', hm, hq, hs'⟩ := (sum_exact hd xs htot).ticks_eq_post hh hl hseq hc
  obtain ⟨rfl, hl'⟩ := sep_lift.mp hq
  exact ⟨m', hr, ht, r', hd', hm, hl', hs'⟩

end Lists.Linked
