import ZigLean.Sep.Full.AutoAll
import Proofs.Basic.Gen
import Proofs.Pointers.Gen
import Proofs.Errors.Gen

/-!
Verification conditions (P02, `docs/vcs.md`) of committed generated code: `Proofs/Basic/Gen.lean`,
`Proofs/Pointers/Gen.lean` and `Proofs/Errors/Gen.lean`, generated from `examples/`. A contract is
a full-state triple of the generated function (of its lifted program for a pure `Result`
function), and its obligations are the goals that the walk of `fsym` over the generated body
leaves; `fsym.report` gives each its origin. Nothing here is written by hand except the
statements and the closing of the obligations.
-/

namespace VCExtract

open Zig Zig.Full FAssn VC

/-! ## A contracted loop-free function receives complete obligations

The walk discharges the safety obligation of `tardiness` (the `sub` precondition, from the branch
condition) and its result obligations, so its report is complete. `FTotalTriple.result_spec`
gives the `Result` contract. -/

/-- info: fsym-report {"residuals":[],"schemaVersion":1,"status":"complete"} -/
#guard_msgs in
theorem tardiness_total (a b : BitVec 32) :
    FTotalTriple emp (StateT.lift (Basic.tardiness a b) : MemM (BitVec 32))
      (fun v => ⟪v.toNat = a.toNat - b.toNat⟫) := by
  set_option fsym.report true in fsym

theorem tardiness_contract (a b : BitVec 32) :
    ∃ v, Basic.tardiness a b = pure v ∧ v.toNat = a.toNat - b.toNat :=
  (tardiness_total a b).result_spec

/-! ## A wrong contract leaves an unprovable obligation

The contract `v = a - b` forgets the saturation at zero. The walk does not repair it: exactly the
non-taken branch remains. -/

/--
error: unsolved goals
a b : BitVec 32
hc : ¬gt false a b = true
⊢ 0#32 = a - b
-/
#guard_msgs in
example (a b : BitVec 32) :
    FTotalTriple emp (StateT.lift (Basic.tardiness a b) : MemM (BitVec 32))
      (fun v => ⟪v = a - b⟫) := by
  fsym

-- That remaining obligation is false (a = 1, b = 2), so this contract has no proof at all.
theorem wrong_obligation_false :
    ¬ ∀ a b : BitVec 32, ¬ gt false a b = true → (0 : BitVec 32) = a - b := by
  intro h
  exact absurd (h 1 2 (by decide)) (by decide)

theorem wrong_contract_false :
    ¬ ∀ a b : BitVec 32, ∃ v, Basic.tardiness a b = pure v ∧ v = a - b := by
  intro h
  obtain ⟨v, hv, he⟩ := h 1 2
  have hrun : Basic.tardiness 1 2 = pure 0 := rfl
  rw [hrun] at hv
  cases hv
  exact absurd he (by decide)

/-! ## Compositional calls use proved contracts

`fsym [tardiness_total]` executes the call of `tardiness` by its contract: its result is a fact
(`x✝¹` below), not its body. Without bounds, the obligations of `weightedTardiness` are the
overflow of its `add` and its `mul` (`rule_premise`) and its result at the return
(`postcondition`). The `mul` bound is undecided, so it is split (`hc`). -/

/--
info: fsym-report {"residuals":[{"goal":{"head":"Eq","text":"(x✝² * x).toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat"},"index":0,"origin":{"condition":"postcondition","judgment":"Zig.Full.FLogic.T","program":{"head":"Pure.pure","text":"pure (x✝² * x)"},"reason":"postcondition_not_proved","rule":{"head":"Zig.Full.Auto.ret","text":"Auto.ret"},"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T emp (pure (x✝² * x)) fun r => ⟪r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat⟫"}}},{"goal":{"head":"LT.lt","text":"x✝².toNat * x.toNat < 2 ^ 32"},"index":1,"origin":{"condition":"rule_premise","judgment":"Zig.Full.FLogic.T","program":{"head":"StateT.lift","text":"StateT.lift (mul false x✝² x)"},"reason":"side_condition_not_proved","rule":{"head":"Zig.VC.Prim.mul_unsigned_step","text":"@Prim.mul_unsigned_step"},"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T emp\n  (StateT.lift (mul false x✝² x) >>= fun x =>\n    (StateT.lift do\n        let e ←\n          (fun x => x.fst) <$> do\n              let p ← pure (x, default)\n              StateT.run (pure (Basic.weightedTardinessExit.ret p.fst)) p.snd\n        match e with\n          | Basic.weightedTardinessExit.ret v => pure v) >>=\n      pure)\n  fun r => ⟪r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat⟫"}}},{"goal":{"head":"Eq","text":"(x✝² * x).toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat"},"index":2,"origin":{"condition":"postcondition","judgment":"Zig.Full.FLogic.T","program":{"head":"Pure.pure","text":"pure (x✝² * x)"},"reason":"postcondition_not_proved","rule":{"head":"Zig.Full.Auto.ret","text":"Auto.ret"},"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T emp (pure (x✝² * x)) fun r => ⟪r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat⟫"}}},{"goal":{"head":"LT.lt","text":"start.toNat + j.duration.toNat < 2 ^ 32"},"index":3,"origin":{"condition":"rule_premise","judgment":"Zig.Full.FLogic.T","program":{"head":"StateT.lift","text":"StateT.lift (add false start j.duration)"},"reason":"side_condition_not_proved","rule":{"head":"Zig.Full.Auto.add_step","text":"@Auto.add_step"},"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T emp\n  (StateT.lift (add false start j.duration) >>= fun x =>\n    (StateT.lift do\n        let e ←\n          (fun x => x.fst) <$> do\n              let p ← pure (x, default)\n              StateT.run\n                  (do\n                    let i4 ← pure j.due\n                    let i5 ← call (Basic.tardiness p.fst i4)\n                    let i6 ← pure j.weight\n                    let i7 ← liftM (intCast false false 32 i6 false)\n                    let i8 ← liftM (mul false i5 i7)\n                    pure (Basic.weightedTardinessExit.ret i8))\n                  p.snd\n        match e with\n          | Basic.weightedTardinessExit.ret v => pure v) >>=\n      pure)\n  fun r => ⟪r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat⟫"}}}],"schemaVersion":1,"status":"stopped"}
-/
#guard_msgs (drop error) in
example (j : Basic.Job) (start : BitVec 32) :
    FTotalTriple emp (StateT.lift (Basic.weightedTardiness j start) : MemM (BitVec 32))
      (fun r => ⟪r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat⟫) := by
  set_option fsym.report true in fsym [tardiness_total]

-- The same statement as `Proofs/Basic/Proofs.lean`'s `weightedTardiness_ok`, from its VCs.
theorem weightedTardiness_contract (j : Basic.Job) (start : BitVec 32)
    (h1 : start.toNat + j.duration.toNat < 2 ^ 32)
    (h2 : (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat < 2 ^ 32) :
    ∃ r, Basic.weightedTardiness j start = pure r ∧
      r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat := by
  refine FTotalTriple.result_spec ?_
  fsym [tardiness_total]
  all_goals simp_all [BitVec.toNat_mul, Nat.mod_eq_of_lt h2]

/-! ## Error returns

A returned Zig error is an obligation of the postcondition at its return, apart from the safety
obligations. -/

theorem parseDigit_total (c : BitVec 8) :
    FTotalTriple emp (StateT.lift (Errors.parseDigit c) : MemM _)
      (fun v => ⟪v = if c.toNat < 48 ∨ 57 < c.toNat then .error "NotDigit" else .ok (c - 48)⟫) := by
  fsym
  all_goals (simp_all [Zig.lt, Zig.gt, BitVec.ult]; try bv_omega)

theorem parseDigit_contract (c : BitVec 8) :
    ∃ v, Errors.parseDigit c = pure v ∧
      v = if c.toNat < 48 ∨ 57 < c.toNat then .error "NotDigit" else .ok (c - 48) :=
  (parseDigit_total c).result_spec

-- `catch 0`: the callee's error return is consumed through the checked unwrap primitives.
theorem digitOrZero_contract (c : BitVec 8) :
    ∃ v, Errors.digitOrZero c = pure v ∧
      v = if c.toNat < 48 ∨ 57 < c.toNat then 0 else c - 48 := by
  refine FTotalTriple.result_spec ?_
  set_option fsym.report true in fsym [parseDigit_total]
  all_goals trace_state
  all_goals sorry

/-! ## Memory effects

Here the walk discharges every obligation: overflow from `fits`, ownership and the heap
postcondition by the planner.

Each contract has a strength example (`ZigLean/Sep/Full/Strength.lean`): the legacy statement that
it replaces, on every `Mem.FSeqPlain` memory (the memories a run reaches, `Mem.init_fseq`, no
stack budget), and total instead of partial. The examples are in
`tests/roadmap/strength-log/Vcs.lean`. -/

section Memory

theorem addTo_contract (p : Ptr) (delta : BitVec 32) (old : BitVec 64)
    (fits : old.toNat + (delta.setWidth 64).toNat < 2 ^ 64) :
    FTotalTriple (up (pts p 8 old)) (Pointers.addTo p delta)
      (fun _ => up (pts p 8 (old + delta.setWidth 64))) := by
  fsym

-- The frame rule preserves a separate client resource.
example (p : Ptr) (delta : BitVec 32) (old : BitVec 64) (R : FAssn)
    (fits : old.toNat + (delta.setWidth 64).toNat < 2 ^ 64) :
    FTotalTriple (up (pts p 8 old) ⋆ R) (Pointers.addTo p delta)
      (fun _ => up (pts p 8 (old + delta.setWidth 64)) ⋆ R) :=
  (addTo_contract p delta old fits).frame

-- Two cells: the planner splits the heap, so `swap p q` needs no separate ownership proof.
theorem swap_contract (p q : Ptr) (x y : BitVec 32) :
    FTotalTriple (up (pts p 4 x) ⋆ up (pts q 4 y)) (Pointers.swap p q)
      (fun _ => up (pts p 4 y) ⋆ up (pts q 4 x)) := by
  fsym

-- The same function on one cell (`Proofs/Pointers/Sep.lean` proves it with explicit memories).
theorem swapSelf_contract (p : Ptr) (old : BitVec 32) :
    FTotalTriple (up (pts p 4 old)) (Pointers.swap p p) (fun _ => up (pts p 4 old)) := by
  fsym

-- A functional result next to the heap effect. Pointer `==` compares addresses
-- (`ptrEqAddr_raw`): two provenance-free pointers are equal iff their addresses are.
theorem same_contract (p q : Ptr) :
    FTotalTriple ⟪p.block = none ∧ q.block = none⟫ (Pointers.same p q)
      (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ emp) := by
  fsym

/-! Mutated contracts: each leaves an obligation that the walk cannot close. -/

/-- The overflow bound dropped. -/
example (p : Ptr) (delta : BitVec 32) (old : BitVec 64) : True := by
  fail_if_success
    have : FTotalTriple (up (pts p 8 old)) (Pointers.addTo p delta)
        (fun _ => up (pts p 8 (old + delta.setWidth 64))) := by
      fsym
  trivial

/-- The cells not swapped. -/
example (p q : Ptr) (x y : BitVec 32) : True := by
  fail_if_success
    have : FTotalTriple (up (pts p 4 x) ⋆ up (pts q 4 y)) (Pointers.swap p q)
        (fun _ => up (pts p 4 x) ⋆ up (pts q 4 y)) := by
      fsym
  trivial

/-- The provenance premise dropped: pointers into blocks are not compared by address. -/
example (p q : Ptr) : True := by
  fail_if_success
    have : FTotalTriple emp (Pointers.same p q) (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ emp) := by
      fsym
  trivial

end Memory

/-! ## Loops request explicit invariants and variants; recursion needs a measure

The walk guesses no invariant: it stops at a generated loop, which is left as the request. It is
proved with the loop rules of `ZigLean/Sep/Full/Loop.lean` (`FTotalTriple.loop_ghost`,
`FTriple.loop`) and then given to callers as a contract. -/

#guard_msgs (drop error) in
example (xs : Array (BitVec 32)) :
    FTotalTriple emp (StateT.lift (Basic.sum xs) : MemM (BitVec 64)) (fun _ => ⟪True⟫) := by
  fsym

#guard_msgs (drop error) in
example (n : BitVec 32) : FTriple plain (Pointers.sumTo n) (fun _ => plain) := by
  fsym

-- A recursive function is not unfolded: its call needs a contract proved by
-- `FTotalTriple.rec_group` with a measure (`Proofs/Pointers/Sep.lean`, `addDown_total`).
/--
info: fsym: no rule for the command
  Pointers.addDown p n
with the precondition
  up (pts p 8 x)
-/
#guard_msgs (drop error) in
example (p : Ptr) (n : BitVec 32) (x : BitVec 64) :
    FTotalTriple (up (pts p 8 x)) (Pointers.addDown p n) (fun _ => up (pts p 8 x)) := by
  fsym

end VCExtract
