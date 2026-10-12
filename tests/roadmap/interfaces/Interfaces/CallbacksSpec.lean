import Interfaces.Callbacks
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region
import ZigLean.Sep.Full.Witness

/-!
# E02's callbacks on the interface seam (`docs/interfaces.md`)

`tests/roadmap/callbacks/callbacks.zig` with its callback type `Visitor` open
(`registry-callbacks-0.17.0.json`): a call through a `Visitor` runs the foreign `ext_visit`'s
model or `sumVisit` for their addresses, and the environment (`Ext.call0`, premise EXT-05) for
any other pointer. `evaluate` is proved once, for every callback, from the callback contract
(`∀ v, FnSpec (visitPre v) visitPost g`) of the function `g` the call runs (`Table.callOr`);
`sumVisit` meets the contract by its translated code, and the dispatch at its address does so
whatever the environment (`Table.contract_of_sel`).
-/

namespace Interfaces.CallbacksSpec

open Zig Zig.Full Zig.Full.FAssn Interfaces.Callbacks

/-- The precondition of a `Visitor` (`fn (*u32, u32) callconv(.c) bool`) call with the arguments
`a`: the `u32` its context points at holds `v` (a logical variable). -/
def visitPre (v : BitVec 32) (a : Ptr × BitVec 32) : FAssn := up (pts a.1 4 v)

/-- The postcondition: it returns `true` and changes only the `u32` its context points at. -/
def visitPost (a : Ptr × BitVec 32) (r : Bool) : FAssn :=
  ⟪r = true⟫ ⋆ FAssn.ex fun v' : BitVec 32 => up (pts a.1 4 v')

/-- The call step of the callback contract. -/
theorem visit_call {Tgt : Type} {g : Ptr × BitVec 32 → ConcM Tgt Bool}
    (h : ∀ v, FnSpec (visitPre v) visitPost g) (ctx : Ptr) (x v : BitVec 32) :
    CTriple (up (pts ctx 4 v)) (g (ctx, x))
      (fun r => ⟪r = true⟫ ⋆ FAssn.ex fun v' : BitVec 32 => up (pts ctx 4 v')) :=
  (h v).call (ctx, x)

variable [Ext]

/-- The program's functions of the `Visitor` type (`ext_visit`'s model and `sumVisit`, at their
addresses in `mem0`). -/
def targets : Table Tgt (Ptr × BitVec 32) Bool :=
  [(⟨some 1, 0⟩, fun a => ConcM.liftMem (air2lean_model_0 a.1 a.2)),
   (⟨some 3, 0⟩, fun a => ConcM.liftMem (sumVisit a.1 a.2))]

/-- The environment's `Visitor` functions: `Ext.call0`. -/
def env : EnvFn Tgt (Ptr × BitVec 32) Bool := fun f a => Ext.call0 f a.1 a.2

set_option maxHeartbeats 2000000 in
/-- **The evaluator for every callback**: the function that `cb` reaches (the foreign model,
`sumVisit` or the environment's) meets the callback contract. -/
theorem evaluate_spec (cb ctx : Ptr) (x v : BitVec 32)
    (h : ∀ v, FnSpec (visitPre v) visitPost (Table.callOr targets env cb)) :
    CTriple (up (pts ctx 4 v)) (evaluate cb ctx x)
      (fun r => ⟪r = true⟫ ⋆ FAssn.ex fun v' : BitVec 32 => up (pts ctx 4 v')) := by
  fsym [visit_call h]

omit [Ext] in
set_option maxHeartbeats 2000000 in
/-- `sumVisit` (translated) adds `x` to the context. -/
theorem sumVisit_spec (ctx : Ptr) (x v : BitVec 32) :
    FTotalTriple (up (pts ctx 4 v)) (sumVisit ctx x)
      (fun r => ⟪r = true⟫ ⋆ up (pts ctx 4 (addWrap v x))) := by
  fsym

omit [Ext] in
/-- `sumVisit` meets the callback contract. -/
theorem sumVisit_visit (v : BitVec 32) :
    FnSpec (Tgt := Tgt) (visitPre v) visitPost fun a => ConcM.liftMem (sumVisit a.1 a.2) :=
  fun a => CTriple.liftMem ((sumVisit_spec a.1 a.2 v).1.post fun _ _ h => by
    obtain ⟨r₁, r₂, hd, e, h₁, h₂⟩ := h
    exact ⟨r₁, r₂, hd, e, h₁, _, h₂⟩)

omit [Ext]

/-- **`runLocal`'s callback through `sum_ops`**: the dispatch at `sumVisit`'s address meets the
contract by the translated code, whatever the environment (`Table.contract_of_sel`). -/
theorem sum_dispatch (e : EnvFn Tgt (Ptr × BitVec 32) Bool) (v : BitVec 32) :
    FnSpec (visitPre v) visitPost (Table.callOr targets e ⟨some 3, 0⟩) :=
  Table.contract_of_sel (C := FnSpec (visitPre v) visitPost) (by rfl) e (sumVisit_visit v)

/-! ## The foreign `ext_visit` arm

The arm at `ext_visit`'s address runs its registry model, `External.claim ctx .write *>
CallbackModel.visit`, whose evidence is the `MemM` contract `CallbackModel.contract` (premise
EXT-02). `FTriple.of_contract` reads such evidence as a triple (`idModel_spec`: a model whose
contract returns its argument and keeps the memory). For `ext_visit` it cannot give the callback
contract: the registered contract lets the callback fail with any error, and a full-state triple
admits only a stack overflow. `model_contract_weaker` is the counterexample: an implementation
that panics meets `CallbackModel.contract` but not `FnSpec (visitPre v) visitPost`. -/

/-- A model that returns its argument and keeps the memory. -/
def idModel (x : BitVec 32) : MemM (BitVec 32) := pure x

def idContract : External.Contract (BitVec 32) (BitVec 32) where
  pre := fun _ _ => True
  post := fun x before r after => r = x ∧ after = before
  frame := fun _ before after => after = before
  access := fun _ _ _ => False
  failure := fun _ _ _ => False
  divergence := fun _ _ => False

theorem idModel_evidence : idContract.Holds .total [] .preserves idModel :=
  fun x before _ => ⟨⟨rfl, rfl⟩, rfl, ⟨#[], by simp, by simp⟩, fun _ => rfl⟩

/-- **The bridge at work**: the model's evidence gives its full-state triple. -/
theorem idModel_spec (x : BitVec 32) (P : FAssn) :
    FTriple P (idModel x) (fun v => ⟪v = x⟫ ⋆ P) :=
  FTriple.of_contract idModel_evidence x (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ he _ => nomatch he)
    (fun _ r _ _ _ hh hp hs ⟨hv, hm⟩ _ _ => ⟨r, hm ▸ hh, sep_lift.2 ⟨hv, hp⟩, hm ▸ hs⟩)

/-- The access record of a model call returns in a single-threaded memory. -/
theorem claim_ok {β : Type} [External.Region β] (x : β) (k : AccessKind) {m : Mem}
    (hs : m.SingleThread) : ∃ m', External.claim x k m = pure ((), m') := by
  unfold External.claim
  split
  · exact ⟨m, rfl⟩
  · split
    · exact ⟨_, recordAccess_run (noRace_of_singleThread hs _ _ _ _)⟩
    · exact ⟨m, rfl⟩

/-- A foreign `ext_visit` that panics on every call. -/
def panicVisit : Ptr × BitVec 32 → MemM Bool := fun _ => throw .panic

/-- It meets the registered contract: the callback may fail with any error. -/
theorem panicVisit_evidence :
    CallbackModel.contract.Holds .«partial» CallbackModel.allErrors .tracked panicVisit :=
  fun _ _ _ => ⟨CallbackModel.mem_allErrors _, trivial⟩

/-- **The registered contract of `ext_visit` does not give the callback contract**: some
implementation that meets it, run as the model arm, violates `FnSpec (visitPre 0) visitPost`. -/
theorem model_contract_weaker :
    ¬ ∀ impl : Ptr × BitVec 32 → MemM Bool,
      CallbackModel.contract.Holds .«partial» CallbackModel.allErrors .tracked impl →
      FnSpec (Tgt := Tgt) (visitPre 0) visitPost
        (fun a => ConcM.liftMem (External.claim a.1 .write *> impl a)) := by
  intro h
  have t : FTriple (visitPre 0 (Witness.p0, 0))
      (External.claim Witness.p0 .write *> panicVisit (Witness.p0, 0)) (visitPost (Witness.p0, 0)) :=
    h panicVisit panicVisit_evidence (Witness.p0, 0) 0
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ :=
    Witness.FAdmit.up Witness.pts32 (Witness.mem1_fseq _ _ (by decide +kernel))
  obtain ⟨m', hm'⟩ := claim_ok Witness.p0 .write hs.1.single
  have hrun : ((External.claim Witness.p0 .write *> panicVisit (Witness.p0, 0)).run m).run =
      some (.error .panic) := by
    show (External.claim Witness.p0 .write >>= fun _ => panicVisit (Witness.p0, 0)) m = _
    simp only [bind, StateT.bind, hm']
    rfl
  have e := t m r rF hh hp hs
  rw [hrun] at e
  exact nomatch (e : Error.panic = .stackOverflow)

end Interfaces.CallbacksSpec
