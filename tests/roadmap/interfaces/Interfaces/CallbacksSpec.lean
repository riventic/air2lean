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
`sumVisit` meets the contract by its translated code, the foreign `ext_visit` by its registered
model contract (`FTriple.of_contract`, assumed: EXT-02), and the dispatch at either address does
so whatever the environment (`Table.contract_of_sel`).
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
set_option maxHeartbeats 2000000 in
/-- `sumVisit` in a thread (the sequential rules with the locality of the owned context). -/
theorem sumVisit_thread (ctx : Ptr) (x v : BitVec 32) :
    FTTotalTriple (up (pts ctx 4 v)) (sumVisit ctx x)
      (fun r => ⟪r = true⟫ ⋆ up (pts ctx 4 (addWrap v x))) := by
  fsym

omit [Ext] in
/-- `sumVisit` meets the callback contract. -/
theorem sumVisit_visit (v : BitVec 32) :
    FnSpec (Tgt := Tgt) (visitPre v) visitPost fun a => ConcM.liftMem (sumVisit a.1 a.2) :=
  fun a => CTriple.liftMem ((sumVisit_thread a.1 a.2 v).toPartial.post fun _ _ h => by
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
CallbackModel.visit`, whose evidence is the registered `MemM` contract `CallbackModel.contract`
(assumed, premise EXT-02): given a context that holds a writable `u32`, a call fails only with a
stack overflow and its memory is a `u32` store to the context, up to the access log.
`FTriple.of_contract` reads that evidence as a full-state triple (`visit_spec`), so the arm meets
the callback contract (`extVisit_visit`) and the dispatch at its address does so whatever the
environment (`ext_dispatch`).

The callback contract that every target of the type meets, `CallbackModel.visitCallback`, is too
weak for this: it lets a call fail with any error, and a full-state triple admits only a stack
overflow. `model_contract_weaker` keeps that as a regression: an implementation that panics
meets `visitCallback`'s contract but not `FnSpec (visitPre v) visitPost`. -/

/-- A `u32` at `ctx` is a writable context of the registered contract. -/
theorem ctxOk_of_pts {ctx : Ptr} {v : BitVec 32} {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : up (pts ctx 4 v) r) (hs : m.FSeq) : CallbackModel.CtxOk ctx m := by
  obtain ⟨_, m₁, _, hrun, -⟩ := (FTotalTriple.store (q := ctx) (by decide) 0).runs hh hp hs
  exact ⟨m₁, hrun⟩

/-- A `u32` at `ctx` is in no `const` global (a store to it succeeds), so a write claim of it
records the write (`External.claim_run`'s side condition). -/
theorem ctx_write_claim {ctx : Ptr} {v : BitVec 32} {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : up (pts ctx 4 v) r) (hs : m.FSeq) (b : BlockId) (blk : Block)
    (hb : ctx.block = some b) (hblk : m.blocks[b]? = some blk) (hK : blk.kind = .constGlobal) :
    AccessKind.write.isWrite = false := by
  obtain ⟨m₁, hrun⟩ := ctxOk_of_pts hh hp hs
  obtain ⟨b', blk', o', hacc, -⟩ := Asm.storeBytes_inv hrun
  obtain ⟨hb', hblk', -⟩ := access_eq (Asm.access_of_accessW hacc)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain rfl : blk = blk' := Option.some.inj (hblk.symm.trans hblk')
  exact absurd hK (Asm.kind_of_accessW hacc)

/-- **`ext_visit`'s model meets the callback contract**, from its registered contract
(`FTriple.of_contract`). -/
theorem visit_spec (v : BitVec 32) (a : Ptr × BitVec 32) :
    FTriple (visitPre v a) (CallbackModel.visit a) (visitPost a) := by
  refine FTriple.of_contract air2lean_model_0_evidence.1 a (fun _ _ _ _ _ _ => trivial)
    (fun m r rF e hh hp hs _ hf => ?_) (fun m r rF res m' hh hp hs hq hfr _ => ?_)
  · rcases hf with he | ⟨-, hc⟩
    · exact he
    · exact absurd (ctxOk_of_pts hh hp hs) hc
  · obtain ⟨w, m₁, hrun, hb, ha, hst⟩ := hfr.2 (ctxOk_of_pts hh hp hs)
    obtain ⟨_, m₂, r', hrun', hh', hq', hs'⟩ :=
      (FTotalTriple.store (q := a.1) (by decide) w).runs hh hp hs
    rw [hrun] at hrun'
    obtain rfl : m₁ = m₂ := by
      have e : some (Except.ok ((), m₁)) = some (Except.ok ((), m₂)) := hrun'
      simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at e
      exact e.2
    exact ⟨r', Holds.congrMem hb ha hh', sep_lift.2 ⟨hq, w, hq'⟩,
      hs'.congrMem hb ha (hst hs.1.single)⟩

/-- The arm at `ext_visit`'s address: the access record, then the model. -/
theorem extVisit_visit (v : BitVec 32) :
    FnSpec (Tgt := Tgt) (visitPre v) visitPost
      fun a => ConcM.liftMem (air2lean_model_0 a.1 a.2) :=
  fun a => CTriple.liftMem (FTriple.bind
    (FTriple.claim a.1 .write _ fun _ _ _ b blk hh hp hs => ctx_write_claim hh hp hs b blk)
    fun _ => visit_spec v a)

/-- **`runExternal`'s callback through `ext_ops`**: the dispatch at `ext_visit`'s address meets
the contract by the registered contract, whatever the environment. -/
theorem ext_dispatch (e : EnvFn Tgt (Ptr × BitVec 32) Bool) (v : BitVec 32) :
    FnSpec (visitPre v) visitPost (Table.callOr targets e ⟨some 1, 0⟩) :=
  Table.contract_of_sel (C := FnSpec (visitPre v) visitPost) (by rfl) e (extVisit_visit v)

/-- A foreign `ext_visit` that panics on every call. -/
def panicVisit : Ptr × BitVec 32 → MemM Bool := fun _ => throw .panic

/-- It meets the type's callback contract, which lets a call fail with any error. -/
theorem panicVisit_evidence : CallbackModel.visitCallback.Holds panicVisit :=
  ⟨CallbackModel.wellFormed, fun _ _ _ => ⟨CallbackModel.mem_allErrors _, trivial⟩⟩

/-- **The type's callback contract does not give the interface contract** (regression for a
model registered with it): some implementation that meets it, run as the model arm, violates
`FnSpec (visitPre 0) visitPost`. -/
theorem model_contract_weaker :
    ¬ ∀ impl : Ptr × BitVec 32 → MemM Bool, CallbackModel.visitCallback.Holds impl →
      FnSpec (Tgt := Tgt) (visitPre 0) visitPost
        (fun a => ConcM.liftMem (External.claim a.1 .write *> impl a)) := by
  intro h
  have t : FTriple (visitPre 0 (Witness.p0, 0))
      (External.claim Witness.p0 .write *> panicVisit (Witness.p0, 0)) (visitPost (Witness.p0, 0)) :=
    h panicVisit panicVisit_evidence (Witness.p0, 0) 0
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ :=
    Witness.FAdmit.up Witness.pts32 (Witness.mem1_fseq _ _ (by decide +kernel))
  obtain ⟨m', hm', -⟩ :=
    External.claim_run Witness.p0 .write hs.1.single (ctx_write_claim hh hp hs)
  have hrun : ((External.claim Witness.p0 .write *> panicVisit (Witness.p0, 0)).run m).run =
      some (.error .panic) := by
    show (External.claim Witness.p0 .write >>= fun _ => panicVisit (Witness.p0, 0)) m = _
    simp only [bind, StateT.bind, hm']
    rfl
  have e := t m r rF hh hp hs
  rw [hrun] at e
  exact nomatch (e : Error.panic = .stackOverflow)

end Interfaces.CallbacksSpec
