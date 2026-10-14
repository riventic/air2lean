import Interfaces.Callbacks
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region

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

/-- **`runLocal`'s callback through `sum_ops`**: the dispatch at `sumVisit`'s address meets the
contract by the translated code, whatever the environment (`Table.contract_of_sel`). -/
theorem sum_dispatch (e : EnvFn Tgt (Ptr × BitVec 32) Bool) (v : BitVec 32) :
    FnSpec (visitPre v) visitPost (Table.callOr targets e ⟨some 3, 0⟩) :=
  Table.contract_of_sel (C := FnSpec (visitPre v) visitPost) (by rfl) e (sumVisit_visit v)

end Interfaces.CallbacksSpec
