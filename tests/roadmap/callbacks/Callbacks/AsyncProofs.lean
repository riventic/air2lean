import Callbacks.Async
import CallbackModel
import ZigLean.External.Callback
import ZigLean.Sep.Loop
import Proofs.Asm.Effects

/-!
# An asynchronous callback (E02, premise EXT-04)

`Callbacks/Async.lean` is the translation of `air-async/0.17.0` (`async_cb.zig`): `runBoth`
spawns a thread that calls a callback through a function pointer while the caller calls it on
another context. The program is concurrent, so the registry binding of `ext_visit` needs a
footprint, and the emitted model call first claims the context block for writing
(`Zig.External.claim`): a call on a context that another thread accesses without
synchronization is a race, `.illegal`, like any other conflicting access.

* `model_claims`: the bound model is `claim ctx .write *> visit`.
* `worker_spec`: in whichever thread it runs, a call that returns changes no block other than
  the context's and keeps the context live; the claim changes no block, the rest is the
  callback contract.
-/

namespace AsyncProofs

open Zig Zig.External Callbacks.Async CallbackModel

theorem model_claims (ctx : Ptr) (x : BitVec 32) :
    air2lean_model_0 ctx x = (claim ctx .write *> visit (ctx, x)) := rfl

theorem visit_holds : visitCallback.Holds visit :=
  ⟨wellFormed, by
    have h := air2lean_model_0_evidence.1
    simpa [air2lean_model_0_contract, contract, visitCallback, allErrors] using h⟩

theorem worker_eq (cb ctx : Ptr) (x : BitVec 32) :
    worker cb ctx x = (if cb = ⟨some 0, 0⟩ then air2lean_model_0 ctx x >>= fun _ => pure ()
      else throw .illegal) := by
  funext m
  by_cases h : cb = ⟨some 0, 0⟩
  · subst h
    simp [worker, StateT.run'_eq, callM]
  · simp [worker, h, StateT.run'_eq]
    rfl

/-- A callback call in any thread: the context stays live and no other block changes. -/
theorem worker_spec {cb ctx : Ptr} {x : BitVec 32} {before after : Mem}
    (run : (worker cb ctx x).run before = pure ((), after)) :
    (Live before ctx → Live after ctx) ∧
      ∀ b, some b ≠ ctx.block → after.blocks[b]? = before.blocks[b]? := by
  rw [worker_eq] at run
  split at run
  · obtain ⟨r, m₁, hA, hp⟩ := Asm.run_bind_ok run
    have hp : some (Except.ok ((), m₁)) = some (Except.ok ((), after)) := hp
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    obtain ⟨_, m₀, hc, hv⟩ := Asm.run_bind_ok (x := claim ctx .write)
      (f := fun _ => visit (ctx, x)) hA
    have hb := claim_blocks hc
    have hcall := CallbackContract.call visit_holds (cc := visitCallback) trivial hv
    refine ⟨fun hl => hcall.2.1 ?_, fun b hne => ?_⟩
    · obtain ⟨b, blk, h1, h2, h3⟩ := hl
      exact ⟨b, blk, h1, hb ▸ h2, h3⟩
    · rw [hcall.2.2 b hne (by simp [visitCallback]), hb]
  · cases run

end AsyncProofs
