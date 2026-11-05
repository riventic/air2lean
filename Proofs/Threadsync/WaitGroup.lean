import Proofs.Threadsync.WaitGroup.Task
import Proofs.Threadsync.WaitGroup.Read
import Proofs.Threadsync.WaitGroup.Join
import ZigLean.Sep.Full.AutoWP
import ZigLean.Conc.RunResult

/-!
# `threadsync.waitGroup` over all schedules

`waitGroup` starts a `Thread.WaitGroup` with 2, spawns two tasks and waits on the group. Each
task adds 1 to a counter under a `Thread.Mutex` and finishes the group; the one whose finish
reads 3 (`main` waits, the other task finished) sets the group's `Thread.ResetEvent`. Then `main`
reads the whole `Tally` struct and joins the tasks. All sync objects are translated from Zig
0.15.2's std code (Linux, macOS, aarch64-linux); the futex under them is the model. The result is
2 under every schedule (`waitGroup_spec`), and no schedule gives an error (`waitGroup_safe`): no
data race on the `Tally` (its whole read included), no deadlock at a futex, no panic.

The proof is in the full-state concurrent separation logic (`docs/sep-threads.md`) and uses only
the contracts of the sync objects (`MutexImpl`, `EventImpl`): this program's `Thread.Mutex` and
`Thread.ResetEvent` are `Threadsync.threadMutex` and `Threadsync.resetEvent`. The protocol and its
steps are in `Proofs/Threadsync/WaitGroup/`: the protocol (`Protocol`), its start (`Start`),
`main`'s `startMany` and spawns (`Main`), its wait (`Wait`), its read of the `Tally` (`Read`),
its joins (`Join`) and the tasks (`Task`). This file walks `main` of the generated code (`fsym`)
and states the results, with one run that the kernel computes (`waitGroup_completes`) in every
translation.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Threadsync

namespace Threadsync.WG

-- `main`'s event wait reaches the translated `std.time.Timer` (OSK-01): the results hold for every
-- OS environment (`[Zig.Os.HasEnv]`).

-- Unification must not unfold `WP` into the program (as in `Proofs/Threadsync/Handoff.lean`).
attribute [local irreducible] Proto.WP

/-- **`main`**: the `Tally` (block 0, a stack block in the plain mode, which `main` keeps) and
its store; the protocol's start with `main`'s part (`inv_of_box`); `startMany(2)`; the two spawns;
the group's wait; the read of the whole `Tally` (its counter is 2); the joins and the free of the
`Tally`. -/
theorem main_spec [Zig.Os.HasEnv] (σ : Placement) (d : Nat) :
    proto.WP 0 waitGroup QM G0 { mem0 σ with current := 0 } d := by
  have := FOwned.start0_facts (σ := σ) (m := mem0 σ) rfl
  unfold waitGroup
  fsym [inv_of_box, inv_spawn1, inv_spawn2, WP.liftMem_pure (projI _ _) rfl, wp_startMany,
    wp_wgWait, wp_read, wp_join1, wp_join2, wp_free, joinedAll_of_threads]

/-! ## The results -/

/-- **`threadsync.waitGroup` gives 2 under every schedule** (every oracle `o`, every `fuel`). -/
theorem waitGroup_spec [Zig.Os.HasEnv] (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o waitGroup (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 2 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ) h
  exact hv

/-- **No run of `threadsync.waitGroup` gives an error**: no data race on the `Tally` (its whole
read included), no deadlock at a futex, no panic, under every schedule. -/
theorem waitGroup_safe [Zig.Os.HasEnv] (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} :
    e ≠ .stackOverflow → (Sched.run env dispatch fuel o waitGroup (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl (main_spec σ)

/-- **One schedule completes**: under the oracle that always picks option 0, the
`std.Thread.WaitGroup` client returns 2 within fuel 1000, from `mem0` with the translation's spawn
policy, in the example OS environment (`Os.Env.example`; the run reads no clock). The kernel
computes the run once the loops on its path are unfolded by their defining equation
(`docs/proof-tools.md`, concrete runs of programs with loops). -/
theorem waitGroup_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0)
      (@waitGroup ⟨Os.Env.example⟩) (mem0 σ)) = some 2 := by
  refine ⟨.fresh, ?_⟩
  delta dispatch task waitGroup Thread_WaitGroup_wait Thread_ResetEvent_wait
    Thread_ResetEvent_FutexImpl_wait Thread_ResetEvent_FutexImpl_waitUntilSet Thread_Mutex_lock
    Zig.osUnfairLockC
  iterate 4 (simp (config := { singlePass := true, maxSteps := 2000 }) only [Zig.loop.eq_1])
  decide +kernel

end Threadsync.WG
