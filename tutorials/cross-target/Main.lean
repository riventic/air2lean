import Proofs.Threadsync.ThreadMutex

/-!
Cross-target verification: `Thread.Mutex.lock` of Zig 0.15.2 is a different function on Linux
(`FutexImpl`) and on macOS (`os_unfair_lock`). Either translation meets the mutex contract
(`Threadsync.threadMutex : MutexImpl Tgt`, rules `lock_wp` and `unlock_wp`): its only
target-specific input is the contended value `mutexC` (3 on Linux, 1 on macOS), which the
repository defines next to the translation it checks. A client theorem that goes through the
contract and does not name the value holds for both targets.

From the repository root:
  lake build Proofs.Threadsync.ThreadMutex
  lake env lean tutorials/cross-target/Main.lean

See tutorials/cross-target/README.md for the two targets, the exercise and the negative control.
-/

namespace CrossTarget

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Threadsync

/- `WP` is only a name here: unfolding it would run the program. -/
attribute [local irreducible] Proto.WP

variable {γ : Type} {L : FLock γ} {K : FPrim γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- After `Thread.Mutex.lock`, the locking thread is the running one. The hypothesis `hc` is
stated with `mutexC`, so the same proof holds for the Linux and the macOS translation. The
protocol counts no turns (`hcost`): a futex wait has no turn charge. `ok` marks the threads that
may run the lock's code (`FLock.Fits`), and `io` is
the `Io` argument of the contract's `lock`, which `Thread.Mutex.lock` ignores. -/
theorem lock_keeps_current (hP : L.Fits K P U ok) (hc : L.c = mutexC) {p : Ptr} (hp : p = L.ptr)
    (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (io : Io) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) (hcost : P.cost = none) :
    P.WP t (Thread_Mutex_lock p) (fun _ _ m' _ => m'.current = t) G m d :=
  WP.mono (fun _ _ _ _ h => h.2.1) (threadMutex.lock_wp hP hcost hp hc t g hg hok io G m d hi)

end CrossTarget
