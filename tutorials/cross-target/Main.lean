import Proofs.Threadsync.Lock

/-!
Cross-target verification: `Thread.Mutex.lock` of Zig 0.15.2 is a different function on Linux
(`FutexImpl`) and on macOS (`os_unfair_lock`). `Threadsync.ThreadMutexOps.lock_spec` is stated
for either translation: its only target-specific input is the contended value `mutexC` (3 on
Linux, 1 on macOS), which the repository defines next to the translation it checks. A client
theorem that goes through `lock_spec` and does not name the value holds for both targets.

From the repository root:
  lake build Proofs.Threadsync.Lock
  lake env lean tutorials/cross-target/Main.lean

See tutorials/cross-target/README.md for the two targets, the exercise and the negative control.
-/

namespace CrossTarget

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Threadsync Threadsync.ThreadMutexOps

/- `WP` is only a name here: unfolding it would run the program. -/
attribute [local irreducible] Proto.WP

variable {γ : Type} {L : Lock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Mem → Prop}

/-- After `Thread.Mutex.lock`, the locking thread is the running one. The hypothesis `hc` is
stated with `mutexC`, so the same proof holds for the Linux and the macOS translation. -/
theorem lock_keeps_current (hP : L.Fits P U) (hc : L.c = mutexC) {p : Ptr} (hp : p = L.ptr)
    (t : ThreadId) (g : γ) (hg : L.ph g = .out) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ _ m' _ => m'.current = t) G m d :=
  WP.mono (fun _ _ _ _ h => h.2.1) (lock_spec hP hc hp t g hg G m d hi)

end CrossTarget
