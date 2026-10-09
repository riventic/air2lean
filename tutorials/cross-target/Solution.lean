import Proofs.Threadsync.Lock

/-! Exercise solution: `Thread.Mutex.unlock` by the holder also leaves the unlocking thread
running, for either target. -/

namespace CrossTarget

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Threadsync Threadsync.ThreadMutexOps

/- `WP` is only a name here: unfolding it would run the program. -/
attribute [local irreducible] Proto.WP

variable {γ : Type} {L : Lock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Mem → Prop}

theorem unlock_keeps_current (hP : L.Fits P U) (hc : L.c = mutexC) {p : Ptr} (hp : p = L.ptr)
    (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_unlock p) (fun _ _ m' _ => m'.current = t) G m d :=
  WP.mono (fun _ _ _ _ h => h.2.1) (unlock_spec hP hc hp t g hg G m d hi)

end CrossTarget
