import Proofs.Threadsync.Lock

/-! Negative control: Lean must reject this file. It uses the macOS contended value (1) with the
translation of this repository's Linux build, whose `mutexC` is 3: a lock proof does not transfer
between targets by changing the constant. -/
-- expect-error: Application type mismatch

namespace CrossTarget

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Threadsync Threadsync.ThreadMutexOps

/- `WP` is only a name here: unfolding it would run the program. -/
attribute [local irreducible] Proto.WP

variable {γ : Type} {L : Lock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Mem → Prop}

theorem lock_keeps_current_macos_constant (hP : L.Fits P U) (hc : L.c = 1) {p : Ptr}
    (hp : p = L.ptr) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ _ m' _ => m'.current = t) G m d :=
  WP.mono (fun _ _ _ _ h => h.2.1) (lock_spec hP hc hp t g hg G m d hi)

end CrossTarget
