import Proofs.Threadsync.Lock

/-! Negative control for the macOS translation (run by CI after the golden swap, see
README.md; on the Linux translation this file would elaborate). It uses the Linux contended
value (3) with the translation of macOS, whose `mutexC` is 1. Lean must reject it. -/
-- expect-error: Application type mismatch

namespace CrossTarget

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Threadsync Threadsync.ThreadMutexOps

/- `WP` is only a name here: unfolding it would run the program. -/
attribute [local irreducible] Proto.WP

variable {γ : Type} {L : Lock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Mem → Prop}

theorem lock_keeps_current_linux_constant (hP : L.Fits P U) (hc : L.c = 3) {p : Ptr}
    (hp : p = L.ptr) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ _ m' _ => m'.current = t) G m d :=
  WP.mono (fun _ _ _ _ h => h.2.1) (lock_spec hP hc hp t g hg G m d hi)

end CrossTarget
