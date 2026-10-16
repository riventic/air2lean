import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.LockRules

/-!
# `fsym` on the OS futex rows at a lock's word (premises OSF-01, OSF-02)

The calls of std's `Thread.Futex.wait`/`wake` (0.14.1, 0.15.2) into the OS rows, as the translated
code makes them (`ZigLean/Sep/Full/OsFutex.lean`): `futex_4arg(WAIT | PRIVATE, c, null)` and
`futex_3arg(WAKE | PRIVATE, n)` on Linux, `__ulock_wait2(COMPARE_AND_WAIT | NO_ERRNO, c, 0, 0)` and
`__ulock_wake(COMPARE_AND_WAIT | NO_ERRNO | WAKE_ALL, 0)` on macOS, at the word of a lock, for
every protocol that has the lock (`FLock.Fits`). The rows are the library's `@[fsym]` rules; the
caller passes the lock's rules at the OS wait and wake (`wp_osWait`, `wp_osWake`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FLock Zig.Os

namespace SepAuto.WPOsFutex

attribute [local irreducible] Proto.WP

variable {Tgt γ : Type} {L : FLock γ} {K : FPrim γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- Linux: the OS wait for `c` at the word, by a thread at `spin`: it goes on at `spin`, with the
return code of a wake, a mismatch or a signal (never `ETIMEDOUT`). -/
theorem linux_wait (hP : L.Fits K P U ok) (hcost : P.cost = none) (t : ThreadId) (g : γ)
    (hg : L.ph g = .spin) (hok : ok g) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Linux.futex_4arg L.ptr 0x80 (BitVec.ofNat 32 L.c) none)
      (fun r G' m' d' => (∃ w : WaitResult, w ≠ .timedOut ∧ r = Linux.waitCode w) ∧ d' < d ∧
        m'.current = t ∧ P.inv (upd G' t g) m') G m d := by
  fsym [wp_osWait hP rfl hg hok hi]

/-- Linux: `unlock`'s wake of one waiter at the word (`futex_3arg(WAKE | PRIVATE, 1)`), by the
thread at `wake`: it goes on at `out`. -/
theorem linux_wake (hP : L.Fits K P U ok) (hcost : P.cost = none) (t : ThreadId) (g : γ)
    (hg : L.ph g = .wake) (hok : ok g) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Linux.futex_3arg L.ptr 0x81 1)
      (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ P.inv (upd G' t (L.set g .out rnil)) m')
      G m d := by
  fsym [wp_osWake hP (w := some (Linux.wakeLimit 1))
    (fun k hk => by cases hk; exact Linux.wakeLimit_pos 1) hg hok hi]

/-- macOS: the OS wait for `c` at the word, by a thread at `spin`: it goes on at `spin`. -/
theorem darwin_wait (hP : L.Fits K P U ok) (hcost : P.cost = none) (t : ThreadId) (g : γ)
    (hg : L.ph g = .spin) (hok : ok g) (hc : L.c < 2 ^ 32) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Darwin.__ulock_wait2 0x01000001 (some L.ptr) (BitVec.ofNat 64 L.c) 0 0)
      (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ P.inv (upd G' t g) m') G m d := by
  have he : (BitVec.ofNat 64 L.c).setWidth 32 = BitVec.ofNat 32 L.c := by
    apply BitVec.eq_of_toNat_eq; simp
  fsym [wp_osWait hP he hg hok hi]

/-- macOS: `wake(p, n)` with `n > 1` sets `WAKE_ALL` (`__ulock_wake(… | WAKE_ALL, 0)`): by the
thread at `wake`, it goes on at `out`, or after a spurious `EINTR` at `wake`. -/
theorem darwin_wakeAll (hP : L.Fits K P U ok) (hcost : P.cost = none) (t : ThreadId) (g : γ)
    (hg : L.ph g = .wake) (hok : ok g) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Darwin.__ulock_wake 0x01000101 (some L.ptr) 0)
      (fun r G' m' d' => d' < d ∧ m'.current = t ∧
        (P.inv (upd G' t (L.set g .out rnil)) m' ∨
         r = Darwin.wakeCode none ∧ P.inv (upd G' t g) m')) G m d := by
  fsym [wp_osWake hP (w := none) (fun k hk => by cases hk) hg hok hi]

end SepAuto.WPOsFutex
