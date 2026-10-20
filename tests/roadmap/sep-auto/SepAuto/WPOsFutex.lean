import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.LockRules
import ZigLean.Sep.Full.Event

/-!
# `fsym` on the OS futex rows at a lock's word (premises OSF-01, OSF-02)

The calls of std's `Thread.Futex.wait`/`wake` (0.14.1, 0.15.2) into the OS rows, as the translated
code makes them (`ZigLean/Sep/Full/OsFutex.lean`): `futex_4arg(WAIT | PRIVATE, c, null)` and
`futex_3arg(WAKE | PRIVATE, n)` on Linux, `__ulock_wait2(COMPARE_AND_WAIT | NO_ERRNO, c, 0, 0)` and
`__ulock_wake(COMPARE_AND_WAIT | NO_ERRNO | WAKE_ALL, 0)` on macOS, at the word of a lock, for
every protocol that has the lock (`FLock.Fits`), and at an event's word (`FEvent`, a word
protocol). The rows are the library's `@[fsym]` rules; the caller passes the lock's or the
event's rules at the OS wait and wake (`wp_osWait`, `wp_osWake`).
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
  fsym [hP.ptrAddr_aligned, wp_osWait hP rfl hg hok hi]

/-- Linux: `unlock`'s wake of one waiter at the word (`futex_3arg(WAKE | PRIVATE, 1)`), by the
thread at `wake`: it goes on at `out`. -/
theorem linux_wake (hP : L.Fits K P U ok) (hcost : P.cost = none) (t : ThreadId) (g : γ)
    (hg : L.ph g = .wake) (hok : ok g) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Linux.futex_3arg L.ptr 0x81 1)
      (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ P.inv (upd G' t (L.set g .out rnil)) m')
      G m d := by
  fsym [hP.ptrAddr_aligned,
    wp_osWake hP (w := some (Linux.wakeLimit 1))
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

/-- Linux: an event's waiter at `w1` waits for `waiting` (1) at the event's word, by the word
protocol's OS wait (`FEvent.wp_osWait`, over `wp_wordOsWait`): it goes on at `w1`. -/
theorem event_wait (E : FEvent γ) (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hg : E.ph g = .w1) (hgo : L.ph g = .out) (G : ThreadId → γ)
    (m : Mem) (hc : m.current = t) (d : Nat) (hi : P.inv (upd G t g) m)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁) :
    P.WP t (Linux.futex_4arg E.W.ptr 0x80 1 none)
      (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ P.inv (upd G' t g) m') G m d := by
  -- workaround (ledger #current-thread-subst): `fsym` substitutes `hc` away after elaborating the
  -- rule term, so the rule takes the current thread itself
  subst hc
  fsym [hE.wordPtrAddr_aligned (hE.wRest rfl),
    FEvent.wp_osWait hE rfl hg hgo rfl hi hlive]

/-- macOS: an event's setter at `sw` wakes every waiter (`__ulock_wake(… | WAKE_ALL, 0)`,
`FEvent.wp_osWake`, over `wp_wordOsWake`): the event is set and it leaves, or after a spurious
`EINTR` it is still at `sw`. -/
theorem event_wakeAll (E : FEvent γ) (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hg : E.ph g = .sw) (hgo : L.ph g = .out) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Darwin.__ulock_wake 0x01000101 (some E.W.ptr) 0)
      (fun r G' m' d' => d' < d ∧ m'.current = t ∧
        (E.IsSet m' ∧ P.inv (upd G' t (E.set g .out)) m' ∨
         r = Darwin.wakeCode none ∧ P.inv (upd G' t g) m')) G m d := by
  fsym [FEvent.wp_osWake hE (w := none) (fun k hk => by cases hk) hg hgo hi]

/-- A retained address run must not make the walker commit to the unaligned case before
checking its guard. The address and protocol are arbitrary. -/
theorem aligned_wake_selection (P : Proto Tgt γ) (t : ThreadId) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (p : Ptr) (a : Int)
    (ha : (Zig.ptrAddr p).run m = pure (a, m)) (hal : a % 4 = 0)
    (Q : BitVec 64 → (ThreadId → γ) → Mem → Nat → Prop)
    (h : P.WP t (Os.futexWake p (some (Linux.wakeLimit 1)) false : ConcM Tgt (Option Nat))
      (fun r => Q (BitVec.ofNat 64 (r.getD 0))) G m d) :
    P.WP t (Linux.futex_3arg p 0x81 1) Q G m d := by
  fsym [h]

/-- The raw row's returned EINVAL keeps the complete state and costs no scheduling turn,
even at depth zero. This exercises the existing registered branch rule through fsym. -/
theorem unaligned_wake (P : Proto Tgt γ) (t : ThreadId) (G : ThreadId → γ) (m : Mem) (d : Nat) :
    P.WP t (Linux.futex_3arg ⟨none, 4097⟩ 0x81 1)
      (fun r G' m' d' => r = negErrno Linux.E.INVAL ∧ G' = G ∧ m' = m ∧ d' = d)
      G m d := by
  fsym

/-- The same returned-error branch for WAIT; all depths include zero without a vacuous
scheduled-success branch, and the complete state stays unchanged. -/
theorem unaligned_wait (P : Proto Tgt γ) (t : ThreadId) (G : ThreadId → γ) (m : Mem) (d : Nat) :
    P.WP t (Linux.futex_4arg ⟨none, 4097⟩ 0x80 7 none)
      (fun r G' m' d' => r = negErrno Linux.E.INVAL ∧ G' = G ∧ m' = m ∧ d' = d)
      G m d := by
  fsym

/-! A finite count covering this key’s queue suffices for broadcast. -/

example {c n : Nat} {p : Ptr} {m m' : Mem} {j : Nat}
    (hr : ((Os.wakeAt c p (some n)).run m).run = some (.ok (some j, m')))
    (hn : (m.waitersAt p).length ≤ n) : m'.waitersAt p = [] :=
  (Os.wakeAt_all_of_le hr hn).2

private def boundPtr : Ptr := ⟨none, 4096⟩
private def otherPtr : Ptr := ⟨none, 8192⟩
private def boundQueue : Mem := {
  waiters := #[(1, boundPtr), (2, boundPtr), (3, otherPtr)]
  woken := #[9]
}

private def boundWake (n c : Nat) (m : Mem) :=
  (((Os.wakeAt c boundPtr (some n)).run m).run).map
    (·.map fun (j, m') => (j, m'.waiters, m'.woken))

/-- Exact and larger bounds clear only the selected key, preserving prior wake bookkeeping. -/
example : boundWake 2 0 boundQueue = some (.ok (some 2, #[(3, otherPtr)], #[9, 1, 2])) ∧
    boundWake 3 0 boundQueue = boundWake 2 0 boundQueue := by
  constructor <;> rfl

/-- A smaller count leaves a waiter, for either valid oracle selection. -/
example : boundWake 1 0 boundQueue = some (.ok (some 1, #[(2, boundPtr), (3, otherPtr)], #[9, 1])) ∧
    boundWake 1 1 boundQueue = some (.ok (some 1, #[(1, boundPtr), (3, otherPtr)], #[9, 2])) := by
  constructor <;> rfl

/-- Zero covers an empty queue at this key, even when another key still has a waiter. -/
example : boundWake 0 0 { waiters := #[(3, otherPtr)], woken := #[9] } =
    some (.ok (some 0, #[(3, otherPtr)], #[9])) := by
  decide +kernel

end SepAuto.WPOsFutex
