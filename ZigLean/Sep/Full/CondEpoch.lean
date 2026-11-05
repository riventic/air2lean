import ZigLean.Sep.Full.Cond
import ZigLean.Sep.Full.WordNewest

/-!
# The epoch ABA of the futex-epoch condition, as a schedule

The condition's waiter (`Io.Condition` of 0.16.0 and 0.17.0, `Thread.Condition.FutexImpl` of
0.15.2; `ZigLean/Sep/Full/Cond.lean`) saves the epoch before it registers and then sleeps at the
futex for that value. The futex compares values, not writes (`Thread.futexWait`: the kernel
reads the word's newest bytes). So after `2^32` increments of the 32-bit epoch the value is the
saved one again, and the wait sleeps though the epoch moved past the signal meant for it.

This module checks that schedule through the model's actual atomic and futex ops (the
condition's own ops; the mutex's unlock and lock between them are not part of the fact), for
every condition (`FCond`), every memory where its two words are valid and nothing is queued at
the epoch (`Calm`), and any threads `t`, `u`, `v` (they need not differ):

- waiter `t` has saved the epoch `e` and registered (the state is `(1, 0)`);
- one round (`Round`) of a waiter `u` and a signaller `v`: `u` registers (`Register`), `v`
  signals (`Signal`: `signals += 1`, `epoch += 1`, a wake that finds no thread at the futex),
  `u`'s futex wait returns at once (the epoch moved) and `u` takes the signal (`Consume`). The
  round leaves the state at `(1, 0)` and adds one to the epoch (`Calm.round`), and rounds
  iterate (`Calm.rounds`);
- after `2^32 - 1` rounds a last signal by `v` posts `t`'s signal (the state is `(1, 1)`) and
  brings the epoch back to `e`. Then `t`'s futex wait sleeps (`epoch_aba`).

No thread is then between its signal and its wake, and until another waiter registers every
`signal` finds `waiters = signals` and does nothing: the signal is pending and its wake is lost.
This is a liveness gap of the algorithm, not a safety one: no wrong value is returned and no
registration is miscounted. It is why the condition contract (`CondImpl`, any number of
waiters) bounds the epoch writes between a waiter's save and its enqueue below `2^32` (PR #397,
ruling 6264821278; the window `FCond.Fits.win`, which the client's rest keeps), and why a
contract may not demand that every implementation wake a sleeping waiter. Each `epoch += 1`
follows its signaller's own post (`FCond.SigStep`), so a client that bounds its posts bounds the
increments in that window; the window counts from the waiter's saved write, which may lag behind
the newest (`FCond.ld_newest` gives the newest at the load, `ZigLean/Sep/Full/Cond.lean`). The
schedule is a kernel-checked fact about the model's op runs in one chosen order, not a run of
the scheduler.
-/

namespace Zig
namespace Full
namespace FCond

open Conc

variable {γ : Type} (C : FCond γ)

/-- The condition's words at a point of the schedule: both valid, the state holding `w` and the
epoch `e`; no thread woken and none in the futex queue at the epoch. -/
structure Calm (m : Mem) (w e : BitVec 32) : Prop where
  s : C.S.Ok m
  ep : C.Ep.Ok m
  sv : C.S.Holds m w
  ev : C.Ep.Holds m e
  cs : m.clocks.size = m.threads.size
  wk : m.woken = #[]
  q : ∀ x ∈ m.waiters, x.2 ≠ C.Ep.key m

/-- `wait`'s registration by `u`, before it unlocks the mutex: an acquire load of the epoch (the
saved value `e`) and `waiters += 1` (relaxed), whose old `waiters` is below `65535` (the code's
assertion). -/
def Register (u : ThreadId) (e : BitVec 32) (m m' : Mem) : Prop :=
  ∃ (w : BitVec 32) (m₁ : Mem),
    ((atomicLoadAt (n := 32) 0 .acquire 4 C.Ep.ptr).run { m with current := u }).run =
      some (.ok (e, m₁)) ∧
    ((atomicRmwAt (n := 32) 0 .add false .relaxed 4 C.S.ptr 1).run m₁).run =
      some (.ok (w, m')) ∧
    w.toNat % 0x10000 < 0xFFFF

/-- `signal` by `v`: a relaxed load of the state `w`, which has `waiters > signals`, a weak
release `cmpxchg` to `signals += 1`, `epoch += 1` (release) and a futex wake of one waiter. -/
def Signal (v : ThreadId) (m m' : Mem) : Prop :=
  ∃ (w x : BitVec 32) (m₁ m₂ m₃ : Mem),
    ((atomicLoadAt (n := 32) 0 .relaxed 4 C.S.ptr).run { m with current := v }).run =
      some (.ok (w, m₁)) ∧
    w.toNat / 0x10000 < w.toNat % 0x10000 ∧
    ((cmpxchgWeakAt (n := 32) 0 .release .relaxed 4 C.S.ptr w (w + 0x10000)).run m₁).run =
      some (.ok (none, m₂)) ∧
    ((atomicRmwAt (n := 32) 0 .add false .release 4 C.Ep.ptr 1).run m₂).run =
      some (.ok (x, m₃)) ∧
    ((Thread.futexWakePtr C.Ep.ptr 1 []).run m₃).run = some (.ok ((), m'))

/-- `wait`'s loop by `u` with the saved epoch `e`: the futex wait returns without sleeping, an
acquire load of the epoch, a relaxed load of the state `w`, which has `signals > 0`, and a weak
acquire `cmpxchg` that takes the signal (`waiters -= 1`, `signals -= 1`). -/
def Consume (u : ThreadId) (e : BitVec 32) (m m' : Mem) : Prop :=
  ∃ (x w : BitVec 32) (m₁ m₂ m₃ : Mem),
    ((Thread.futexWait C.Ep.ptr e false).run { m with current := u }).run =
      some (.ok (false, m₁)) ∧
    ((atomicLoadAt (n := 32) 0 .acquire 4 C.Ep.ptr).run m₁).run = some (.ok (x, m₂)) ∧
    ((atomicLoadAt (n := 32) 0 .relaxed 4 C.S.ptr).run m₂).run = some (.ok (w, m₃)) ∧
    0 < w.toNat / 0x10000 ∧
    ((cmpxchgWeakAt 0 .acquire .relaxed 4 C.S.ptr w (w - 0x10001)).run m₃).run =
      some (.ok (none, m'))

/-- One round of waiter `u` and signaller `v` (module doc). -/
def Round (u v : ThreadId) (m m' : Mem) : Prop :=
  ∃ e m₁ m₂, C.Register u e m m₁ ∧ C.Signal v m₁ m₂ ∧ C.Consume u e m₂ m'

/-- `k` rounds of `u` and `v`. -/
def Rounds (u v : ThreadId) : Nat → Mem → Mem → Prop
  | 0, m, m' => m' = m
  | k + 1, m, m' => ∃ m₁, Rounds u v k m m₁ ∧ C.Round u v m₁ m'

variable {C}

theorem apartSE : C.S.b ≠ C.Ep.b ∨ C.S.o + 4 ≤ C.Ep.o ∨ C.Ep.o + 4 ≤ C.S.o :=
  .inr (.inl (by have := C.ep_o; omega))

theorem apartES : C.Ep.b ≠ C.S.b ∨ C.Ep.o + 4 ≤ C.S.o ∨ C.S.o + 4 ≤ C.Ep.o :=
  .inr (.inr (by have := C.ep_o; omega))

namespace Calm

variable {m : Mem} {w x : BitVec 32}

theorem cur (hA : C.Calm m w x) (t : ThreadId) : C.Calm { m with current := t } w x :=
  ⟨(hA.s.withCurrent t).1, (hA.ep.withCurrent t).1, hA.sv, hA.ev, hA.cs, hA.wk, hA.q⟩

theorem next {m' : Mem} {w' x' : BitVec 32} (hA : C.Calm m w x)
    (hs : FStepIn (fun _ => none) m m') (hS : C.S.Ok m') (hE : C.Ep.Ok m')
    (hsv : C.S.Holds m' w') (hev : C.Ep.Holds m' x') : C.Calm m' w' x' :=
  ⟨hS, hE, hsv, hev, by rw [hs.size, hs.threads]; exact hA.cs, by rw [hs.woken]; exact hA.wk,
    by rw [hs.waiters, hA.ep.key_of_addrs hs.addrs]; exact hA.q⟩

/-! ## The steps of the schedule -/

section Steps

variable (ht : m.current < m.threads.size)
include ht

theorem loadS (hA : C.Calm m w x) (ord : AtomicOrder) :
    ∃ m', ((atomicLoadAt (n := 32) 0 ord 4 C.S.ptr).run m).run = some (.ok (w, m')) ∧
      C.Calm m' w x ∧ m'.threads = m.threads ∧ m'.current = m.current := by
  obtain ⟨m', h, hS, hv, hs⟩ := hA.s.load_newest (ord := ord) ht hA.cs hA.sv
  obtain ⟨hE, hh⟩ := hA.s.apart_run hA.ep (by rw [hA.cs]; exact ht) apartSE (.inl ⟨0, ord, w, h⟩)
  exact ⟨m', h, hA.next hs hS hE hv (hA.ep.holds_of_hist hE hh hA.ev), hs.threads, hs.current⟩

theorem loadE (hA : C.Calm m w x) (ord : AtomicOrder) :
    ∃ m', ((atomicLoadAt (n := 32) 0 ord 4 C.Ep.ptr).run m).run = some (.ok (x, m')) ∧
      C.Calm m' w x ∧ m'.threads = m.threads ∧ m'.current = m.current := by
  obtain ⟨m', h, hE, hv, hs⟩ := hA.ep.load_newest (ord := ord) ht hA.cs hA.ev
  obtain ⟨hS, hh⟩ := hA.ep.apart_run hA.s (by rw [hA.cs]; exact ht) apartES (.inl ⟨0, ord, x, h⟩)
  exact ⟨m', h, hA.next hs hS hE (hA.s.holds_of_hist hS hh hA.sv) hv, hs.threads, hs.current⟩

theorem rmwS (hA : C.Calm m w x) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
    (v : BitVec 32) :
    ∃ m', ((atomicRmwAt 0 op signed ord 4 C.S.ptr v).run m).run = some (.ok (w, m')) ∧
      C.Calm m' (op.apply signed w v) x ∧ m'.threads = m.threads ∧ m'.current = m.current := by
  obtain ⟨m', h, hS, hv, hs⟩ := hA.s.rmw_newest (op := op) (signed := signed) (ord := ord)
    (v := v) ht hA.cs hA.sv
  obtain ⟨hE, hh⟩ := hA.s.apart_run hA.ep (by rw [hA.cs]; exact ht) apartSE
    (.inr (.inl ⟨0, op, signed, ord, v, w, h⟩))
  exact ⟨m', h, hA.next hs hS hE hv (hA.ep.holds_of_hist hE hh hA.ev), hs.threads, hs.current⟩

theorem rmwE (hA : C.Calm m w x) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
    (v : BitVec 32) :
    ∃ m', ((atomicRmwAt 0 op signed ord 4 C.Ep.ptr v).run m).run = some (.ok (x, m')) ∧
      C.Calm m' w (op.apply signed x v) ∧ m'.threads = m.threads ∧ m'.current = m.current := by
  obtain ⟨m', h, hE, hv, hs⟩ := hA.ep.rmw_newest (op := op) (signed := signed) (ord := ord)
    (v := v) ht hA.cs hA.ev
  obtain ⟨hS, hh⟩ := hA.ep.apart_run hA.s (by rw [hA.cs]; exact ht) apartES
    (.inr (.inl ⟨0, op, signed, ord, v, x, h⟩))
  exact ⟨m', h, hA.next hs hS hE (hA.s.holds_of_hist hS hh hA.sv) hv, hs.threads, hs.current⟩

theorem casS (hA : C.Calm m w x) (succ fail : AtomicOrder) (new : BitVec 32) :
    ∃ m', ((cmpxchgWeakAt 0 succ fail 4 C.S.ptr w new).run m).run = some (.ok (none, m')) ∧
      C.Calm m' new x ∧ m'.threads = m.threads ∧ m'.current = m.current := by
  obtain ⟨m', h, hS, hv, hs⟩ := hA.s.weakCas_newest (succ := succ) (fail := fail) (new := new)
    ht hA.cs hA.sv
  obtain ⟨hE, hh⟩ := hA.s.apart_run hA.ep (by rw [hA.cs]; exact ht) apartSE
    (.inr (.inr (.inr (.inl ⟨0, succ, fail, w, new, none, h⟩))))
  exact ⟨m', h, hA.next hs hS hE hv (hA.ep.holds_of_hist hE hh hA.ev), hs.threads, hs.current⟩

/-- A futex wait at the epoch for a value it does not hold returns at once. -/
theorem waitGo (hA : C.Calm m w x) {e : BitVec 32} (hne : x ≠ e) :
    ∃ m', ((Thread.futexWait C.Ep.ptr e false).run m).run = some (.ok (false, m')) ∧
      C.Calm m' w x ∧ m'.threads = m.threads ∧ m'.current = m.current := by
  have h := hA.ep.futexWait_newest (e := e) (sh := false) ht (by rw [hA.wk]; simp) hA.ev
  rw [if_neg hne, decide_eq_false hne] at h
  refine ⟨_, h, ?_, rfl, rfl⟩
  obtain ⟨hE, hhE⟩ := hA.ep.record_native (k := .atomicRead) rfl ht hA.cs rfl
  obtain ⟨hS, hhS⟩ := hA.s.record_apart_native (k := .atomicRead) apartES
  exact ⟨hS, hE, hA.s.holds_of_hist hS hhS hA.sv, hA.ep.holds_of_hist hE hhE hA.ev,
    by simp [Mem.recordAt, hA.cs], hA.wk, hA.q⟩

end Steps

/-! ## The schedule -/

variable {u v : ThreadId}

theorem register (hA : C.Calm m w x) (hu : u < m.threads.size)
    (hg : w.toNat % 0x10000 < 0xFFFF) :
    ∃ m', C.Register u x m m' ∧ C.Calm m' (w + 1) x ∧ m'.threads = m.threads := by
  obtain ⟨m₁, h₁, hA₁, ht₁, hc₁⟩ := (hA.cur u).loadE hu .acquire
  obtain ⟨m', h₂, hA₂, ht₂, -⟩ := hA₁.rmwS (by rw [ht₁, hc₁]; exact hu) .add false .relaxed 1
  exact ⟨m', ⟨w, m₁, h₁, h₂, hg⟩, hA₂, by rw [ht₂, ht₁]⟩

theorem signal (hA : C.Calm m w x) (hv : v < m.threads.size)
    (hg : w.toNat / 0x10000 < w.toNat % 0x10000) :
    ∃ m', C.Signal v m m' ∧ C.Calm m' (w + 0x10000) (x + 1) ∧ m'.threads = m.threads := by
  obtain ⟨m₁, h₁, hA₁, ht₁, hc₁⟩ := (hA.cur v).loadS hv .relaxed
  obtain ⟨m₂, h₂, hA₂, ht₂, hc₂⟩ := hA₁.casS (by rw [ht₁, hc₁]; exact hv) .release .relaxed
    (w + 0x10000)
  obtain ⟨m₃, h₃, hA₃, ht₃, -⟩ := hA₂.rmwE (by rw [ht₂, hc₂, ht₁, hc₁]; exact hv)
    .add false .release 1
  have h₄ : ((Thread.futexWakePtr C.Ep.ptr 1 []).run m₃).run = some (.ok ((), m₃)) := by
    rw [Thread.futexWakePtr_eq hA₃.ep.keyAt]; exact Thread.futexWake_run_idle hA₃.q
  exact ⟨m₃, ⟨w, x, m₁, m₂, m₃, h₁, hg, h₂, h₃, h₄⟩, hA₃, by rw [ht₃, ht₂, ht₁]⟩

theorem consume (hA : C.Calm m w x) (hu : u < m.threads.size) {e : BitVec 32} (hne : x ≠ e)
    (hg : 0 < w.toNat / 0x10000) :
    ∃ m', C.Consume u e m m' ∧ C.Calm m' (w - 0x10001) x ∧ m'.threads = m.threads := by
  obtain ⟨m₁, h₁, hA₁, ht₁, hc₁⟩ := (hA.cur u).waitGo hu hne
  obtain ⟨m₂, h₂, hA₂, ht₂, hc₂⟩ := hA₁.loadE (by rw [ht₁, hc₁]; exact hu) .acquire
  obtain ⟨m₃, h₃, hA₃, ht₃, hc₃⟩ := hA₂.loadS (by rw [ht₂, hc₂, ht₁, hc₁]; exact hu) .relaxed
  obtain ⟨m', h₄, hA₄, ht₄, -⟩ := hA₃.casS (by rw [ht₃, hc₃, ht₂, hc₂, ht₁, hc₁]; exact hu)
    .acquire .relaxed (w - 0x10001)
  exact ⟨m', ⟨x, w, m₁, m₂, m₃, h₁, h₂, h₃, hg, h₄⟩, hA₄, by rw [ht₄, ht₃, ht₂, ht₁]⟩

/-- **One round** leaves the state at `(1, 0)` and adds one to the epoch. -/
theorem round (hA : C.Calm m 1 x) (hu : u < m.threads.size) (hv : v < m.threads.size) :
    ∃ m', C.Round u v m m' ∧ C.Calm m' 1 (x + 1) ∧ m'.threads = m.threads := by
  obtain ⟨m₁, h₁, hA₁, ht₁⟩ := hA.register hu (by decide)
  obtain ⟨m₂, h₂, hA₂, ht₂⟩ := hA₁.signal (by rw [ht₁]; exact hv) (by decide)
  obtain ⟨m', h₃, hA₃, ht₃⟩ := hA₂.consume (by rw [ht₂, ht₁]; exact hu) (add_one_ne x)
    (by decide)
  have h1 : (1 : BitVec 32) + 1 + 0x10000 - 0x10001 = 1 := by decide
  rw [h1] at hA₃
  exact ⟨m', ⟨x, m₁, m₂, h₁, h₂, h₃⟩, hA₃, by rw [ht₃, ht₂, ht₁]⟩

/-- **The rounds iterate**: `k` rounds add `k` to the epoch (modulo `2^32`). -/
theorem rounds (hA : C.Calm m 1 x) (hu : u < m.threads.size) (hv : v < m.threads.size)
    (k : Nat) :
    ∃ m', C.Rounds u v k m m' ∧ C.Calm m' 1 (x + BitVec.ofNat 32 k) ∧ m'.threads = m.threads := by
  induction k with
  | zero => exact ⟨m, rfl, by simpa using hA, rfl⟩
  | succ k ih =>
    obtain ⟨m₁, h₁, hA₁, ht₁⟩ := ih
    obtain ⟨m', h₂, hA₂, ht₂⟩ := hA₁.round (by rw [ht₁]; exact hu) (by rw [ht₁]; exact hv)
    have hk : x + BitVec.ofNat 32 k + 1 = x + BitVec.ofNat 32 (k + 1) := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      try rfl
    rw [hk] at hA₂
    exact ⟨m', ⟨m₁, h₁, h₂⟩, hA₂, by rw [ht₂, ht₁]⟩

end Calm

/-- **The epoch ABA schedule** (module doc). The state is `(1, 0)` and the epoch `e`, as after
waiter `t` saved `e` and registered (`Calm.register`; `t`'s own registration is not part of the
statement). After `2^32 - 1` rounds of a waiter `u` and a signaller `v` and a last
signal by `v`, the state is `(1, 1)`: `t`'s signal is pending. The epoch holds `e` again, and
`t`'s futex wait for `e` sleeps. -/
theorem epoch_aba {m : Mem} {t u v : ThreadId} {e : BitVec 32} (hA : C.Calm m 1 e)
    (ht : t < m.threads.size) (hu : u < m.threads.size) (hv : v < m.threads.size) :
    ∃ m₁ m₂ m₃, C.Rounds u v (2 ^ 32 - 1) m m₁ ∧ C.Signal v m₁ m₂ ∧
      ((Thread.futexWait C.Ep.ptr e false).run { m₂ with current := t }).run =
        some (.ok (true, m₃)) ∧
      (t, C.Ep.key m₃) ∈ m₃.waiters ∧ C.S.Holds m₃ 0x10001 ∧ C.Ep.Holds m₃ e := by
  obtain ⟨m₁, h₁, hA₁, ht₁⟩ := hA.rounds hu hv (2 ^ 32 - 1)
  obtain ⟨m₂, h₂, hA₂, ht₂⟩ := hA₁.signal (by rw [ht₁]; exact hv) (by decide)
  have he : e + BitVec.ofNat 32 (2 ^ 32 - 1) + 1 = e := by
    have h0 : BitVec.ofNat 32 (2 ^ 32 - 1) + 1 = 0 := by decide
    rw [BitVec.add_assoc, h0]
    exact BitVec.add_zero e
  have hs : (1 : BitVec 32) + 0x10000 = 0x10001 := by decide
  rw [he, hs] at hA₂
  have hA₃ := hA₂.cur t
  have h := hA₃.ep.futexWait_newest (e := e) (sh := false)
    (show t < m₂.threads.size by rw [ht₂, ht₁]; exact ht)
    (by rw [hA₃.wk]; simp) hA₃.ev
  rw [if_pos rfl, decide_eq_true rfl] at h
  exact ⟨m₁, m₂, _, h₁, h₂, h, Array.mem_push.mpr (.inr rfl), hA₃.sv, hA₃.ev⟩

end FCond
end Full
end Zig
