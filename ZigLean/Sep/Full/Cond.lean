import ZigLean.Sep.Full.Event

/-!
# The futex-epoch condition, over full-state resources

A condition variable with a futex epoch (`Io.Condition` of 0.16.0 and 0.17.0,
`Thread.Condition.FutexImpl` of 0.15.2): a `u32` state word `S` (`waiters` in the low 16 bits,
`signals` in the high 16) and a `u32` epoch word `Ep` right after it. A waiter, holding the
mutex, loads the epoch (acquire), does `waiters += 1`, unlocks the mutex and then loops: a futex
wait at the epoch with the loaded value, an acquire load of the epoch, a relaxed load of the
state, and, while `signals > 0`, a weak acquire `cmpxchg` that takes one signal (`waiters -= 1`,
`signals -= 1`); after it took one it locks the mutex again. A signaller loads the state and,
while `waiters > signals`, does a weak release `cmpxchg` with `signals += 1`, then `epoch += 1`
(release) and wakes one waiter at the epoch. This module is the component once for every
protocol that has such a condition next to its mutex (`FLock.FitsOn`), and the rules of the
condition's ops in generated code; an implementation of a Zig version walks its code with them
(`CondImpl`).

`FCond γ` is the two words and a thread's place in the condition's code (`CPh`: `en` a waiter
before its epoch load, `ld i e` it loaded epoch write `i` (the newest) with the value `e`,
`reg i jr sn e` it did `waiters += 1` (state write `jr`; `sn`: it loaded epoch write `i + 1`),
`inc` a signaller after its `signals += 1`, `wk` after its `epoch += 1`). `FCond.Inv` is the
condition's invariant, modelled on the legacy `Proofs/Sync/Semaphore.lean` (`Era`): the state's
writes are `(0, 0)`, `(1, 0)`, `(1, 1)` (`SV`); while a waiter is registered, the state has its
write `jr` (`1`) and at most a signal after it (`0x10001`), and the epoch its write `i` and at
most one more, after the signal (`Era`); a thread asleep at the epoch is the registered waiter,
and the epoch is still write `i` or a signaller will wake it (no lost wakeup).

**Scope (one waiter, the newest epoch).** A waiter enters only when every other thread is out of
the condition's code (`hone`: no other waiter, no signaller between its `signals += 1` and its
wake) and after every epoch write (`hhb`), so that its acquire load reads the newest epoch write
and the futex value cannot be an older write's (ABA). A signaller's stops come after the
registration of a waiter (`hseen`). Reason: as for the event (`ZigLean/Sep/Full/Event.lean`),
the memory model's facts of a read give its happens-before floor, not the read-read coherence of
`Mem.seen`, and a full-state frame does not keep `Mem.seen`. Several waiters are a follow-up.

**The client's part.** Roles: `FCond.sx` are the ghost values that may signal (`Inv.sx`). A
thread in the condition's critical code (`en`, `ld`) holds the mutex (`Inv.crit`); one between
its signal and its wake (`inc`, `wk`) is out of the lock's code (`Inv.lp`); both run no lock
code, so a client's `FitsOn` `ok` excludes them (`CPh.busy`, `Fits.ok_c`) and a lock step keeps
the invariant (`Inv.lstep`). A step of the condition's code keeps the client's rest `U` given
the code's transition (`CPh.Next`; the entry `out → en` is the client's `hent` of
`CondImpl.wait_wp`) and the epoch's writes (`Fits.step`).
-/

namespace Zig
namespace Full

open Conc Proto

/-- Where a thread is in a condition's code (module doc). -/
inductive CPh where
  | out
  | en
  | ld (i : Nat) (e : BitVec 32)
  | reg (i jr : Nat) (sn : Bool) (e : BitVec 32)
  | inc
  | wk
  deriving DecidableEq

namespace CPh

/-- A waiter's place. -/
def waits : CPh → Bool
  | .en | .ld _ _ | .reg _ _ _ _ => true
  | _ => false

/-- The critical code: the waiter holds the mutex. -/
def crit : CPh → Bool
  | .en | .ld _ _ => true
  | _ => false

/-- A signaller between its `signals += 1` and its wake. -/
def sig : CPh → Bool
  | .inc | .wk => true
  | _ => false

/-- A place where the thread runs no lock code. -/
def busy (p : CPh) : Bool := p.crit || p.sig

/-- The transitions of the condition's code, without the entry `out → en` (module doc). -/
def Next : CPh → CPh → Prop
  | .en, .ld _ _ => True
  | .ld _ _, .reg _ _ _ _ => True
  | .reg _ _ _ _, .reg _ _ _ _ => True
  | .reg _ _ _ _, .out => True
  | .out, .inc => True
  | .inc, .wk => True
  | .wk, .out => True
  | a, b => a = b

theorem Next.refl (a : CPh) : Next a a := by
  cases a <;> simp [Next]

/-- A step of the code into a waiter's place comes from one. -/
theorem Next.waits {a b : CPh} (h : Next a b) (hb : b.waits = true) : a.waits = true := by
  cases a <;> cases b <;> first | rfl | exact hb | (simp [Next] at h; done) | (simp [CPh.waits] at hb; done)

/-- A step of the code into the critical code comes from it. -/
theorem Next.crit {a b : CPh} (h : Next a b) (hb : b.crit = true) : a.crit = true := by
  cases a <;> cases b <;> first | rfl | exact hb | (simp [Next] at h; done) | (simp [CPh.crit] at hb; done)

end CPh

/-- A futex-epoch condition (module doc): its state and epoch words, and a thread's place in
its code. -/
structure FCond (γ : Type) where
  S : Word 32 4
  Ep : Word 32 4
  ep_b : Ep.b = S.b
  ep_o : Ep.o = S.o + 4
  ph : γ → CPh
  set : γ → CPh → γ
  ph_set : ∀ g p, ph (set g p) = p
  set_set : ∀ g p q, set (set g p) q = set g q
  set_self : ∀ g, set g (ph g) = g
  /-- The ghost values of the threads that may signal (the protocol's roles). -/
  sx : γ → Prop
  sx_set : ∀ g p, sx (set g p) ↔ sx g

namespace FCond

variable {γ : Type} (C : FCond γ)

/-- The newest write of the state. -/
abbrev lastS (m : Mem) : Word.Entry := (C.S.hist m)[(C.S.hist m).size - 1]!

/-- The newest write of the epoch. -/
abbrev lastE (m : Mem) : Word.Entry := (C.Ep.hist m)[(C.Ep.hist m).size - 1]!

/-- A value of the state: `(0, 0)`, `(1, 0)` or `(1, 1)`. -/
def SV (x : Word.Entry) : Prop :=
  x.Val (0 : BitVec 32) ∨ x.Val (1 : BitVec 32) ∨ x.Val (0x10001 : BitVec 32)

/-- A signal is pending: the newest state is `(1, 1)`. -/
def Signalled (m : Mem) : Prop := (C.lastS m).Val (0x10001 : BitVec 32)

/-- The writes of the condition while thread `u` waits (`CPh.reg i jr sn e`). -/
structure Era (G : ThreadId → γ) (m : Mem) (u i jr : Nat) (sn : Bool) (e : BitVec 32) :
    Prop where
  ssz : (C.S.hist m).size = jr + 1 ∨ (C.S.hist m).size = jr + 2
  s0 : (C.S.hist m)[jr]!.Val (1 : BitVec 32)
  s1 : (C.S.hist m).size = jr + 2 → (C.S.hist m)[jr + 1]!.Val (0x10001 : BitVec 32)
  esz : (C.Ep.hist m).size = i + 1 ∨ ((C.Ep.hist m).size = i + 2 ∧ (C.S.hist m).size = jr + 2 ∧
    VClock.le (C.S.hist m)[jr + 1]!.clock (C.Ep.hist m)[i + 1]!.relClock = true)
  eval : (C.Ep.hist m)[i]!.Val e ∧
    ((C.Ep.hist m).size = i + 2 → (C.Ep.hist m)[i + 1]!.Val (e + 1))
  seen : sn = true → (C.Ep.hist m).size = i + 2 ∧
    VClock.le (C.Ep.hist m)[i + 1]!.relClock (m.clocks[u]!) = true
  cs : VClock.le (C.S.hist m)[jr]!.clock (m.clocks[u]!) = true
  ce : VClock.le (C.Ep.hist m)[i]!.clock (m.clocks[u]!) = true
  pend : (C.S.hist m).size = jr + 2 → (C.Ep.hist m).size = i + 1 → ∃ v, C.ph (G v) = .inc

/-- The condition's invariant, with the lock's places (module doc). -/
structure Inv (L : FLock γ) (G : ThreadId → γ) (m : Mem) : Prop where
  sv : ∀ k < (C.S.hist m).size, SV (C.S.hist m)[k]!
  /-- One waiter at a time (module doc, scope). -/
  one : ∀ u v, (C.ph (G u)).waits → (C.ph (G v)).waits → u = v
  /-- Without a registered waiter the state is `(0, 0)`. -/
  idle : (∀ u i jr sn e, C.ph (G u) ≠ .reg i jr sn e) → (C.lastS m).Val (0 : BitVec 32)
  era : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Era G m u i jr sn e
  /-- Every epoch write happened before the waiter at `en`. -/
  en : ∀ u, C.ph (G u) = .en → ∀ j < (C.Ep.hist m).size,
    VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[u]!) = true
  /-- The waiter at `ld i e` loaded the newest epoch write `i`. -/
  ld : ∀ u i e, C.ph (G u) = .ld i e → (C.Ep.hist m).size = i + 1 ∧
    (C.Ep.hist m)[i]!.Val e ∧ VClock.le (C.Ep.hist m)[i]!.clock (m.clocks[u]!) = true
  /-- No signaller between its signal and its wake while a waiter is in the critical code. -/
  nosig : ∀ u v, (C.ph (G u)).crit → (C.ph (G v)).sig = false
  /-- One signaller between its signal and its wake. -/
  sone : ∀ u v, (C.ph (G u)).sig → (C.ph (G v)).sig → u = v
  inc : ∀ u v i jr sn e, C.ph (G u) = .inc → C.ph (G v) = .reg i jr sn e →
    (C.S.hist m).size = jr + 2 ∧ (C.Ep.hist m).size = i + 1 ∧
    VClock.le (C.S.hist m)[jr + 1]!.clock (m.clocks[u]!) = true
  wk : ∀ u v i jr sn e, C.ph (G u) = .wk → C.ph (G v) = .reg i jr sn e →
    (C.Ep.hist m).size = i + 2
  /-- A thread in the futex queue at the epoch is the registered waiter, and the epoch is still
  its write `i` or a signaller will wake it (no lost wakeup). -/
  q : ∀ w ∈ m.waiters, w.2 = C.Ep.ptr → ∃ i jr e, C.ph (G w.1) = .reg i jr false e ∧
    ((C.Ep.hist m).size = i + 1 ∨ ∃ v, C.ph (G v) = .wk)
  /-- A waiter in the futex queue is at the epoch or at the mutex. -/
  qw : ∀ w ∈ m.waiters, (C.ph (G w.1)).waits → w.2 = C.Ep.ptr ∨ w.2 = L.ptr
  crit : ∀ u, (C.ph (G u)).crit → L.ph (G u) = .holds
  lp : ∀ u, (C.ph (G u)).sig → L.ph (G u) = .out
  sx : ∀ u, (C.ph (G u)).sig → C.sx (G u)

/-- A step of thread `t` in the condition's code, as the protocol's rest sees it: no change, an
op at the state or the epoch (a read, or an RMW of the newest write), the futex wait's sleep at
the epoch, the return of a futex wait, or a futex wake at the epoch. -/
inductive MStep (t : ThreadId) (m : Mem) : Mem → Prop
  | same : MStep t m m
  | op {W : Word 32 4} {m' : Mem} : (W = C.S ∨ W = C.Ep) → W.Op t { m with current := t } m' →
      W.Ok m' → (W.hist m' = W.hist m ∨ ∃ (ord : AtomicOrder) (v : BitVec 32),
        W.hist m' = (W.hist m).push (Word.rmwEnt m' t ord (W.hist m)[(W.hist m).size - 1]! v)) →
      MStep t m m'
  | sleep {M : Mem} : C.Ep.Op t { m with current := t } M → C.Ep.hist M = C.Ep.hist m →
      C.Ep.Ok M → M.blocks = m.blocks → MStep t m { M with waiters := M.waiters.push (t, C.Ep.ptr) }
  | woken : MStep t m { m with current := t, woken := m.woken.erase t }
  | resume : MStep t m { m with current := t }
  | wake {m' : Mem} (c : Nat) (cs : List Nat) :
      ((Thread.futexWake C.Ep.ptr c cs).run { m with current := t }).run = some (.ok ((), m')) →
      MStep t m m'

/-- A protocol keeps the condition (module doc). -/
structure Fits (L : FLock γ) {Tgt : Type} (P : Proto Tgt γ)
    (U : (ThreadId → γ) → Res → Mem → Prop) (ok : γ → Prop) : Prop where
  rS : C.S.InRest U
  rE : C.Ep.InRest U
  apS : C.S.ApartL L.toLockWord
  apE : C.Ep.ApartL L.toLockWord
  inv : ∀ G rX m, U G rX m → C.Inv L G m
  fin : ∀ g, P.fin g → C.ph g = .out
  joins : ∀ g, P.joins g → C.ph g = .out
  /-- The condition's place and the lock's are independent parts of a ghost value. -/
  lph : ∀ g p, L.ph (C.set g p) = L.ph g
  lpart : ∀ g p, L.part (C.set g p) = L.part g
  lheld : ∀ g p, L.held (C.set g p) = L.held g
  lR : ∀ G t p r, L.R G r → L.R (upd G t (C.set (G t) p)) r
  ph_l : ∀ g q h, C.ph (L.set g q h) = C.ph g
  set_l : ∀ g p q h, C.set (L.set g q h) p = L.set (C.set g p) q h
  ph_part : ∀ g r, C.ph (L.setPart g r) = C.ph g
  set_part : ∀ g p r, C.set (L.setPart g r) p = L.setPart (C.set g p) r
  sx_l : ∀ g q h, C.sx (L.set g q h) ↔ C.sx g
  sx_part : ∀ g r, C.sx (L.setPart g r) ↔ C.sx g
  /-- A thread out of the condition's busy code runs lock code: `ok` reads no other place. -/
  ok_c : ∀ g p q, p.busy = false → q.busy = false → (ok (C.set g p) ↔ ok (C.set g q))
  /-- A step of a thread out of the lock's code on its own part (a stack block of the
  condition's code) keeps the rest, given the lock's and the condition's invariants after it. -/
  own : ∀ G rY m m' t r (W : Word 32 4), (W = C.S ∨ W = C.Ep) → L.ph (G t) = .out →
    U G (rsum (W.cellsR m) rY) m → (∀ l, W.In l → rY.heap l = none) → m.current = t →
    StepIn (rsum (W.cellsR m) rY).heap.erase m m' → W.KeepK m m' →
    L.Inv (upd G t (L.setPart (G t) r)) (rsum (W.cellsR m') rY) m' →
    C.Inv L (upd G t (L.setPart (G t) r)) m' →
    U (upd G t (L.setPart (G t) r)) (rsum (W.cellsR m') rY) m'
  /-- A step of the condition's code keeps the rest, with the stepping thread's transition
  (`CPh.Next`), its lock place (the same, or `out`/`away` around a futex wait), and the epoch's
  writes (they change only at a signaller's `epoch += 1`), given the condition's invariant after
  it. -/
  step : ∀ G rY m m' t p q h (W : Word 32 4), (W = C.S ∨ W = C.Ep) → CPh.Next (C.ph (G t)) p →
    ((q = L.ph (G t) ∧ h = L.held (G t)) ∨
      ((L.ph (G t) = .out ∨ L.ph (G t) = .away) ∧ (q = .out ∨ q = .away) ∧ h = rnil)) →
    U G (rsum (W.cellsR m) rY) m → (∀ l, W.In l → rY.heap l = none) → C.MStep t m m' →
    (C.Ep.hist m' = C.Ep.hist m ∨ C.ph (G t) = .inc) →
    C.Inv L (upd G t (L.set (C.set (G t) p) q h)) m' →
    U (upd G t (L.set (C.set (G t) p) q h)) (rsum (W.cellsR m') rY) m'

variable {C}

/-! ## Facts of the writes -/

theorem add_one_ne (e : BitVec 32) : e + 1 ≠ e := by bv_omega

theorem SV.cases {x : Word.Entry} (h : SV x) {b : BitVec 32} (hb : x.Val b) :
    b = 0 ∨ b = 1 ∨ b = 0x10001 := by
  rcases h with h | h | h
  · exact .inl (FEvent.val_eq hb h)
  · exact .inr (.inl (FEvent.val_eq hb h))
  · exact .inr (.inr (FEvent.val_eq hb h))

/-- The newest write of a word with a write pushed. -/
theorem last_push {h : Array Word.Entry} {x : Word.Entry} : (h.push x)[(h.push x).size - 1]! = x := by
  simp only [Array.size_push, Nat.add_sub_cancel]; exact FEvent.get_push_eq

theorem ne_of_val {x : Word.Entry} {a b : BitVec 32} (ha : x.Val a) (hne : a ≠ b) : ¬ x.Val b :=
  fun hb => hne (FEvent.val_eq ha hb)

variable {L : FLock γ}

/-- A registered waiter: the newest state write is its `(1, 0)` or the signal `(1, 1)`. -/
theorem Era.last {G : ThreadId → γ} {m : Mem} {u i jr : Nat} {sn : Bool} {e : BitVec 32}
    (h : C.Era G m u i jr sn e) :
    ((C.S.hist m).size = jr + 1 ∧ (C.lastS m).Val (1 : BitVec 32)) ∨
    ((C.S.hist m).size = jr + 2 ∧ (C.lastS m).Val (0x10001 : BitVec 32)) := by
  rcases h.ssz with hs | hs
  · refine .inl ⟨hs, ?_⟩; unfold FCond.lastS; rw [hs, Nat.add_sub_cancel]; exact h.s0
  · refine .inr ⟨hs, ?_⟩; unfold FCond.lastS; rw [hs, show jr + 2 - 1 = jr + 1 by omega]
    exact h.s1 hs

/-- `Era` after a step that keeps the writes and moves the clocks forward. -/
theorem Era.mono {G G' : ThreadId → γ} {m m' : Mem} {u i jr : Nat} {sn : Bool} {e : BitVec 32}
    (h : C.Era G m u i jr sn e) (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m)
    (hc : VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hinc : ∀ v, C.ph (G v) = .inc → ∃ w, C.ph (G' w) = .inc) : C.Era G' m' u i jr sn e where
  ssz := by rw [hS]; exact h.ssz
  s0 := by rw [hS]; exact h.s0
  s1 := by rw [hS]; exact h.s1
  esz := by rw [hS, hE]; exact h.esz
  eval := by rw [hE]; exact h.eval
  seen := fun hsn => by
    rw [hE]; obtain ⟨h1, h2⟩ := h.seen hsn; exact ⟨h1, VClock.le_trans h2 hc⟩
  cs := by rw [hS]; exact VClock.le_trans h.cs hc
  ce := by rw [hE]; exact VClock.le_trans h.ce hc
  pend := fun h1 h2 => by
    rw [hS] at h1; rw [hE] at h2
    obtain ⟨v, hv⟩ := h.pend h1 h2; exact hinc v hv

/-! ## The invariant after a step -/

/-- A step that keeps the writes of both words and the futex queue (a read, a return from a
futex wait, a change of `t`'s lock place): the other threads keep their ghost values, and `t`
changes its place as the premises say. -/
theorem Inv.move {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} (hI : C.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u)
    (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m)
    (hap : C.Ep.ptr ≠ L.ptr) (hwt : ∀ w, w.2 ≠ L.ptr → w ∈ m'.waiters → w ∈ m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hwaits : (C.ph (G' t)).waits → (C.ph (G t)).waits)
    (hcr : (C.ph (G' t)).crit → (C.ph (G t)).crit ∧ L.ph (G' t) = .holds)
    (hsig : (C.ph (G' t)).sig ∨ (C.ph (G t)).sig →
      C.ph (G' t) = C.ph (G t) ∧ L.ph (G' t) = L.ph (G t) ∧ (C.sx (G t) → C.sx (G' t)))
    (hen : C.ph (G' t) = .en → ∀ j < (C.Ep.hist m).size,
      VClock.le (C.Ep.hist m)[j]!.clock (m'.clocks[t]!) = true)
    (hld : ∀ i e, C.ph (G' t) = .ld i e → (C.Ep.hist m).size = i + 1 ∧
      (C.Ep.hist m)[i]!.Val e ∧ VClock.le (C.Ep.hist m)[i]!.clock (m'.clocks[t]!) = true)
    (hreg : ∀ i jr sn e, C.ph (G' t) = .reg i jr sn e → ∃ sn', C.ph (G t) = .reg i jr sn' e ∧
      (sn = true → sn' = true ∨ ((C.Ep.hist m).size = i + 2 ∧
        VClock.le (C.Ep.hist m)[i + 1]!.relClock (m'.clocks[t]!) = true)))
    (hreg' : ∀ i jr sn e, C.ph (G t) = .reg i jr sn e → ∃ sn', C.ph (G' t) = .reg i jr sn' e)
    (htq : ∀ w ∈ m.waiters, w.1 = t → ((C.ph (G' t)).waits → w.2 = C.Ep.ptr ∨ w.2 = L.ptr) ∧
      (w.2 = C.Ep.ptr → C.ph (G' t) = C.ph (G t))) :
    C.Inv L G' m' := by
  -- the other threads
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  have hsig' : ∀ u, (C.ph (G u)).sig → C.ph (G' u) = C.ph (G u) := fun u hu => by
    by_cases e : u = t
    · subst e; exact (hsig (.inr hu)).1
    · exact hph u e
  have hinc : ∀ v, C.ph (G v) = .inc → ∃ w, C.ph (G' w) = .inc := fun v hv =>
    ⟨v, by rw [hsig' v (by rw [hv]; rfl), hv]⟩
  have hwk : ∀ v, C.ph (G v) = .wk → C.ph (G' v) = .wk := fun v hv => by
    rw [hsig' v (by rw [hv]; rfl), hv]
  have hregu : ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → ∃ sn', C.ph (G u) = .reg i jr sn' e :=
    fun u i jr sn e hu => by
      by_cases e' : u = t
      · subst e'; obtain ⟨sn', h, -⟩ := hreg i jr sn e hu; exact ⟨sn', h⟩
      · exact ⟨sn, by rw [← hph u e']; exact hu⟩
  have hsigu : ∀ u, (C.ph (G' u)).sig → (C.ph (G u)).sig := fun u hu => by
    by_cases e : u = t
    · subst e; rw [← (hsig (.inl hu)).1]; exact hu
    · rwa [hph u e] at hu
  refine ⟨by rw [hS]; exact hI.sv, fun u v hu hv => ?_, fun hn => ?_, fun u i jr sn e hu => ?_,
    fun u hu j hj => ?_, fun u i e hu => ?_, fun u v hu => ?_, fun u v hu hv => ?_,
    fun u v i jr sn e hu hv => ?_, fun u v i jr sn e hu hv => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · -- one
    have key : ∀ x, (C.ph (G' x)).waits → (C.ph (G x)).waits := fun x hx => by
      by_cases e : x = t
      · subst e; exact hwaits hx
      · rwa [hph x e] at hx
    exact hI.one u v (key u hu) (key v hv)
  · -- idle
    unfold FCond.lastS; rw [hS]; refine hI.idle fun u i jr sn e hu => ?_
    by_cases e' : u = t
    · subst e'; obtain ⟨sn', h⟩ := hreg' i jr sn e hu; exact hn u i jr sn' e h
    · exact hn u i jr sn e (by rw [hph u e']; exact hu)
  · -- era
    by_cases e' : u = t
    · subst e'
      obtain ⟨sn', h, hsn⟩ := hreg i jr sn e hu
      have hera := (hI.era u i jr sn' e h).mono hS hE (hclk u) hinc
      refine { hera with seen := fun hs => ?_ }
      rcases hsn hs with rfl | ⟨h1, h2⟩
      · exact hera.seen rfl
      · rw [hE]; exact ⟨h1, h2⟩
    · exact (hI.era u i jr sn e (by rw [← hph u e']; exact hu)).mono hS hE (hclk u) hinc
  · -- en
    rw [hE] at hj ⊢
    by_cases e' : u = t
    · subst e'; exact hen hu j hj
    · rw [hph u e'] at hu; exact VClock.le_trans (hI.en u hu j hj) (hclk u)
  · -- ld
    rw [hE]
    by_cases e' : u = t
    · subst e'; exact hld i e hu
    · rw [hph u e'] at hu
      obtain ⟨h1, h2, h3⟩ := hI.ld u i e hu
      exact ⟨h1, h2, VClock.le_trans h3 (hclk u)⟩
  · -- nosig
    cases hs : (C.ph (G' v)).sig
    · rfl
    · have hcu : (C.ph (G u)).crit := by
        by_cases e : u = t
        · subst e; exact (hcr hu).1
        · rwa [hph u e] at hu
      have := hI.nosig u v hcu
      rw [hsigu v hs] at this; cases this
  · -- sone
    exact hI.sone u v (hsigu u hu) (hsigu v hv)
  · -- inc
    have hu' : C.ph (G u) = .inc := by rw [← hsig' u (hsigu u (by rw [hu]; rfl))]; exact hu
    obtain ⟨sn', hv'⟩ := hregu v i jr sn e hv
    obtain ⟨h1, h2, h3⟩ := hI.inc u v i jr sn' e hu' hv'
    rw [hS, hE]; exact ⟨h1, h2, VClock.le_trans h3 (hclk u)⟩
  · -- wk
    have hu' : C.ph (G u) = .wk := by rw [← hsig' u (hsigu u (by rw [hu]; rfl))]; exact hu
    obtain ⟨sn', hv'⟩ := hregu v i jr sn e hv
    rw [hE]; exact hI.wk u v i jr sn' e hu' hv'
  · -- q
    have hw := hwt w (by rw [hp]; exact hap) hw
    obtain ⟨i, jr, e, h1, h2⟩ := hI.q w hw hp
    refine ⟨i, jr, e, ?_, ?_⟩
    · by_cases e' : w.1 = t
      · rw [e', (htq w hw e').2 hp, ← e']; exact h1
      · rw [hph _ e']; exact h1
    · rw [hE]
      rcases h2 with h2 | ⟨v, hv⟩
      · exact .inl h2
      · exact .inr ⟨v, hwk v hv⟩
  · -- qw
    by_cases hl : w.2 = L.ptr
    · exact .inr hl
    have hw := hwt w hl hw
    by_cases e' : w.1 = t
    · exact (htq w hw e').1 (by rw [← e']; exact hp)
    · rw [hph _ e'] at hp; exact hI.qw w hw hp
  · -- crit
    by_cases e' : u = t
    · subst e'; exact (hcr hu).2
    · rw [hph u e'] at hu; rw [hG u e']; exact hI.crit u hu
  · -- lp
    by_cases e' : u = t
    · subst e'
      obtain ⟨h1, h2, -⟩ := hsig (.inl hu)
      rw [h2]; exact hI.lp u (by rw [← h1]; exact hu)
    · rw [hph u e'] at hu; rw [hG u e']; exact hI.lp u hu
  · -- sx
    by_cases e' : u = t
    · subst e'
      obtain ⟨h1, -, h3⟩ := hsig (.inl hu)
      exact h3 (hI.sx u (by rw [← h1]; exact hu))
    · rw [hph u e'] at hu; rw [hG u e']; exact hI.sx u hu

/-- A thread enters the wait (`out` → `en`) holding the mutex, when every other thread is out of
the condition's code and every epoch write happened before it (module doc, scope). -/
theorem Inv.enter {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ}
    (hI : C.Inv L (upd G t g) m) (hg : C.ph g = .out) (hgh : L.ph (C.set g .en) = .holds)
    (hnq : ∀ w ∈ m.waiters, w.1 ≠ t) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true) :
    C.Inv L (upd G t (C.set g .en)) m := by
  have hen : C.ph (upd G t (C.set g .en) t) = .en := by rw [upd_self, C.ph_set]
  have hout : ∀ u, u ≠ t → C.ph (upd G t (C.set g .en) u) = .out := fun u e => by
    rw [upd_ne _ _ e, hone u e]
  have hph0 : ∀ u, C.ph (upd G t g u) = .out := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hg]
    · rw [upd_ne _ _ e, hone u e]
  -- every thread is at `en` (`t`) or out
  have hcase : ∀ u, (u = t ∧ C.ph (upd G t (C.set g .en) u) = .en) ∨
      (u ≠ t ∧ C.ph (upd G t (C.set g .en) u) = .out) := fun u => by
    by_cases e : u = t
    · subst e; exact .inl ⟨rfl, hen⟩
    · exact .inr ⟨e, hout u e⟩
  refine ⟨hI.sv, fun u v hu hv => ?_, fun _ => ?_, fun u i jr sn e hu => ?_, fun u hu j hj => ?_,
    fun u i e hu => ?_, fun u v _ => ?_, fun u v hu _ => ?_, fun u v i jr sn e hu _ => ?_,
    fun u v i jr sn e hu _ => ?_, fun w hw hp => ?_, fun w hw hp => ?_, fun u hu => ?_,
    fun u hu => ?_, fun u hu => ?_⟩
  · rcases hcase u with ⟨rfl, -⟩ | ⟨-, h⟩
    · rcases hcase v with ⟨rfl, -⟩ | ⟨-, h⟩
      · rfl
      · rw [h] at hv; cases hv
    · rw [h] at hu; cases hu
  · exact hI.idle fun u i jr sn e hu => by rw [hph0] at hu; cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase u with ⟨rfl, -⟩ | ⟨-, h⟩
    · exact hhb j hj
    · rw [h] at hu; cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase v with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> rfl
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · obtain ⟨i, jr, e, h1, -⟩ := hI.q w hw hp
    rw [hph0] at h1; cases h1
  · rcases hcase w.1 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (hnq w hw)
    · rw [h] at hp; cases hp
  · rcases hcase u with ⟨rfl, -⟩ | ⟨-, h⟩
    · rw [upd_self]; exact hgh
    · rw [h] at hu; cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu

/-- The waiter's `waiters += 1` (`ld i e` → `reg i jr false e`, state write `jr`). -/
theorem Inv.reg {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    {i : Nat} {e : BitVec 32} (hI : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u)
    (ht0 : C.ph (G t) = .ld i e) (ht1 : C.ph (G' t) = .reg i (C.S.hist m).size false e)
    (hS : C.S.hist m' = (C.S.hist m).push (Word.rmwEnt m' t ord (C.lastS m) (1 : BitVec 32)))
    (hE : C.Ep.hist m' = C.Ep.hist m) (hwt : m'.waiters = m.waiters)
    (hnq : ∀ w ∈ m.waiters, w.1 ≠ t)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    C.Inv L G' m' := by
  have hsz : (C.S.hist m').size = (C.S.hist m).size + 1 := by rw [hS]; simp
  have hold : ∀ k, k < (C.S.hist m).size → (C.S.hist m')[k]! = (C.S.hist m)[k]! := fun k hk => by
    rw [hS]; exact FEvent.get_push_lt hk
  have hnew : (C.S.hist m')[(C.S.hist m).size]! = Word.rmwEnt m' t ord (C.lastS m) (1 : BitVec 32) := by
    rw [hS]; exact FEvent.get_push_eq
  have htw : (C.ph (G t)).waits := by rw [ht0]; rfl
  -- every other thread is out of the waiter's places
  have hnw : ∀ u, u ≠ t → (C.ph (G u)).waits = false := fun u hu => by
    cases h : (C.ph (G u)).waits
    · rfl
    · exact absurd (hI.one u t h htw) hu
  have hns : ∀ u, (C.ph (G u)).sig = false := fun u => hI.nosig t u (by rw [ht0]; rfl)
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  -- a place of another thread that is a waiter's or a signaller's is impossible
  have hno : ∀ u, u ≠ t → ∀ p, C.ph (G' u) = p → (p.waits || p.sig) = true → False := by
    intro u hu p hp hw
    rw [hph u hu] at hp
    have h1 := hnw u hu; have h2 := hns u
    rw [hp] at h1 h2; rw [h1, h2] at hw; cases hw
  have hsig' : ∀ u, (C.ph (G' u)).sig = false := fun u => by
    by_cases e : u = t
    · subst e; rw [ht1]; rfl
    · cases h : (C.ph (G' u)).sig
      · rfl
      · exact (hno u e _ rfl (by rw [h, Bool.or_true])).elim
  have hwt' : ∀ u, (C.ph (G' u)).waits → u = t := fun u h => by
    by_cases e : u = t
    · exact e
    · exact (hno u e _ rfl (by rw [h, Bool.true_or])).elim
  have hninc : ∀ u p, C.ph (G' u) = p → p.sig = true → False := fun u p hp h => by
    have := hsig' u; rw [hp, h] at this; cases this
  refine ⟨fun k hk => ?_, fun u v hu hv => (hwt' u hu).trans (hwt' v hv).symm,
    fun hn => absurd ht1 (hn t _ _ _ _), fun u i' jr sn e' hu => ?_,
    fun u hu => absurd (hwt' u (by rw [hu]; rfl)) (fun h => by subst h; rw [ht1] at hu; cases hu),
    fun u i' e' hu => absurd (hwt' u (by rw [hu]; rfl)) (fun h => by subst h; rw [ht1] at hu; cases hu),
    fun u v _ => hsig' v, fun u v hu _ => (hninc u _ rfl hu).elim,
    fun u v i' jr sn e' hu _ => (hninc u _ hu rfl).elim,
    fun u v i' jr sn e' hu _ => (hninc u _ hu rfl).elim,
    fun w hw hp => ?_, fun w hw hp => ?_, fun u hu => ?_,
    fun u hu => (hninc u _ rfl hu).elim, fun u hu => (hninc u _ rfl hu).elim⟩
  · rw [hsz] at hk
    rcases (by omega : k < (C.S.hist m).size ∨ k = (C.S.hist m).size) with hk' | rfl
    · rw [hold k hk']; exact hI.sv k hk'
    · rw [hnew]; exact .inr (.inl FEvent.rmwEnt_val)
  · -- the new registration
    have e1 := hwt' u (by rw [hu]; rfl); subst e1
    rw [ht1] at hu; cases hu
    obtain ⟨hi1, hie, hic⟩ := hI.ld u i e ht0
    exact {
      ssz := .inl hsz
      s0 := by rw [hnew]; exact FEvent.rmwEnt_val
      s1 := fun h => by omega
      esz := .inl (by rw [hE]; exact hi1)
      eval := ⟨by rw [hE]; exact hie, fun h => by rw [hE] at h; omega⟩
      seen := fun h => by cases h
      cs := by rw [hnew]; exact VClock.le_refl _
      ce := by rw [hE]; exact VClock.le_trans hic (hclk u)
      pend := fun h => by omega }
  · rw [hwt] at hw
    obtain ⟨i', jr, e', h1, -⟩ := hI.q w hw hp
    have := hI.one w.1 t (by rw [h1]; rfl) htw
    exact absurd this (hnq w hw)
  · rw [hwt] at hw
    exact absurd (hwt' w.1 hp) (hnq w hw)
  · have e1 := hwt' u (by
      cases h : (C.ph (G' u)) <;> rw [h] at hu <;> first | rfl | cases hu)
    subst e1; rw [ht1] at hu; cases hu

/-- The waiter takes the signal (`reg` → `out`): its `cmpxchg((1, 1) → (0, 0))` succeeded. -/
theorem Inv.consume {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    {i jr : Nat} {sn : Bool} {e : BitVec 32} (hI : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u)
    (ht0 : C.ph (G t) = .reg i jr sn e) (ht1 : C.ph (G' t) = .out)
    (hS : C.S.hist m' = (C.S.hist m).push (Word.rmwEnt m' t ord (C.lastS m) (0 : BitVec 32)))
    (hwt : m'.waiters = m.waiters) (hnq : ∀ w ∈ m.waiters, w.1 ≠ t) :
    C.Inv L G' m' := by
  have hsz : (C.S.hist m').size = (C.S.hist m).size + 1 := by rw [hS]; simp
  have hold : ∀ k, k < (C.S.hist m).size → (C.S.hist m')[k]! = (C.S.hist m)[k]! := fun k hk => by
    rw [hS]; exact FEvent.get_push_lt hk
  have htw : (C.ph (G t)).waits := by rw [ht0]; rfl
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  -- no thread is a waiter after it
  have hnw : ∀ u, (C.ph (G' u)).waits = false := fun u => by
    by_cases e' : u = t
    · subst e'; rw [ht1]; rfl
    · cases h : (C.ph (G' u)).waits
      · rfl
      · rw [hph u e'] at h; exact absurd (hI.one u t h htw) e'
  have hnw' : ∀ u p, C.ph (G' u) = p → p.waits = true → False := fun u p hp h => by
    have := hnw u; rw [hp, h] at this; cases this
  have hsg : ∀ u, (C.ph (G' u)).sig → (C.ph (G u)).sig := fun u hu => by
    by_cases e' : u = t
    · subst e'; rw [ht1] at hu; cases hu
    · rwa [hph u e'] at hu
  refine ⟨fun k hk => ?_, fun u v hu _ => (hnw' u _ rfl hu).elim, fun _ => ?_,
    fun u i' jr' sn' e' hu => (hnw' u _ hu rfl).elim,
    fun u hu => (hnw' u _ hu rfl).elim, fun u i' e' hu => (hnw' u _ hu rfl).elim,
    fun u v hu => (hnw' u _ rfl (by revert hu; cases C.ph (G' u) <;> simp [CPh.crit, CPh.waits])).elim,
    fun u v hu hv => hI.sone u v (hsg u hu) (hsg v hv),
    fun u v i' jr' sn' e' _ hv => (hnw' v _ hv rfl).elim,
    fun u v i' jr' sn' e' _ hv => (hnw' v _ hv rfl).elim, fun w hw hp => ?_,
    fun w hw hp => (hnw' w.1 _ rfl hp).elim, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hsz] at hk
    rcases (by omega : k < (C.S.hist m).size ∨ k = (C.S.hist m).size) with hk' | rfl
    · rw [hold k hk']; exact hI.sv k hk'
    · rw [hS, FEvent.get_push_eq]; exact .inl FEvent.rmwEnt_val
  · unfold FCond.lastS; rw [hS, last_push]; exact FEvent.rmwEnt_val
  · rw [hwt] at hw
    obtain ⟨i', jr', e', h1, -⟩ := hI.q w hw hp
    exact absurd (hI.one w.1 t (by rw [h1]; rfl) htw) (hnq w hw)
  · exact (hnw' u _ rfl (by revert hu; cases C.ph (G' u) <;> simp [CPh.crit, CPh.waits])).elim
  · have e' : u ≠ t := fun h => by subst h; rw [ht1] at hu; cases hu
    rw [hph u e'] at hu; rw [hG u e']; exact hI.lp u hu
  · have e' : u ≠ t := fun h => by subst h; rw [ht1] at hu; cases hu
    rw [hph u e'] at hu; rw [hG u e']; exact hI.sx u hu

/-- A registered waiter, from the newest state write `(1, 0)`. -/
theorem Inv.reg_of {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m)
    (h1 : (C.lastS m).Val (1 : BitVec 32)) : ∃ u i jr sn e, C.ph (G u) = .reg i jr sn e := by
  refine Classical.byContradiction fun hn => ?_
  exact absurd (FEvent.val_eq (hI.idle fun u i jr sn e hu => hn ⟨u, i, jr, sn, e, hu⟩) h1)
    (by decide)

/-- A signaller's `signals += 1` (`out` → `inc`): its `cmpxchg((1, 0) → (1, 1))` succeeded. -/
theorem Inv.signal {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    (hI : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u)
    (ht0 : C.ph (G t) = .out) (ht1 : C.ph (G' t) = .inc) (hlpt : L.ph (G' t) = .out)
    (hsxt : C.sx (G' t)) (hold1 : (C.lastS m).Val (1 : BitVec 32))
    (hS : C.S.hist m' = (C.S.hist m).push (Word.rmwEnt m' t ord (C.lastS m) (0x10001 : BitVec 32)))
    (hE : C.Ep.hist m' = C.Ep.hist m) (hwt : m'.waiters = m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    C.Inv L G' m' := by
  have hsz : (C.S.hist m').size = (C.S.hist m).size + 1 := by rw [hS]; simp
  have hold : ∀ k, k < (C.S.hist m).size → (C.S.hist m')[k]! = (C.S.hist m)[k]! := fun k hk => by
    rw [hS]; exact FEvent.get_push_lt hk
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  -- the registered waiter: its write is the newest, the epoch is still its write `i`
  have hera : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e →
      (C.S.hist m).size = jr + 1 ∧ (C.Ep.hist m).size = i + 1 ∧ sn = false := by
    intro u i jr sn e hu
    have h := hI.era u i jr sn e hu
    have hs : (C.S.hist m).size = jr + 1 := by
      rcases h.last with ⟨hs, -⟩ | ⟨-, h2⟩
      · exact hs
      · exact absurd (FEvent.val_eq hold1 h2) (by decide)
    have he : (C.Ep.hist m).size = i + 1 := by
      rcases h.esz with he | ⟨-, hs', -⟩
      · exact he
      · omega
    refine ⟨hs, he, ?_⟩
    cases hsn : sn
    · rfl
    · have := (h.seen hsn).1; omega
  obtain ⟨r, ri, rjr, rsn, re, hr⟩ := hI.reg_of hold1
  -- no signaller between its signal and its wake
  have hns : ∀ u, (C.ph (G u)).sig = false := fun u => by
    cases h : C.ph (G u) with
    | inc => have := (hI.inc u r ri rjr rsn re h hr).1; have := (hera r ri rjr rsn re hr).1; omega
    | wk => have := hI.wk u r ri rjr rsn re h hr; have := (hera r ri rjr rsn re hr).2.1; omega
    | _ => rfl
  have hrt : r ≠ t := fun h => by subst h; rw [ht0] at hr; cases hr
  have hsig : ∀ u, (C.ph (G' u)).sig → u = t := fun u hu => by
    by_cases e' : u = t
    · exact e'
    · rw [hph u e', hns u] at hu; cases hu
  have hwts : ∀ u, (C.ph (G' u)).waits → u ≠ t ∧ (C.ph (G u)).waits := fun u hu => by
    have e' : u ≠ t := fun h => by subst h; rw [ht1] at hu; cases hu
    exact ⟨e', by rwa [hph u e'] at hu⟩
  -- a waiter is the registered one
  have hwr : ∀ u, (C.ph (G u)).waits → ∃ i jr sn e, C.ph (G u) = .reg i jr sn e := fun u hu => by
    have := hI.one u r hu (by rw [hr]; rfl); subst this; exact ⟨_, _, _, _, hr⟩
  refine ⟨fun k hk => ?_, fun u v hu hv => hI.one u v (hwts u hu).2 (hwts v hv).2,
    fun hn => absurd (hph r hrt ▸ hr) (hn r ri rjr rsn re), fun u i jr sn e hu => ?_,
    fun u hu => ?_, fun u i e hu => ?_, fun u v hu => ?_, fun u v hu hv => (hsig u hu).trans (hsig v hv).symm,
    fun u v i jr sn e hu hv => ?_, fun u v i jr sn e hu hv => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hsz] at hk
    rcases (by omega : k < (C.S.hist m).size ∨ k = (C.S.hist m).size) with hk' | rfl
    · rw [hold k hk']; exact hI.sv k hk'
    · rw [hS, FEvent.get_push_eq]; exact .inr (.inr FEvent.rmwEnt_val)
  · -- the waiter's era: the signal is the state's next write
    have e' : u ≠ t := fun h => by subst h; rw [ht1] at hu; cases hu
    rw [hph u e'] at hu
    have h := hI.era u i jr sn e hu
    obtain ⟨hs, he, rfl⟩ := hera u i jr sn e hu
    exact {
      ssz := .inr (by omega)
      s0 := by rw [hold jr (by omega)]; exact h.s0
      s1 := fun _ => by rw [hS, show jr + 1 = (C.S.hist m).size by omega, FEvent.get_push_eq]
                        exact FEvent.rmwEnt_val
      esz := .inl (by rw [hE]; exact he)
      eval := ⟨by rw [hE]; exact h.eval.1, fun h' => by rw [hE] at h'; omega⟩
      seen := fun h' => by cases h'
      cs := by rw [hold jr (by omega)]; exact VClock.le_trans h.cs (hclk u)
      ce := by rw [hE]; exact VClock.le_trans h.ce (hclk u)
      pend := fun _ _ => ⟨t, ht1⟩ }
  · obtain ⟨e', hw⟩ := hwts u (by rw [hu]; rfl)
    obtain ⟨i, jr, sn, e, h⟩ := hwr u hw
    rw [hph u e', h] at hu; cases hu
  · obtain ⟨e', hw⟩ := hwts u (by rw [hu]; rfl)
    obtain ⟨i', jr, sn, e'', h⟩ := hwr u hw
    rw [hph u e', h] at hu; cases hu
  · obtain ⟨e', hw⟩ := hwts u (by revert hu; cases C.ph (G' u) <;> simp [CPh.crit, CPh.waits])
    obtain ⟨i, jr, sn, e, h⟩ := hwr u hw
    rw [hph u e', h] at hu; cases hu
  · -- `t` is the signaller at `inc`
    have := hsig u (by rw [hu]; rfl); subst this
    have e' : v ≠ u := fun h => by subst h; rw [ht1] at hv; cases hv
    rw [hph v e'] at hv
    obtain ⟨hs, he, -⟩ := hera v i jr sn e hv
    refine ⟨by omega, by rw [hE]; exact he, ?_⟩
    rw [hS, show jr + 1 = (C.S.hist m).size by omega, FEvent.get_push_eq]; exact VClock.le_refl _
  · have := hsig u (by rw [hu]; rfl); subst this; rw [ht1] at hu; cases hu
  · rw [hwt] at hw
    obtain ⟨i, jr, e, h1, h2⟩ := hI.q w hw hp
    have e' : w.1 ≠ t := fun h => by rw [h, ht0] at h1; cases h1
    refine ⟨i, jr, e, by rw [hph _ e']; exact h1, ?_⟩
    rw [hE]
    rcases h2 with h2 | ⟨v, hv⟩
    · exact .inl h2
    · have := hns v; rw [hv] at this; cases this
  · rw [hwt] at hw
    obtain ⟨e', hw'⟩ := hwts w.1 hp
    rw [← hph _ e'] at hw'
    exact hI.qw w hw (by rw [← hph _ e']; exact hw')
  · obtain ⟨e', hw⟩ := hwts u (by revert hu; cases C.ph (G' u) <;> simp [CPh.crit, CPh.waits])
    obtain ⟨i, jr, sn, e, h⟩ := hwr u hw
    rw [hph u e', h] at hu; cases hu
  · have := hsig u hu; subst this; exact hlpt
  · have := hsig u hu; subst this; exact hsxt

/-- The signaller's `epoch += 1`, a release (`inc` → `wk`). -/
theorem Inv.bump {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    {o : BitVec 32} (hI : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u)
    (ht0 : C.ph (G t) = .inc) (ht1 : C.ph (G' t) = .wk) (hlpt : L.ph (G' t) = L.ph (G t))
    (hsxt : C.sx (G t) → C.sx (G' t)) (hrel : ord.isRel = true)
    (hold : (C.lastE m).Val o)
    (hE : C.Ep.hist m' = (C.Ep.hist m).push (Word.rmwEnt m' t ord (C.lastE m) (o + 1)))
    (hS : C.S.hist m' = C.S.hist m) (hwt : m'.waiters = m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    C.Inv L G' m' := by
  have hsz : (C.Ep.hist m').size = (C.Ep.hist m).size + 1 := by rw [hE]; simp
  have hold' : ∀ k, k < (C.Ep.hist m).size → (C.Ep.hist m')[k]! = (C.Ep.hist m)[k]! :=
    fun k hk => by rw [hE]; exact FEvent.get_push_lt hk
  have hnew : (C.Ep.hist m')[(C.Ep.hist m).size]! = Word.rmwEnt m' t ord (C.lastE m) (o + 1) := by
    rw [hE]; exact FEvent.get_push_eq
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  have hts : (C.ph (G t)).sig := by rw [ht0]; rfl
  -- no waiter in the critical code, no other signaller
  have hnc : ∀ u, (C.ph (G u)).crit = false := fun u => by
    cases h : (C.ph (G u)).crit
    · rfl
    · have := hI.nosig u t h; rw [hts] at this; cases this
  have hos : ∀ u, (C.ph (G u)).sig → u = t := fun u hu => hI.sone u t hu hts
  have hnc' : ∀ u p, C.ph (G' u) = p → p.crit = true → False := fun u p hp h => by
    by_cases e' : u = t
    · subst e'; rw [ht1] at hp; subst hp; cases h
    · rw [hph u e'] at hp; have := hnc u; rw [hp, h] at this; cases this
  have hsg : ∀ u, (C.ph (G' u)).sig → u = t := fun u hu => by
    by_cases e' : u = t
    · exact e'
    · rw [hph u e'] at hu; exact hos u hu
  have hwts : ∀ u, (C.ph (G' u)).waits → u ≠ t := fun u hu h => by
    subst h; rw [ht1] at hu; cases hu
  -- the registered waiter
  have hreg : ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → u ≠ t ∧ C.ph (G u) = .reg i jr sn e :=
    fun u i jr sn e hu => by
      have e' := hwts u (by rw [hu]; rfl); exact ⟨e', by rw [← hph u e']; exact hu⟩
  have hidle : (∀ u i jr sn e, C.ph (G' u) ≠ .reg i jr sn e) →
      ∀ u i jr sn e, C.ph (G u) ≠ .reg i jr sn e := fun hn u i jr sn e hu => by
    have e' : u ≠ t := fun h => by subst h; rw [ht0] at hu; cases hu
    exact hn u i jr sn e (by rw [hph u e']; exact hu)
  refine ⟨by rw [hS]; exact hI.sv, fun u v hu hv => ?_, fun hn => ?_, fun u i jr sn e hu => ?_,
    fun u hu => (hnc' u _ hu rfl).elim, fun u i e hu => (hnc' u _ hu rfl).elim,
    fun u v hu => (hnc' u _ rfl hu).elim,
    fun u v hu hv => (hsg u hu).trans (hsg v hv).symm,
    fun u v i jr sn e hu hv => ?_, fun u v i jr sn e hu hv => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, fun u hu => (hnc' u _ rfl hu).elim, fun u hu => ?_, fun u hu => ?_⟩
  · exact hI.one u v (by rwa [← hph u (hwts u hu)]) (by rwa [← hph v (hwts v hv)])
  · unfold FCond.lastS; rw [hS]; exact hI.idle (hidle hn)
  · obtain ⟨e', hu'⟩ := hreg u i jr sn e hu
    have h := hI.era u i jr sn e hu'
    obtain ⟨hs2, he1, hcl⟩ := hI.inc t u i jr sn e ht0 hu'
    have hoe : o = e := by
      have := h.eval.1; unfold FCond.lastE at hold; rw [he1, Nat.add_sub_cancel] at hold
      exact FEvent.val_eq hold this
    subst hoe
    exact {
      ssz := by rw [hS]; exact h.ssz
      s0 := by rw [hS]; exact h.s0
      s1 := by rw [hS]; exact h.s1
      esz := .inr ⟨by omega, by rw [hS]; exact hs2, by
        rw [hS, show i + 1 = (C.Ep.hist m).size by omega, hnew]
        simp only [Word.rmwEnt, hrel, ↓reduceIte]
        exact VClock.le_trans (VClock.le_trans hcl (hclk t)) (VClock.le_merge_right _ _)⟩
      eval := ⟨by rw [hold' i (by omega)]; exact h.eval.1, fun _ => by
        rw [show i + 1 = (C.Ep.hist m).size by omega, hnew]; exact FEvent.rmwEnt_val⟩
      seen := fun hsn => by have := (h.seen hsn).1; omega
      cs := by rw [hS]; exact VClock.le_trans h.cs (hclk u)
      ce := by rw [hold' i (by omega)]; exact VClock.le_trans h.ce (hclk u)
      pend := fun _ h' => by omega }
  · have := hsg u (by rw [hu]; rfl); subst this; rw [ht1] at hu; cases hu
  · have := hsg u (by rw [hu]; rfl); subst this
    obtain ⟨-, hv'⟩ := hreg v i jr sn e hv
    have := (hI.inc u v i jr sn e ht0 hv').2.1; omega
  · rw [hwt] at hw
    obtain ⟨i, jr, e, h1, -⟩ := hI.q w hw hp
    have e' : w.1 ≠ t := fun h => by rw [h, ht0] at h1; cases h1
    exact ⟨i, jr, e, by rw [hph _ e']; exact h1, .inr ⟨t, ht1⟩⟩
  · rw [hwt] at hw
    have e' := hwts w.1 hp
    rw [hph _ e'] at hp; exact hI.qw w hw hp
  · have := hsg u hu; subst this; rw [hlpt]; exact hI.lp u hts
  · have := hsg u hu; subst this; exact hsxt (hI.sx u hts)

/-- The signaller's wake at the epoch (`wk` → `out`), of at least one waiter: the registered
waiter is not in the futex queue any more. -/
theorem Inv.wake {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g : γ} {c : Nat}
    {cs : List Nat} (hI : C.Inv L G m) (ht : C.ph (G t) = .wk) (hg : C.ph g = .out) (hc : 1 ≤ c)
    (h : ((Thread.futexWake C.Ep.ptr c cs).run { m with current := t }).run = some (.ok ((), m'))) :
    C.Inv L (upd G t g) m' := by
  have hm' := Proto.modify_ok h
  subst hm'
  have hts : (C.ph (G t)).sig := by rw [ht]; rfl
  have hos : ∀ u, (C.ph (G u)).sig → u = t := fun u hu => hI.sone u t hu hts
  have hph : ∀ u, u ≠ t → C.ph (upd G t g u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  have hsg : ∀ u, (C.ph (upd G t g u)).sig = false := fun u => by
    by_cases e' : u = t
    · subst e'; rw [upd_self, hg]; rfl
    · cases h : (C.ph (upd G t g u)).sig
      · rfl
      · rw [hph u e'] at h; exact absurd (hos u h) e'
  have hsg' : ∀ u p, C.ph (upd G t g u) = p → p.sig = true → False := fun u p hp h => by
    have := hsg u; rw [hp, h] at this; cases this
  have hwts : ∀ u, (C.ph (upd G t g u)).waits → u ≠ t := fun u hu h => by
    subst h; rw [upd_self, hg] at hu; cases hu
  -- every thread at the epoch's futex was woken
  have hgone : ∀ w ∈ m.waiters, w.2 = C.Ep.ptr →
      (Thread.wakeSet m.waiters C.Ep.ptr c cs).contains w.1 = true := fun w hw hp => by
    have hne : ((m.waiters.filter (·.2 == C.Ep.ptr)).toList.map (·.1)) ≠ [] := by
      intro he
      have : w.1 ∈ ((m.waiters.filter (·.2 == C.Ep.ptr)).toList.map (·.1)) :=
        List.mem_map.mpr ⟨w, by simp [hw, hp], rfl⟩
      rw [he] at this; cases this
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _
      (Thread.wakePick_ne_nil (cs := cs) (by omega : 0 < c) hne)
    have hu' : u ∈ Thread.wakeSet m.waiters C.Ep.ptr c cs := by
      unfold Thread.wakeSet; exact List.mem_toArray.mpr hu
    obtain ⟨w', hw', hp', rfl⟩ := Thread.mem_wakeSet hu'
    obtain ⟨_, _, _, h1, -⟩ := hI.q w' hw' hp'
    obtain ⟨_, _, _, h2, -⟩ := hI.q w hw hp
    have e : w'.1 = w.1 := hI.one _ _ (by rw [h1]; rfl) (by rw [h2]; rfl)
    rw [← e]; exact Array.contains_iff_mem.mpr hu'
  refine ⟨hI.sv, fun u v hu hv => ?_, fun hn => hI.idle fun u i jr sn e hu => ?_,
    fun u i jr sn e hu => ?_, fun u hu => ?_, fun u i e hu => ?_, fun u v hu => hsg v,
    fun u v hu _ => (hsg' u _ rfl hu).elim, fun u v i jr sn e hu _ => (hsg' u _ hu rfl).elim,
    fun u v i jr sn e hu _ => (hsg' u _ hu rfl).elim, fun w hw hp => ?_, fun w hw hp => ?_,
    fun u hu => ?_, fun u hu => (hsg' u _ rfl hu).elim, fun u hu => (hsg' u _ rfl hu).elim⟩
  · exact hI.one u v (by rwa [← hph u (hwts u hu)]) (by rwa [← hph v (hwts v hv)])
  · have e' : u ≠ t := fun h => by subst h; rw [ht] at hu; cases hu
    exact hn u i jr sn e (by rw [hph u e']; exact hu)
  · have e' := hwts u (by rw [hu]; rfl)
    rw [hph u e'] at hu
    have h := hI.era u i jr sn e hu
    have hw := hI.wk t u i jr sn e ht hu
    exact { h with pend := fun _ h' => by change (C.Ep.hist m).size = i + 1 at h'; omega }
  · have e' := hwts u (by rw [hu]; rfl)
    rw [hph u e'] at hu; exact hI.en u hu
  · have e' := hwts u (by rw [hu]; rfl)
    rw [hph u e'] at hu; exact hI.ld u i e hu
  · have hw' : w ∈ m.waiters ∧
        (Thread.wakeSet m.waiters C.Ep.ptr c cs).contains w.1 = false := by
      simpa [Array.mem_filter] using hw
    rw [hgone w hw'.1 hp] at hw'
    cases hw'.2
  · simp only [Array.mem_filter] at hw
    have e' := hwts w.1 hp
    rw [hph _ e'] at hp; exact hI.qw w hw.1 hp
  · have e' : u ≠ t := fun h => by subst h; rw [upd_self, hg] at hu; cases hu
    rw [hph u e'] at hu; rw [upd_ne _ _ e']; exact hI.crit u hu

/-- The waiter's sleep at the epoch, which held its value `e`: the epoch is still its write `i`. -/
theorem Inv.sleep {G : ThreadId → γ} {M : Mem} {t : ThreadId} {i jr : Nat} {e : BitVec 32}
    (hI : C.Inv L G M) (ht : C.ph (G t) = .reg i jr false e) (hv : (C.lastE M).Val e) :
    C.Inv L G { M with waiters := M.waiters.push (t, C.Ep.ptr) } := by
  have h := hI.era t i jr false e ht
  have hsz : (C.Ep.hist M).size = i + 1 := by
    rcases h.esz with h1 | ⟨h1, -⟩
    · exact h1
    · exfalso
      have := (h.eval.2 h1)
      unfold FCond.lastE at hv; rw [h1, show i + 2 - 1 = i + 1 by omega] at hv
      exact add_one_ne e (FEvent.val_eq this hv)
  have hS : C.S.hist ({ M with waiters := M.waiters.push (t, C.Ep.ptr) } : Mem) = C.S.hist M := rfl
  have hE : C.Ep.hist ({ M with waiters := M.waiters.push (t, C.Ep.ptr) } : Mem) = C.Ep.hist M :=
    rfl
  have hcl : ({ M with waiters := M.waiters.push (t, C.Ep.ptr) } : Mem).clocks = M.clocks := rfl
  refine ⟨by rw [hS]; exact hI.sv, hI.one, by unfold FCond.lastS; rw [hS]; exact hI.idle,
    fun u i jr sn e hu => (hI.era u i jr sn e hu).mono hS hE (by rw [hcl]; exact VClock.le_refl _)
      (fun v hv => ⟨v, hv⟩),
    fun u hu j hj => by rw [hE] at hj ⊢; rw [hcl]; exact hI.en u hu j hj,
    fun u i e hu => by rw [hE, hcl]; exact hI.ld u i e hu, hI.nosig, hI.sone,
    fun u v i jr sn e hu hv => by rw [hS, hE, hcl]; exact hI.inc u v i jr sn e hu hv,
    fun u v i jr sn e hu hv => by rw [hE]; exact hI.wk u v i jr sn e hu hv,
    fun w hw hp => ?_, fun w hw hp => ?_, hI.crit, hI.lp, hI.sx⟩
  · rw [hE]
    rcases Array.mem_push.mp hw with hw | rfl
    · exact hI.q w hw hp
    · exact ⟨i, jr, e, ht, .inl hsz⟩
  · rcases Array.mem_push.mp hw with hw | rfl
    · exact hI.qw w hw hp
    · exact .inl rfl

/-- **A lock step of a thread out of the condition's busy code** keeps the condition's invariant
(for a client's `FLock.FitsOn.stable`, whose `ok` excludes the busy threads; module doc). -/
theorem Inv.lstep {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {p : LPh} {h : Res}
    (hI : C.Inv L G m) (hwS : C.S.Ok m) (hwE : C.Ep.Ok m) (hapS : C.S.ApartL L.toLockWord)
    (hapE : C.Ep.ApartL L.toLockWord) (hb : (C.ph (G t)).busy = false)
    (hph : ∀ g q h, C.ph (L.set g q h) = C.ph g) (hs : L.Step t m m') :
    C.Inv L (upd G t (L.set (G t) p h)) m' := by
  have hpt : C.ph (upd G t (L.set (G t) p h) t) = C.ph (G t) := by rw [upd_self, hph]
  have hnc : (C.ph (G t)).crit = false := by
    unfold CPh.busy at hb; revert hb; cases (C.ph (G t)).crit <;> simp
  have hns : (C.ph (G t)).sig = false := by
    unfold CPh.busy at hb; revert hb; cases (C.ph (G t)).sig <;> simp
  refine hI.move (fun u hu => upd_ne _ _ hu)
    (Word.hist_keep hwS (Word.keep_lockWordStep hs hapS))
    (Word.hist_keep hwE (Word.keep_lockWordStep hs hapE)) hapE.ptr_ne
    (fun w hl hw => (hs.waiters w hl).mp hw) (fun u => ?_) (by rw [hpt]; exact id)
    (fun h' => by rw [hpt, hnc] at h'; cases h') (fun h' => by
      rw [hpt] at h'; rcases h' with h' | h' <;> rw [hns] at h' <;> cases h')
    (fun h' => by rw [hpt] at h'; rw [h'] at hnc; cases hnc)
    (fun i e h' => by rw [hpt] at h'; rw [h'] at hnc; cases hnc)
    (fun i jr sn e h' => ⟨sn, by rw [← hpt]; exact h', fun hsn => .inl hsn⟩)
    (fun i jr sn e h' => ⟨sn, by rw [hpt]; exact h'⟩)
    (fun w hw e => ⟨fun h' => hI.qw w hw (by rw [e, ← hpt]; exact h'), fun _ => hpt⟩)
  by_cases e : u = t
  · subst e; exact hs.mine
  · rw [hs.others u e]; exact VClock.le_refl _

/-- A waiter's read of state write `j` at `reg i jr sn e`: its `(1, 0)` (only before it loaded
the epoch's next write) or the signal `(1, 1)`. -/
theorem Inv.readS {G : ThreadId → γ} {m : Mem} {t : ThreadId} {i jr : Nat} {sn : Bool}
    {e : BitVec 32} (hI : C.Inv L G m) (ht : C.ph (G t) = .reg i jr sn e) {j : Nat}
    {b : BitVec 32} (hj : j < (C.S.hist m).size) (hv : (C.S.hist m)[j]!.Val b)
    (hfl : Word.Floor (C.S.hist m) (m.clocks[t]!) j) :
    (b = 1 ∧ sn = false) ∨ b = 0x10001 := by
  have h := hI.era t i jr sn e ht
  have hge : jr ≤ j := hfl jr (by rcases h.ssz with h' | h' <;> omega) h.cs
  have hsn : sn = true → jr + 1 ≤ j := fun hs => by
    obtain ⟨h1, h2⟩ := h.seen hs
    rcases h.esz with h3 | ⟨-, h3, h4⟩
    · omega
    · exact hfl (jr + 1) (by omega) (VClock.le_trans h4 h2)
  rcases h.ssz with hs | hs
  · have : j = jr := by omega
    subst this
    refine .inl ⟨FEvent.val_eq hv h.s0, ?_⟩
    cases hs' : sn
    · rfl
    · have := hsn hs'; omega
  · rcases (by omega : j = jr ∨ j = jr + 1) with rfl | rfl
    · refine .inl ⟨FEvent.val_eq hv h.s0, ?_⟩
      cases hs' : sn
      · rfl
      · have := hsn hs'; omega
    · exact .inr (FEvent.val_eq hv (h.s1 hs))

/-- A signaller's read of state write `j`, after every registration (`hseen`): a value of the
state; a value other than `(1, 0)` means a registered waiter was signalled. -/
theorem Inv.readSig {G : ThreadId → γ} {m : Mem} {t : ThreadId} (hI : C.Inv L G m) {j : Nat}
    {b : BitVec 32} (hj : j < (C.S.hist m).size) (hv : (C.S.hist m)[j]!.Val b)
    (hfl : Word.Floor (C.S.hist m) (m.clocks[t]!) j)
    (hseen : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e →
      VClock.le (C.S.hist m)[jr]!.clock (m.clocks[t]!) = true) :
    (b = 0 ∨ b = 1 ∨ b = 0x10001) ∧
      (b ≠ 1 → ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m) := by
  refine ⟨(hI.sv j hj).cases hv, fun hb u i jr sn e hu => ?_⟩
  have h := hI.era u i jr sn e hu
  have hge : jr ≤ j := hfl jr (by rcases h.ssz with h' | h' <;> omega) (hseen u i jr sn e hu)
  rcases h.last with ⟨hs, -⟩ | ⟨-, h2⟩
  · have : j = jr := by omega
    subst this; exact absurd (FEvent.val_eq hv h.s0) hb
  · exact h2

/-! ## The protocol after a step -/

variable {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- An op at the state keeps the epoch's writes. -/
theorem Fits.keepE (hC : C.Fits L P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} (hU : U G rX m) (hop : C.S.Op t m m') : C.Ep.hist m' = C.Ep.hist m :=
  Word.hist_keep (hC.rE _ _ _ hU).1 (Word.keep_op hop (.inr (.inl (by have := C.ep_o; omega))))

/-- An op at the epoch keeps the state's writes. -/
theorem Fits.keepS (hC : C.Fits L P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} (hU : U G rX m) (hop : C.Ep.Op t m m') : C.S.hist m' = C.S.hist m :=
  Word.hist_keep (hC.rS _ _ _ hU).1 (Word.keep_op hop (.inr (.inr (by have := C.ep_o; omega))))

/-- After a step of the condition's code by `t` (`g`, new place `p`) that keeps `t`'s lock
place: the protocol's invariant, from the lock's invariant after the step, the rest before it,
and the condition's invariant after it. -/
theorem Fits.back (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ} {rY : Res}
    {m₁ m' : Mem} {t : ThreadId} {g : γ} {p : CPh} {W : Word 32 4} (hW : W = C.S ∨ W = C.Ep)
    (hg₁ : G₁ t = g) (hn : CPh.Next (C.ph g) p) (hU : U G₁ (rsum (W.cellsR m₁) rY) m₁)
    (hY : ∀ l, W.In l → rY.heap l = none) (hs : C.MStep t m₁ m')
    (hEp : C.Ep.hist m' = C.Ep.hist m₁ ∨ C.ph g = .inc)
    (hL : L.Inv G₁ (rsum (W.cellsR m') rY) m') (hI : C.Inv L (upd G₁ t (C.set g p)) m') :
    P.inv (upd G₁ t (C.set g p)) m' := by
  subst hg₁
  have hset : L.set (C.set (G₁ t) p) (L.ph (G₁ t)) (L.held (G₁ t)) = C.set (G₁ t) p := by
    have := L.set_self (C.set (G₁ t) p); rwa [hC.lph, hC.lheld] at this
  have hU' := hC.step G₁ rY m₁ m' t p (L.ph (G₁ t)) (L.held (G₁ t)) W hW hn (.inl ⟨rfl, rfl⟩)
    hU hY hs hEp (by rw [hset]; exact hI)
  rw [hset] at hU'
  have hL' := hL.relabel (g := C.set (G₁ t) p) (hC.lph _ _) (hC.lpart _ _) (hC.lheld _ _)
    (fun r hr => hC.lR G₁ t p r hr)
  exact (hP.inv _ _).mpr ⟨_, hL', hU'⟩

/-- The facts at a stop of `t` (not at a futex) before an op at a word: the condition's
invariant, `t` is not in the futex queue. -/
theorem Fits.atOp (hC : C.Fits L P U ok) {G₁ : ThreadId → γ} {rX rX' : Res} {m₁ m' : Mem}
    {t : ThreadId} {W : Word 32 4} (hU : U G₁ rX m₁) (hw : L.ph (G₁ t) ≠ .wait)
    (ha : L.ph (G₁ t) ≠ .away) (hop : W.Op t m₁ m') (hL : L.Inv G₁ rX' m') :
    C.Inv L G₁ m₁ ∧ ∀ w ∈ m₁.waiters, w.1 ≠ t := by
  refine ⟨hC.inv _ _ _ hU, ?_⟩
  have := hL.w.notQ (t := t) hw ha
  rw [hop.waiters] at this
  exact FEvent.notQ_mem this

/-- A thread enters the wait (`out` → `en`) holding the mutex (module doc, scope; `hent`: the
client's rest allows it). -/
theorem Fits.enter (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m : Mem}
    {t : ThreadId} {g : γ} (hgx : C.ph g = .out) (hgh : L.ph g = .holds)
    (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hi : P.inv (upd G t g) m) : P.inv (upd G t (C.set g .en)) m := by
  obtain ⟨rX, hL, hU⟩ := (hP.inv _ _).mp hi
  have hnq : ∀ w ∈ m.waiters, w.1 ≠ t := by
    have := hL.w.notQ (t := t) (show L.ph (upd G t g t) ≠ .wait by rw [upd_self, hgh]; decide)
      (show L.ph (upd G t g t) ≠ .away by rw [upd_self, hgh]; decide)
    exact FEvent.notQ_mem this
  have hI := (hC.inv _ _ _ hU).enter hgx (by rw [hC.lph]; exact hgh) hnq hone hhb
  have hL' := hL.relabel (t := t) (g := C.set g .en) (by rw [upd_self, hC.lph])
    (by rw [upd_self, hC.lpart]) (by rw [upd_self, hC.lheld]) (fun r hr => by
      have := hC.lR (upd G t g) t .en r hr; rwa [upd_self] at this)
  rw [upd_upd] at hL'
  exact (hP.inv _ _).mpr ⟨rX, hL', hent rX hU hI⟩

/-- A sleeping waiter of a signalled condition is not in a deadlock: a signaller between its
signal and its wake runs. -/
theorem Fits.live (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) {G : ThreadId → γ} {rX : Res}
    {m : Mem} {t : ThreadId} (hI : C.Inv L G m) (hL : L.Inv G rX m) (ht : (C.ph (G t)).waits)
    (hs : C.Signalled m) : P.Live t G m := by
  intro hin hall
  obtain ⟨w, hw, he⟩ := Array.any_eq_true'.mp hin
  have e : w.1 = t := by simpa using he
  have hp : w.2 = C.Ep.ptr := by
    rcases hI.qw w hw (by rw [e]; exact ht) with h | h
    · exact h
    · exact absurd (Array.any_eq_true'.mpr ⟨w, hw, by simp [h]⟩) (hP.noWaits hL hall)
  obtain ⟨i, jr, e', h1, h2⟩ := hI.q w hw hp
  have h := hI.era w.1 i jr false e' h1
  have hs2 : (C.S.hist m).size = jr + 2 := by
    rcases h.last with ⟨-, h3⟩ | ⟨h3, -⟩
    · exact absurd (FEvent.val_eq h3 hs) (by decide)
    · exact h3
  -- a signaller runs
  obtain ⟨v, hv⟩ : ∃ v, (C.ph (G v)).sig := by
    rcases h2 with h2 | ⟨v, hv⟩
    · obtain ⟨v, hv⟩ := h.pend hs2 h2; exact ⟨v, by rw [hv]; rfl⟩
    · exact ⟨v, by rw [hv]; rfl⟩
  have hlo := hI.lp v hv
  have hvt := (hL.ht (t := v) (by rw [hlo]; decide)).1
  rcases hall v hvt with h' | h' | h'
  · rw [hC.fin _ h'] at hv; cases hv
  · have := hL.w.notQ (t := v) (show L.ph (G v) ≠ .wait by rw [hlo]; decide)
      (show L.ph (G v) ≠ .away by rw [hlo]; decide)
    rw [this] at h'; cases h'
  · rw [hC.joins _ h'] at hv; cases hv

end FCond

end Full
end Zig
