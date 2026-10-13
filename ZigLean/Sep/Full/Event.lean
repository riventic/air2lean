import ZigLean.Sep.Full.WordRules

/-!
# The futex event, over full-state resources

A one-shot futex event (`Io.Event` of 0.16.0, `Thread.ResetEvent.FutexImpl` of 0.15.2): a `u32`
word `W` with the values `unset` 0, `waiting` 1 and `is_set` 2, and no reset. A waiter does an
acquire `cmpxchg(unset → waiting)` and then, while the word holds `waiting`, a futex wait and an
acquire load; a setter does a release `xchg(is_set)` and wakes every waiter if it read
`waiting`. This module is the component once for every protocol that has such an event next to
a lock (`FLock.FitsOn`), and the rules of the event's ops in generated code; an implementation
of a Zig version walks its code with them (`EventImpl`).

`FEvent γ` is the word and a thread's place in the event's code (`EPh`: `out`, `w0` registered
before its first write, `w1` it saw or wrote `waiting` and may sleep, `sw` a setter that read
`waiting` and has not woken yet). `FEvent.Inv` is the event's invariant: the writes are 0, 1, 2
and never get smaller, the waiter saw a `waiting` write (it happened before it), a thread in the
futex queue at the word is at `w1`, and the newest write is `waiting` or a setter is at `sw`
(no lost wakeup). `FEvent.Fits` says that a protocol keeps the event: its rest `U` carries the
invariant and has the word's cells (`Word.InRest`), and it is stable under each step of the
event's code (`MStep`, with the place change of the stepping thread).

**Scope (one waiter at a time).** A thread enters the wait (`w0`) only when no other thread is
at `w0` or `w1`, and after every `waiting` write so far happened before it (`hone`/`hhb` of
`Inv.enter`). Reason: the memory model's facts of a read (`Word.Ok.load`, `Ok.cas`) give the
happens-before floor of the read (`Word.Floor`), not the read-read coherence of `Mem.seen`, and a
full-state frame (`Word.Keep`, `FStepIn`) does not keep `Mem.seen`; so a waiter whose `cmpxchg`
read another waiter's `waiting` without a happens-before edge could not exclude that its next
load reads `unset` (the code's `unreachable`). With one waiter, the waiter's own `waiting`
write (or one that happened before it) is in its floor. Several waiters are a follow-up.
-/

namespace Zig
namespace Full

open Conc Proto

/-- Where a thread is in an event's code (module doc). -/
inductive EPh where
  | out
  /-- A waiter before its first write or read of `waiting`. -/
  | w0
  /-- A waiter that wrote or saw `waiting`: it can sleep at the word. -/
  | w1
  /-- A setter whose `xchg` read `waiting`, before its wake. -/
  | sw
  deriving DecidableEq

/-- A waiter's place. -/
def EPh.Waiting (p : EPh) : Prop := p = .w0 ∨ p = .w1

/-- A futex event (module doc): its word, and a thread's place in its code. -/
structure FEvent (γ : Type) where
  W : Word 32 4
  ph : γ → EPh
  set : γ → EPh → γ
  ph_set : ∀ g p, ph (set g p) = p
  set_set : ∀ g p q, set (set g p) q = set g q
  set_self : ∀ g, set g (ph g) = g

namespace FEvent

variable {γ : Type} (E : FEvent γ)

/-- The newest write of the word. -/
abbrev newest (m : Mem) : Word.Entry := (E.W.hist m)[(E.W.hist m).size - 1]!

/-- The event is set: its newest write is `is_set`. -/
def IsSet (m : Mem) : Prop := (E.newest m).Val (2 : BitVec 32)

/-- The event's invariant, with the lock's places (module doc). -/
structure Inv (L : FLock γ) (G : ThreadId → γ) (m : Mem) : Prop where
  /-- The writes are `unset`, `waiting` or `is_set`. -/
  vals : ∀ j < (E.W.hist m).size, ∃ k < 3, (E.W.hist m)[j]!.Val (BitVec.ofNat 32 k)
  /-- They never get smaller. -/
  mono : ∀ i j (a b : BitVec 32), i ≤ j → j < (E.W.hist m).size → (E.W.hist m)[i]!.Val a →
    (E.W.hist m)[j]!.Val b → a.toNat ≤ b.toNat
  /-- One waiter at a time (module doc, scope). -/
  one : ∀ u v, (E.ph (G u)).Waiting → (E.ph (G v)).Waiting → u = v
  /-- Every `waiting` write happened before the waiter at `w0`. -/
  hb : ∀ u, E.ph (G u) = .w0 → ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
    VClock.le (E.W.hist m)[j]!.clock (m.clocks[u]!) = true
  /-- A `waiting` write happened before the waiter at `w1`. -/
  seen : ∀ u, E.ph (G u) = .w1 → ∃ i < (E.W.hist m).size,
    (E.W.hist m)[i]!.Val (1 : BitVec 32) ∧ VClock.le (E.W.hist m)[i]!.clock (m.clocks[u]!) = true
  /-- A thread in the event's code is out of the lock's code; a sleeping waiter is `away`. -/
  lp : ∀ u, E.ph (G u) ≠ .out →
    L.ph (G u) = .out ∨ (E.ph (G u) = .w1 ∧ L.ph (G u) = .away)
  /-- A waiter in the futex queue is at the word. -/
  qw : ∀ w ∈ m.waiters, E.ph (G w.1) = .w1 → w.2 = E.W.ptr
  /-- A thread in the futex queue at the word is a waiter, and the newest write is `waiting` or a
  setter will wake it (no lost wakeup). -/
  q : ∀ w ∈ m.waiters, w.2 = E.W.ptr → E.ph (G w.1) = .w1 ∧
    ((E.newest m).Val (1 : BitVec 32) ∨ ∃ u, E.ph (G u) = .sw)

/-- A step of thread `t` in the event's code, as the protocol's rest sees it: no change, an op
at the word (a read, or an RMW of the newest write), the futex wait's sleep, the return of a
futex wait (woken, or at once), or a futex wake at the word. -/
inductive MStep (t : ThreadId) (m : Mem) : Mem → Prop
  | same : MStep t m m
  | op {m' : Mem} : E.W.Op t { m with current := t } m' → E.W.Ok m' →
      (E.W.hist m' = E.W.hist m ∨ ∃ (ord : AtomicOrder) (v : BitVec 32),
        E.W.hist m' = (E.W.hist m).push (Word.rmwEnt m' t ord (E.newest m) v)) → MStep t m m'
  | sleep {M : Mem} : E.W.Op t { m with current := t } M → E.W.hist M = E.W.hist m → E.W.Ok M →
      M.blocks = m.blocks → MStep t m { M with waiters := M.waiters.push (t, E.W.ptr) }
  | woken : MStep t m { m with current := t, woken := m.woken.erase t }
  | resume : MStep t m { m with current := t }
  | wake {m' : Mem} (c : Nat) (cs : List Nat) :
      ((Thread.futexWake E.W.ptr c cs).run { m with current := t }).run = some (.ok ((), m')) →
      MStep t m m'

/-- A protocol keeps the event (module doc). -/
structure Fits (L : FLock γ) {Tgt : Type} (P : Proto Tgt γ)
    (U : (ThreadId → γ) → Res → Mem → Prop) (ok : γ → Prop) : Prop where
  rest : E.W.InRest U
  ap : E.W.ApartL L.toLockWord
  inv : ∀ G rX m, U G rX m → E.Inv L G m
  fin : ∀ g, P.fin g → E.ph g = .out
  joins : ∀ g, P.joins g → E.ph g = .out
  /-- The event's place and the lock's are independent parts of a ghost value. -/
  lph : ∀ g p, L.ph (E.set g p) = L.ph g
  lpart : ∀ g p, L.part (E.set g p) = L.part g
  lheld : ∀ g p, L.held (E.set g p) = L.held g
  lR : ∀ G t p r, L.R G r → L.R (upd G t (E.set (G t) p)) r
  ph_l : ∀ g q h, E.ph (L.set g q h) = E.ph g
  set_l : ∀ g p q h, E.set (L.set g q h) p = L.set (E.set g p) q h
  ok_e : ∀ g p, ok (E.set g p) ↔ ok g
  /-- A step of the event's code keeps the rest, with the new place `p` of the stepping thread
  (and its lock place `q`: a waiter goes `away` while it sleeps), given the event's invariant
  after it. -/
  step : ∀ G rY m m' t p q, ok (G t) → (L.ph (G t) = .out ∨ L.ph (G t) = .away) →
    (q = .out ∨ q = .away) → U G (rsum (E.W.cellsR m) rY) m →
    (∀ l, E.W.In l → rY.heap l = none) → E.MStep t m m' →
    E.Inv L (upd G t (L.set (E.set (G t) p) q rnil)) m' →
    U (upd G t (L.set (E.set (G t) p) q rnil)) (rsum (E.W.cellsR m') rY) m'

variable {E}

/-! ## Facts of the writes -/

theorem val_eq {x : Word.Entry} {a b : BitVec 32} (ha : x.Val a) (hb : x.Val b) : a = b := by
  unfold Word.Entry.Val at ha hb; rw [ha] at hb; cases hb; rfl

theorem rmwEnt_val {M : Mem} {t : ThreadId} {ord : AtomicOrder} {last : Word.Entry}
    {v : BitVec 32} : (Word.rmwEnt M t ord last v).Val v := intOfBytes_rmw v

theorem get_push_lt {h : Array Word.Entry} {x : Word.Entry} {k : Nat} (hk : k < h.size) :
    (h.push x)[k]! = h[k]! := by
  have h1 : k < (h.push x).size := by simp; omega
  rw [getElem!_pos (h.push x) k h1, getElem!_pos h k hk, Array.getElem_push_lt hk]

theorem get_push_eq {h : Array Word.Entry} {x : Word.Entry} : (h.push x)[h.size]! = x := by
  rw [getElem!_pos _ _ (by simp)]; simp

/-- The word has a write. -/
theorem hist_pos {W : Word 32 4} {m : Mem} (hw : W.Ok m) : 0 < (W.hist m).size := by
  unfold Word.hist
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none => simp
  | some i =>
    obtain ⟨-, h0, -⟩ := hw.loc i _ (Word.loc_of_find hf)
    simpa using h0

/-- A read of `b` at write `j` while the invariant holds: the newest write is at least `b`. -/
theorem Inv.newest_ge {L : FLock γ} {G : ThreadId → γ} {m : Mem} (hI : E.Inv L G m)
    {j : Nat} {b : BitVec 32} (hj : j < (E.W.hist m).size) (hb : (E.W.hist m)[j]!.Val b) :
    ∃ k < 3, (E.newest m).Val (BitVec.ofNat 32 k) ∧ b.toNat ≤ k := by
  obtain ⟨k, hk, hv⟩ := hI.vals _ (by omega : (E.W.hist m).size - 1 < (E.W.hist m).size)
  refine ⟨k, hk, hv, ?_⟩
  have := hI.mono j _ b _ (by omega) (by omega) hb hv
  have hk' : (BitVec.ofNat 32 k).toNat = k := by simp; omega
  omega

/-- A read of `is_set`: the event is set. -/
theorem Inv.isSet_of {L : FLock γ} {G : ThreadId → γ} {m : Mem} (hI : E.Inv L G m)
    {j : Nat} (hj : j < (E.W.hist m).size) (hb : (E.W.hist m)[j]!.Val (2 : BitVec 32)) :
    E.IsSet m := by
  obtain ⟨k, hk, hv, hle⟩ := hI.newest_ge hj hb
  have : k = 2 := by simp at hle; omega
  subst this; exact hv

/-- A waiter at `w1` (with a `waiting` write `i` before it) reads at least `waiting`. -/
theorem Inv.read_ge {L : FLock γ} {G : ThreadId → γ} {m : Mem} (hI : E.Inv L G m) {i j : Nat}
    {c : VClock} (hi : i < (E.W.hist m).size) (hv : (E.W.hist m)[i]!.Val (1 : BitVec 32))
    (hc : VClock.le (E.W.hist m)[i]!.clock c = true) (hfl : Word.Floor (E.W.hist m) c j)
    (hj : j < (E.W.hist m).size) {b : BitVec 32} (hb : (E.W.hist m)[j]!.Val b) : 1 ≤ b.toNat := by
  have := hI.mono i j 1 b (hfl i hi hc) hj hv hb
  simpa using this

/-- A write of the word is one of `unset`, `waiting` and `is_set`. -/
theorem Inv.val3 {L : FLock γ} {G : ThreadId → γ} {m : Mem} (hI : E.Inv L G m) {j : Nat}
    (hj : j < (E.W.hist m).size) {b : BitVec 32} (hb : (E.W.hist m)[j]!.Val b) :
    b = 0 ∨ b = 1 ∨ b = 2 := by
  obtain ⟨k, hk, hv⟩ := hI.vals j hj
  have := val_eq hb hv
  subst this
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-! ## The invariant after a step -/

variable {L : FLock γ}

/-- Thread `t` enters the wait (`out` → `w0`), when no other thread is a waiter and every
`waiting` write happened before it (module doc, scope). -/
theorem Inv.enter {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ}
    (hI : E.Inv L (upd G t g) m) (hg : E.ph g = .out) (hgo : L.ph (E.set g .w0) = .out)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true) :
    E.Inv L (upd G t (E.set g .w0)) m := by
  have hnw : ∀ u, u ≠ t → ¬ (E.ph (upd G t (E.set g .w0) u)).Waiting := fun u hu hw => by
    rw [upd_ne _ _ hu] at hw
    rcases hone u hu with h | h <;> rw [h] at hw <;> rcases hw with h | h <;> cases h
  have hph : E.ph (upd G t (E.set g .w0) t) = .w0 := by rw [upd_self, E.ph_set]
  refine ⟨hI.vals, hI.mono, fun u v hu hv => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_,
    fun w hw hp => ?_, fun w hw hp => ?_⟩
  · by_cases eu : u = t
    · by_cases ev : v = t
      · rw [eu, ev]
      · exact absurd hv (hnw v ev)
    · exact absurd hu (hnw u eu)
  · by_cases eu : u = t
    · subst eu; exact hhb
    · exact absurd (.inl hu) (hnw u eu)
  · by_cases eu : u = t
    · subst eu; rw [hph] at hu; cases hu
    · exact absurd (.inr hu) (hnw u eu)
  · by_cases eu : u = t
    · subst eu; exact .inl (by rw [upd_self]; exact hgo)
    · have := hI.lp u (by rwa [upd_ne _ _ eu] at hu ⊢)
      rwa [upd_ne _ _ eu] at this ⊢
  · by_cases e : w.1 = t
    · rw [e, hph] at hp; cases hp
    · rw [upd_ne _ _ e] at hp
      exact hI.qw w hw (by rw [upd_ne _ _ e]; exact hp)
  · obtain ⟨h1, h2⟩ := hI.q w hw hp
    have e : w.1 ≠ t := fun e => by rw [e, upd_self, hg] at h1; cases h1
    refine ⟨by rw [upd_ne _ _ e] at h1 ⊢; exact h1, ?_⟩
    rcases h2 with h | ⟨u, hu⟩
    · exact .inl h
    · have eu : u ≠ t := fun e => by rw [e, upd_self, hg] at hu; cases hu
      exact .inr ⟨u, by rw [upd_ne _ _ eu] at hu ⊢; exact hu⟩

/-- A step of `t` that keeps the writes and the futex queue (a read, a return from a futex wait,
a change of `t`'s lock place): the other threads keep their ghost values, and `t` changes its
place as the premises say. -/
theorem Inv.move {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} (hI : E.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u) (hh : E.W.hist m' = E.W.hist m)
    (hwt : m'.waiters = m.waiters) (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hone : (E.ph (G' t)).Waiting → (E.ph (G t)).Waiting)
    (hw0 : E.ph (G' t) = .w0 → E.ph (G t) = .w0)
    (hw1 : E.ph (G' t) = .w1 → ∃ i < (E.W.hist m).size, (E.W.hist m)[i]!.Val (1 : BitVec 32) ∧
      VClock.le (E.W.hist m)[i]!.clock (m'.clocks[t]!) = true)
    (hsw : E.ph (G t) = .sw → E.ph (G' t) = .sw)
    (hlpt : E.ph (G' t) ≠ .out →
      L.ph (G' t) = .out ∨ (E.ph (G' t) = .w1 ∧ L.ph (G' t) = .away))
    (htq : ∀ w ∈ m.waiters, w.1 = t →
      (E.ph (G' t) = .w1 → w.2 = E.W.ptr) ∧ (w.2 = E.W.ptr → E.ph (G' t) = .w1)) :
    E.Inv L G' m' := by
  have key : ∀ x, (E.ph (G' x)).Waiting → (E.ph (G x)).Waiting := fun x hx => by
    by_cases e : x = t
    · subst e; exact hone hx
    · rwa [hG x e] at hx
  refine ⟨by rw [hh]; exact hI.vals, by rw [hh]; exact hI.mono,
    fun u v hu hv => hI.one u v (key u hu) (key v hv), fun u hu j hj hv => ?_, fun u hu => ?_,
    fun u hu => ?_, fun w hw hp => ?_, fun w hw hp => ?_⟩
  · rw [hh] at hj hv ⊢
    have hu' : E.ph (G u) = .w0 := by
      by_cases e : u = t
      · subst e; exact hw0 hu
      · rwa [hG u e] at hu
    exact VClock.le_trans (hI.hb u hu' j hj hv) (hclk u)
  · rw [hh]
    by_cases e : u = t
    · subst e; exact hw1 hu
    · rw [hG u e] at hu
      obtain ⟨i, hi, hv, hc⟩ := hI.seen u hu
      exact ⟨i, hi, hv, VClock.le_trans hc (hclk u)⟩
  · by_cases e : u = t
    · subst e; exact hlpt hu
    · rw [hG u e] at hu ⊢; exact hI.lp u hu
  · rw [hwt] at hw
    by_cases e : w.1 = t
    · exact (htq w hw e).1 (by rw [← e]; exact hp)
    · rw [hG _ e] at hp; exact hI.qw w hw hp
  · rw [hwt] at hw
    obtain ⟨h1, h2⟩ := hI.q w hw hp
    refine ⟨?_, ?_⟩
    · by_cases e : w.1 = t
      · rw [e]; exact (htq w hw e).2 hp
      · rw [hG _ e]; exact h1
    · unfold FEvent.newest; rw [hh]
      rcases h2 with h | ⟨u, hu⟩
      · exact .inl h
      · refine .inr ⟨u, ?_⟩
        by_cases e : u = t
        · subst e; exact hsw hu
        · rw [hG u e]; exact hu

/-- The waiter's successful `cmpxchg(unset → waiting)` (`w0` → `w1`). -/
theorem Inv.casOk {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    (hI : E.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u) (ht0 : E.ph (G t) = .w0)
    (ht1 : E.ph (G' t) = .w1) (hlpt : L.ph (G' t) = .out)
    (hv0 : (E.newest m).Val (0 : BitVec 32))
    (hh : E.W.hist m' = (E.W.hist m).push (Word.rmwEnt m' t ord (E.newest m) (1 : BitVec 32)))
    (hwt : m'.waiters = m.waiters) (hnq : ∀ w ∈ m.waiters, w.1 ≠ t)
    (hpos : 0 < (E.W.hist m).size) :
    E.Inv L G' m' := by
  have hsz : (E.W.hist m').size = (E.W.hist m).size + 1 := by rw [hh]; simp
  have hold : ∀ j, j < (E.W.hist m).size → (E.W.hist m')[j]! = (E.W.hist m)[j]! := fun j hj => by
    rw [hh]; exact get_push_lt hj
  have hnew : (E.W.hist m')[(E.W.hist m).size]!.Val (1 : BitVec 32) := by
    rw [hh, get_push_eq]; exact rmwEnt_val
  -- `t` is the only waiter
  have hot : ∀ u, u ≠ t → ¬ (E.ph (G u)).Waiting := fun u hu hw => hu (hI.one u t hw (.inl ht0))
  have key : ∀ u, u ≠ t → ¬ (E.ph (G' u)).Waiting := fun u hu hw => by
    rw [hG u hu] at hw; exact hot u hu hw
  refine ⟨fun j hj => ?_, fun i j a b hij hj ha hb => ?_, fun u v hu hv => ?_,
    fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw hp => ?_, fun w hw hp => ?_⟩
  · rw [hsz] at hj
    rcases (by omega : j < (E.W.hist m).size ∨ j = (E.W.hist m).size) with hj | rfl
    · rw [hold j hj]; exact hI.vals j hj
    · exact ⟨1, by omega, hnew⟩
  · rw [hsz] at hj
    rcases (by omega : j < (E.W.hist m).size ∨ j = (E.W.hist m).size) with hj' | rfl
    · rw [hold i (by omega)] at ha; rw [hold j hj'] at hb
      exact hI.mono i j a b hij hj' ha hb
    · have hb1 := val_eq hb hnew; subst hb1
      rcases (by omega : i < (E.W.hist m).size ∨ i = (E.W.hist m).size) with hi | rfl
      · rw [hold i hi] at ha
        have := hI.mono i _ a 0 (by omega) (by omega) ha hv0
        simp at this ⊢; omega
      · have := val_eq ha hnew; subst this; exact Nat.le_refl _
  · by_cases eu : u = t
    · by_cases ev : v = t
      · rw [eu, ev]
      · exact absurd hv (key v ev)
    · exact absurd hu (key u eu)
  · exfalso
    by_cases eu : u = t
    · subst eu; rw [ht1] at hu; cases hu
    · exact key u eu (.inl hu)
  · by_cases eu : u = t
    · subst eu
      refine ⟨(E.W.hist m).size, by omega, hnew, ?_⟩
      rw [hh, get_push_eq]; exact VClock.le_refl _
    · exact absurd (.inr hu) (key u eu)
  · by_cases eu : u = t
    · subst eu; exact .inl hlpt
    · rw [hG u eu] at hu ⊢; exact hI.lp u hu
  · rw [hwt] at hw
    have e := hnq w hw
    rw [hG _ e] at hp; exact hI.qw w hw hp
  · rw [hwt] at hw
    exfalso
    have e := hnq w hw
    exact hot _ e (.inr (hI.q w hw hp).1)

/-- A setter's `xchg(is_set)` (`out` → `sw` if it read `waiting`, else `out`). -/
theorem Inv.xchg {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    (hI : E.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u) (ht0 : E.ph (G t) = .out)
    (ht1 : E.ph (G' t) = .sw ∨ E.ph (G' t) = .out)
    (hsw : (E.newest m).Val (1 : BitVec 32) → E.ph (G' t) = .sw) (hlpt : L.ph (G' t) = .out)
    (hh : E.W.hist m' = (E.W.hist m).push (Word.rmwEnt m' t ord (E.newest m) (2 : BitVec 32)))
    (hwt : m'.waiters = m.waiters) (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hnq : ∀ w ∈ m.waiters, w.1 ≠ t) :
    E.Inv L G' m' := by
  have hsz : (E.W.hist m').size = (E.W.hist m).size + 1 := by rw [hh]; simp
  have hold : ∀ j, j < (E.W.hist m).size → (E.W.hist m')[j]! = (E.W.hist m)[j]! := fun j hj => by
    rw [hh]; exact get_push_lt hj
  have hnew : (E.W.hist m')[(E.W.hist m).size]!.Val (2 : BitVec 32) := by
    rw [hh, get_push_eq]; exact rmwEnt_val
  have hnw : ¬ (E.ph (G' t)).Waiting := fun hw => by
    rcases ht1 with h | h <;> rw [h] at hw <;> rcases hw with h | h <;> cases h
  have key : ∀ x, (E.ph (G' x)).Waiting → (E.ph (G x)).Waiting ∧ x ≠ t := fun x hx => by
    by_cases e : x = t
    · subst e; exact absurd hx hnw
    · rw [hG x e] at hx; exact ⟨hx, e⟩
  refine ⟨fun j hj => ?_, fun i j a b hij hj ha hb => ?_, fun u v hu hv => ?_,
    fun u hu j hj hv => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw hp => ?_, fun w hw hp => ?_⟩
  · rw [hsz] at hj
    rcases (by omega : j < (E.W.hist m).size ∨ j = (E.W.hist m).size) with hj | rfl
    · rw [hold j hj]; exact hI.vals j hj
    · exact ⟨2, by omega, hnew⟩
  · rw [hsz] at hj
    rcases (by omega : j < (E.W.hist m).size ∨ j = (E.W.hist m).size) with hj' | rfl
    · rw [hold i (by omega)] at ha; rw [hold j hj'] at hb
      exact hI.mono i j a b hij hj' ha hb
    · have hb2 := val_eq hb hnew; subst hb2
      rcases (by omega : i < (E.W.hist m).size ∨ i = (E.W.hist m).size) with hi | rfl
      · rw [hold i hi] at ha
        rcases hI.val3 hi ha with rfl | rfl | rfl <;> decide
      · have := val_eq ha hnew; subst this; exact Nat.le_refl _
  · exact hI.one u v (key u hu).1 (key v hv).1
  · have hu' := key u (.inl hu)
    rw [hG u hu'.2] at hu
    rw [hsz] at hj
    rcases (by omega : j < (E.W.hist m).size ∨ j = (E.W.hist m).size) with hj' | rfl
    · rw [hold j hj'] at hv ⊢
      exact VClock.le_trans (hI.hb u hu j hj' hv) (hclk u)
    · have := val_eq hv hnew; cases this
  · have hu' := key u (.inr hu)
    rw [hG u hu'.2] at hu
    obtain ⟨i, hi, hv, hc⟩ := hI.seen u hu
    exact ⟨i, by omega, by rw [hold i hi]; exact hv,
      by rw [hold i hi]; exact VClock.le_trans hc (hclk u)⟩
  · by_cases eu : u = t
    · subst eu; exact .inl hlpt
    · rw [hG u eu] at hu ⊢; exact hI.lp u hu
  · rw [hwt] at hw
    have e := hnq w hw
    rw [hG _ e] at hp; exact hI.qw w hw hp
  · rw [hwt] at hw
    have e := hnq w hw
    obtain ⟨h1, h2⟩ := hI.q w hw hp
    refine ⟨by rw [hG _ e]; exact h1, .inr ?_⟩
    rcases h2 with h | ⟨u, hu⟩
    · exact ⟨t, hsw h⟩
    · have eu : u ≠ t := fun e => by rw [e, ht0] at hu; cases hu
      exact ⟨u, by rw [hG u eu]; exact hu⟩

/-- The waiter's sleep at the word, which held `waiting`. -/
theorem Inv.sleep {G : ThreadId → γ} {m M : Mem} {t : ThreadId} (hI : E.Inv L G m)
    (ht : E.ph (G t) = .w1) (hop : E.W.Op t { m with current := t } M)
    (hh : E.W.hist M = E.W.hist m) (hv : (E.newest m).Val (1 : BitVec 32)) :
    E.Inv L G { M with waiters := M.waiters.push (t, E.W.ptr) } := by
  have hh' : E.W.hist { M with waiters := M.waiters.push (t, E.W.ptr) } = E.W.hist m := hh
  have hclk : ∀ u, VClock.le (m.clocks[u]!) (M.clocks[u]!) = true := hop.clocks
  have hwt : M.waiters = m.waiters := hop.waiters
  refine ⟨by rw [hh']; exact hI.vals, by rw [hh']; exact hI.mono, hI.one,
    fun u hu j hj hv => ?_, fun u hu => ?_, hI.lp, fun w hw hp => ?_, fun w hw hp => ?_⟩
  · rw [hh'] at hj hv ⊢; exact VClock.le_trans (hI.hb u hu j hj hv) (hclk u)
  · rw [hh']
    obtain ⟨i, hi, hv, hc⟩ := hI.seen u hu
    exact ⟨i, hi, hv, VClock.le_trans hc (hclk u)⟩
  · rcases Array.mem_push.mp hw with hw | rfl
    · rw [hwt] at hw; exact hI.qw w hw hp
    · rfl
  · unfold FEvent.newest; rw [hh']
    rcases Array.mem_push.mp hw with hw | rfl
    · rw [hwt] at hw; exact hI.q w hw hp
    · exact ⟨ht, .inl hv⟩

/-- The setter's wake of every waiter at the word (`sw` → `out`; one waiter at a time, so the
wake of at least one waiter empties the queue at the word). -/
theorem Inv.wake {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g : γ} {c : Nat}
    {cs : List Nat} (hI : E.Inv L G m) (ht : E.ph (G t) = .sw) (hg : E.ph g = .out)
    (hc : 1 ≤ c)
    (h : ((Thread.futexWake E.W.ptr c cs).run { m with current := t }).run = some (.ok ((), m'))) :
    E.Inv L (upd G t g) m' := by
  have hm' := Proto.modify_ok h
  subst hm'
  have hnw : ∀ x, (E.ph (upd G t g x)).Waiting → (E.ph (G x)).Waiting ∧ x ≠ t := fun x hx => by
    by_cases e : x = t
    · subst e; rw [upd_self, hg] at hx; rcases hx with h | h <;> cases h
    · rw [upd_ne _ _ e] at hx; exact ⟨hx, e⟩
  -- a waiter left at the word was woken
  have hgone : ∀ w ∈ m.waiters, w.2 = E.W.ptr →
      (Thread.wakeSet m.waiters E.W.ptr c cs).contains w.1 = true := fun w hw hp => by
    have hne : ((m.waiters.filter (·.2 == E.W.ptr)).toList.map (·.1)) ≠ [] := by
      intro he
      have : w.1 ∈ ((m.waiters.filter (·.2 == E.W.ptr)).toList.map (·.1)) :=
        List.mem_map.mpr ⟨w, by simp [hw, hp], rfl⟩
      rw [he] at this; cases this
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _
      (Thread.wakePick_ne_nil (cs := cs) (by omega : 0 < c) hne)
    have hu' : u ∈ Thread.wakeSet m.waiters E.W.ptr c cs := by
      unfold Thread.wakeSet; exact List.mem_toArray.mpr hu
    obtain ⟨w', hw', hp', rfl⟩ := Thread.mem_wakeSet hu'
    have e : w'.1 = w.1 := hI.one _ _ (.inr (hI.q w' hw' hp').1) (.inr (hI.q w hw hp).1)
    rw [← e]; exact Array.contains_iff_mem.mpr hu'
  refine ⟨hI.vals, hI.mono, fun u v hu hv => hI.one u v (hnw u hu).1 (hnw v hv).1,
    fun u hu j hj hv => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_⟩
  · have := hnw u (.inl hu); rw [upd_ne _ _ this.2] at hu; exact hI.hb u hu j hj hv
  · have := hnw u (.inr hu); rw [upd_ne _ _ this.2] at hu; exact hI.seen u hu
  · by_cases e : u = t
    · subst e; rw [upd_self, hg] at hu; exact absurd rfl hu
    · rw [upd_ne _ _ e] at hu ⊢; exact hI.lp u hu
  · simp only [Array.mem_filter] at hw
    by_cases e : w.1 = t
    · rw [e, upd_self, hg] at hp; cases hp
    · rw [upd_ne _ _ e] at hp; exact hI.qw w hw.1 hp
  · have hw' : w ∈ m.waiters ∧
        (Thread.wakeSet m.waiters E.W.ptr c cs).contains w.1 = false := by
      simpa [Array.mem_filter] using hw
    rw [hgone w hw'.1 hp] at hw'
    cases hw'.2

/-- A change of `t`'s ghost value that keeps its place in the event's code. -/
theorem Inv.relabel {G G' : ThreadId → γ} {m : Mem} {t : ThreadId} (hI : E.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u) (hph : E.ph (G' t) = E.ph (G t))
    (hlpt : E.ph (G' t) ≠ .out →
      L.ph (G' t) = .out ∨ (E.ph (G' t) = .w1 ∧ L.ph (G' t) = .away)) :
    E.Inv L G' m :=
  hI.move hG rfl rfl (fun _ => VClock.le_refl _) (by rw [hph]; exact id)
    (by rw [hph]; exact id) (fun h => hI.seen t (by rw [← hph]; exact h)) (by rw [hph]; exact id)
    hlpt (fun w hw e => ⟨fun h => hI.qw w hw (by rw [e, ← hph]; exact h),
      fun h => by rw [hph, ← e]; exact (hI.q w hw h).1⟩)

/-- `g` at the place it has. -/
theorem set_of {g : γ} {p : EPh} (h : E.ph g = p) : E.set g p = g := h ▸ E.set_self g

theorem cur_eq {m : Mem} {t : ThreadId} (h : m.current = t) : { m with current := t } = m := by
  subst h; rfl

/-- A thread not in the futex queue. -/
theorem notQ_mem {ws : Array (ThreadId × Ptr)} {t : ThreadId} (h : ws.any (·.1 == t) = false) :
    ∀ w ∈ ws, w.1 ≠ t := fun w hw e => by
  have : ws.any (·.1 == t) = true := Array.any_eq_true'.mpr ⟨w, hw, by simp [e]⟩
  rw [h] at this; cases this

/-! ## The protocol after a step -/

variable {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- A sleeping waiter of a set event is not in a deadlock: a setter at `sw` runs. -/
theorem Fits.live (hE : E.Fits L P U ok) {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId}
    (hI : E.Inv L G m) (hL : L.Inv G rX m) (ht : E.ph (G t) = .w1) (hs : E.IsSet m) :
    P.Live t G m := by
  intro hin hall
  obtain ⟨w, hw, he⟩ := Array.any_eq_true'.mp hin
  have e : w.1 = t := by simpa using he
  have hp := hI.qw w hw (by rw [e]; exact ht)
  rcases (hI.q w hw hp).2 with h1 | ⟨u, hu⟩
  · have := val_eq h1 hs; cases this
  · have hlo : L.ph (G u) = .out := by
      rcases hI.lp u (by rw [hu]; decide) with h | ⟨h, -⟩
      · exact h
      · rw [hu] at h; cases h
    have hut := (hL.ht (t := u) (by rw [hlo]; decide)).1
    rcases hall u hut with h | h | h
    · rw [hE.fin _ h] at hu; cases hu
    · have := hL.w.notQ (t := u) (show L.ph (G u) ≠ .wait by rw [hlo]; decide)
        (show L.ph (G u) ≠ .away by rw [hlo]; decide)
      rw [this] at h; cases h
    · rw [hE.joins _ h] at hu; cases hu

/-- After a step of the event's code by `t` at `out` of the lock (`g`, new place `p`): the
protocol's invariant, from the lock's invariant after the step, the rest before it, and the
event's invariant after it. -/
theorem Fits.back (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ} {rY : Res}
    {m₁ m' : Mem} {t : ThreadId} {g : γ} {p : EPh} (hg₁ : G₁ t = g) (hgo : L.ph g = .out)
    (hok : ok g) (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hs : E.MStep t m₁ m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hI : E.Inv L (upd G₁ t (E.set g p)) m') :
    P.inv (upd G₁ t (E.set g p)) m' := by
  subst hg₁
  have hheld : L.held (G₁ t) = rnil := hL.idle t (by rw [hgo]; decide)
  have hset : L.set (E.set (G₁ t) p) .out rnil = E.set (G₁ t) p := by
    have := L.set_self (E.set (G₁ t) p); rwa [hE.lph, hE.lheld, hgo, hheld] at this
  have hU' := hE.step G₁ rY m₁ m' t p .out hok (.inl hgo) (.inl rfl) hU hY hs (by rw [hset]; exact hI)
  rw [hset] at hU'
  have hL' := hL.ghost (t := t) (g := E.set (G₁ t) p) hgo (.inl (by rw [hE.lph]; exact hgo))
    (hE.lpart _ _) (by rw [hE.lheld]; exact hheld) (fun _ => hL.ht (by rw [hgo]; decide))
    (fun r hr => hE.lR G₁ t p r hr)
  exact (hP.inv _ _).mpr ⟨_, hL', hU'⟩

/-- The facts at a stop of `t` (at `out` of the lock) before an op at the word: the event's
invariant, `t` is not in the futex queue. -/
theorem Fits.atOp (hE : E.Fits L P U ok) {G₁ : ThreadId → γ} {rY : Res} {m₁ m' : Mem}
    {t : ThreadId} (hgo : L.ph (G₁ t) = .out) (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁)
    (hop : E.W.Op t m₁ m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m') :
    E.Inv L G₁ m₁ ∧ (∀ w ∈ m₁.waiters, w.1 ≠ t) ∧ E.W.Ok m₁ := by
  refine ⟨hE.inv _ _ _ hU, ?_, (hE.rest _ _ _ hU).1⟩
  have := hL.w.notQ (t := t) (show L.ph (G₁ t) ≠ .wait by rw [hgo]; decide)
    (show L.ph (G₁ t) ≠ .away by rw [hgo]; decide)
  rw [hop.waiters] at this
  exact notQ_mem this

/-- A waiter's read at the word (`w0` or `w1`) of write `j` with the value `b`: `unset` (only
at `w0`: it stays), `waiting` (it goes to `w1`), or `is_set` (it leaves; the event is set). -/
theorem Fits.afterRead (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} (hg₁ : G₁ t = g) (hgw : (E.ph g).Waiting)
    (hgo : L.ph g = .out) (hok : ok g) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hop : E.W.Op t m₁ m') (hw' : E.W.Ok m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hh : E.W.hist m' = E.W.hist m₁) {j : Nat} {b : BitVec 32} (hj : j < (E.W.hist m₁).size)
    (hv : (E.W.hist m₁)[j]!.Val b) (hfl : Word.Floor (E.W.hist m₁) (m₁.clocks[t]!) j) :
    (b = 0 ∧ E.ph g = .w0 ∧ P.inv (upd G₁ t (E.set g .w0)) m') ∨
    (b = 1 ∧ P.inv (upd G₁ t (E.set g .w1)) m') ∨
    (b = 2 ∧ E.IsSet m' ∧ P.inv (upd G₁ t (E.set g .out)) m') := by
  obtain ⟨hI, hnq, -⟩ := hE.atOp (by rw [hg₁]; exact hgo) hU hop hL
  have hs : E.MStep t m₁ m' := .op (by rw [cur_eq hc₁]; exact hop) hw' (.inl hh)
  have hclk := hop.clocks
  have hlo : ∀ p, L.ph (upd G₁ t (E.set g p) t) = .out := fun p => by
    rw [upd_self, hE.lph]; exact hgo
  have hgt : E.ph (G₁ t) = E.ph g := by rw [hg₁]
  -- the new invariant at place `p`
  have hmv : ∀ p, ((E.ph (E.set g p)).Waiting → (E.ph g).Waiting) →
      (p = .w0 → E.ph g = .w0) →
      (p = .w1 → ∃ i < (E.W.hist m₁).size, (E.W.hist m₁)[i]!.Val (1 : BitVec 32) ∧
        VClock.le (E.W.hist m₁)[i]!.clock (m'.clocks[t]!) = true) →
      E.Inv L (upd G₁ t (E.set g p)) m' := fun p h1 h2 h3 =>
    hI.move (fun u hu => upd_ne _ _ hu) hh hop.waiters hclk
      (by rw [upd_self, hgt]; exact h1) (by rw [upd_self, hgt, E.ph_set]; exact h2)
      (by rw [upd_self, E.ph_set]; exact h3)
      (by rw [hgt]; intro h; rcases hgw with e | e <;> rw [e] at h <;> cases h)
      (fun _ => .inl (hlo p)) (fun w hw e => absurd e (hnq w hw))
  rcases hI.val3 hj hv with rfl | rfl | rfl
  · -- `unset`: only at `w0`
    have hw0 : E.ph g = .w0 := by
      rcases hgw with e | e
      · exact e
      · obtain ⟨i, hi, hv1, hc⟩ := hI.seen t (by rw [hgt]; exact e)
        have := hI.read_ge hi hv1 hc hfl hj hv
        simp at this
    refine .inl ⟨rfl, hw0, hE.back hP hg₁ hgo hok hU hY hs hL
      (hmv .w0 (fun _ => hgw) (fun _ => hw0) (fun h => by cases h))⟩
  · refine .inr (.inl ⟨rfl, hE.back hP hg₁ hgo hok hU hY hs hL
      (hmv .w1 (fun _ => hgw) (fun h => by cases h) fun _ => ?_)⟩)
    rcases hgw with e | e
    · exact ⟨j, hj, hv, VClock.le_trans (hI.hb t (by rw [hgt]; exact e) j hj hv) (hclk t)⟩
    · obtain ⟨i, hi, hv1, hc⟩ := hI.seen t (by rw [hgt]; exact e)
      exact ⟨i, hi, hv1, VClock.le_trans hc (hclk t)⟩
  · have hset : E.IsSet m' := by
      have := hI.isSet_of hj hv
      unfold FEvent.IsSet FEvent.newest at this ⊢; rw [hh]; exact this
    refine .inr (.inr ⟨rfl, hset, hE.back hP hg₁ hgo hok hU hY hs hL
      (hmv .out (by rw [E.ph_set]; intro h; rcases h with h | h <;> cases h)
        (fun h => by cases h) (fun h => by cases h))⟩)

/-- A read at the word by a thread out of the event's code (`g`): it stays; a read of `is_set`
means the event is set. -/
theorem Fits.afterPeek (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} (hg₁ : G₁ t = g) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hok : ok g) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hop : E.W.Op t m₁ m') (hw' : E.W.Ok m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hh : E.W.hist m' = E.W.hist m₁) {j : Nat} {b : BitVec 32} (hj : j < (E.W.hist m₁).size)
    (hv : (E.W.hist m₁)[j]!.Val b) :
    P.inv (upd G₁ t g) m' ∧ (b = 2 → E.IsSet m') := by
  obtain ⟨hI, hnq, -⟩ := hE.atOp (by rw [hg₁]; exact hgo) hU hop hL
  have hs : E.MStep t m₁ m' := .op (by rw [cur_eq hc₁]; exact hop) hw' (.inl hh)
  have hgt : E.ph (G₁ t) = .out := by rw [hg₁]; exact hgx
  have hI' : E.Inv L (upd G₁ t (E.set g .out)) m' :=
    hI.move (fun u hu => upd_ne _ _ hu) hh hop.waiters hop.clocks
      (by rw [upd_self, E.ph_set, hgt]; exact id) (by rw [upd_self, E.ph_set]; intro h; cases h)
      (by rw [upd_self, E.ph_set]; intro h; cases h) (by rw [hgt]; intro h; cases h)
      (by rw [upd_self, E.ph_set]; intro h; exact absurd rfl h) (fun w hw e => absurd e (hnq w hw))
  have := hE.back hP hg₁ hgo hok hU hY hs hL hI'
  rw [set_of hgx] at this
  refine ⟨this, fun hb => ?_⟩
  subst hb
  have := hI.isSet_of hj hv
  unfold FEvent.IsSet FEvent.newest at this ⊢; rw [hh]; exact this

/-- The waiter's successful `cmpxchg(unset → waiting)`: it goes to `w1`. -/
theorem Fits.afterCasOk (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {ord : AtomicOrder} (hg₁ : G₁ t = g)
    (hg : E.ph g = .w0) (hgo : L.ph g = .out) (hok : ok g) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hop : E.W.Op t m₁ m') (hw' : E.W.Ok m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hv : (E.newest m₁).Val (0 : BitVec 32))
    (hh : E.W.hist m' = (E.W.hist m₁).push (Word.rmwEnt m' t ord (E.newest m₁) (1 : BitVec 32))) :
    P.inv (upd G₁ t (E.set g .w1)) m' := by
  obtain ⟨hI, hnq, hw₁⟩ := hE.atOp (by rw [hg₁]; exact hgo) hU hop hL
  refine hE.back hP hg₁ hgo hok hU hY (.op (by rw [cur_eq hc₁]; exact hop) hw' (.inr ⟨ord, 1, hh⟩))
    hL (hI.casOk (fun u hu => upd_ne _ _ hu) (by rw [hg₁]; exact hg)
      (by rw [upd_self, E.ph_set]) (by rw [upd_self, hE.lph]; exact hgo) hv hh hop.waiters hnq
      (hist_pos hw₁))

/-- A setter's `xchg(is_set)`, by a thread out of the event's code (`g`), that read `o`: the event
is set, and the setter is at `sw` if it read `waiting` (it must wake), else out. -/
theorem Fits.afterXchg (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {ord : AtomicOrder} (hg₁ : G₁ t = g)
    (hgx : E.ph g = .out) (hgo : L.ph g = .out) (hok : ok g) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hop : E.W.Op t m₁ m') (hw' : E.W.Ok m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    {o : BitVec 32} (hv : (E.newest m₁).Val o)
    (hh : E.W.hist m' = (E.W.hist m₁).push (Word.rmwEnt m' t ord (E.newest m₁) (2 : BitVec 32))) :
    E.IsSet m' ∧ ((o = 1 ∧ P.inv (upd G₁ t (E.set g .sw)) m') ∨
      (o ≠ 1 ∧ P.inv (upd G₁ t (E.set g .out)) m')) := by
  obtain ⟨hI, hnq, -⟩ := hE.atOp (by rw [hg₁]; exact hgo) hU hop hL
  have hs : E.MStep t m₁ m' := .op (by rw [cur_eq hc₁]; exact hop) hw' (.inr ⟨ord, 2, hh⟩)
  have hgt : E.ph (G₁ t) = .out := by rw [hg₁]; exact hgx
  have hset : E.IsSet m' := by
    unfold FEvent.IsSet FEvent.newest; rw [hh]
    simp only [Array.size_push, Nat.add_sub_cancel]
    rw [get_push_eq]; exact rmwEnt_val
  have hx : ∀ p, (p = .sw ∨ p = .out) → ((E.newest m₁).Val (1 : BitVec 32) → p = .sw) →
      E.Inv L (upd G₁ t (E.set g p)) m' := fun p hp h1 =>
    hI.xchg (fun u hu => upd_ne _ _ hu) hgt (by rw [upd_self, E.ph_set]; exact hp)
      (by rw [upd_self, E.ph_set]; exact h1) (by rw [upd_self, hE.lph]; exact hgo) hh hop.waiters
      hop.clocks hnq
  refine ⟨hset, ?_⟩
  by_cases ho : o = 1
  · subst ho
    exact .inl ⟨rfl, hE.back hP hg₁ hgo hok hU hY hs hL (hx .sw (.inl rfl) fun _ => rfl)⟩
  · exact .inr ⟨ho, hE.back hP hg₁ hgo hok hU hY hs hL (hx .out (.inr rfl) fun h1 =>
      absurd (val_eq hv h1) ho)⟩

/-- A thread enters the wait (`out` → `w0`; module doc, scope). -/
theorem Fits.enter (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m : Mem}
    {t : ThreadId} {g : γ} (hgx : E.ph g = .out) (hgo : L.ph g = .out) (hok : ok g)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) : P.inv (upd G t (E.set g .w0)) m := by
  obtain ⟨rX, hL, hU⟩ := (hP.inv _ _).mp hi
  obtain ⟨-, rY, rfl, hY⟩ := hE.rest _ _ _ hU
  have hI := hE.inv _ _ _ hU
  have := hE.back hP (upd_self G t g) hgo hok hU hY .same hL
    (by rw [upd_upd]; exact hI.enter hgx (by rw [hE.lph]; exact hgo) hone hhb)
  rwa [upd_upd] at this

/-- The setter's wake at the word (`sw` → `out`), of at least one waiter. -/
theorem Fits.afterWake (hE : E.Fits L P U ok) (hP : L.FitsOn P U ok) {G₁ : ThreadId → γ}
    {rX : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {c : Nat} {cs : List Nat} (hg₁ : G₁ t = g)
    (hg : E.ph g = .sw) (hgo : L.ph g = .out) (hok : ok g) (hc : 1 ≤ c) (hU : U G₁ rX m₁)
    (hw : ((Thread.futexWake E.W.ptr c cs).run { m₁ with current := t }).run =
      some (.ok ((), m'))) (hL : L.Inv G₁ rX m') :
    m'.current = t ∧ P.inv (upd G₁ t (E.set g .out)) m' := by
  have hm' := Proto.modify_ok hw
  obtain ⟨-, rY, rfl, hY⟩ := hE.rest _ _ _ hU
  have hcl : E.W.cellsR m' = E.W.cellsR m₁ := Word.cellsR_congr (by rw [hm'])
  refine ⟨by rw [hm'], hE.back hP hg₁ hgo hok hU hY (.wake c cs hw) (by rw [hcl]; exact hL) ?_⟩
  exact (hE.inv _ _ _ hU).wake (by rw [hg₁]; exact hg) (E.ph_set _ _) hc hw

end FEvent

end Full
end Zig
