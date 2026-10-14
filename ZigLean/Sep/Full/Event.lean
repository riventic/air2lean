import ZigLean.Sep.Full.WordRules

/-!
# The futex event, over full-state resources

A one-shot futex event (`Io.Event` of 0.16.0, `Thread.ResetEvent.FutexImpl` of 0.15.2): a `u32`
word `W` with the values `unset` 0, `waiting` 1 and `is_set` 2, and no reset. A waiter does an
acquire `cmpxchg(unset → waiting)` and then, while the word holds `waiting`, a futex wait and an
acquire load; a setter does a release `xchg(is_set)` and wakes every waiter if it read
`waiting`. This module is the component once for every protocol that has such an event next to
a lock (`FLock.Fits`, the event as a primitive over its word: `FEvent.prim`, `FPrim.ofWords`),
and the rules of the event's ops in generated code; an implementation
of a Zig version walks its code with them (`EventImpl`).

`FEvent γ` is the word and a thread's place in the event's code (`EPh`: `out`, `w0` registered
before its first write, `w1` it saw or wrote `waiting` and may sleep, `sw` a setter that read
`waiting` and has not woken yet). `FEvent.Inv` is the event's invariant: the writes are 0, 1, 2
and never get smaller, the waiter saw a `waiting` write (it happened before it), a thread in the
futex queue at the word is at `w1`, and the newest write is `waiting` or a setter is at `sw`
(no lost wakeup). A protocol keeps the event (`FLock.Fits` with `E.prim L`): its rest `U`
carries the invariant and has the word's cells (`Word.InRest`), and it is stable under each step
of the event's code (`MStep`, with the place change of the stepping thread).

**Roles.** `FEvent.wx` are the ghost values of the threads that may wait (the protocol says which
threads those are); the invariant keeps that each waiter and the writer of each `waiting` write
may wait (`Inv.wx`, `Inv.wby`), so a client with one such thread discharges `hone` and `hhb`
from the invariant. `FEvent.sx` are the ghost values of the threads that may set it: a setter at
`sw` has one (`Inv.sx`), so a client can tell which threads are in the setter's code. A step of
the event's code changes the stepping thread's lock place only for a waiter's sleep (`w1`,
`away`), so the event's steps keep the places of the other components of a protocol.
**Lock steps.** A thread in the event's code runs no lock code: a client's
`FLock.Fits` `ok` excludes it, and then a lock step keeps the event's invariant
(`Inv.lstep`).

**Scope (one waiter at a time).** A thread enters the wait (`w0`) only when no other thread is
at `w0` or `w1`, and after every `waiting` write so far happened before it (`hone`/`hhb` of
`Inv.enter`). Reason: the memory model's facts of a read (`Word.Ok.load`, `Ok.cas`) give the
happens-before floor of the read (`Word.Floor`), not the read-read coherence of `Mem.seen`, and a
full-state frame (`Word.Keep`, `FStepIn`) does not keep `Mem.seen`; so a waiter whose `cmpxchg`
read another waiter's `waiting` without a happens-before edge could not exclude that its next
load reads `unset` (the code's `unreachable`). With one waiter, the waiter's own `waiting`
write (or one that happened before it) is in its floor. Several waiters are a follow-up.
Likewise only the threads with the setter role set the event (`EventImpl.set_wp` takes `E.sx`);
lifting both limits is the same follow-up.
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
structure FEvent (γ : Type) extends FPlace γ EPh where
  W : Word 32 4
  /-- The ghost values of the threads that may wait at the event (the protocol's roles). -/
  wx : γ → Prop
  wx_set : ∀ g p, wx (set g p) ↔ wx g
  /-- The ghost values of the threads that may set the event (the protocol's roles). -/
  sx : γ → Prop
  sx_set : ∀ g p, sx (set g p) ↔ sx g

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
  qw : ∀ w ∈ m.waiters, E.ph (G w.1) = .w1 → w.2 = E.W.ptr ∨ w.2 = L.ptr
  /-- A thread in the futex queue at the word is a waiter, and the newest write is `waiting` or a
  setter will wake it (no lost wakeup). -/
  q : ∀ w ∈ m.waiters, w.2 = E.W.ptr → E.ph (G w.1) = .w1 ∧
    ((E.newest m).Val (1 : BitVec 32) ∨ ∃ u, E.ph (G u) = .sw)
  /-- A setter at `sw` has set the event. -/
  swset : ∀ u, E.ph (G u) = .sw → (E.newest m).Val (2 : BitVec 32)
  /-- A waiter has a ghost value that may wait. -/
  wx : ∀ u, (E.ph (G u)).Waiting → E.wx (G u)
  /-- Each `waiting` write happened before a thread that may wait (it wrote it). -/
  wby : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
    ∃ u, E.wx (G u) ∧ VClock.le (E.W.hist m)[j]!.clock (m.clocks[u]!) = true
  /-- A setter at `sw` has a ghost value that may set. -/
  sx : ∀ u, E.ph (G u) = .sw → E.sx (G u)

/-- **The event at its start**: every thread out of its code, no thread in the futex queue, and
the word has its first write, `unset`. -/
theorem Inv.start {L : FLock γ} {G : ThreadId → γ} {m : Mem} (hW : (E.W.hist m).size = 1)
    (hW0 : (E.W.hist m)[0]!.Val (0 : BitVec 32)) (hout : ∀ u, E.ph (G u) = .out)
    (hq : m.waiters = #[]) : E.Inv L G m where
  vals j hj := by obtain rfl : j = 0 := by omega
                  exact ⟨0, by decide, hW0⟩
  mono i j a b _ hj ha hb := by
    obtain rfl : j = 0 := by omega
    obtain rfl : i = 0 := by omega
    obtain rfl := Except.ok.inj (Option.some.inj (ha.symm.trans hb)); exact Nat.le_refl _
  one u _ h := by rw [hout u] at h; rcases h with h | h <;> cases h
  hb u h := by rw [hout u] at h; cases h
  seen u h := by rw [hout u] at h; cases h
  lp u h := absurd (hout u) h
  qw w hw := by simp [hq] at hw
  q w hw := by simp [hq] at hw
  swset u h := by rw [hout u] at h; cases h
  wx u h := by rw [hout u] at h; rcases h with h | h <;> cases h
  wby j hj hv := by
    obtain rfl : j = 0 := by omega
    exact absurd (Except.ok.inj (Option.some.inj (hW0.symm.trans hv))) (by decide)
  sx u h := by rw [hout u] at h; cases h

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

/-- **The event as a primitive next to the lock `L`** (`FPrim.ofWords`; a protocol keeps it:
`L.Fits (E.prim L) P U ok`). Its word is `W`; the roles are `wx` (`true`) and `sx` (`false`); no
place is calm (`ok` may read every place). A step of its code is an `MStep` with the new place `p`
of the stepping thread, out of the lock's code or `away`, and its lock place `q`: only a waiter at
`w1` goes `away`, while it sleeps; it holds no lock resource. A thread steps on its own part (the
stack blocks of the event's code: `wp_liftPart`) out of the lock's code. -/
abbrev prim (L : FLock γ) : FPrim γ :=
  FPrim.ofWords L E.toFPlace .out (fun _ => False) (fun b g => cond b (E.wx g) (E.sx g))
    (· = E.W) (E.Inv L)
    (fun _ t g p q h m m' => (L.ph g = .out ∨ L.ph g = .away) ∧
      (q = .out ∨ (q = .away ∧ p = .w1)) ∧ h = rnil ∧ E.MStep t m m')
    (· = .out)

variable {E}

/-! ## A step of the event's code, as the memory sees it

From the facts of an op at the word (`Word.Op.block`, `Word.Op.word`, …): the threads stay, the
clocks grow, only the word's bytes change, a new access is at the word, each block stays as live,
as large and of the same kind, a lock's word apart from the event's keeps its location, a new
waiter is the stepping thread at the word, and a word at the event's or apart from it stays valid,
with a new write only at the event's word. -/

namespace MStep

variable {t : ThreadId} {m m' : Mem}

theorem threads (hs : E.MStep t m m') : m'.threads = m.threads := by
  cases hs with
  | op hop => exact hop.threads
  | sleep hop => exact hop.threads
  | wake c cs h => rw [Proto.modify_ok h]
  | _ => rfl

theorem clocks (hs : E.MStep t m m') (u : Nat) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  cases hs with
  | op hop => exact hop.clocks u
  | sleep hop => exact hop.clocks u
  | wake c cs h => rw [Proto.modify_ok h]; exact VClock.le_refl _
  | _ => exact VClock.le_refl _

theorem cells (hs : E.MStep t m m') {l : Zig.Loc} (hl : ¬ E.W.In l) : m'.heap l = m.heap l := by
  cases hs with
  | op hop => exact hop.cells l hl
  | @sleep M _ _ _ hbl => show M.heap l = m.heap l; unfold Mem.heap; rw [hbl]
  | wake c cs h => rw [Proto.modify_ok h]; rfl
  | _ => rfl

theorem fp (hs : E.MStep t m m') {e : FootprintEntry} (he : e ∈ m'.footprint) :
    e ∈ m.footprint ∨ (e.block = E.W.b ∧ e.off = E.W.o) := by
  cases hs with
  | op hop => exact hop.of_cur.fpAt e he
  | sleep hop => exact hop.of_cur.fpAt e he
  | wake c cs h => rw [Proto.modify_ok h] at he; exact .inl he
  | _ => exact .inl he

theorem block (hs : E.MStep t m m') {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  cases hs with
  | op hop => exact hop.of_cur.block hb
  | @sleep M _ _ _ hbl => exact ⟨blk, by show M.blocks[b]? = _; rw [hbl]; exact hb, rfl, rfl, rfl⟩
  | wake c cs h => rw [Proto.modify_ok h]; exact ⟨blk, hb, rfl, rfl, rfl⟩
  | _ => exact ⟨blk, hb, rfl, rfl, rfl⟩

theorem lockLoc (hs : E.MStep t m m') {L : LockWord} (hap : E.W.ApartL L) {i : Nat} {l : ALoc}
    (hl : L.Loc m i l) : L.Loc m' i l := by
  cases hs with
  | op hop => exact hop.of_cur.lockLoc hap hl
  | sleep hop => exact hop.of_cur.lockLoc hap hl
  | wake c cs h => rw [Proto.modify_ok h]; exact hl
  | _ => exact hl

theorem waiters (hs : E.MStep t m m') {w : ThreadId × Ptr} (hw : w ∈ m'.waiters) :
    w ∈ m.waiters ∨ w = (t, E.W.ptr) := by
  cases hs with
  | op hop => exact .inl (hop.of_cur.waiters ▸ hw)
  | sleep hop =>
    rcases Array.mem_push.mp hw with h | h
    · exact .inl (hop.of_cur.waiters ▸ h)
    · exact .inr h
  | wake c cs h => rw [Proto.modify_ok h] at hw; exact .inl (Array.mem_filter.mp hw).1
  | _ => exact .inl hw

theorem word {W' : Word 32 4} (hs : E.MStep t m m') (hok : W'.Ok m)
    (hap : W' = E.W ∨ E.W.b ≠ W'.b ∨ E.W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ E.W.o) :
    W'.Ok m' ∧ (W'.hist m' = W'.hist m ∨ (W' = E.W ∧ ∃ x, W'.hist m' = (W'.hist m).push x)) := by
  have hk : ∀ {m₁ : Mem}, m₁.blocks = m.blocks → m₁.atomics = m.atomics →
      m₁.footprint = m.footprint → m₁.threads = m.threads → m₁.clocks = m.clocks →
      W'.Ok m₁ ∧ (W'.hist m₁ = W'.hist m ∨ (W' = E.W ∧ ∃ x, W'.hist m₁ = (W'.hist m).push x)) :=
    fun hb ha hf ht hc => by
      have := Word.keep_of (W := W') hb ha hf ht fun u => by rw [hc]; exact VClock.le_refl _
      exact ⟨hok.keep this, .inl (Word.hist_keep hok this)⟩
  cases hs with
  | same => exact hk rfl rfl rfl rfl rfl
  | op hop hw hh =>
    rcases hap with rfl | hap
    · exact ⟨hw, hh.imp id fun ⟨_, _, h⟩ => ⟨rfl, _, h⟩⟩
    · exact (hop.of_cur.word hok hap).imp_right .inl
  | @sleep M hop hh hw _ =>
    have hM : W'.Ok M ∧ W'.hist M = W'.hist m := by
      rcases hap with rfl | hap
      · exact ⟨hw, hh⟩
      · exact hop.of_cur.word hok hap
    exact ⟨hM.1.keep (Word.keep_waiters _ _),
      .inl ((Word.hist_keep hM.1 (Word.keep_waiters _ _)).trans hM.2)⟩
  | woken => exact hk rfl rfl rfl rfl rfl
  | resume => exact hk rfl rfl rfl rfl rfl
  | wake c cs h => rw [Proto.modify_ok h]; exact hk rfl rfl rfl rfl rfl

end MStep

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

/-- A change of `t`'s ghost value that keeps whether it may wait. -/
theorem wx_of {G G' : ThreadId → γ} {t : ThreadId} (hG : ∀ u, u ≠ t → G' u = G u)
    (h : E.wx (G t) → E.wx (G' t)) {u : ThreadId} (hu : E.wx (G u)) : E.wx (G' u) := by
  by_cases e : u = t
  · subst e; exact h hu
  · rw [hG u e]; exact hu

/-- `t` at a new place of the event's code may wait as before. -/
theorem wx_upd_set {G : ThreadId → γ} {t : ThreadId} {g : γ} {p : EPh} (hg : G t = g) :
    E.wx (G t) → E.wx (upd G t (E.set g p) t) := fun h => by
  rw [upd_self, E.wx_set, ← hg]; exact h

/-- `t` at a new place of the event's code may set as before. -/
theorem sx_upd_set {G : ThreadId → γ} {t : ThreadId} {g : γ} {p : EPh} (hg : G t = g) :
    E.sx (G t) → E.sx (upd G t (E.set g p) t) := fun h => by
  rw [upd_self, E.sx_set, ← hg]; exact h

/-- `wby` after a step that keeps the writes and moves the clocks forward. -/
theorem Inv.wby_of {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} (hI : E.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u) (h : E.wx (G t) → E.wx (G' t))
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    {j : Nat} (hj : j < (E.W.hist m).size) (hv : (E.W.hist m)[j]!.Val (1 : BitVec 32)) :
    ∃ u, E.wx (G' u) ∧ VClock.le (E.W.hist m)[j]!.clock (m'.clocks[u]!) = true :=
  let ⟨u, hu, hc⟩ := hI.wby j hj hv
  ⟨u, wx_of hG h hu, VClock.le_trans hc (hclk u)⟩

/-- Thread `t` enters the wait (`out` → `w0`), when no other thread is a waiter and every
`waiting` write happened before it (module doc, scope). -/
theorem Inv.enter {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ}
    (hI : E.Inv L (upd G t g) m) (hg : E.ph g = .out) (hgo : L.ph (E.set g .w0) = .out)
    (hwx : E.wx g) (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true) :
    E.Inv L (upd G t (E.set g .w0)) m := by
  have hnw : ∀ u, u ≠ t → ¬ (E.ph (upd G t (E.set g .w0) u)).Waiting := fun u hu hw => by
    rw [upd_ne _ _ hu] at hw
    rcases hone u hu with h | h <;> rw [h] at hw <;> rcases hw with h | h <;> cases h
  have hph : E.ph (upd G t (E.set g .w0) t) = .w0 := by rw [upd_self, E.ph_set]
  have hG : ∀ u, u ≠ t → upd G t (E.set g .w0) u = upd G t g u := fun u hu => by
    rw [upd_ne _ _ hu, upd_ne _ _ hu]
  have hwt : E.wx (upd G t g t) → E.wx (upd G t (E.set g .w0) t) := fun _ => by
    rw [upd_self]; exact (E.wx_set _ _).mpr hwx
  refine ⟨hI.vals, hI.mono, fun u v hu hv => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_,
    fun w hw hp => ?_, fun w hw hp => ?_, fun u hu => ?_,
    fun u hu => if e : u = t then by subst e; exact hwt (by rw [upd_self]; exact hwx)
      else absurd hu (hnw u e),
    fun j hj hv => hI.wby_of hG hwt (fun _ => VClock.le_refl _) hj hv,
    fun u hu => if e : u = t then by subst e; rw [hph] at hu; cases hu
      else by rw [hG u e] at hu ⊢; exact hI.sx u hu⟩
  rotate_right
  · by_cases eu : u = t
    · subst eu; rw [hph] at hu; cases hu
    · rw [upd_ne _ _ eu] at hu; exact hI.swset u (by rw [upd_ne _ _ eu]; exact hu)
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
    (hsw : E.ph (G t) = .sw ↔ E.ph (G' t) = .sw)
    (hlpt : E.ph (G' t) ≠ .out →
      L.ph (G' t) = .out ∨ (E.ph (G' t) = .w1 ∧ L.ph (G' t) = .away))
    (htq : ∀ w ∈ m.waiters, w.1 = t →
      (E.ph (G' t) = .w1 → w.2 = E.W.ptr ∨ w.2 = L.ptr) ∧ (w.2 = E.W.ptr → E.ph (G' t) = .w1))
    (hwxt : E.wx (G t) → E.wx (G' t)) (hsxt : E.sx (G t) → E.sx (G' t)) :
    E.Inv L G' m' := by
  have key : ∀ x, (E.ph (G' x)).Waiting → (E.ph (G x)).Waiting := fun x hx => by
    by_cases e : x = t
    · subst e; exact hone hx
    · rwa [hG x e] at hx
  refine ⟨by rw [hh]; exact hI.vals, by rw [hh]; exact hI.mono,
    fun u v hu hv => hI.one u v (key u hu) (key v hv), fun u hu j hj hv => ?_, fun u hu => ?_,
    fun u hu => ?_, fun w hw hp => ?_, fun w hw hp => ?_, fun u hu => ?_,
    fun u hu => wx_of hG hwxt (hI.wx u (key u hu)),
    fun j hj hv => by rw [hh] at hj hv ⊢; exact hI.wby_of hG hwxt hclk hj hv,
    fun u hu => if e : u = t then by subst e; exact hsxt (hI.sx u (hsw.mpr hu))
      else by rw [hG u e] at hu ⊢; exact hI.sx u hu⟩
  rotate_right
  · unfold FEvent.newest; rw [hh]
    by_cases e : u = t
    · subst e; exact hI.swset u (hsw.mpr hu)
    · rw [hG u e] at hu; exact hI.swset u hu
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
        · subst e; exact hsw.mp hu
        · rw [hG u e]; exact hu

/-- The waiter's successful `cmpxchg(unset → waiting)` (`w0` → `w1`). -/
theorem Inv.casOk {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    (hI : E.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u) (ht0 : E.ph (G t) = .w0)
    (ht1 : E.ph (G' t) = .w1) (hlpt : L.ph (G' t) = .out)
    (hv0 : (E.newest m).Val (0 : BitVec 32))
    (hh : E.W.hist m' = (E.W.hist m).push (Word.rmwEnt m' t ord (E.newest m) (1 : BitVec 32)))
    (hwt : m'.waiters = m.waiters) (hnq : ∀ w ∈ m.waiters, w.1 ≠ t)
    (hpos : 0 < (E.W.hist m).size)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hwxt : E.wx (G t) → E.wx (G' t)) :
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
  have hwx : E.wx (G' t) := hwxt (hI.wx t (.inl ht0))
  refine ⟨fun j hj => ?_, fun i j a b hij hj ha hb => ?_, fun u v hu hv => ?_,
    fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw hp => ?_, fun w hw hp => ?_,
    fun u hu => ?_,
    fun u hu => if e : u = t then e ▸ hwx else absurd hu (key u e),
    fun j hj hv => ?_,
    fun u hu => if e : u = t then by subst e; rw [ht1] at hu; cases hu
      else by rw [hG u e] at hu ⊢; exact hI.sx u hu⟩
  rotate_right
  · -- the `waiting` writes: the new one is `t`'s
    rw [hsz] at hj
    rcases (by omega : j < (E.W.hist m).size ∨ j = (E.W.hist m).size) with hj' | rfl
    · rw [hold j hj'] at hv ⊢; exact hI.wby_of hG hwxt hclk hj' hv
    · refine ⟨t, hwx, ?_⟩
      rw [hh, get_push_eq]; exact VClock.le_refl _
  rotate_right
  · -- no setter at `sw`: the newest write was `unset`
    exfalso
    have eu : u ≠ t := fun e => by rw [e, ht1] at hu; cases hu
    rw [hG u eu] at hu
    have := val_eq hv0 (hI.swset u hu); cases this
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
    (hnq : ∀ w ∈ m.waiters, w.1 ≠ t) (hwxt : E.wx (G t) → E.wx (G' t))
    (hsx : E.ph (G' t) = .sw → E.sx (G' t)) :
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
    fun u hu j hj hv => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw hp => ?_, fun w hw hp => ?_,
    fun _ _ => ?_, fun u hu => wx_of hG hwxt (hI.wx u (key u hu).1), fun j hj hv => ?_,
    fun u hu => if e : u = t then by subst e; exact hsx hu
      else by rw [hG u e] at hu ⊢; exact hI.sx u hu⟩
  rotate_right
  · rw [hsz] at hj
    rcases (by omega : j < (E.W.hist m).size ∨ j = (E.W.hist m).size) with hj' | rfl
    · rw [hold j hj'] at hv ⊢; exact hI.wby_of hG hwxt hclk hj' hv
    · have := val_eq hv hnew; cases this
  rotate_right
  · unfold FEvent.newest; rw [hsz, Nat.add_sub_cancel]; exact hnew
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
    fun u hu j hj hv => ?_, fun u hu => ?_, hI.lp, fun w hw hp => ?_, fun w hw hp => ?_,
    fun u hu => by unfold FEvent.newest; rw [hh']; exact hI.swset u hu, hI.wx,
    fun j hj hv => by rw [hh'] at hj hv ⊢; exact hI.wby_of (t := t) (fun _ _ => rfl) id hclk hj hv,
    hI.sx⟩
  · rw [hh'] at hj hv ⊢; exact VClock.le_trans (hI.hb u hu j hj hv) (hclk u)
  · rw [hh']
    obtain ⟨i, hi, hv, hc⟩ := hI.seen u hu
    exact ⟨i, hi, hv, VClock.le_trans hc (hclk u)⟩
  · rcases Array.mem_push.mp hw with hw | rfl
    · rw [hwt] at hw; exact hI.qw w hw hp
    · exact .inl rfl
  · unfold FEvent.newest; rw [hh']
    rcases Array.mem_push.mp hw with hw | rfl
    · rw [hwt] at hw; exact hI.q w hw hp
    · exact ⟨ht, .inl hv⟩

/-- The setter's wake of every waiter at the word (`sw` → `out`; one waiter at a time, so the
wake of at least one waiter empties the queue at the word). -/
theorem Inv.wake {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g : γ} {c : Nat}
    {cs : List Nat} (hI : E.Inv L G m) (ht : E.ph (G t) = .sw) (hg : E.ph g = .out)
    (hc : 1 ≤ c) (hwxg : E.wx (G t) → E.wx g)
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
    fun w hw hp => ?_, fun u hu => ?_,
    fun u hu => by have := hnw u hu; rw [upd_ne _ _ this.2]; exact hI.wx u this.1,
    fun j hj hv => hI.wby_of (fun u hu => upd_ne _ _ hu) (by rw [upd_self]; exact hwxg)
      (fun _ => VClock.le_refl _) hj hv,
    fun u hu => if e : u = t then by subst e; rw [upd_self, hg] at hu; cases hu
      else by rw [upd_ne _ _ e] at hu ⊢; exact hI.sx u hu⟩
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
  · by_cases e : u = t
    · subst e; rw [upd_self, hg] at hu; cases hu
    · rw [upd_ne _ _ e] at hu; exact hI.swset u hu

/-- A change of `t`'s ghost value that keeps its place in the event's code. -/
theorem Inv.relabel {G G' : ThreadId → γ} {m : Mem} {t : ThreadId} (hI : E.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u) (hph : E.ph (G' t) = E.ph (G t))
    (hlpt : E.ph (G' t) ≠ .out →
      L.ph (G' t) = .out ∨ (E.ph (G' t) = .w1 ∧ L.ph (G' t) = .away))
    (hwxt : E.wx (G t) → E.wx (G' t)) (hsxt : E.sx (G t) → E.sx (G' t)) :
    E.Inv L G' m :=
  hI.move hG rfl rfl (fun _ => VClock.le_refl _) (by rw [hph]; exact id)
    (by rw [hph]; exact id) (fun h => hI.seen t (by rw [← hph]; exact h)) (by rw [hph])
    hlpt (fun w hw e => ⟨fun h => hI.qw w hw (by rw [e, ← hph]; exact h),
      fun h => by rw [hph, ← e]; exact (hI.q w hw h).1⟩) hwxt hsxt

/-- A step that keeps the writes and the futex queue and only moves the clocks forward (a step of
a thread on its own part), with a change of `t`'s ghost value that keeps its places. -/
theorem Inv.frame {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} (hI : E.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u) (hph : E.ph (G' t) = E.ph (G t))
    (hlph : L.ph (G' t) = L.ph (G t)) (hh : E.W.hist m' = E.W.hist m)
    (hwt : m'.waiters = m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hwxt : E.wx (G t) → E.wx (G' t)) (hsxt : E.sx (G t) → E.sx (G' t)) :
    E.Inv L G' m' :=
  hI.move hG hh hwt hclk (by rw [hph]; exact id) (by rw [hph]; exact id)
    (fun h => let ⟨i, hi, hv, hc⟩ := hI.seen t (by rw [← hph]; exact h)
      ⟨i, hi, hv, VClock.le_trans hc (hclk t)⟩) (by rw [hph])
    (fun h => by rw [hph] at h ⊢; rw [hlph]; exact hI.lp t h)
    (fun w hw e => ⟨fun h => hI.qw w hw (by rw [e, ← hph]; exact h),
      fun h => by rw [hph, ← e]; exact (hI.q w hw h).1⟩) hwxt hsxt

/-- **A step of another component of the protocol** (a condition's code) by `t`, which keeps
`t`'s place in the event and the word's writes: `t` keeps its lock place or goes `out` of the
lock, and a new waiter in the futex queue is `t` at another word, not as the event's waiter. -/
theorem Inv.other {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} (hI : E.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u) (hph : E.ph (G' t) = E.ph (G t))
    (hlpt : E.ph (G t) ≠ .out → L.ph (G' t) = L.ph (G t) ∨ L.ph (G' t) = .out)
    (hh : E.W.hist m' = E.W.hist m)
    (hwt : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ (w.1 = t ∧ w.2 ≠ E.W.ptr ∧ E.ph (G t) ≠ .w1))
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hwxt : E.wx (G t) → E.wx (G' t)) (hsxt : E.sx (G t) → E.sx (G' t)) :
    E.Inv L G' m' := by
  have hp : ∀ u, E.ph (G' u) = E.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; exact hph
    · rw [hG u e]
  refine ⟨by rw [hh]; exact hI.vals, by rw [hh]; exact hI.mono,
    fun u v hu hv => hI.one u v (by rw [← hp]; exact hu) (by rw [← hp]; exact hv),
    fun u hu j hj hv => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw hq => ?_, fun w hw hq => ?_,
    fun u hu => ?_, fun u hu => wx_of hG hwxt (hI.wx u (by rw [← hp]; exact hu)),
    fun j hj hv => by rw [hh] at hj hv ⊢; exact hI.wby_of hG hwxt hclk hj hv,
    fun u hu => ?_⟩
  · rw [hp] at hu; rw [hh] at hj hv ⊢; exact VClock.le_trans (hI.hb u hu j hj hv) (hclk u)
  · rw [hp] at hu; rw [hh]
    obtain ⟨i, hi, hv, hc⟩ := hI.seen u hu
    exact ⟨i, hi, hv, VClock.le_trans hc (hclk u)⟩
  · rw [hp] at hu
    by_cases e : u = t
    · subst e
      rcases hI.lp u hu with h | ⟨h1, h2⟩
      · rcases hlpt hu with h' | h'
        · exact .inl (h'.trans h)
        · exact .inl h'
      · rcases hlpt hu with h' | h'
        · exact .inr ⟨by rw [hph]; exact h1, h'.trans h2⟩
        · exact .inl h'
    · rw [hG u e] at ⊢; exact hI.lp u hu
  · rw [hp] at hq
    rcases hwt w hw with h | ⟨e, -, hn⟩
    · exact hI.qw w h hq
    · rw [e] at hq; exact absurd hq hn
  · rcases hwt w hw with h | ⟨-, hn, -⟩
    · obtain ⟨h1, h2⟩ := hI.q w h hq
      refine ⟨by rw [hp]; exact h1, ?_⟩
      unfold FEvent.newest; rw [hh]
      rcases h2 with h2 | ⟨v, hv⟩
      · exact .inl h2
      · exact .inr ⟨v, by rw [hp]; exact hv⟩
    · exact absurd hq hn
  · rw [hp] at hu; unfold FEvent.newest; rw [hh]; exact hI.swset u hu
  · rw [hp] at hu
    by_cases e : u = t
    · subst e; exact hsxt (hI.sx u hu)
    · rw [hG u e]; exact hI.sx u hu

/-- **A lock step of a thread out of the event's code** keeps the event's invariant: the word's
writes and the futex queue at it stay (for a client's `FLock.Fits.stable`, whose `ok` excludes
the threads in the event's code; module doc). -/
theorem Inv.lstep {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {p : LPh} {h : Res}
    (hI : E.Inv L G m) (hw : E.W.Ok m) (hap : E.W.ApartL L.toLockWord)
    (hout : E.ph (G t) = .out) (hph : ∀ g q h, E.ph (L.set g q h) = E.ph g)
    (hwx : ∀ g q h, E.wx (L.set g q h) ↔ E.wx g) (hsx : ∀ g q h, E.sx (L.set g q h) ↔ E.sx g)
    (hs : L.Step t m m') :
    E.Inv L (upd G t (L.set (G t) p h)) m' := by
  have hh : E.W.hist m' = E.W.hist m := Word.hist_keep hw (Word.keep_lockWordStep hs hap)
  have hp : ∀ u, E.ph (upd G t (L.set (G t) p h) u) = E.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hph]
    · rw [upd_ne _ _ e]
  have hx : ∀ u, E.wx (upd G t (L.set (G t) p h) u) ↔ E.wx (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hwx]
    · rw [upd_ne _ _ e]
  have hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    by_cases e : u = t
    · subst e; exact hs.mine
    · rw [hs.others u e]; exact VClock.le_refl _
  have hwq : ∀ w ∈ m'.waiters, w.2 ≠ L.ptr → w ∈ m.waiters := fun w hw' hl =>
    (hs.waiters w hl).mp hw'
  refine ⟨by rw [hh]; exact hI.vals, by rw [hh]; exact hI.mono,
    fun u v hu hv => hI.one u v (by rw [← hp]; exact hu) (by rw [← hp]; exact hv),
    fun u hu j hj hv => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw' hq => ?_,
    fun w hw' hq => ?_, fun u hu => ?_, fun u hu => (hx u).mpr (hI.wx u (by rw [← hp]; exact hu)),
    fun j hj hv => ?_, fun u hu => ?_⟩
  rotate_right
  · rw [hp] at hu
    by_cases e : u = t
    · subst e; rw [upd_self, hsx]; exact hI.sx u hu
    · rw [upd_ne _ _ e]; exact hI.sx u hu
  · rw [hp] at hu; rw [hh] at hj hv ⊢; exact VClock.le_trans (hI.hb u hu j hj hv) (hclk u)
  · rw [hp] at hu; rw [hh]
    obtain ⟨i, hi, hv, hc⟩ := hI.seen u hu
    exact ⟨i, hi, hv, VClock.le_trans hc (hclk u)⟩
  · have e : u ≠ t := fun e => by rw [e, hp, hout] at hu; exact hu rfl
    rw [upd_ne _ _ e] at hu ⊢; exact hI.lp u hu
  · rw [hp] at hq
    by_cases hl : w.2 = L.ptr
    · exact .inr hl
    · exact hI.qw w (hwq w hw' hl) hq
  · obtain ⟨h1, h2⟩ := hI.q w (hwq w hw' (by rw [hq]; exact hap.ptr_ne)) hq
    refine ⟨by rw [hp]; exact h1, ?_⟩
    unfold FEvent.newest; rw [hh]
    rcases h2 with h2 | ⟨v, hv⟩
    · exact .inl h2
    · exact .inr ⟨v, by rw [hp]; exact hv⟩
  · rw [hp] at hu; unfold FEvent.newest; rw [hh]; exact hI.swset u hu
  · rw [hh] at hj hv ⊢
    obtain ⟨u, hu, hc⟩ := hI.wby j hj hv
    exact ⟨u, (hx u).mpr hu, VClock.le_trans hc (hclk u)⟩

/-- `g` at the place it has. -/
theorem set_of {g : γ} {p : EPh} (h : E.ph g = p) : E.set g p = g := h ▸ E.set_self g

theorem cur_eq {m : Mem} {t : ThreadId} (h : m.current = t) : { m with current := t } = m := by
  subst h; rfl

/-! ## The protocol after a step

The lemmas about a protocol that keeps the event (`L.Fits (E.prim L) P U ok`) are in the namespace
`FLock.Fits`, next to the generic ones of `FPrim.ofWords` (`Fits.back`, `Fits.atOp`,
`ZigLean/Sep/Full/WordRules.lean`). -/

variable {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- A sleeping waiter of a set event is not in a deadlock: a setter at `sw` runs. -/
theorem _root_.Zig.Full.FLock.Fits.liveSet (hE : L.Fits (E.prim L) P U ok) {G : ThreadId → γ} {rX : Res}
    {m : Mem} {t : ThreadId} (hI : E.Inv L G m) (hL : L.Inv G rX m) (ht : E.ph (G t) = .w1)
    (hs : E.IsSet m) : P.Live t G m := by
  intro hin hall
  obtain ⟨w, hw, he⟩ := Array.any_eq_true'.mp hin
  have e : w.1 = t := by simpa using he
  have hp : w.2 = E.W.ptr := by
    rcases hI.qw w hw (by rw [e]; exact ht) with h | h
    · exact h
    · exact absurd (Array.any_eq_true'.mpr ⟨w, hw, by simp [h]⟩) (hE.noWaits hL hall)
  rcases (hI.q w hw hp).2 with h1 | ⟨u, hu⟩
  · have := val_eq h1 hs; cases this
  · have hlo : L.ph (G u) = .out := by
      rcases hI.lp u (by rw [hu]; decide) with h | ⟨h, -⟩
      · exact h
      · rw [hu] at h; cases h
    have hut := (hL.ht (t := u) (by rw [hlo]; decide)).1
    rcases hall u hut with h | h | h
    · rw [hE.kfin _ h] at hu; cases hu
    · have := hL.w.notQ (t := u) (show L.ph (G u) ≠ .wait by rw [hlo]; decide)
        (show L.ph (G u) ≠ .away by rw [hlo]; decide)
      rw [this] at h; cases h
    · rw [hE.kjoins _ h] at hu; cases hu

/-- After a step of the event's code by `t` at `out` of the lock (`g`, new place `p`): the
protocol's invariant, from the lock's invariant after the step, the rest before it, and the
event's invariant after it. -/
theorem _root_.Zig.Full.FLock.Fits.backOut (hE : L.Fits (E.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {p : EPh} (hg₁ : G₁ t = g)
    (hgo : L.ph g = .out) (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁)
    (hY : ∀ l, E.W.In l → rY.heap l = none) (hs : E.MStep t m₁ m')
    (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m') (hI : E.Inv L (upd G₁ t (E.set g p)) m') :
    P.inv (upd G₁ t (E.set g p)) m' :=
  hE.back rfl hg₁ ⟨.inl hgo, .inl hgo, hg₁ ▸ hL.idle t (by rw [hg₁, hgo]; decide), hs⟩ hU hY hL hI

/-- The facts at a stop of `t` (at `out` of the lock) before an op at the word: the event's
invariant, `t` is not in the futex queue, the word is `Ok`. -/
theorem _root_.Zig.Full.FLock.Fits.atWord (hE : L.Fits (E.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} (hgo : L.ph (G₁ t) = .out)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hop : E.W.Op t m₁ m')
    (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m') :
    E.Inv L G₁ m₁ ∧ (∀ w ∈ m₁.waiters, w.1 ≠ t) ∧ E.W.Ok m₁ :=
  let ⟨hI, hnq⟩ := hE.atOp hU (by rw [hgo]; decide) (by rw [hgo]; decide) hop hL
  ⟨hI, hnq, ((hE.wRest rfl) _ _ _ hU).1⟩

/-- A waiter's read at the word (`w0` or `w1`) of write `j` with the value `b`: `unset` (only
at `w0`: it stays), `waiting` (it goes to `w1`), or `is_set` (it leaves; the event is set). -/
theorem _root_.Zig.Full.FLock.Fits.afterRead (hE : L.Fits (E.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} (hg₁ : G₁ t = g) (hgw : (E.ph g).Waiting)
    (hgo : L.ph g = .out) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hop : E.W.Op t m₁ m') (hw' : E.W.Ok m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hh : E.W.hist m' = E.W.hist m₁) {j : Nat} {b : BitVec 32} (hj : j < (E.W.hist m₁).size)
    (hv : (E.W.hist m₁)[j]!.Val b) (hfl : Word.Floor (E.W.hist m₁) (m₁.clocks[t]!) j) :
    (b = 0 ∧ E.ph g = .w0 ∧ P.inv (upd G₁ t (E.set g .w0)) m') ∨
    (b = 1 ∧ P.inv (upd G₁ t (E.set g .w1)) m') ∨
    (b = 2 ∧ E.IsSet m' ∧ P.inv (upd G₁ t (E.set g .out)) m') := by
  obtain ⟨hI, hnq, -⟩ := hE.atWord (by rw [hg₁]; exact hgo) hU hop hL
  have hs : E.MStep t m₁ m' := .op (by rw [cur_eq hc₁]; exact hop) hw' (.inl hh)
  have hclk := hop.clocks
  have hlo : ∀ p, L.ph (upd G₁ t (E.set g p) t) = .out := fun p => by
    rw [upd_self, hE.lph]; exact hgo
  have hgt : E.ph (G₁ t) = E.ph g := by rw [hg₁]
  -- the new invariant at place `p`
  have hmv : ∀ p, p ≠ .sw → ((E.ph (E.set g p)).Waiting → (E.ph g).Waiting) →
      (p = .w0 → E.ph g = .w0) →
      (p = .w1 → ∃ i < (E.W.hist m₁).size, (E.W.hist m₁)[i]!.Val (1 : BitVec 32) ∧
        VClock.le (E.W.hist m₁)[i]!.clock (m'.clocks[t]!) = true) →
      E.Inv L (upd G₁ t (E.set g p)) m' := fun p hps h1 h2 h3 =>
    hI.move (fun u hu => upd_ne _ _ hu) hh hop.waiters hclk
      (by rw [upd_self, hgt]; exact h1) (by rw [upd_self, hgt, E.ph_set]; exact h2)
      (by rw [upd_self, E.ph_set]; exact h3)
      (by
        rw [hgt, upd_self, E.ph_set]
        refine ⟨fun h => ?_, fun h => absurd h hps⟩
        rcases hgw with e | e <;> rw [e] at h <;> cases h)
      (fun _ => .inl (hlo p)) (fun w hw e => absurd e (hnq w hw)) (wx_upd_set hg₁)
      (sx_upd_set hg₁)
  rcases hI.val3 hj hv with rfl | rfl | rfl
  · -- `unset`: only at `w0`
    have hw0 : E.ph g = .w0 := by
      rcases hgw with e | e
      · exact e
      · obtain ⟨i, hi, hv1, hc⟩ := hI.seen t (by rw [hgt]; exact e)
        have := hI.read_ge hi hv1 hc hfl hj hv
        simp at this
    refine .inl ⟨rfl, hw0, hE.backOut hg₁ hgo hU hY hs hL
      (hmv .w0 (by decide) (fun _ => hgw) (fun _ => hw0) (fun h => by cases h))⟩
  · refine .inr (.inl ⟨rfl, hE.backOut hg₁ hgo hU hY hs hL
      (hmv .w1 (by decide) (fun _ => hgw) (fun h => by cases h) fun _ => ?_)⟩)
    rcases hgw with e | e
    · exact ⟨j, hj, hv, VClock.le_trans (hI.hb t (by rw [hgt]; exact e) j hj hv) (hclk t)⟩
    · obtain ⟨i, hi, hv1, hc⟩ := hI.seen t (by rw [hgt]; exact e)
      exact ⟨i, hi, hv1, VClock.le_trans hc (hclk t)⟩
  · have hset : E.IsSet m' := by
      have := hI.isSet_of hj hv
      unfold FEvent.IsSet FEvent.newest at this ⊢; rw [hh]; exact this
    refine .inr (.inr ⟨rfl, hset, hE.backOut hg₁ hgo hU hY hs hL
      (hmv .out (by decide) (by rw [E.ph_set]; intro h; rcases h with h | h <;> cases h)
        (fun h => by cases h) (fun h => by cases h))⟩)

/-- A read at the word by a thread out of the event's code (`g`): it stays; a read of `is_set`
means the event is set. -/
theorem _root_.Zig.Full.FLock.Fits.afterPeek (hE : L.Fits (E.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} (hg₁ : G₁ t = g) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hop : E.W.Op t m₁ m') (hw' : E.W.Ok m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hh : E.W.hist m' = E.W.hist m₁) {j : Nat} {b : BitVec 32} (hj : j < (E.W.hist m₁).size)
    (hv : (E.W.hist m₁)[j]!.Val b) :
    P.inv (upd G₁ t g) m' ∧ (b = 2 → E.IsSet m') := by
  obtain ⟨hI, hnq, -⟩ := hE.atWord (by rw [hg₁]; exact hgo) hU hop hL
  have hs : E.MStep t m₁ m' := .op (by rw [cur_eq hc₁]; exact hop) hw' (.inl hh)
  have hgt : E.ph (G₁ t) = .out := by rw [hg₁]; exact hgx
  have hI' : E.Inv L (upd G₁ t (E.set g .out)) m' :=
    hI.move (fun u hu => upd_ne _ _ hu) hh hop.waiters hop.clocks
      (by rw [upd_self, E.ph_set, hgt]; exact id) (by rw [upd_self, E.ph_set]; intro h; cases h)
      (by rw [upd_self, E.ph_set]; intro h; cases h) (by rw [hgt, upd_self, E.ph_set])
      (by rw [upd_self, E.ph_set]; intro h; exact absurd rfl h) (fun w hw e => absurd e (hnq w hw))
      (wx_upd_set hg₁) (sx_upd_set hg₁)
  have := hE.backOut hg₁ hgo hU hY hs hL hI'
  rw [set_of hgx] at this
  refine ⟨this, fun hb => ?_⟩
  subst hb
  have := hI.isSet_of hj hv
  unfold FEvent.IsSet FEvent.newest at this ⊢; rw [hh]; exact this

/-- The waiter's successful `cmpxchg(unset → waiting)`: it goes to `w1`. -/
theorem _root_.Zig.Full.FLock.Fits.afterCasOk (hE : L.Fits (E.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {ord : AtomicOrder} (hg₁ : G₁ t = g)
    (hg : E.ph g = .w0) (hgo : L.ph g = .out) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hop : E.W.Op t m₁ m') (hw' : E.W.Ok m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hv : (E.newest m₁).Val (0 : BitVec 32))
    (hh : E.W.hist m' = (E.W.hist m₁).push (Word.rmwEnt m' t ord (E.newest m₁) (1 : BitVec 32))) :
    P.inv (upd G₁ t (E.set g .w1)) m' := by
  obtain ⟨hI, hnq, hw₁⟩ := hE.atWord (by rw [hg₁]; exact hgo) hU hop hL
  refine hE.backOut hg₁ hgo hU hY (.op (by rw [cur_eq hc₁]; exact hop) hw' (.inr ⟨ord, 1, hh⟩))
    hL (hI.casOk (fun u hu => upd_ne _ _ hu) (by rw [hg₁]; exact hg)
      (by rw [upd_self, E.ph_set]) (by rw [upd_self, hE.lph]; exact hgo) hv hh hop.waiters hnq
      (hist_pos hw₁) hop.clocks (wx_upd_set hg₁))

/-- A setter's `xchg(is_set)`, by a thread out of the event's code (`g`), that read `o`: the event
is set, and the setter is at `sw` if it read `waiting` (it must wake), else out. -/
theorem _root_.Zig.Full.FLock.Fits.afterXchg (hE : L.Fits (E.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {ord : AtomicOrder} (hg₁ : G₁ t = g)
    (hgx : E.ph g = .out) (hgo : L.ph g = .out) (hsx : E.sx g) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hop : E.W.Op t m₁ m') (hw' : E.W.Ok m') (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    {o : BitVec 32} (hv : (E.newest m₁).Val o)
    (hh : E.W.hist m' = (E.W.hist m₁).push (Word.rmwEnt m' t ord (E.newest m₁) (2 : BitVec 32))) :
    E.IsSet m' ∧ ((o = 1 ∧ P.inv (upd G₁ t (E.set g .sw)) m') ∨
      (o ≠ 1 ∧ P.inv (upd G₁ t (E.set g .out)) m')) := by
  obtain ⟨hI, hnq, -⟩ := hE.atWord (by rw [hg₁]; exact hgo) hU hop hL
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
      hop.clocks hnq (wx_upd_set hg₁) (fun _ => by rw [upd_self, E.sx_set]; exact hsx)
  refine ⟨hset, ?_⟩
  by_cases ho : o = 1
  · subst ho
    exact .inl ⟨rfl, hE.backOut hg₁ hgo hU hY hs hL (hx .sw (.inl rfl) fun _ => rfl)⟩
  · exact .inr ⟨ho, hE.backOut hg₁ hgo hU hY hs hL (hx .out (.inr rfl) fun h1 =>
      absurd (val_eq hv h1) ho)⟩

/-- A thread enters the wait (`out` → `w0`; module doc, scope). -/
theorem _root_.Zig.Full.FLock.Fits.enterWait (hE : L.Fits (E.prim L) P U ok) {G : ThreadId → γ}
    {m : Mem}
    {t : ThreadId} {g : γ} (hgx : E.ph g = .out) (hgo : L.ph g = .out) (hwx : E.wx g)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) : P.inv (upd G t (E.set g .w0)) m := by
  obtain ⟨rX, hL, hU⟩ := (hE.inv _ _).mp hi
  obtain ⟨-, rY, rfl, hY⟩ := (hE.wRest rfl) _ _ _ hU
  have hI := hE.wInv _ _ _ hU
  have := hE.backOut (upd_self G t g) hgo hU hY .same hL
    (by rw [upd_upd]; exact hI.enter hgx (by rw [hE.lph]; exact hgo) hwx hone hhb)
  rwa [upd_upd] at this

/-- The setter's wake at the word (`sw` → `out`), of at least one waiter. -/
theorem _root_.Zig.Full.FLock.Fits.afterWake (hE : L.Fits (E.prim L) P U ok) {G₁ : ThreadId → γ}
    {rX : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {c : Nat} {cs : List Nat} (hg₁ : G₁ t = g)
    (hg : E.ph g = .sw) (hgo : L.ph g = .out) (hc : 1 ≤ c) (hU : U G₁ rX m₁)
    (hw : ((Thread.futexWake E.W.ptr c cs).run { m₁ with current := t }).run =
      some (.ok ((), m'))) (hL : L.Inv G₁ rX m') :
    m'.current = t ∧ E.IsSet m' ∧ P.inv (upd G₁ t (E.set g .out)) m' := by
  have hm' := Proto.modify_ok hw
  obtain ⟨-, rY, rfl, hY⟩ := (hE.wRest rfl) _ _ _ hU
  have hI := hE.wInv _ _ _ hU
  have hcl : E.W.cellsR m' = E.W.cellsR m₁ := Word.cellsR_congr (by rw [hm'])
  have hh : E.W.hist m' = E.W.hist m₁ := by rw [hm']; rfl
  refine ⟨by rw [hm'], ?_, hE.backOut hg₁ hgo hU hY (.wake c cs hw) (by rw [hcl]; exact hL) ?_⟩
  · have := hI.swset t (by rw [hg₁]; exact hg)
    unfold FEvent.IsSet FEvent.newest at this ⊢; rw [hh]; exact this
  exact hI.wake (by rw [hg₁]; exact hg) (E.ph_set _ _) hc
    (fun h => (E.wx_set _ _).mpr (by rw [← hg₁]; exact h)) hw

/-! ## The ops of the event's code in generated code (`WP`) -/

variable {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ}

/-- The waiter's `cmpxchg(unset → waiting)` at `w0`, with a decode (`cmpxchgAsC`, `Io.Event`): on
success it is at `w1`; on failure it read `waiting` (`w1`) or `is_set` (out, set). -/
theorem wp_casAs {α : Type} [Packed α 32] (hE : L.Fits (E.prim L) P U ok)
    {succ fail : AtomicOrder} {exp new : α} (he : Packed.toBits exp = (0 : BitVec 32))
    (hn : Packed.toBits new = (1 : BitVec 32))
    (hdec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 2) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    (hg : E.ph g = .w0) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      (P.inv (upd G₁ t (E.set g .w1)) m' → Q (none, s) G₁ m' k) ∧
      (∀ b r, (Packed.ofBits? (α := α) b).run = some (.ok r) →
        (b = 1 ∧ P.inv (upd G₁ t (E.set g .w1)) m') ∨
        (b = 2 ∧ E.IsSet m' ∧ P.inv (upd G₁ t (E.set g .out)) m') → Q (some r, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgAsC succ fail 4 E.W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  refine FLock.wp_wordCasAs hE (hE.wRest rfl) (hE.wAp rfl) (by rw [hgo]; decide) hi
    (fun G₁ rY m₁ _ _ hU j hj b hv => hdec b ((hE.wInv _ _ _ hU).val3 hj hv))
    fun k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hop hL => ⟨fun hv _ hh _ => ?_,
      fun j b r hne hd hj hv hfl _ hh => ?_⟩
  · rw [he] at hv; rw [hn] at hh
    exact (h k hk G₁ m' hop.current).1
      (hE.afterCasOk hg₁ hg hgo hc₁ hU hY hop hw' hL hv hh)
  · rcases hE.afterRead hg₁ (.inl hg) hgo hc₁ hU hY hop hw' hL hh hj hv hfl with
      ⟨rfl, -⟩ | h1 | h1
    · exact absurd he.symm hne
    · exact (h k hk G₁ m' hop.current).2 b r hd (.inl h1)
    · exact (h k hk G₁ m' hop.current).2 b r hd (.inr h1)

/-- The waiter's `cmpxchg(unset → waiting)` at `w0` on bits (`cmpxchgC`,
`Thread.ResetEvent`). -/
theorem wp_cas (hE : L.Fits (E.prim L) P U ok) {succ fail : AtomicOrder}
    {exp new : BitVec 32} (he : exp = 0) (hn : new = 1)
    (hg : E.ph g = .w0) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      (P.inv (upd G₁ t (E.set g .w1)) m' → Q (none, s) G₁ m' k) ∧
      (∀ b, (b = 1 ∧ P.inv (upd G₁ t (E.set g .w1)) m') ∨
        (b = 2 ∧ E.IsSet m' ∧ P.inv (upd G₁ t (E.set g .out)) m') → Q (some b, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgC (n := 32) succ fail 4 E.W.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  subst he hn
  refine FLock.wp_wordCas hE (hE.wRest rfl) (hE.wAp rfl) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hop hL => ⟨fun hv _ hh _ => ?_,
      fun j b hne hj hv hfl _ hh => ?_⟩
  · exact (h k hk G₁ m' hop.current).1
      (hE.afterCasOk hg₁ hg hgo hc₁ hU hY hop hw' hL hv hh)
  · rcases hE.afterRead hg₁ (.inl hg) hgo hc₁ hU hY hop hw' hL hh hj hv hfl with
      ⟨rfl, -⟩ | h1 | h1
    · exact absurd rfl hne
    · exact (h k hk G₁ m' hop.current).2 b (.inl h1)
    · exact (h k hk G₁ m' hop.current).2 b (.inr h1)

/-- A waiter's load at the word (`w0` or `w1`; `atomicLoadC`). -/
theorem wp_load (hE : L.Fits (E.prim L) P U ok) {ord : AtomicOrder}
    (hg : (E.ph g).Waiting) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b, m'.current = t →
      (b = 0 ∧ E.ph g = .w0 ∧ P.inv (upd G₁ t (E.set g .w0)) m') ∨
      (b = 1 ∧ P.inv (upd G₁ t (E.set g .w1)) m') ∨
      (b = 2 ∧ E.IsSet m' ∧ P.inv (upd G₁ t (E.set g .out)) m') → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) ord 4 E.W.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordLoad hE (hE.wRest rfl) (hE.wAp rfl) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hY hj hv hfl _ hh hw' hop hL =>
      h k hk G₁ m' b hop.current (hE.afterRead hg₁ hg hgo hc₁ hU hY hop hw' hL hh hj hv hfl)

/-- A waiter's load at the word with a decode (`atomicLoadAsC`). -/
theorem wp_loadAs {α : Type} [Packed α 32] (hE : L.Fits (E.prim L) P U ok)
    {ord : AtomicOrder}
    (hdec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 2) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    (hg : (E.ph g).Waiting) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b r, m'.current = t →
      (Packed.ofBits? (α := α) b).run = some (.ok r) →
      (b = 0 ∧ E.ph g = .w0 ∧ P.inv (upd G₁ t (E.set g .w0)) m') ∨
      (b = 1 ∧ P.inv (upd G₁ t (E.set g .w1)) m') ∨
      (b = 2 ∧ E.IsSet m' ∧ P.inv (upd G₁ t (E.set g .out)) m') → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadAsC α ord 4 E.W.ptr : CM Tgt σ α).run s) Q G m n :=
  FLock.wp_wordLoadAs hE (hE.wRest rfl) (hE.wAp rfl) (by rw [hgo]; decide) hi
    (fun G₁ rY m₁ _ _ hU j hj b hv => hdec b ((hE.wInv _ _ _ hU).val3 hj hv))
    fun k hk G₁ rY m₁ m' b r j hg₁ hc₁ hU hY hd hj hv hfl _ hh hw' hop hL =>
      h k hk G₁ m' b r hop.current hd
        (hE.afterRead hg₁ hg hgo hc₁ hU hY hop hw' hL hh hj hv hfl)

/-- A load at the word by a thread out of the event's code (`atomicLoadC`). -/
theorem wp_peek (hE : L.Fits (E.prim L) P U ok) {ord : AtomicOrder}
    (hg : E.ph g = .out) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b, m'.current = t → P.inv (upd G₁ t g) m' →
      (b = 2 → E.IsSet m') → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) ord 4 E.W.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordLoad hE (hE.wRest rfl) (hE.wAp rfl) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hY hj hv _ _ hh hw' hop hL =>
      let ⟨h1, h2⟩ := hE.afterPeek hg₁ hg hgo hc₁ hU hY hop hw' hL hh hj hv
      h k hk G₁ m' b hop.current h1 h2

/-- A setter's `xchg(is_set)` with a decode (`atomicRmwAsC`, `Io.Event`), by a thread out of the
event's code: the event is set; the setter is at `sw` if it read `waiting`. -/
theorem wp_xchgAs {α : Type} [Packed α 32] (hE : L.Fits (E.prim L) P U ok)
    {ord : AtomicOrder} {v : α} (hv2 : Packed.toBits v = (2 : BitVec 32))
    (hdec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 2) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    (hg : E.ph g = .out) (hgo : L.ph g = .out) (hsx : E.sx g) (hi : P.inv (upd G t g) m)
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' o r, m'.current = t → (o = 0 ∨ o = 1 ∨ o = 2) →
      (Packed.ofBits? (α := α) o).run = some (.ok r) → E.IsSet m' →
      (o = 1 ∧ P.inv (upd G₁ t (E.set g .sw)) m') ∨
      (o ≠ 1 ∧ P.inv (upd G₁ t (E.set g .out)) m') → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC .xchg ord 4 E.W.ptr v : CM Tgt σ α).run s) Q G m n :=
  FLock.wp_wordRmwAs hE (hE.wRest rfl) (hE.wAp rfl) (by rw [hgo]; decide) hi
    (fun G₁ rY m₁ _ _ hU b hv => hdec b ((hE.wInv _ _ _ hU).val3
      (by have := hist_pos ((hE.wRest rfl) _ _ _ hU).1; omega) hv))
    fun k hk G₁ rY m₁ m' o r hg₁ hc₁ hU hY hd hv _ hh _ hw' hop hL => by
      have hh' : E.W.hist m' = (E.W.hist m₁).push
          (Word.rmwEnt m' t ord (E.newest m₁) (2 : BitVec 32)) := by
        rw [hh, ← hv2]; rfl
      obtain ⟨hs, h1⟩ := hE.afterXchg hg₁ hg hgo hsx hc₁ hU hY hop hw' hL hv hh'
      exact h k hk G₁ m' o r hop.current ((hE.wInv _ _ _ hU).val3
        (by have := hist_pos ((hE.wRest rfl) _ _ _ hU).1; omega) hv) hd hs h1

/-- A setter's `xchg(2)` on bits (`atomicRmwC`, `Thread.ResetEvent`). -/
theorem wp_xchg (hE : L.Fits (E.prim L) P U ok) {signed : Bool}
    {ord : AtomicOrder} {v : BitVec 32} (hv2 : v = 2)
    (hg : E.ph g = .out) (hgo : L.ph g = .out) (hsx : E.sx g) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' o, m'.current = t → E.IsSet m' →
      (o = 1 ∧ P.inv (upd G₁ t (E.set g .sw)) m') ∨
      (o ≠ 1 ∧ P.inv (upd G₁ t (E.set g .out)) m') → Q (o, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwC .xchg signed ord 4 E.W.ptr v : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordRmw hE (hE.wRest rfl) (hE.wAp rfl) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' o hg₁ hc₁ hU hY hv _ hh _ hw' hop hL => by
      have hh' : E.W.hist m' = (E.W.hist m₁).push
          (Word.rmwEnt m' t ord (E.newest m₁) (2 : BitVec 32)) := by
        rw [hh, ← hv2]; rfl
      obtain ⟨hs, h1⟩ := hE.afterXchg hg₁ hg hgo hsx hc₁ hU hY hop hw' hL hv hh'
      exact h k hk G₁ m' o hop.current hs h1

/-- The setter's wake at the word (`futexWakeC`, at least one waiter) at `sw`: it leaves. -/
theorem wp_wake (hE : L.Fits (E.prim L) P U ok) {io : Io} {c : BitVec 32}
    (hc : 1 ≤ c.toNat) (hg : E.ph g = .sw) (hgo : L.ph g = .out)    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t → E.IsSet m' →
      P.inv (upd G₁ t (E.set g .out)) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWakeC io E.W.ptr c : CM Tgt σ Unit).run s) Q G m n :=
  FLock.wp_wordWake hE (hE.wAp rfl) hi fun k hk G₁ rX m₁ cs m' hg₁ hU hw hL =>
    let ⟨h1, h2, h3⟩ := hE.afterWake hg₁ hg hgo hc hU hw hL
    h k hk G₁ m' h1 h2 h3

/-- **The waiter's futex wait** at the word with the value `waiting` (`futexWaitC`), at `w1`: it
goes on at `w1`. A set event's sleeper is not in a deadlock (`Fits.liveSet`); for an event that is
not set, the client shows it (`hlive`). -/
theorem wp_wait (hE : L.Fits (E.prim L) P U ok) {ε : Type} {w : Nat}
    [Packed ε w] {io : Io} {e : ε} (he : (Packed.toBits e).setWidth 32 = (1 : BitVec 32))
    (hg : E.ph g = .w1) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t → P.inv (upd G₁ t g) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWaitC io E.W.ptr e : CM Tgt σ Unit).run s) Q G m n := by
  have hheld : L.held g = rnil := by
    obtain ⟨rX, hL, -⟩ := (hE.inv _ _).mp hi
    have := hL.idle t (by rw [upd_self, hgo]; decide); rwa [upd_self] at this
  have hga : E.ph (L.set g .away rnil) = .w1 := by rw [hE.ph_l]; exact hg
  -- the ghost value of `t` after a step at the word while it is `w1`, at the lock place `q`
  have hgq : ∀ q, L.set (E.set (L.set g .away rnil) .w1) q rnil = L.set g q rnil := fun q => by
    rw [set_of hga, L.set_set]
  have hgo' : L.set g .out rnil = g := by
    have := L.set_self g; rwa [hgo, hheld] at this
  refine FLock.wp_wordWait hE (hE.wRest rfl) (hE.wAp rfl) hgo hi (fun rX hU => ?_)
    (fun G₁ m₁ hg₁ hi₁ => ?_) (fun G₁ rY m₁ M hg₁ hU hY hop hh hok₂ hbl hU32 => ?_)
    (fun G₁ rY m₁ M hg₁ hU hY hM => ?_) h
  · -- `t` goes away
    obtain ⟨-, rY, rfl, hY⟩ := (hE.wRest rfl) _ _ _ hU
    have hI := hE.wInv _ _ _ hU
    have := hE.wStep (G := upd G t g) (rY := rY) (m := m) (m' := m) (t := t) (p := .w1)
      (q := .away) (h := rnil) rfl ⟨.inl (by rw [upd_self]; exact hgo), .inr ⟨rfl, rfl⟩, rfl, .same⟩
      hU hY
    rw [upd_self, upd_upd, set_of hg] at this
    exact this (hI.relabel (fun u hu => by rw [upd_ne _ _ hu, upd_ne _ _ hu])
      (by rw [upd_self, upd_self, hE.ph_l])
      (fun _ => .inr ⟨by rw [upd_self, hE.ph_l]; exact hg, by rw [upd_self, L.ph_set]⟩)
      (fun h => by rw [upd_self] at h ⊢; exact (hE.role_l true _ _ _).mpr h)
      (fun h => by rw [upd_self] at h ⊢; exact (hE.role_l false _ _ _).mpr h))
  · -- no deadlock
    by_cases hs : E.IsSet m₁
    · obtain ⟨rX, hL, hU⟩ := (hE.inv _ _).mp hi₁
      exact hE.liveSet (hE.wInv _ _ _ hU) hL (by rw [hg₁]; exact hga) hs
    · exact hlive G₁ m₁ (by rw [hg₁]; exact hga) (by rw [hg₁, L.ph_set]) hi₁ hs
  · -- `t` sleeps: the word held `waiting`
    have hI := hE.wInv _ _ _ hU
    have hw₁ := ((hE.wRest rfl) _ _ _ hU).1
    have hv : (E.newest m₁).Val (1 : BitVec 32) := by rw [he] at hU32; exact hw₁.holds_last.mp hU32
    have hst := hE.wStep (G := G₁) (rY := rY) (m := m₁) (t := t) (p := .w1) (q := .away)
      (h := rnil) rfl ⟨.inr (by rw [hg₁, L.ph_set]), .inr ⟨rfl, rfl⟩, rfl, .sleep hop hh hok₂ hbl⟩
      hU hY
    rw [hg₁, hgq, ← hg₁, upd_same, Word.cellsR_congr (W := E.W) (show
      ({ M with waiters := M.waiters.push (t, E.W.ptr) } : Mem).blocks = m₁.blocks from hbl)] at hst
    exact hst (hI.sleep (by rw [hg₁]; exact hga) hop hh hv)
  · -- `t` is back at `w1`, out of the lock's code
    have hI := hE.wInv _ _ _ hU
    have hst := hE.wStep (G := G₁) (rY := rY) (m := m₁) (m' := M) (t := t) (p := .w1)
      (q := .out) (h := rnil) rfl ⟨.inr (by rw [hg₁, L.ph_set]), .inl rfl, rfl, ?_⟩ hU hY
    · rw [hg₁, hgq, hgo'] at hst
      have hbl : M.blocks = m₁.blocks := by
        rcases hM with rfl | rfl | ⟨-, -, -, hb⟩
        · rfl
        · rfl
        · exact hb
      rw [Word.cellsR_congr (W := E.W) hbl] at hst
      refine hst (hI.move (G' := upd G₁ t g) (fun u hu => upd_ne _ _ hu) ?_ ?_ ?_
        (by rw [upd_self, hg₁, hga, hg]; exact id) (by rw [upd_self, hg]; intro h; cases h)
        (fun _ => ?_) (by rw [hg₁, hga, upd_self, hg])
        (fun _ => .inl (by rw [upd_self]; exact hgo))
        (fun w hw e => ⟨fun _ => hI.qw w hw (by rw [e, hg₁]; exact hga),
          fun hp => by rw [upd_self]; exact hg⟩)
        (fun h => by rw [upd_self]; rw [hg₁] at h; exact (hE.role_l true _ _ _).mp h)
        (fun h => by rw [upd_self]; rw [hg₁] at h; exact (hE.role_l false _ _ _).mp h))
      · rcases hM with rfl | rfl | ⟨-, hh, -⟩
        · rfl
        · rfl
        · exact hh
      · rcases hM with rfl | rfl | ⟨hop, -⟩
        · rfl
        · rfl
        · exact hop.waiters
      · rcases hM with rfl | rfl | ⟨hop, -⟩
        · exact fun _ => VClock.le_refl _
        · exact fun _ => VClock.le_refl _
        · exact hop.clocks
      · obtain ⟨i, hi, hv, hc⟩ := hI.seen t (by rw [hg₁]; exact hga)
        refine ⟨i, hi, hv, VClock.le_trans hc ?_⟩
        rcases hM with rfl | rfl | ⟨hop, -⟩
        · exact VClock.le_refl _
        · exact VClock.le_refl _
        · exact hop.clocks t
    · rcases hM with rfl | rfl | ⟨hop, hh, hok₂, -⟩
      · exact .woken
      · exact .resume
      · exact .op hop hok₂ (.inl hh)

/-- **A step of a thread on its own part** in the event's code (`g`, out of the lock's code; a
stack block: `allocStack`, its stores and loads, `free`), with a thread triple: its part becomes
the triple's post (`FLock.setPart`; `Fits.wOwn`). -/
theorem wp_liftPart (hE : L.Fits (E.prim L) P U ok) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple Pa x Qa) (hp : Pa (L.part g))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      E.W.hist m' = E.W.hist m → P.inv (upd G t (L.setPart g r')) m' → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n :=
  FLock.wp_liftPartW hE (hE.wRest rfl) (.inl hgo) hi hc htt hp
    (fun a m' r' rY hr hq hc' hU hL hY hs hk hL' => by
      have hh := Word.hist_keepK ((hE.wRest rfl) _ _ _ hU).1 hk
      have hI' : E.Inv L (upd G t (L.setPart g r')) m' :=
        (hE.wInv _ _ _ hU).frame (t := t) (fun u hu => by rw [upd_ne _ _ hu, upd_ne _ _ hu])
          (by rw [upd_self, upd_self, hE.ph_part]) (by rw [upd_self, upd_self, L.ph_setPart])
          hh hs.waiters hs.clock
          (fun h => by rw [upd_self] at h ⊢; exact (hE.role_part true _ _).mpr h)
          (fun h => by rw [upd_self] at h ⊢; exact (hE.role_part false _ _).mpr h)
      have hU' := hE.wOwn (G := upd G t g) (t := t) (r := r') rfl
        (by rw [upd_self]; exact hgo) hU hL hY hc hs hk
        (by rw [upd_self, upd_upd]; exact hL') (by rw [upd_self, upd_upd]; exact hI')
      rw [upd_self, upd_upd] at hU'
      exact h a m' r' hr hq hc' hh ((hE.inv _ _).mpr ⟨_, hL', hU'⟩)) hret

/-- `wp_liftPart` for a step of generated code (`liftM`). -/
theorem wp_liftPartM (hE : L.Fits (E.prim L) P U ok) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple Pa x Qa) (hp : Pa (L.part g))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      E.W.hist m' = E.W.hist m → P.inv (upd G t (L.setPart g r')) m' → Q (a, s) G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((liftM x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (wp_liftPart hE hgo hi hc htt hp (fun a m' r' hr hq hc' hh hi' =>
    WP.pure' (h a m' r' hr hq hc' hh hi')) hret)

end FEvent

/-- **An event implementation** in generated code: its `wait` and `set`, with the rules that a
client uses, for every protocol that has the event next to a lock (`L.Fits (E.prim L) P U ok`)
and counts no turns.

- `wait_wp`: a thread out of the event's and the lock's code, with a ghost value that may wait
  (`FEvent.wx`), that waits returns when the event is set. It enters only as the only waiter,
  after every `waiting` write (`hone`, `hhb`; the scope of the module doc), and the client shows
  that its sleep at an event that is not set is not a deadlock (`hlive`).
- `set_wp`: a thread out of the event's and the lock's code, with a ghost value that may set
  (`FEvent.sx`), that sets it returns with the event set. -/
structure EventImpl (Tgt : Type) where
  wait : Ptr → Io → ConcM Tgt Unit
  set : Ptr → Io → ConcM Tgt Unit
  wait_wp : ∀ {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, L.Fits (E.prim L) P U ok →
    P.cost = none → ∀ {p : Ptr}, p = E.W.ptr → ∀ (t : ThreadId) (g : γ), E.ph g = .out →
    L.ph g = .out → E.wx g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat),
    (∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw) →
    (∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true) →
    (∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁) →
    P.inv (upd G t g) m →
    P.WP t (wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      P.inv (upd G' t g) m') G m d
  set_wp : ∀ {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, L.Fits (E.prim L) P U ok →
    P.cost = none → ∀ {p : Ptr}, p = E.W.ptr → ∀ (t : ThreadId) (g : γ), E.ph g = .out →
    L.ph g = .out → E.sx g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat),
    P.inv (upd G t g) m →
    P.WP t (set p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      P.inv (upd G' t g) m') G m d

end Full
end Zig
