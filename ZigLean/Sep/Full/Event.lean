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
`waiting` and has not woken yet, `sd` a setter after its set). `FEvent.Inv` is the event's
invariant: the writes are 0, 1, 2 and never get smaller, the waiter saw a `waiting` write (it
happened before it), a thread in the futex queue at the word is at `w1`, the newest write is
`waiting` or a setter is at `sw` (no lost wakeup), each `is_set` write is a release write (its
release clock covers its writer's clock), and the release clocks grow along the writes (each is
an RMW of the newest). A protocol keeps the event (`FLock.Fits` with `E.prim L`): its rest `U`
carries the invariant and has the word's cells (`Word.InRest`), and it is stable under each step
of the event's code (`MStep`, with the place change of the stepping thread and what it writes:
`Next`).

**Setters.** The event's steps write only the waiter's `waiting` (`w0` → `w1`, a thread that may
wait) and a setter's release `is_set` (`out` → `sw`/`sd`, a thread that may set); a thread at
`sw` or `sd` writes nothing and leaves them only to `sd` (`EPh.Next`), and `set` returns at `sd`
(`EventImpl.set_wp`). So a set orders memory: each set writes `is_set` at most once (not at all
when it finds the event set), as a release write that carries the setter's clock; a waiter that read an `is_set` write with acquire
(`Synced`) has the writer's clock of the first `is_set` write below its own (`Inv.synced_first`).
A protocol tells the setters apart by their ghost values: a thread that may not set (`sx`) does
not write `is_set`, and a thread at `sd` does not write it again until the protocol moves it
out (its own ghost step). Several setters are allowed; a client with several setters that need
their writes ordered before the waiter's reads shows which `is_set` write is the first.
A relaxed set and a set that writes twice make a `WaitGroup` race, and the contract excludes
both (`tests/roadmap/sync-contracts/EventSet.lean`).

**Roles.** `FEvent.wx` are the ghost values of the threads that may wait (the protocol says which
threads those are); the invariant keeps that each waiter and the writer of each `waiting` write
may wait (`Inv.wx`, `Inv.wby`), so a client with one such thread discharges `hone` and `hhb`
from the invariant. `FEvent.sx` are the ghost values of the threads that may set it: a setter (at
`sw` or `sd`, `EPh.Setting`) has one (`Inv.sx`), so a client can tell which threads are in the
setter's code. The roles also make the word's live set (`FEvent.Live`: a thread with a role, minus
a setter that has set): a plain access to the word (a whole read of the struct) need only be
below those threads, and every access to the word is by one of them (a peek takes a role). A step
of
the event's code changes the stepping thread's lock place only for a waiter's sleep (`w1`,
`away`), so the event's steps keep the places of the other components of a protocol.
**Gone setters.** A setter may run the set path after it left the lock's protocol (lock place
`gone`, e.g. a `WaitGroup`'s last `finish` after its `fetchSub`): the set ops take the setter's
existence from its resumption (the scheduler resumes only a thread that exists), not from its lock
place, and a setter at `sw` exists (`Inv.swex`), so the waiter's liveness (`Fits.liveSet`) still
finds it.
**Lock steps.** A thread in the event's code runs no lock code: a client's
`FLock.Fits` `ok` excludes it, and then a lock step keeps the event's invariant
(`Inv.lstep`).

**Scope (one waiter at a time).** A thread enters the wait (`w0`) only when no other thread is
at `w0` or `w1` (`EPh.Waiting`), and after every `waiting` write so far happened before it (`hone`/`hhb` of
`Inv.enter`). Reason: the memory model's facts of a read (`Word.Ok.load`, `Ok.cas`) give the
happens-before floor of the read (`Word.Floor`), not the read-read coherence of `Mem.seen`, and a
full-state frame (`FStepIn`) does not keep `Mem.seen`; so a waiter whose `cmpxchg`
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
  /-- A setter after its set (its `is_set` write and wake, or its read of `is_set`): it does not
  write the word again (`EPh.Next`). -/
  | sd
  deriving DecidableEq

/-- A waiter's place. -/
def EPh.Waiting (p : EPh) : Prop := p = .w0 ∨ p = .w1

/-- A setter's place. -/
def EPh.Setting (p : EPh) : Prop := p = .sw ∨ p = .sd

/-- A waiter's place is not a setter's. -/
theorem EPh.Waiting.not_setting {p : EPh} (h : p.Waiting) : ¬ p.Setting := by
  rcases h with rfl | rfl <;> rintro (h | h) <;> cases h

/-- **A place change of a step of the event's code that writes nothing** (`s`: the event is
set): a setter at `sw` stays or is done (`sd`; its wake, and the invariant's `q` keeps that no
waiter is lost), a setter at `sd` stays, and only a thread out of the
event's code that finds it set goes to `sd` without its own write; `sw` and the other ways into
`sd` are a setter's `is_set` write (`FEvent.Next`). So a thread writes `is_set` at most once from
`out` before the client moves it out of `sd` (module doc, **Setters**). -/
def EPh.Next : EPh → EPh → Prop → Prop
  | .sw, p, _ => p = .sw ∨ p = .sd
  | .sd, p, _ => p = .sd
  | .out, .sd, s => s
  | _, .sw, _ => False
  | _, .sd, _ => False
  | _, _, _ => True

/-- A place change away from the setter's places and to none of them. -/
theorem EPh.Next.of_ne {a p : EPh} {s : Prop} (ha : a ≠ .sw) (ha' : a ≠ .sd) (hp : p ≠ .sw)
    (hp' : p ≠ .sd) : EPh.Next a p s := by
  cases a <;> cases p <;> first | trivial | contradiction

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

/-- Thread `t` synchronized with a set: an `is_set` write of the word happened before it (its
release clock is below `t`'s clock). An acquire read of `is_set` gives it (`Synced.of_read`); a
waiter that returns has it (`EventImpl.wait_wp`), so what happened before a set happened before
the waiter's next step. -/
def Synced (t : ThreadId) (m : Mem) : Prop :=
  ∃ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (2 : BitVec 32) ∧
    VClock.le (E.W.hist m)[j]!.relClock (m.clocks[t]!) = true

/-- An acquire read of the write `j`, which is `is_set` (the facts of the word's rules: the read
write, its acquire, the unchanged history): the reader synchronized with a set. -/
theorem Synced.of_read {E : FEvent γ} {t : ThreadId} {m₁ m' : Mem} {j : Nat} (hj : j < (E.W.hist m₁).size)
    (hv : (E.W.hist m₁)[j]!.Val (2 : BitVec 32))
    (hacq : VClock.le (E.W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true)
    (hh : E.W.hist m' = E.W.hist m₁) : E.Synced t m' :=
  ⟨j, by rw [hh]; exact hj, by rw [hh]; exact hv, by rw [hh]; exact hacq⟩

/-- `Synced` after a step that keeps the word's history and the clocks (a waiter's `free` of
its own stack block, `Proto.free_clocks`; a pure step, `Proto.lift_clocks`: `@[fsym_run]` facts). -/
theorem Synced.of_clocks {E : FEvent γ} {t : ThreadId} {m m' : Mem}
    (hh : E.W.hist m' = E.W.hist m) (hc : m'.clocks = m.clocks) (hs : E.Synced t m) :
    E.Synced t m' := by
  unfold Synced; rw [hh, hc]; exact hs

/-- **What a step of the event's code by `t` (at `g`, to the place `p`) writes** (module doc,
**Setters**): no write, with a place change of `EPh.Next`; or one RMW of the newest write that is
the waiter's `waiting` (`w0` → `w1`, a thread that may wait) or a setter's release `is_set` (`out`
→ `sw`/`sd`, a thread that may set). -/
def Next (t : ThreadId) (g : γ) (p : EPh) (m m' : Mem) : Prop :=
  (E.W.hist m' = E.W.hist m ∧ EPh.Next (E.ph g) p (E.IsSet m)) ∨
  ∃ (ord : AtomicOrder) (v : BitVec 32),
    E.W.hist m' = (E.W.hist m).push (Word.rmwEnt m' t ord (E.newest m) v) ∧
    ((v = 1 ∧ E.wx g ∧ E.ph g = .w0 ∧ p = .w1) ∨
     (v = 2 ∧ E.sx g ∧ ord.isRel = true ∧ E.ph g = .out ∧ p.Setting))

/-- **The word's live set** (`Word.Ok`): a thread that may wait or may set (the protocol's roles),
unless it is a setter that has set (`sw`, `sd`: it does not write or read the word there; its
wake is no access). A thread out of it does not access the word, so a plain access to it (a whole
read of the struct the event is in) need not be below that thread. A client step that puts a
thread in the set (gives it a role, or moves a setter from `sd` back to `out`: `Inv.toOut`) has
its rest show the word for the larger set (the plain accesses are below that thread). A thread
without a role does not access the word (`wp_peek` takes one). -/
def Live (g : γ) : Prop := (E.wx g ∨ E.sx g) ∧ ¬ (E.ph g).Setting

/-- A step preserving the event's history preserves its set state. -/
theorem IsSet_of_hist_eq {m m' : Mem} (hh : E.W.hist m' = E.W.hist m)
    (hs : E.IsSet m) : E.IsSet m' := by
  simpa only [IsSet, newest, hh] using hs

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
  /-- A thread in the event's code is out of the lock's code, or a setter that left the lock for
  good (`gone`); a sleeping waiter is `away`. -/
  lp : ∀ u, E.ph (G u) ≠ .out →
    L.ph (G u) = .out ∨ ((E.ph (G u)).Setting ∧ L.ph (G u) = .gone) ∨
      (E.ph (G u) = .w1 ∧ L.ph (G u) = .away)
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
  /-- A setter (at `sw` or `sd`) has a ghost value that may set. -/
  sx : ∀ u, (E.ph (G u)).Setting → E.sx (G u)
  /-- Message ids at the word remain distinct and below the next fresh id. -/
  fresh : E.W.Fresh m
  /-- A setter at `sw` is a thread of the memory (`Fits.liveSet` names it as the thread that can
  go on; that it has not ended comes from the protocol's `fin`). -/
  swex : ∀ u, E.ph (G u) = .sw → u < m.threads.size
  /-- **Each `is_set` write is a release write**: its release clock covers its writer's clock at
  the write (the write's `clock`). -/
  rel : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (2 : BitVec 32) →
    VClock.le (E.W.hist m)[j]!.clock (E.W.hist m)[j]!.relClock = true
  /-- **The release sequence**: each write is an RMW of the newest, so a later write's release
  clock covers an earlier one's. -/
  relMono : ∀ i j, i ≤ j → j < (E.W.hist m).size →
    VClock.le (E.W.hist m)[i]!.relClock (E.W.hist m)[j]!.relClock = true

/-- **The event at its start**: every thread out of its code, no thread in the futex queue, and
the word has its first write, `unset`. -/
theorem Inv.start {L : FLock γ} {G : ThreadId → γ} {m : Mem} (hW : (E.W.hist m).size = 1)
    (hW0 : (E.W.hist m)[0]!.Val (0 : BitVec 32)) (hout : ∀ u, E.ph (G u) = .out)
    (hq : m.waiters = #[]) (hF : E.W.Fresh m) : E.Inv L G m where
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
  sx u h := by rw [hout u] at h; rcases h with h | h <;> cases h
  swex u h := by rw [hout u] at h; cases h
  fresh := hF
  rel j hj hv := by
    obtain rfl : j = 0 := by omega
    exact absurd (Except.ok.inj (Option.some.inj (hW0.symm.trans hv))) (by decide)
  relMono i j hij hj := by
    obtain rfl : j = 0 := by omega
    obtain rfl : i = 0 := by omega
    exact VClock.le_refl _

variable {E} in
/-- **A waiter is live** (`Inv.wx`). -/
theorem Inv.live {L : FLock γ} {G : ThreadId → γ} {m : Mem} (hI : E.Inv L G m) {u : ThreadId}
    (h : (E.ph (G u)).Waiting) : E.Live (G u) :=
  ⟨.inl (hI.wx u h), h.not_setting⟩

/-- A step of thread `t` in the event's code, as the protocol's rest sees it: no change, an op
at the word (a read, or an RMW of the newest write), the futex wait's sleep, the return of a
futex wait (woken, or at once), or a futex wake at the word. An op and the sleep's compare access
the word: they come with the word for `t` alone (`t` is in the live set, so its access does not
race; `Word.Ok.single`), and a step keeps the word for every live set (`MStep.word`). -/
inductive MStep (t : ThreadId) (m : Mem) : Mem → Prop
  | same : MStep t m m
  | op {m' : Mem} : E.W.Ok { m with current := t } (· = t) →
      t < m.clocks.size → m.clocks.size = m.threads.size →
      ((∃ (c : Nat) (ord : AtomicOrder) (v : BitVec 32),
          ((atomicLoadAt c ord 4 E.W.ptr).run { m with current := t }).run =
            some (.ok (v, m'))) ∨
        (∃ (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
            (v old : BitVec 32),
          ((atomicRmwAt c op signed ord 4 E.W.ptr v).run { m with current := t }).run =
            some (.ok (old, m'))) ∨
        (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec 32)
            (r : Option (BitVec 32)),
          ((cmpxchgAt c succ fail 4 E.W.ptr expected new).run { m with current := t }).run =
            some (.ok (r, m'))) ∨
        (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec 32)
            (r : Option (BitVec 32)),
          ((cmpxchgWeakAt c succ fail 4 E.W.ptr expected new).run { m with current := t }).run =
            some (.ok (r, m'))) ∨
        m' = ({ m with current := t } : Mem).recordAt E.W.b E.W.o 4 .atomicRead) →
      (E.W.hist m' = E.W.hist m ∨ ∃ (ord : AtomicOrder) (v : BitVec 32),
        E.W.hist m' = (E.W.hist m).push (Word.rmwEnt m' t ord (E.newest m) v)) →
      MStep t m m'
  | sleep {M : Mem} : E.W.Ok { m with current := t } (· = t) →
      t < m.clocks.size → m.clocks.size = m.threads.size →
      M = ({ m with current := t } : Mem).recordAt E.W.b E.W.o 4 .atomicRead →
      E.W.hist M = E.W.hist m →
      MStep t m { M with waiters := M.waiters.push (t, E.W.ptr) }
  | woken : MStep t m { m with current := t, woken := m.woken.erase t }
  | resume : MStep t m { m with current := t }
  | wake {m' : Mem} (c : Nat) (cs : List Nat) :
      ((Thread.futexWake E.W.ptr c cs).run { m with current := t }).run =
        some (.ok ((), m')) → MStep t m m'

/-- **The event as a primitive next to the lock `L`** (`FPrim.ofWords`; a protocol keeps it:
`L.Fits (E.prim L) P U ok`). Its word is `W`; the roles are `wx` (`true`) and `sx` (`false`); no
place is calm (`ok` may read every place). A step of its code is an `MStep` with the new place `p`
of the stepping thread, out of the lock's code or `away` in its own futex wait (at `w1`: a thread
in another primitive's futex wait does not step in the event's code), or `gone` (a setter that left
the lock for good stays `gone`), and its lock place `q`: only a waiter at `w1` goes `away`, while
it sleeps; it holds no lock resource. Its writes and place changes are those of `Next`: the
waiter's `waiting` and a setter's one release `is_set` (module doc, **Setters**). A thread steps on
its own part (the stack blocks of the event's code: `wp_liftPart`) out of the lock's code. The
rest keeps the word for the live set `Live` (`Word.Ok`). -/
abbrev prim (L : FLock γ) : FPrim γ :=
  FPrim.ofWords L E.toFPlace .out (fun _ => False) (fun b g => cond b (E.wx g) (E.sx g))
    (· = E.W) (fun _ => E.Live) (E.Inv L)
    (fun _ t g p q h m m' => (((L.ph g = .out ∨ (L.ph g = .away ∧ E.ph g = .w1)) ∧
      (q = .out ∨ (q = .away ∧ p = .w1))) ∨ (L.ph g = .gone ∧ q = .gone)) ∧ h = rnil ∧
      E.MStep t m m' ∧ E.Next t g p m m')
    (· = .out)

variable {E}

/-! ## A step of the event's code, as the memory sees it

From the actual native primitive run and its word facts: the threads stay, the
clocks grow, only the word's bytes change, a new access is at the word, each block stays as live,
as large and of the same kind, a lock's word apart from the event's keeps its location, a new
waiter is the stepping thread at the word, and a word at the event's or apart from it stays valid,
with a new write only at the event's word. -/

namespace MStep

variable {t : ThreadId} {m m' : Mem}

theorem nextMsg (hs : E.MStep t m m') : m.nextMsg ≤ m'.nextMsg := by
  cases hs with
  | @op M hw hc _ hop _ =>
    have hs : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hw hc (fun _ _ _ => rfl) hop
    exact hs.nextMsg
  | @sleep M _ _ _ hr _ =>
    subst M
    exact Nat.le_refl _
  | wake c cs h => rw [Proto.modify_ok h]; exact Nat.le_refl _
  | _ => exact Nat.le_refl _

/-- A step carries the existing atomic-location map at the explicitly named actor. -/
theorem atomics (hs : E.MStep t m m') (hF : Heap)
    (hoff : ∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) :
    ∃ σ, AMap hF { m with current := t } { m' with current := t } σ := by
  cases hs with
  | @op M hw hc _ hop _ =>
    have hs : FStepIn hF { m with current := t } m' := by
      exact Word.actualRun_fstep hw hc hoff hop
    obtain ⟨σ, ha⟩ := hs.atomics
    exact ⟨σ, ha.withCurrent (t := t) rfl⟩
  | @sleep M _ _ _ hr _ =>
    subst M
    exact ⟨some, AMap.of_eq rfl rfl⟩
  | wake c cs h => rw [Proto.modify_ok h]; exact ⟨some, AMap.of_eq rfl rfl⟩
  | _ => exact ⟨some, AMap.of_eq rfl rfl⟩

theorem threads (hs : E.MStep t m m') : m'.threads = m.threads := by
  cases hs with
  | @op M hw hc _ hop _ =>
    have hs : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hw hc (fun _ _ _ => rfl) hop
    exact hs.threads
  | @sleep M _ _ _ hr _ =>
    subst M
    rfl
  | wake c cs h => rw [Proto.modify_ok h]
  | _ => rfl

theorem clocks (hs : E.MStep t m m') (u : Nat) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  cases hs with
  | @op M hw hc _ hop _ =>
    have hs : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hw hc (fun _ _ _ => rfl) hop
    exact hs.clock u
  | @sleep M hw hc _ hr _ =>
    subst M
    exact (Word.record_fstep (hF := fun _ => none) (k := .atomicRead)
      hw hc (fun _ _ _ => rfl)).clock u
  | wake c cs h => rw [Proto.modify_ok h]; exact VClock.le_refl _
  | _ => exact VClock.le_refl _

theorem cells (hs : E.MStep t m m') {l : Zig.Loc} (hl : ¬ E.W.In l) : m'.heap l = m.heap l := by
  cases hs with
  | @op M hw hc _ hop _ =>
    exact (Word.actualRun_rest hw hc hop).heap l hl
  | @sleep M _ _ _ hr _ =>
    subst M
    rfl
  | wake c cs h => rw [Proto.modify_ok h]; rfl
  | _ => rfl

theorem fp (hs : E.MStep t m m') {e : FootprintEntry} (he : e ∈ m'.footprint) :
    e ∈ m.footprint ∨ (e.block = E.W.b ∧ e.off = E.W.o) := by
  cases hs with
  | @op M hw _ _ hop _ =>
    exact Word.actualRun_fpAt hw hop he
  | @sleep M _ _ _ hr _ =>
    rw [hr] at he
    exact Word.record_fpAt (W := E.W) (m := { m with current := t }) he
  | wake c cs h => rw [Proto.modify_ok h] at he; exact .inl he
  | _ => exact .inl he

/-- **A new access of a step of the event's code** is by the stepping thread, before its new
clock; a new write access comes with a write of the word (`Word.actualRun_fpWrite`), so a step that
keeps the word's history (`FEvent.Next`: a setter at `sw` or `sd`, a thread that may not write)
adds only reads. A client that bounds the writes to a block (a whole read of it later) needs this. -/
theorem fpNew (hs : E.MStep t m m') {e : FootprintEntry} (he : e ∈ m'.footprint) :
    (∃ e₀ ∈ m.footprint, e.Narrows e₀) ∨ (e.tid = t ∧ VClock.le e.clock (m'.clocks[t]!) = true ∧
      (e.kind.isWrite = true → ∃ x, E.W.hist m' = (E.W.hist m).push x)) := by
  by_cases hm : e ∈ m.footprint
  · exact .inl ⟨e, hm, .refl e⟩
  cases hs with
  | @op M hw hc hcs hop _ =>
    have hst : FStepIn (fun _ => none) { m with current := t } m' :=
      Word.actualRun_fstep hw hc (fun _ _ _ => rfl) hop
    rcases hst.fp e he with h | ⟨htid, -⟩
    · exact .inl h
    rcases hst.fpc e he with h | hcl
    · exact .inl h
    refine .inr ⟨htid, hcl, fun hk => ?_⟩
    rcases Word.actualRun_fpWrite hw (hcs ▸ hc : t < m.threads.size) rfl hcs hop he hk with h | h
    · exact absurd h hm
    · exact h
  | @sleep M hw hc _ hr _ =>
    have hst : FStepIn (fun _ => none) { m with current := t } M := by
      rw [hr]; exact Word.record_fstep (k := .atomicRead) hw hc (fun _ _ _ => rfl)
    have he' : e ∈ M.footprint := he
    rcases hst.fp e he' with h | ⟨htid, -⟩
    · exact .inl h
    rcases hst.fpc e he' with h | hcl
    · exact .inl h
    refine .inr ⟨htid, hcl, fun hk => ?_⟩
    rw [hr] at he'
    simp only [Mem.recordAt, Array.mem_push] at he'
    rcases he' with he' | rfl
    · exact absurd he' hm
    · cases hk
  | wake c cs h => rw [Proto.modify_ok h] at he; exact absurd he hm
  | _ => exact absurd he hm

theorem block (hs : E.MStep t m m') {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  cases hs with
  | @op M hw _ _ hop _ =>
    exact Word.actualRun_block hw hop hb
  | @sleep M _ _ _ hr _ =>
    subst M
    exact ⟨blk, hb, rfl, rfl, rfl⟩
  | wake c cs h => rw [Proto.modify_ok h]; exact ⟨blk, hb, rfl, rfl, rfl⟩
  | _ => exact ⟨blk, hb, rfl, rfl, rfl⟩

theorem lockLoc (hs : E.MStep t m m') {L : LockWord} (hap : E.W.ApartL L) {i : Nat} {l : ALoc}
    (hl : L.Loc m i l) : L.Loc m' i l := by
  cases hs with
  | @op M hw _ _ hop _ =>
    exact Word.actualRun_lockLoc hw hop hap hl
  | @sleep M _ _ _ hr _ =>
    subst M
    exact hl
  | wake c cs h => rw [Proto.modify_ok h]; exact hl
  | _ => exact hl

theorem waiters (hs : E.MStep t m m') {w : ThreadId × Ptr} (hw : w ∈ m'.waiters) :
    w ∈ m.waiters ∨ w = (t, E.W.ptr) := by
  cases hs with
  | @op M hv hc _ hop _ =>
    have hstep : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hv hc (fun _ _ _ => rfl) hop
    exact .inl (hstep.waiters ▸ hw)
  | @sleep M _ _ _ hr _ =>
    rw [hr] at hw
    rcases Array.mem_push.mp hw with hw | hw
    · exact .inl hw
    · exact .inr hw
  | wake c cs h => rw [Proto.modify_ok h] at hw; exact .inl (Array.mem_filter.mp hw).1
  | _ => exact .inl hw

/-- A step of the event's code keeps the queue at another futex `p` exactly, when a thread queued
at `p` is not queued at the event's word (`hone`, for the wake: `FLock.futexWake_waitersAt`). -/
theorem waiters_at (hs : E.MStep t m m') {p : Ptr} (hp : p ≠ E.W.ptr)
    (hone : ∀ w ∈ m.waiters, w.2 = p → ∀ w' ∈ m.waiters, w'.1 = w.1 → w'.2 ≠ E.W.ptr) :
    m'.waiters.filter (·.2 == p) = m.waiters.filter (·.2 == p) := by
  cases hs with
  | @op M hv hc _ hop _ =>
    have hstep : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hv hc (fun _ _ _ => rfl) hop
    rw [hstep.waiters]
  | @sleep M _ _ _ hr _ =>
    subst hr
    apply Array.toList_inj.mp
    simp only [Array.toList_filter, Array.toList_push, List.filter_append, List.filter_cons,
      List.filter_nil, beq_eq_false_iff_ne.mpr (Ne.symm hp), Bool.false_eq_true, ↓reduceIte,
      List.append_nil]
    rfl
  | wake c cs h => exact FLock.futexWake_waitersAt (m := { m with current := t }) hone h
  | _ => rfl

/-- A pending wake of another thread stays: only `t`'s own goes (`woken`), and a wake adds. -/
theorem woken_ne (hs : E.MStep t m m') {u : ThreadId} (hu : u ≠ t)
    (h : m.woken.contains u = true) : m'.woken.contains u = true := by
  cases hs with
  | @op M hv hc _ hop _ =>
    have hstep : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hv hc (fun _ _ _ => rfl) hop
    rw [hstep.woken]; exact h
  | @sleep M _ _ _ hr _ =>
    subst hr
    exact h
  | woken => show (m.woken.erase t).contains u = true; rw [FLock.woken_erase hu]; exact h
  | wake c cs h' =>
    rw [Proto.modify_ok h']
    show (m.woken ++ _).contains u = true
    rw [Array.contains_iff_mem] at h ⊢
    exact Array.mem_append_left _ h
  | _ => exact h

theorem word {W' : Word 32 4} {B : ThreadId → Prop} (hs : E.MStep t m m') (hok : W'.Ok m B)
    (hap : W' = E.W ∨ E.W.b ≠ W'.b ∨ E.W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ E.W.o) :
    W'.Ok m' B ∧ (W'.hist m' = W'.hist m ∨ (W' = E.W ∧ ∃ x, W'.hist m' = (W'.hist m).push x)) := by
  have hmem : ∀ l, ¬ E.W.In l → m'.heap l = m.heap l := fun _ hl => hs.cells hl
  have hk : ∀ {m₁ : Mem}, m₁.blocks = m.blocks → m₁.atomics = m.atomics →
      m₁.footprint = m.footprint → m₁.threads = m.threads → m₁.clocks = m.clocks →
      W'.Ok m₁ B ∧ (W'.hist m₁ = W'.hist m ∨
        (W' = E.W ∧ ∃ x, W'.hist m₁ = (W'.hist m).push x)) :=
    fun hb ha hf ht hc => by
      obtain ⟨hw', hh⟩ := hok.fields_native hb ha hf ht
        (fun u => by rw [hc]; exact VClock.le_refl _)
      exact ⟨hw', .inl hh⟩
  cases hs with
  | same => exact hk rfl rfl rfl rfl rfl
  | @op M hw hc hcs hop hh =>
    rcases hap with rfl | hap
    · obtain ⟨hv, -⟩ := hok.fields_native (m' := { m with current := t })
        rfl rfl rfl rfl (fun _ => VClock.le_refl _)
      exact ⟨Word.actualRun_okOf hw hv (hcs ▸ hc) hcs hop, hh.imp id fun ⟨ord, v, h⟩ =>
        ⟨rfl, Word.rmwEnt m' t ord (E.newest m) v, h⟩⟩
    · obtain ⟨hv, hvHist⟩ := hok.fields_native (m' := { m with current := t })
        rfl rfl rfl rfl (fun _ => VClock.le_refl _)
      have hsteps : ∀ hF : Heap,
          (∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) →
          FStepIn hF { m with current := t } m' := by
        intro hF hoff
        exact Word.actualRun_fstep hw hc hoff hop
      have hpres := Word.preserve_apart (W := E.W) hv hsteps hmem hap
      exact ⟨hpres.1, .inl (hpres.2.trans hvHist)⟩
  | @sleep M hw hc hcs hr hh =>
    have hM : W'.Ok M B ∧ W'.hist M = W'.hist m := by
      rcases hap with rfl | hap
      · obtain ⟨hv, -⟩ := hok.fields_native (m' := { m with current := t })
          rfl rfl rfl rfl (fun _ => VClock.le_refl _)
        exact ⟨Word.actualRun_okOf hw hv (hcs ▸ hc) hcs (.inr (.inr (.inr (.inr hr)))), hh⟩
      · obtain ⟨hv, hvHist⟩ := hok.fields_native (m' := { m with current := t })
          rfl rfl rfl rfl (fun _ => VClock.le_refl _)
        have hsteps : ∀ hF : Heap,
            (∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) →
            FStepIn hF { m with current := t } M := by
          intro hF hoff
          rw [hr]
          exact Word.record_fstep (k := .atomicRead) hw hc hoff
        have hcells : ∀ l, ¬ E.W.In l →
            M.heap l = ({ m with current := t } : Mem).heap l :=
          fun l _ => by rw [hr]; rfl
        have hpres := Word.preserve_apart (W := E.W) hv hsteps hcells hap
        exact ⟨hpres.1, hpres.2.trans hvHist⟩
    obtain ⟨hw'', hh'⟩ := hM.1.fields_native
      (m' := { M with waiters := M.waiters.push (t, E.W.ptr) })
      rfl rfl rfl rfl (fun _ => VClock.le_refl _)
    exact ⟨hw'', .inl (hh'.trans hM.2)⟩
  | woken => exact hk rfl rfl rfl rfl rfl
  | resume => exact hk rfl rfl rfl rfl rfl
  | wake c cs h => rw [Proto.modify_ok h]; exact hk rfl rfl rfl rfl rfl

/-- `word` for a shared word of any width apart from the event's (a client's other word, e.g. a
`WaitGroup`'s 64-bit state next to its event): it stays valid, with the same history. -/
theorem wordApart {n' nb' : Nat} {V : Word n' nb'} {B : ThreadId → Prop} (hs : E.MStep t m m')
    (hok : V.Ok m B) (hap : E.W.b ≠ V.b ∨ E.W.o + 4 ≤ V.o ∨ V.o + nb' ≤ E.W.o) :
    V.Ok m' B ∧ V.hist m' = V.hist m := by
  have hmem : ∀ l, ¬ E.W.In l → m'.heap l = m.heap l := fun _ hl => hs.cells hl
  have hk : ∀ {m₁ : Mem}, m₁.blocks = m.blocks → m₁.atomics = m.atomics →
      m₁.footprint = m.footprint → m₁.threads = m.threads → m₁.clocks = m.clocks →
      V.Ok m₁ B ∧ V.hist m₁ = V.hist m :=
    fun hb ha hf ht hc => hok.fields_native hb ha hf ht (fun u => by rw [hc]; exact VClock.le_refl _)
  obtain ⟨hv, hvHist⟩ := hok.fields_native (m' := { m with current := t })
    rfl rfl rfl rfl (fun _ => VClock.le_refl _)
  cases hs with
  | same => exact hk rfl rfl rfl rfl rfl
  | @op M hw hc _ hop _ =>
    have hsteps : ∀ hF : Heap,
        (∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) →
        FStepIn hF { m with current := t } m' := fun hF hoff =>
      Word.actualRun_fstep hw hc hoff hop
    have hpres := Word.preserve_apart (W := E.W) hv hsteps hmem hap
    exact ⟨hpres.1, hpres.2.trans hvHist⟩
  | @sleep M hw hc _ hr _ =>
    have hsteps : ∀ hF : Heap,
        (∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) →
        FStepIn hF { m with current := t } M := fun hF hoff => by
      rw [hr]; exact Word.record_fstep (k := .atomicRead) hw hc hoff
    have hcells : ∀ l, ¬ E.W.In l → M.heap l = ({ m with current := t } : Mem).heap l :=
      fun l _ => by rw [hr]; rfl
    have hM := Word.preserve_apart (W := E.W) hv hsteps hcells hap
    obtain ⟨hw'', hh'⟩ := hM.1.fields_native
      (m' := { M with waiters := M.waiters.push (t, E.W.ptr) })
      rfl rfl rfl rfl (fun _ => VClock.le_refl _)
    exact ⟨hw'', hh'.trans (hM.2.trans hvHist)⟩
  | woken => exact hk rfl rfl rfl rfl rfl
  | resume => exact hk rfl rfl rfl rfl rfl
  | wake c cs h => rw [Proto.modify_ok h]; exact hk rfl rfl rfl rfl rfl

end MStep

/-! ## Facts of the writes -/

theorem val_eq {x : Word.Entry} {a b : BitVec 32} (ha : x.Val a) (hb : x.Val b) : a = b := by
  unfold Word.Entry.Val at ha hb; rw [ha] at hb; cases hb; rfl

theorem rmwEnt_val {M : Mem} {t : ThreadId} {ord : AtomicOrder} {last : Word.Entry}
    {v : BitVec 32} : (Word.rmwEnt M t ord last v).Val v := intOfBytes_rmw v

/-- The word has a write. -/
theorem hist_pos {W : Word 32 4} {m : Mem} {A : ThreadId → Prop} (hw : W.Ok m A) :
    0 < (W.hist m).size := by
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

/-- **A waiter synchronized with a set is synchronized with the first set**: the writer's clock
at the first `is_set` write `j` is below the clock of a thread that synchronized with a set
(`Synced`; the release sequence, `Inv.rel` and `Inv.relMono`). A client with one setter whose
write read a value other than `is_set` knows its write is the first (`Inv.mono`), so what happened
before that set happened before the waiter's next step. -/
theorem Inv.synced_first {L : FLock γ} {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    (hI : E.Inv L G m) (hs : E.Synced t m) {j : Nat} (hj : j < (E.W.hist m).size)
    (hv : (E.W.hist m)[j]!.Val (2 : BitVec 32))
    (hfirst : ∀ i < j, ¬ (E.W.hist m)[i]!.Val (2 : BitVec 32)) :
    VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true := by
  obtain ⟨j', hj', hv', hle⟩ := hs
  have hjj : j ≤ j' := Nat.le_of_not_lt fun h => hfirst j' h hv'
  exact VClock.le_trans (hI.rel j hj hv) (VClock.le_trans (hI.relMono j j' hjj hj') hle)

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
    (hwx : E.wx g) (hone : ∀ u, u ≠ t → ¬ (E.ph (G u)).Waiting)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true) :
    E.Inv L (upd G t (E.set g .w0)) m := by
  have hnw : ∀ u, u ≠ t → ¬ (E.ph (upd G t (E.set g .w0) u)).Waiting := fun u hu hw => by
    rw [upd_ne _ _ hu] at hw
    exact hone u hu hw
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
    fun u hu => if e : u = t then by subst e; rw [hph] at hu; rcases hu with hu | hu <;> cases hu
      else by rw [hG u e] at hu ⊢; exact hI.sx u hu, hI.fresh,
    fun u hu => if e : u = t then by subst e; rw [hph] at hu; cases hu
      else by rw [hG u e] at hu; exact hI.swex u hu, hI.rel, hI.relMono⟩
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
    (hth : m.threads.size ≤ m'.threads.size)
    (hone : (E.ph (G' t)).Waiting → (E.ph (G t)).Waiting)
    (hw0 : E.ph (G' t) = .w0 → E.ph (G t) = .w0)
    (hw1 : E.ph (G' t) = .w1 → ∃ i < (E.W.hist m).size, (E.W.hist m)[i]!.Val (1 : BitVec 32) ∧
      VClock.le (E.W.hist m)[i]!.clock (m'.clocks[t]!) = true)
    (hsw : E.ph (G t) = .sw ↔ E.ph (G' t) = .sw)
    (hlpt : E.ph (G' t) ≠ .out →
      L.ph (G' t) = .out ∨ ((E.ph (G' t)).Setting ∧ L.ph (G' t) = .gone) ∨
        (E.ph (G' t) = .w1 ∧ L.ph (G' t) = .away))
    (htq : ∀ w ∈ m.waiters, w.1 = t →
      (E.ph (G' t) = .w1 → w.2 = E.W.ptr ∨ w.2 = L.ptr) ∧ (w.2 = E.W.ptr → E.ph (G' t) = .w1))
    (hwxt : E.wx (G t) → E.wx (G' t)) (hsxt : (E.ph (G' t)).Setting → E.sx (G' t))
    (hF : E.W.Fresh m') :
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
    fun u hu => if e : u = t then by subst e; exact hsxt hu
      else by rw [hG u e] at hu ⊢; exact hI.sx u hu, hF,
    fun u hu => Nat.lt_of_lt_of_le (if e : u = t then by subst e; exact hI.swex u (hsw.mpr hu)
      else by rw [hG u e] at hu; exact hI.swex u hu) hth,
    by rw [hh]; exact hI.rel, by rw [hh]; exact hI.relMono⟩
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
    (hpos : 0 < (E.W.hist m).size) (hth : m.threads.size ≤ m'.threads.size)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hwxt : E.wx (G t) → E.wx (G' t)) (hF : E.W.Fresh m') :
    E.Inv L G' m' := by
  have hsz : (E.W.hist m').size = (E.W.hist m).size + 1 := by rw [hh]; simp
  have hold : ∀ j, j < (E.W.hist m).size → (E.W.hist m')[j]! = (E.W.hist m)[j]! := fun j hj => by
    rw [hh]; exact Word.get_push_lt hj
  have hnew : (E.W.hist m')[(E.W.hist m).size]!.Val (1 : BitVec 32) := by
    rw [hh, Word.get_push_eq]; exact rmwEnt_val
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
    fun u hu => if e : u = t then by subst e; rw [ht1] at hu; rcases hu with hu | hu <;> cases hu
      else by rw [hG u e] at hu ⊢; exact hI.sx u hu, hF,
    fun u hu => if e : u = t then by subst e; rw [ht1] at hu; cases hu
      else by rw [hG u e] at hu; exact Nat.lt_of_lt_of_le (hI.swex u hu) hth,
    by rw [hh]; exact Word.rel_push hI.rel fun hv => absurd (val_eq rmwEnt_val hv) (by decide),
    by rw [hh]; exact Word.relMono_push hI.relMono Word.rmwEnt_relLe⟩
  rotate_right
  · -- the `waiting` writes: the new one is `t`'s
    rw [hsz] at hj
    rcases (by omega : j < (E.W.hist m).size ∨ j = (E.W.hist m).size) with hj' | rfl
    · rw [hold j hj'] at hv ⊢; exact hI.wby_of hG hwxt hclk hj' hv
    · refine ⟨t, hwx, ?_⟩
      rw [hh, Word.get_push_eq]; exact VClock.le_refl _
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
      rw [hh, Word.get_push_eq]; exact VClock.le_refl _
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

/-- A setter's release `xchg(is_set)` (`out` → `sw` if it read `waiting`, else `sd`). -/
theorem Inv.xchg {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    (hI : E.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u) (ht0 : E.ph (G t) = .out)
    (ht1 : (E.ph (G' t)).Setting)
    (hsw : (E.newest m).Val (1 : BitVec 32) → E.ph (G' t) = .sw)
    (hlpt : L.ph (G' t) = .out ∨ L.ph (G' t) = .gone) (hrel : ord.isRel = true)
    (hh : E.W.hist m' = (E.W.hist m).push (Word.rmwEnt m' t ord (E.newest m) (2 : BitVec 32)))
    (hwt : m'.waiters = m.waiters) (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hth : m.threads.size ≤ m'.threads.size) (ht' : t < m'.threads.size)
    (hnq : ∀ w ∈ m.waiters, w.1 ≠ t) (hwxt : E.wx (G t) → E.wx (G' t))
    (hsx : E.sx (G' t)) (hF : E.W.Fresh m') :
    E.Inv L G' m' := by
  have hsz : (E.W.hist m').size = (E.W.hist m).size + 1 := by rw [hh]; simp
  have hold : ∀ j, j < (E.W.hist m).size → (E.W.hist m')[j]! = (E.W.hist m)[j]! := fun j hj => by
    rw [hh]; exact Word.get_push_lt hj
  have hnew : (E.W.hist m')[(E.W.hist m).size]!.Val (2 : BitVec 32) := by
    rw [hh, Word.get_push_eq]; exact rmwEnt_val
  have hnw : ¬ (E.ph (G' t)).Waiting := fun hw => by
    rcases ht1 with h | h <;> rw [h] at hw <;> rcases hw with h | h <;> cases h
  have key : ∀ x, (E.ph (G' x)).Waiting → (E.ph (G x)).Waiting ∧ x ≠ t := fun x hx => by
    by_cases e : x = t
    · subst e; exact absurd hx hnw
    · rw [hG x e] at hx; exact ⟨hx, e⟩
  refine ⟨fun j hj => ?_, fun i j a b hij hj ha hb => ?_, fun u v hu hv => ?_,
    fun u hu j hj hv => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw hp => ?_, fun w hw hp => ?_,
    fun _ _ => ?_, fun u hu => wx_of hG hwxt (hI.wx u (key u hu).1), fun j hj hv => ?_,
    fun u hu => if e : u = t then by subst e; exact hsx
      else by rw [hG u e] at hu ⊢; exact hI.sx u hu, hF,
    fun u hu => if e : u = t then e ▸ ht'
      else by rw [hG u e] at hu; exact Nat.lt_of_lt_of_le (hI.swex u hu) hth,
    by rw [hh]; exact Word.rel_push hI.rel fun _ => Word.rmwEnt_rel hrel,
    by rw [hh]; exact Word.relMono_push hI.relMono Word.rmwEnt_relLe⟩
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
    · subst eu
      rcases hlpt with h | h
      · exact .inl h
      · exact .inr (.inl ⟨ht1, h⟩)
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
    (ht : E.ph (G t) = .w1) (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (M.clocks[u]!) = true)
    (hwt : M.waiters = m.waiters) (hth : m.threads.size ≤ M.threads.size)
    (hh : E.W.hist M = E.W.hist m) (hv : (E.newest m).Val (1 : BitVec 32))
    (hF : E.W.Fresh M) :
    E.Inv L G { M with waiters := M.waiters.push (t, E.W.ptr) } := by
  have hh' : E.W.hist { M with waiters := M.waiters.push (t, E.W.ptr) } = E.W.hist m := hh
  refine ⟨by rw [hh']; exact hI.vals, by rw [hh']; exact hI.mono, hI.one,
    fun u hu j hj hv => ?_, fun u hu => ?_, hI.lp, fun w hw hp => ?_, fun w hw hp => ?_,
    fun u hu => by unfold FEvent.newest; rw [hh']; exact hI.swset u hu, hI.wx,
    fun j hj hv => by rw [hh'] at hj hv ⊢; exact hI.wby_of (t := t) (fun _ _ => rfl) id hclk hj hv,
    hI.sx, hF, fun u hu => Nat.lt_of_lt_of_le (hI.swex u hu) hth,
    by rw [hh']; exact hI.rel, by rw [hh']; exact hI.relMono⟩
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

/-- The setter's wake of every waiter at the word (`sw` → `sd`; one waiter at a time, so the
wake of at least one waiter empties the queue at the word). -/
theorem Inv.wake {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g : γ} {c : Nat}
    {cs : List Nat} (hI : E.Inv L G m) (ht : E.ph (G t) = .sw) (hg : E.ph g = .sd)
    (hgo : L.ph g = .out ∨ L.ph g = .gone)
    (hc : 1 ≤ c) (hwxg : E.wx (G t) → E.wx g) (hsxg : E.sx (G t) → E.sx g)
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
    fun u hu => if e : u = t then by subst e; rw [upd_self]; exact hsxg (hI.sx u (.inl ht))
      else by rw [upd_ne _ _ e] at hu ⊢; exact hI.sx u hu, hI.fresh,
    fun u hu => if e : u = t then by subst e; rw [upd_self, hg] at hu; cases hu
      else by rw [upd_ne _ _ e] at hu; exact hI.swex u hu, hI.rel, hI.relMono⟩
  · have := hnw u (.inl hu); rw [upd_ne _ _ this.2] at hu; exact hI.hb u hu j hj hv
  · have := hnw u (.inr hu); rw [upd_ne _ _ this.2] at hu; exact hI.seen u hu
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu ⊢
      rcases hgo with h | h
      · exact .inl h
      · exact .inr (.inl ⟨.inr hg, h⟩)
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
      L.ph (G' t) = .out ∨ ((E.ph (G' t)).Setting ∧ L.ph (G' t) = .gone) ∨
        (E.ph (G' t) = .w1 ∧ L.ph (G' t) = .away))
    (hwxt : E.wx (G t) → E.wx (G' t)) (hsxt : E.sx (G t) → E.sx (G' t)) :
    E.Inv L G' m :=
  hI.move hG rfl rfl (fun _ => VClock.le_refl _) (Nat.le_refl _) (by rw [hph]; exact id)
    (by rw [hph]; exact id) (fun h => hI.seen t (by rw [← hph]; exact h)) (by rw [hph])
    hlpt (fun w hw e => ⟨fun h => hI.qw w hw (by rw [e, ← hph]; exact h),
      fun h => by rw [hph, ← e]; exact (hI.q w hw h).1⟩) hwxt
    (fun h => hsxt (hI.sx t (by rw [← hph]; exact h))) hI.fresh

/-- A step that keeps the writes and the futex queue and only moves the clocks forward (a step of
a thread on its own part), with a change of `t`'s ghost value that keeps its places. -/
theorem Inv.frame {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} (hI : E.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u) (hph : E.ph (G' t) = E.ph (G t))
    (hlph : L.ph (G' t) = L.ph (G t)) (hh : E.W.hist m' = E.W.hist m)
    (hwt : m'.waiters = m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hth : m.threads.size ≤ m'.threads.size)
    (hwxt : E.wx (G t) → E.wx (G' t)) (hsxt : E.sx (G t) → E.sx (G' t))
    (hF : E.W.Fresh m') :
    E.Inv L G' m' :=
  hI.move hG hh hwt hclk hth (by rw [hph]; exact id) (by rw [hph]; exact id)
    (fun h => let ⟨i, hi, hv, hc⟩ := hI.seen t (by rw [← hph]; exact h)
      ⟨i, hi, hv, VClock.le_trans hc (hclk t)⟩) (by rw [hph])
    (fun h => by rw [hph] at h ⊢; rw [hlph]; exact hI.lp t h)
    (fun w hw e => ⟨fun h => hI.qw w hw (by rw [e, ← hph]; exact h),
      fun h => by rw [hph, ← e]; exact (hI.q w hw h).1⟩) hwxt
    (fun h => hsxt (hI.sx t (by rw [← hph]; exact h))) hF

/-- **A thread out of the event's code or done (`out`, `sd`) gets a ghost value there** (`g`, at
`out` or `sd`; a client's own ghost step, e.g. a setter's end after its `set`, before it sets or
waits again, or a setter that finds the event set, `Fits.doneSet`): the writes and the queue stay,
it keeps its waiter role (`hwx`), and at `sd` it is out of the lock's code or gone from it (`hgo`)
and may set (`hsx`). -/
theorem Inv.toOut {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ} (hI : E.Inv L G m)
    (ht : E.ph (G t) = .out ∨ E.ph (G t) = .sd) (hg : E.ph g = .out ∨ E.ph g = .sd)
    (hgo : E.ph g = .sd → L.ph g = .out ∨ L.ph g = .gone) (hwx : E.wx (G t) → E.wx g)
    (hsx : E.ph g = .sd → E.sx g) :
    E.Inv L (upd G t g) m := by
  have hgt : E.ph (upd G t g t) = .out ∨ E.ph (upd G t g t) = .sd := by rw [upd_self]; exact hg
  refine hI.move (fun u hu => upd_ne _ _ hu) rfl rfl (fun _ => VClock.le_refl _) (Nat.le_refl _)
    (fun h => ?_) (fun h => ?_) (fun h => ?_)
    ⟨fun h => (by rcases ht with e | e <;> rw [e] at h <;> cases h), fun h => ?_⟩
    (fun h => ?_)
    (fun w hw e => ⟨fun h => ?_, fun h => by
      have := (hI.q w hw h).1; rw [e] at this; rcases ht with e' | e' <;> rw [e'] at this <;>
        cases this⟩)
    (fun h => by rw [upd_self]; exact hwx h)
    (fun h => by
      rw [upd_self] at h ⊢
      rcases h with e | e
      · rcases hg with e' | e' <;> rw [e'] at e <;> cases e
      · exact hsx e) hI.fresh
  · rcases hgt with e | e <;> rw [e] at h <;> rcases h with h | h <;> cases h
  all_goals first
    | (rcases hgt with e | e <;> rw [e] at h <;> cases h)
    | (rw [upd_self] at h ⊢
       have hsd : E.ph g = .sd := hg.resolve_left h
       rcases hgo hsd with e | e
       · exact .inl e
       · exact .inr (.inl ⟨.inr hsd, e⟩))

/-- **A step of another component of the protocol** (a condition's code) by `t`, which keeps
`t`'s place in the event and the word's writes: `t` keeps its lock place or goes `out` of the
lock, and a new waiter in the futex queue is `t` at another word, not as the event's waiter. -/
theorem Inv.other {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} (hI : E.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u) (hph : E.ph (G' t) = E.ph (G t))
    (hlpt : E.ph (G t) ≠ .out → L.ph (G' t) = L.ph (G t) ∨ L.ph (G' t) = .out)
    (hh : E.W.hist m' = E.W.hist m)
    (hwt : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ (w.1 = t ∧ w.2 ≠ E.W.ptr ∧ E.ph (G t) ≠ .w1))
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hth : m.threads.size ≤ m'.threads.size)
    (hwxt : E.wx (G t) → E.wx (G' t)) (hsxt : E.sx (G t) → E.sx (G' t))
    (hF : E.W.Fresh m') :
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
    fun u hu => ?_, hF,
    fun u hu => Nat.lt_of_lt_of_le (hI.swex u (by rw [← hp]; exact hu)) hth,
    by rw [hh]; exact hI.rel, by rw [hh]; exact hI.relMono⟩
  · rw [hp] at hu; rw [hh] at hj hv ⊢; exact VClock.le_trans (hI.hb u hu j hj hv) (hclk u)
  · rw [hp] at hu; rw [hh]
    obtain ⟨i, hi, hv, hc⟩ := hI.seen u hu
    exact ⟨i, hi, hv, VClock.le_trans hc (hclk u)⟩
  · rw [hp] at hu
    by_cases e : u = t
    · subst e
      rcases hI.lp u hu with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hlpt hu with h' | h'
        · exact .inl (h'.trans h)
        · exact .inl h'
      · rcases hlpt hu with h' | h'
        · exact .inr (.inl ⟨by rw [hph]; exact h1, h'.trans h2⟩)
        · exact .inl h'
      · rcases hlpt hu with h' | h'
        · exact .inr (.inr ⟨by rw [hph]; exact h1, h'.trans h2⟩)
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
    {B : ThreadId → Prop} (hI : E.Inv L G m) (hw : E.W.Ok m B) (hap : E.W.ApartL L.toLockWord)
    (hout : E.ph (G t) = .out) (hph : ∀ g q h, E.ph (L.set g q h) = E.ph g)
    (hwx : ∀ g q h, E.wx (L.set g q h) ↔ E.wx g) (hsx : ∀ g q h, E.sx (L.set g q h) ↔ E.sx g)
    (hs : L.Step t m m') :
    E.Inv L (upd G t (L.set (G t) p h)) m' := by
  have hoff : L.Off (E.W.cellsR m).heap.erase := by
    intro x h1 h2
    have hn : ¬ E.W.In (L.b, x) := by
      rintro ⟨hb, h3, h4⟩
      rcases hap with hb' | h | h
      · exact hb' hb
      · omega
      · omega
    simp [FHeap.erase, Word.cellsR, cellsAt_none hn]
  obtain ⟨σ, hA⟩ := hs.atomics (E.W.cellsR m).heap.erase hoff
  have hF : E.W.Fresh m' := Word.Fresh.amap
    (m := { m with current := t }) (m' := { m' with current := t }) hI.fresh hA hs.nextMsg
    (fun x h1 h2 => by
      have hcell := cellsAt_some (W := E.W.In) (l := (E.W.b, x)) ⟨rfl, h1, h2⟩
        (hw.cellIn ⟨rfl, h1, h2⟩) (m := m)
      intro hnone
      exact hcell (Option.map_eq_none_iff.mp hnone))
    (fun i l hl => (hw.loc i l hl).1)
  have hh := (hw.lockStep hs hap).2
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
    (hs.waiters_mem w hl).mp hw'
  refine ⟨by rw [hh]; exact hI.vals, by rw [hh]; exact hI.mono,
    fun u v hu hv => hI.one u v (by rw [← hp]; exact hu) (by rw [← hp]; exact hv),
    fun u hu j hj hv => ?_, fun u hu => ?_, fun u hu => ?_, fun w hw' hq => ?_,
    fun w hw' hq => ?_, fun u hu => ?_, fun u hu => (hx u).mpr (hI.wx u (by rw [← hp]; exact hu)),
    fun j hj hv => ?_, fun u hu => ?_, hF,
    fun u hu => by rw [hp] at hu; rw [hs.threads]; exact hI.swex u hu,
    by rw [hh]; exact hI.rel, by rw [hh]; exact hI.relMono⟩
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
theorem _root_.Zig.Full.FLock.Fits.liveSet (hE : L.Fits (E.prim L) P U ok) {G : ThreadId → γ}
    {rX : Res}
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
  · -- the setter is out of the lock's code or left it (`gone`): not in the futex queue
    have hlo : L.ph (G u) ≠ .wait ∧ L.ph (G u) ≠ .away := by
      rcases hI.lp u (by rw [hu]; decide) with h | ⟨-, h⟩ | ⟨h, -⟩
      · rw [h]; decide
      · rw [h]; decide
      · rw [hu] at h; cases h
    rcases hall u (hI.swex u hu) with h | h | h
    · rw [hE.kfin _ h] at hu; cases hu
    · have := hL.w.notQ (t := u) hlo.1 hlo.2
      rw [this] at h; cases h
    · rw [hE.kjoins _ h] at hu; cases hu

/-- After a step of the event's code by `t` at `out` of the lock or `gone` from it (`g`, new place
`p`): the protocol's invariant, from the lock's invariant after the step, the rest and the lock's
word invariant before it, and the event's invariant after it. -/
theorem _root_.Zig.Full.FLock.Fits.backOut (hE : L.Fits (E.prim L) P U ok)
    {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {p : EPh} (hg₁ : G₁ t = g)
    (hgo : L.ph g = .out ∨ L.ph g = .gone) (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁)
    (hwL : L.WInv (L.pl G₁) m₁)
    (hY : ∀ l, E.W.In l → rY.heap l = none) (hs : E.MStep t m₁ m') (hn : E.Next t g p m₁ m')
    (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m') (hI : E.Inv L (upd G₁ t (E.set g p)) m') :
    P.inv (upd G₁ t (E.set g p)) m' :=
  hE.back rfl hg₁ ⟨hgo.imp (fun h => ⟨.inl h, .inl h⟩) fun h => ⟨h, h⟩,
    hg₁ ▸ hL.idle t (by rw [hg₁]; rcases hgo with h | h <;> rw [h] <;> decide), hs, hn⟩ hU hwL hY hL hI

/-- The facts at a stop of `t` (at `out` of the lock, or `gone` from it) before an op at the word:
the event's invariant, `t` is not in the futex queue, the word is `Ok`. -/
theorem _root_.Zig.Full.FLock.Fits.atWord (hE : L.Fits (E.prim L) P U ok)
    {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} (hgo : L.ph (G₁ t) = .out ∨ L.ph (G₁ t) = .gone)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hwait : m'.waiters = m₁.waiters)
    (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m') :
    E.Inv L G₁ m₁ ∧ (∀ w ∈ m₁.waiters, w.1 ≠ t) ∧ E.W.Ok m₁ (fun u => E.Live (G₁ u)) :=
  let ⟨hI, hnq⟩ := hE.atOp hU (by rcases hgo with h | h <;> rw [h] <;> decide)
    (by rcases hgo with h | h <;> rw [h] <;> decide) hwait hL
  ⟨hI, hnq, ((hE.wRest rfl) _ _ _ hU).1⟩

/-- **A waiter is live** (at `w0` or `w1`: it may wait, `Inv.wx`). -/
theorem _root_.Zig.Full.FLock.Fits.liveWaiter (hE : L.Fits (E.prim L) P U ok)
    {G : ThreadId → γ} {t : ThreadId} {g : γ} {m : Mem} (hi : P.inv (upd G t g) m)
    (hg : (E.ph g).Waiting) : E.Live g := by
  obtain ⟨rX, -, hU⟩ := (hE.inv _ _).mp hi
  have := (hE.wInv _ _ _ hU).live (u := t) (by rw [upd_self]; exact hg)
  rwa [upd_self] at this

/-- A thread out of the event's code that may wait or set is live. -/
theorem live_out {g : γ} (hg : E.ph g = .out) (hr : E.wx g ∨ E.sx g) : E.Live g :=
  ⟨hr, fun h => by rcases h with h | h <;> rw [hg] at h <;> cases h⟩

/-- The live set does not read the lock's place. -/
theorem _root_.Zig.Full.FLock.Fits.live_l (hE : L.Fits (E.prim L) P U ok) {g : γ} {q : LPh}
    {h : Res} : E.Live (L.set g q h) ↔ E.Live g := by
  have hw := hE.role_l true g q h
  have hs := hE.role_l false g q h
  simp only [Bool.cond_true, Bool.cond_false] at hw hs
  unfold Live
  rw [hw, hs, show E.ph (L.set g q h) = E.ph g from hE.ph_l g q h]

/-- A waiter's read at the word (`w0` or `w1`) of write `j` with the value `b`: `unset` (only
at `w0`: it stays), `waiting` (it goes to `w1`), or `is_set` (it leaves; the event is set, and
an acquire read (`hacq`, the word rules' acquire fact) synchronized with a set: `Synced`). -/
theorem _root_.Zig.Full.FLock.Fits.afterRead (hE : L.Fits (E.prim L) P U ok)
    {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} (hg₁ : G₁ t = g) (hgw : (E.ph g).Waiting)
    (hgo : L.ph g = .out)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hwL : L.WInv (L.pl G₁) m₁)
    (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hms : E.MStep t m₁ m')
    (hA : ∀ hF, (∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) →
      FStepIn hF m₁ m')
    (hS : E.W.Fresh m₁ → E.W.Fresh m' ∧ ∀ u, E.W.ownPos m₁ u ≤ E.W.ownPos m' u)
    (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hh : E.W.hist m' = E.W.hist m₁) {j : Nat} {b : BitVec 32} (hj : j < (E.W.hist m₁).size)
    (hv : (E.W.hist m₁)[j]!.Val b) (hfl : Word.Floor (E.W.hist m₁) (m₁.clocks[t]!) j)
    {ord : AtomicOrder}
    (hacq : ord.isAcq = true → VClock.le (E.W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) :
    (b = 0 ∧ E.ph g = .w0 ∧ P.inv (upd G₁ t (E.set g .w0)) m') ∨
    (b = 1 ∧ P.inv (upd G₁ t (E.set g .w1)) m') ∨
    (b = 2 ∧ E.IsSet m' ∧ (ord.isAcq = true → E.Synced t m') ∧
      P.inv (upd G₁ t (E.set g .out)) m') := by
  have hop := hA (fun _ => none) (fun _ _ _ => rfl)
  obtain ⟨hI, hnq, -⟩ := hE.atWord (.inl (by rw [hg₁]; exact hgo)) hU hop.waiters hL
  have hclk := hop.clock
  have hlo : ∀ p, L.ph (upd G₁ t (E.set g p) t) = .out := fun p => by
    rw [upd_self, hE.lph]; exact hgo
  have hgt : E.ph (G₁ t) = E.ph g := by rw [hg₁]
  have hgn : E.ph g ≠ .sw ∧ E.ph g ≠ .sd := by
    rcases hgw with e | e <;> rw [e] <;> exact ⟨nofun, nofun⟩
  have hn : ∀ p, p ≠ .sw → p ≠ .sd → E.Next t g p m₁ m' := fun p hps hpd =>
    .inl ⟨hh, EPh.Next.of_ne hgn.1 hgn.2 hps hpd⟩
  -- the new invariant at place `p`
  have hmv : ∀ p, p ≠ .sw → p ≠ .sd → ((E.ph (E.set g p)).Waiting → (E.ph g).Waiting) →
      (p = .w0 → E.ph g = .w0) →
      (p = .w1 → ∃ i < (E.W.hist m₁).size, (E.W.hist m₁)[i]!.Val (1 : BitVec 32) ∧
        VClock.le (E.W.hist m₁)[i]!.clock (m'.clocks[t]!) = true) →
      E.Inv L (upd G₁ t (E.set g p)) m' := fun p hps hpd h1 h2 h3 =>
    hI.move (fun u hu => upd_ne _ _ hu) hh hop.waiters hclk (Nat.le_of_eq (by rw [hop.threads]))
      (by rw [upd_self, hgt]; exact h1) (by rw [upd_self, hgt, E.ph_set]; exact h2)
      (by rw [upd_self, E.ph_set]; exact h3)
      (by
        rw [hgt, upd_self, E.ph_set]
        exact ⟨fun h => absurd h hgn.1, fun h => absurd h hps⟩)
      (fun _ => .inl (hlo p)) (fun w hw e => absurd e (hnq w hw)) (wx_upd_set hg₁)
      (fun h => by rw [upd_self, E.ph_set] at h; exact (h.elim hps hpd).elim) (hS hI.fresh).1
  rcases hI.val3 hj hv with rfl | rfl | rfl
  · -- `unset`: only at `w0`
    have hw0 : E.ph g = .w0 := by
      rcases hgw with e | e
      · exact e
      · obtain ⟨i, hi, hv1, hc⟩ := hI.seen t (by rw [hgt]; exact e)
        have := hI.read_ge hi hv1 hc hfl hj hv
        simp at this
    refine .inl ⟨rfl, hw0, hE.backOut hg₁ (.inl hgo) hU hwL hY hms (hn _ nofun nofun) hL
      (hmv .w0 nofun nofun (fun _ => hgw) (fun _ => hw0) (fun h => by cases h))⟩
  · refine .inr (.inl ⟨rfl, hE.backOut hg₁ (.inl hgo) hU hwL hY hms (hn _ nofun nofun) hL
      (hmv .w1 nofun nofun (fun _ => hgw) (fun h => by cases h) fun _ => ?_)⟩)
    rcases hgw with e | e
    · exact ⟨j, hj, hv, VClock.le_trans (hI.hb t (by rw [hgt]; exact e) j hj hv) (hclk t)⟩
    · obtain ⟨i, hi, hv1, hc⟩ := hI.seen t (by rw [hgt]; exact e)
      exact ⟨i, hi, hv1, VClock.le_trans hc (hclk t)⟩
  · have hset : E.IsSet m' := by
      have := hI.isSet_of hj hv
      unfold FEvent.IsSet FEvent.newest at this ⊢; rw [hh]; exact this
    refine .inr (.inr ⟨rfl, hset, fun ha => Synced.of_read hj hv (hacq ha) hh,
      hE.backOut hg₁ (.inl hgo) hU hwL hY hms (hn _ nofun nofun) hL
      (hmv .out nofun nofun (by rw [E.ph_set]; intro h; rcases h with h | h <;> cases h)
        (fun h => by cases h) (fun h => by cases h))⟩)

/-- A read at the word by a thread out of the event's code (`g`, out of the lock's code or gone
from it): it stays; a read of `is_set` means the event is set. -/
theorem _root_.Zig.Full.FLock.Fits.afterPeek (hE : L.Fits (E.prim L) P U ok)
    {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} (hg₁ : G₁ t = g) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .gone)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hwL : L.WInv (L.pl G₁) m₁)
    (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hms : E.MStep t m₁ m')
    (hA : ∀ hF, (∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) →
      FStepIn hF m₁ m')
    (hS : E.W.Fresh m₁ → E.W.Fresh m' ∧ ∀ u, E.W.ownPos m₁ u ≤ E.W.ownPos m' u)
    (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hh : E.W.hist m' = E.W.hist m₁) {j : Nat} {b : BitVec 32} (hj : j < (E.W.hist m₁).size)
    (hv : (E.W.hist m₁)[j]!.Val b) :
    P.inv (upd G₁ t g) m' ∧ (b = 2 → E.IsSet m') := by
  have hop := hA (fun _ => none) (fun _ _ _ => rfl)
  obtain ⟨hI, hnq, -⟩ := hE.atWord (by rw [hg₁]; exact hgo) hU hop.waiters hL
  have hgt : E.ph (G₁ t) = .out := by rw [hg₁]; exact hgx
  have hI' : E.Inv L (upd G₁ t (E.set g .out)) m' :=
    hI.move (fun u hu => upd_ne _ _ hu) hh hop.waiters hop.clock
      (Nat.le_of_eq (by rw [hop.threads])) (by rw [upd_self, E.ph_set, hgt]; exact id) (by rw [upd_self, E.ph_set]; intro h; cases h)
      (by rw [upd_self, E.ph_set]; intro h; cases h) (by rw [hgt, upd_self, E.ph_set])
      (by rw [upd_self, E.ph_set]; intro h; exact absurd rfl h) (fun w hw e => absurd e (hnq w hw))
      (wx_upd_set hg₁) (by rw [upd_self, E.ph_set]; intro h; rcases h with h | h <;> cases h)
      (hS hI.fresh).1
  have := hE.backOut hg₁ hgo hU hwL hY hms (.inl ⟨hh, by rw [hgx]; trivial⟩) hL hI'
  rw [set_of hgx] at this
  refine ⟨this, fun hb => ?_⟩
  subst hb
  have := hI.isSet_of hj hv
  unfold FEvent.IsSet FEvent.newest at this ⊢; rw [hh]; exact this

/-- The waiter's successful `cmpxchg(unset → waiting)`: it goes to `w1`. -/
theorem _root_.Zig.Full.FLock.Fits.afterCasOk (hE : L.Fits (E.prim L) P U ok)
    {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {ord : AtomicOrder} (hg₁ : G₁ t = g)
    (hg : E.ph g = .w0) (hgo : L.ph g = .out)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hwL : L.WInv (L.pl G₁) m₁)
    (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hms : E.MStep t m₁ m')
    (hA : ∀ hF, (∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) →
      FStepIn hF m₁ m')
    (hS : E.W.Fresh m₁ → E.W.Fresh m' ∧ ∀ u, E.W.ownPos m₁ u ≤ E.W.ownPos m' u)
    (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    (hv : (E.newest m₁).Val (0 : BitVec 32))
    (hh : E.W.hist m' = (E.W.hist m₁).push (Word.rmwEnt m' t ord (E.newest m₁) (1 : BitVec 32))) :
    P.inv (upd G₁ t (E.set g .w1)) m' := by
  have hop := hA (fun _ => none) (fun _ _ _ => rfl)
  obtain ⟨hI, hnq, hw₁⟩ := hE.atWord (.inl (by rw [hg₁]; exact hgo)) hU hop.waiters hL
  have hwx : E.wx g := by
    have := hI.wx t (by rw [hg₁, hg]; exact .inl rfl); rwa [hg₁] at this
  refine hE.backOut hg₁ (.inl hgo) hU hwL hY hms (.inr ⟨ord, 1, hh, .inl ⟨rfl, hwx, hg, rfl⟩⟩)
    hL (hI.casOk (fun u hu => upd_ne _ _ hu) (by rw [hg₁]; exact hg)
      (by rw [upd_self, E.ph_set]) (by rw [upd_self, hE.lph]; exact hgo) hv hh hop.waiters hnq
      (hist_pos hw₁) (Nat.le_of_eq (by rw [hop.threads])) hop.clock (wx_upd_set hg₁) (hS hI.fresh).1)

/-- A setter's release `xchg(is_set)`, by a thread out of the event's code (`g`, out of the lock's
code or gone from it), that read `o`: the event is set, and the setter is at `sw` if it read
`waiting` (it must wake), else done (`sd`). -/
theorem _root_.Zig.Full.FLock.Fits.afterXchg (hE : L.Fits (E.prim L) P U ok)
    {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {ord : AtomicOrder} (hg₁ : G₁ t = g)
    (hgx : E.ph g = .out) (hgo : L.ph g = .out ∨ L.ph g = .gone) (hsx : E.sx g)
    (hrel : ord.isRel = true)
    (hct : t < m₁.clocks.size)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hwL : L.WInv (L.pl G₁) m₁)
    (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hms : E.MStep t m₁ m')
    (hA : ∀ hF, (∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) →
      FStepIn hF m₁ m')
    (hS : E.W.Fresh m₁ → E.W.Fresh m' ∧ ∀ u, E.W.ownPos m₁ u ≤ E.W.ownPos m' u)
    (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m')
    {o : BitVec 32} (hv : (E.newest m₁).Val o)
    (hh : E.W.hist m' = (E.W.hist m₁).push (Word.rmwEnt m' t ord (E.newest m₁) (2 : BitVec 32))) :
    E.IsSet m' ∧ ((o = 1 ∧ P.inv (upd G₁ t (E.set g .sw)) m') ∨
      (o ≠ 1 ∧ P.inv (upd G₁ t (E.set g .sd)) m')) := by
  have hop := hA (fun _ => none) (fun _ _ _ => rfl)
  obtain ⟨hI, hnq, -⟩ := hE.atWord (by rw [hg₁]; exact hgo) hU hop.waiters hL
  have hgt : E.ph (G₁ t) = .out := by rw [hg₁]; exact hgx
  have hset : E.IsSet m' := by
    unfold FEvent.IsSet FEvent.newest; rw [hh]
    simp only [Array.size_push, Nat.add_sub_cancel]
    rw [Word.get_push_eq]; exact rmwEnt_val
  have hx : ∀ p, p.Setting → ((E.newest m₁).Val (1 : BitVec 32) → p = .sw) →
      E.Inv L (upd G₁ t (E.set g p)) m' := fun p hp h1 =>
    hI.xchg (fun u hu => upd_ne _ _ hu) hgt (by rw [upd_self, E.ph_set]; exact hp)
      (by rw [upd_self, E.ph_set]; exact h1) (by rw [upd_self, hE.lph]; exact hgo) hrel hh
      hop.waiters hop.clock (Nat.le_of_eq (by rw [hop.threads]))
      (by rw [← hL.w.csize, hop.size]; exact hct) hnq (wx_upd_set hg₁)
      (by rw [upd_self, E.sx_set]; exact hsx) (hS hI.fresh).1
  have hn : ∀ p, p.Setting → E.Next t g p m₁ m' := fun p hp =>
    .inr ⟨ord, 2, hh, .inr ⟨rfl, hsx, hrel, hgx, hp⟩⟩
  refine ⟨hset, ?_⟩
  by_cases ho : o = 1
  · subst ho
    exact .inl ⟨rfl, hE.backOut hg₁ hgo hU hwL hY hms (hn _ (.inl rfl)) hL
      (hx .sw (.inl rfl) fun _ => rfl)⟩
  · exact .inr ⟨ho, hE.backOut hg₁ hgo hU hwL hY hms (hn _ (.inr rfl)) hL (hx .sd (.inr rfl) fun h1 =>
      absurd (val_eq hv h1) ho)⟩

/-- A thread enters the wait (`out` → `w0`; module doc, scope). -/
theorem _root_.Zig.Full.FLock.Fits.enterWait (hE : L.Fits (E.prim L) P U ok) {G : ThreadId → γ}
    {m : Mem}
    {t : ThreadId} {g : γ} (hgx : E.ph g = .out) (hgo : L.ph g = .out) (hwx : E.wx g)
    (hone : ∀ u, u ≠ t → ¬ (E.ph (G u)).Waiting)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) : P.inv (upd G t (E.set g .w0)) m := by
  obtain ⟨rX, hL, hU⟩ := (hE.inv _ _).mp hi
  obtain ⟨-, rY, rfl, hY⟩ := (hE.wRest rfl) _ _ _ hU
  have hI := hE.wInv _ _ _ hU
  have := hE.backOut (p := .w0) (upd_self G t g) (.inl hgo) hU hL.w hY .same
    (.inl ⟨rfl, by rw [hgx]; trivial⟩)
    hL (by rw [upd_upd]; exact hI.enter hgx (by rw [hE.lph]; exact hgo) hwx hone hhb)
  rwa [upd_upd] at this

/-- **A setter that finds the event set is done** (`out` → `sd`, no write: `EPh.Next`), e.g.
after a read of `is_set` (0.15.2's `set`). -/
theorem _root_.Zig.Full.FLock.Fits.doneSet (hE : L.Fits (E.prim L) P U ok) {G : ThreadId → γ}
    {m : Mem} {t : ThreadId} {g : γ} (hgx : E.ph g = .out) (hgo : L.ph g = .out ∨ L.ph g = .gone)
    (hsx : E.sx g) (hs : E.IsSet m) (hi : P.inv (upd G t g) m) :
    P.inv (upd G t (E.set g .sd)) m := by
  obtain ⟨rX, hL, hU⟩ := (hE.inv _ _).mp hi
  obtain ⟨-, rY, rfl, hY⟩ := (hE.wRest rfl) _ _ _ hU
  have hI := hE.wInv _ _ _ hU
  have := hE.backOut (p := .sd) (upd_self G t g) hgo hU hL.w hY .same
    (.inl ⟨rfl, by rw [hgx]; exact hs⟩) hL
    (hI.toOut (t := t) (g := E.set g .sd) (by rw [upd_self]; exact .inl hgx)
      (.inr (E.ph_set _ _)) (fun _ => by rw [hE.lph]; exact hgo)
      (by rw [upd_self, E.wx_set]; exact id) (fun _ => (E.sx_set _ _).mpr hsx))
  rwa [upd_upd] at this

/-- The setter's wake at the word (`sw` → `sd`), of at least one waiter. -/
theorem _root_.Zig.Full.FLock.Fits.afterWake (hE : L.Fits (E.prim L) P U ok)
    {G₁ : ThreadId → γ}
    {rX : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {c : Nat} {cs : List Nat} (hg₁ : G₁ t = g)
    (hg : E.ph g = .sw) (hgo : L.ph g = .out ∨ L.ph g = .gone) (hc : 1 ≤ c) (hU : U G₁ rX m₁)
    (hwL : L.WInv (L.pl G₁) m₁) (hw : ((Thread.futexWake E.W.ptr c cs).run { m₁ with current := t }).run =
      some (.ok ((), m'))) (hL : L.Inv G₁ rX m') :
    m'.current = t ∧ E.IsSet m' ∧ P.inv (upd G₁ t (E.set g .sd)) m' := by
  have hm' := Proto.modify_ok hw
  obtain ⟨-, rY, rfl, hY⟩ := (hE.wRest rfl) _ _ _ hU
  have hI := hE.wInv _ _ _ hU
  have hcl : E.W.cellsR m' = E.W.cellsR m₁ := Word.cellsR_congr (by rw [hm'])
  have hh : E.W.hist m' = E.W.hist m₁ := by rw [hm']; rfl
  refine ⟨by rw [hm'], ?_, hE.backOut hg₁ hgo hU hwL hY (.wake c cs hw)
    (.inl ⟨hh, by rw [hg]; exact .inr rfl⟩) (by rw [hcl]; exact hL) ?_⟩
  · have := hI.swset t (by rw [hg₁]; exact hg)
    unfold FEvent.IsSet FEvent.newest at this ⊢; rw [hh]; exact this
  exact hI.wake (by rw [hg₁]; exact hg) (E.ph_set _ _) (by rw [hE.lph]; exact hgo) hc
    (fun h => (E.wx_set _ _).mpr (by rw [← hg₁]; exact h))
    (fun h => (E.sx_set _ _).mpr (by rw [← hg₁]; exact h)) hw

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
        (b = 2 ∧ E.IsSet m' ∧ (fail.isAcq = true → E.Synced t m') ∧
          P.inv (upd G₁ t (E.set g .out)) m') → Q (some r, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgAsC succ fail 4 E.W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  have hlv := hE.liveWaiter hi (.inl hg)
  refine FLock.wp_wordCasAs hE (hE.wRest rfl) (hE.wAp rfl) hi
    (fun G₁ rY m₁ _ _ hU j hj b hv => hdec b ((hE.wInv _ _ _ hU).val3 hj hv)) (hlv := hlv)
    fun k hk G₁ rY m₁ m' hg₁ hc₁ hU hwL hY _ hw₀ hct hrun hA hS hL =>
      let hop := hA (fun _ => none) (fun _ _ _ => rfl)
      let hms := MStep.op (E := E) (t := t) (m := m₁) (m' := m')
        (by rw [FEvent.cur_eq hc₁]; exact hw₀.single (hg₁ ▸ hlv)) hct hwL.csize (by
          rw [FEvent.cur_eq hc₁]
          rcases hrun with ⟨c, r, hr⟩
          exact .inr (.inr (.inl ⟨c, _, _, _, _, r, hr⟩)))
      ⟨fun hv _ hh _ _hR => ?_,
      fun j b r hne hd hj hv hfl hacq hh _hR => ?_⟩
  · rw [he] at hv; rw [hn] at hh
    exact (h k hk G₁ m' (hop.current.trans hc₁)).1
      (hE.afterCasOk hg₁ hg hgo hU hwL hY (hms (.inr ⟨_, _, hh⟩)) hA hS hL hv hh)
  · rcases hE.afterRead hg₁ (.inl hg) hgo hU hwL hY (hms (.inl hh)) hA hS hL hh hj hv hfl hacq with
      ⟨rfl, -⟩ | h1 | h1
    · exact absurd he.symm hne
    · exact (h k hk G₁ m' (hop.current.trans hc₁)).2 b r hd (.inl h1)
    · exact (h k hk G₁ m' (hop.current.trans hc₁)).2 b r hd (.inr h1)

/-- The waiter's `cmpxchg(unset → waiting)` at `w0` on bits (`cmpxchgC`,
`Thread.ResetEvent`). -/
theorem wp_cas (hE : L.Fits (E.prim L) P U ok) {succ fail : AtomicOrder}
    {exp new : BitVec 32} (he : exp = 0) (hn : new = 1)
    (hg : E.ph g = .w0) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      (P.inv (upd G₁ t (E.set g .w1)) m' → Q (none, s) G₁ m' k) ∧
      (∀ b, (b = 1 ∧ P.inv (upd G₁ t (E.set g .w1)) m') ∨
        (b = 2 ∧ E.IsSet m' ∧ (fail.isAcq = true → E.Synced t m') ∧
          P.inv (upd G₁ t (E.set g .out)) m') → Q (some b, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgC (n := 32) succ fail 4 E.W.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  subst he hn
  have hlv := hE.liveWaiter hi (.inl hg)
  refine FLock.wp_wordCas hE (hE.wRest rfl) (hE.wAp rfl) hi (hlv := hlv)
    fun k hk G₁ rY m₁ m' hg₁ hc₁ hU hwL hY _ hw₀ hct hrun hA hS hL =>
      let hop := hA (fun _ => none) (fun _ _ _ => rfl)
      let hms := MStep.op (E := E) (t := t) (m := m₁) (m' := m')
        (by rw [FEvent.cur_eq hc₁]; exact hw₀.single (hg₁ ▸ hlv)) hct hwL.csize (by
          rw [FEvent.cur_eq hc₁]
          rcases hrun with ⟨c, r, hr⟩
          exact .inr (.inr (.inl ⟨c, _, _, _, _, r, hr⟩)))
      ⟨fun hv _ hh _ _hR => ?_,
      fun j b hne hj hv hfl hacq hh _hR => ?_⟩
  · exact (h k hk G₁ m' (hop.current.trans hc₁)).1
      (hE.afterCasOk hg₁ hg hgo hU hwL hY (hms (.inr ⟨_, _, hh⟩)) hA hS hL hv hh)
  · rcases hE.afterRead hg₁ (.inl hg) hgo hU hwL hY (hms (.inl hh)) hA hS hL hh hj hv hfl hacq with
      ⟨rfl, -⟩ | h1 | h1
    · exact absurd rfl hne
    · exact (h k hk G₁ m' (hop.current.trans hc₁)).2 b (.inl h1)
    · exact (h k hk G₁ m' (hop.current.trans hc₁)).2 b (.inr h1)

/-- A waiter's load at the word (`w0` or `w1`; `atomicLoadC`). -/
theorem wp_load (hE : L.Fits (E.prim L) P U ok) {ord : AtomicOrder}
    (hg : (E.ph g).Waiting) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b, m'.current = t →
      (b = 0 ∧ E.ph g = .w0 ∧ P.inv (upd G₁ t (E.set g .w0)) m') ∨
      (b = 1 ∧ P.inv (upd G₁ t (E.set g .w1)) m') ∨
      (b = 2 ∧ E.IsSet m' ∧ (ord.isAcq = true → E.Synced t m') ∧
        P.inv (upd G₁ t (E.set g .out)) m') → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) ord 4 E.W.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  have hlv := hE.liveWaiter hi hg
  FLock.wp_wordLoad hE (hE.wRest rfl) (hE.wAp rfl) hi (hlv := hlv)
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hwL hY hj hv hfl hacq hh _ hw₀ hct hrun hA hS _hR hL =>
      let hop := hA (fun _ => none) (fun _ _ _ => rfl)
      h k hk G₁ m' b (hop.current.trans hc₁) (hE.afterRead hg₁ hg hgo hU hwL hY (by
        refine .op (by rw [FEvent.cur_eq hc₁]; exact hw₀.single (hg₁ ▸ hlv)) hct
          hwL.csize ?_ (.inl hh)
        rw [FEvent.cur_eq hc₁]
        exact (by rcases hrun with ⟨c, hr⟩; exact .inl ⟨c, _, _, hr⟩)) hA hS hL hh hj hv hfl hacq)

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
      (b = 2 ∧ E.IsSet m' ∧ (ord.isAcq = true → E.Synced t m') ∧
        P.inv (upd G₁ t (E.set g .out)) m') → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadAsC α ord 4 E.W.ptr : CM Tgt σ α).run s) Q G m n :=
  have hlv := hE.liveWaiter hi hg
  FLock.wp_wordLoadAs hE (hE.wRest rfl) (hE.wAp rfl) hi
    (fun G₁ rY m₁ _ _ hU j hj b hv => hdec b ((hE.wInv _ _ _ hU).val3 hj hv))
    (hlv := hlv)
    fun k hk G₁ rY m₁ m' b r j hg₁ hc₁ hU hwL hY hd hj hv hfl hacq hh _ hw₀ hct hrun hA hS _hR hL =>
      let hop := hA (fun _ => none) (fun _ _ _ => rfl)
      h k hk G₁ m' b r (hop.current.trans hc₁) hd
        (hE.afterRead hg₁ hg hgo hU hwL hY (by
        refine .op (by rw [FEvent.cur_eq hc₁]; exact hw₀.single (hg₁ ▸ hlv)) hct
          hwL.csize ?_ (.inl hh)
        rw [FEvent.cur_eq hc₁]
        exact (by rcases hrun with ⟨c, hr⟩; exact .inl ⟨c, _, _, hr⟩)) hA hS hL hh hj hv hfl hacq)

/-- A load at the word by a thread out of the event's code (`atomicLoadC`), out of the lock's code
or gone from it, that may wait or set (live: `FEvent.Live`). -/
theorem wp_peek (hE : L.Fits (E.prim L) P U ok) {ord : AtomicOrder}
    (hg : E.ph g = .out) (hgo : L.ph g = .out ∨ L.ph g = .gone) (hr : E.wx g ∨ E.sx g)
    (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b, m'.current = t → P.inv (upd G₁ t g) m' →
      (b = 2 → E.IsSet m') → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) ord 4 E.W.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordLoad hE (hE.wRest rfl) (hE.wAp rfl) hi (hlv := live_out (E := E) hg hr)
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hwL hY hj hv _ _ hh _ hw₀ hct hrun hA hS _hR hL =>
      let hop := hA (fun _ => none) (fun _ _ _ => rfl)
      let ⟨h1, h2⟩ := hE.afterPeek hg₁ hg hgo hU hwL hY (by
        refine .op (by rw [FEvent.cur_eq hc₁]; exact hw₀.single (hg₁ ▸ live_out (E := E) hg hr)) hct
          hwL.csize ?_ (.inl hh)
        rw [FEvent.cur_eq hc₁]
        exact (by rcases hrun with ⟨c, hr⟩; exact .inl ⟨c, _, _, hr⟩)) hA hS hL hh hj hv
      h k hk G₁ m' b (hop.current.trans hc₁) h1 h2

/-- A setter's `xchg(is_set)` with a decode (`atomicRmwAsC`, `Io.Event`), by a thread out of the
event's code: the event is set; the setter is at `sw` if it read `waiting`, else done (`sd`). -/
theorem wp_xchgAs {α : Type} [Packed α 32] (hE : L.Fits (E.prim L) P U ok)
    {ord : AtomicOrder} {v : α} (hv2 : Packed.toBits v = (2 : BitVec 32))
    (hdec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 2) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    (hg : E.ph g = .out) (hgo : L.ph g = .out ∨ L.ph g = .gone) (hsx : E.sx g)
    (hrel : ord.isRel = true) (hi : P.inv (upd G t g) m)
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' o r, m'.current = t → (o = 0 ∨ o = 1 ∨ o = 2) →
      (Packed.ofBits? (α := α) o).run = some (.ok r) → E.IsSet m' →
      (o = 1 ∧ P.inv (upd G₁ t (E.set g .sw)) m') ∨
      (o ≠ 1 ∧ P.inv (upd G₁ t (E.set g .sd)) m') → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC .xchg ord 4 E.W.ptr v : CM Tgt σ α).run s) Q G m n :=
  FLock.wp_wordRmwAs hE (hE.wRest rfl) (hE.wAp rfl) hi
    (fun G₁ rY m₁ _ _ hU b hv => hdec b ((hE.wInv _ _ _ hU).val3
      (by have := hist_pos ((hE.wRest rfl) _ _ _ hU).1; omega) hv))
    (hlv := live_out (E := E) hg (.inr hsx))
    fun k hk G₁ rY m₁ m' o r hg₁ hc₁ hU hwL hY hd hv _ hh _ _ hw₀ hct hrun hA hS _hR hL => by
      have hop := hA (fun _ => none) (fun _ _ _ => rfl)
      have hh' : E.W.hist m' = (E.W.hist m₁).push
          (Word.rmwEnt m' t ord (E.newest m₁) (2 : BitVec 32)) := by
        rw [hh, ← hv2]; rfl
      obtain ⟨hs, h1⟩ := hE.afterXchg hg₁ hg hgo hsx hrel hct hU hwL hY (by
        refine .op (by
          rw [FEvent.cur_eq hc₁]; exact hw₀.single (hg₁ ▸ live_out (E := E) hg (.inr hsx))) hct
          hwL.csize ?_ (.inr ⟨_, _, hh'⟩)
        rw [FEvent.cur_eq hc₁]
        exact (by rcases hrun with ⟨c, hr⟩; exact .inr (.inl ⟨c, _, _, _, _, _, hr⟩))) hA hS hL hv hh'
      exact h k hk G₁ m' o r (hop.current.trans hc₁) ((hE.wInv _ _ _ hU).val3
        (by have := hist_pos ((hE.wRest rfl) _ _ _ hU).1; omega) hv) hd hs h1

/-- A setter's `xchg(2)` on bits (`atomicRmwC`, `Thread.ResetEvent`). -/
theorem wp_xchg (hE : L.Fits (E.prim L) P U ok) {signed : Bool}
    {ord : AtomicOrder} {v : BitVec 32} (hv2 : v = 2)
    (hg : E.ph g = .out) (hgo : L.ph g = .out ∨ L.ph g = .gone) (hsx : E.sx g)
    (hrel : ord.isRel = true) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' o, m'.current = t → E.IsSet m' →
      (o = 1 ∧ P.inv (upd G₁ t (E.set g .sw)) m') ∨
      (o ≠ 1 ∧ P.inv (upd G₁ t (E.set g .sd)) m') → Q (o, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwC .xchg signed ord 4 E.W.ptr v : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordRmw hE (hE.wRest rfl) (hE.wAp rfl) hi (hlv := live_out (E := E) hg (.inr hsx))
    fun k hk G₁ rY m₁ m' o hg₁ hc₁ hU hwL hY hv _ hh _ _ hw₀ hct hrun hA hS _hR hL => by
      have hop := hA (fun _ => none) (fun _ _ _ => rfl)
      have hh' : E.W.hist m' = (E.W.hist m₁).push
          (Word.rmwEnt m' t ord (E.newest m₁) (2 : BitVec 32)) := by
        rw [hh, ← hv2]; rfl
      obtain ⟨hs, h1⟩ := hE.afterXchg hg₁ hg hgo hsx hrel hct hU hwL hY (by
        refine .op (by
          rw [FEvent.cur_eq hc₁]; exact hw₀.single (hg₁ ▸ live_out (E := E) hg (.inr hsx))) hct
          hwL.csize ?_ (.inr ⟨_, _, hh'⟩)
        rw [FEvent.cur_eq hc₁]
        exact (by rcases hrun with ⟨c, hr⟩; exact .inr (.inl ⟨c, _, _, _, _, _, hr⟩))) hA hS hL hv hh'
      exact h k hk G₁ m' o (hop.current.trans hc₁) hs h1

/-- The setter's wake at the word (`futexWakeC`, at least one waiter) at `sw`: it leaves. -/
theorem wp_wake (hE : L.Fits (E.prim L) P U ok) {io : Io} {c : BitVec 32}
    (hc : 1 ≤ c.toNat) (hg : E.ph g = .sw) (hgo : L.ph g = .out ∨ L.ph g = .gone)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t → E.IsSet m' →
      P.inv (upd G₁ t (E.set g .sd)) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWakeC io E.W.ptr c : CM Tgt σ Unit).run s) Q G m n :=
  FLock.wp_wordWake hE (hE.wAp rfl) hi fun k hk G₁ rX m₁ cs m' hg₁ hU hwL hw hL =>
    let ⟨h1, h2, h3⟩ := hE.afterWake hg₁ hg hgo hc hU hwL hw hL
    h k hk G₁ m' h1 h2 h3

/-! ### The waiter's futex wait at `w1`: its facts for `FLock.wp_wordWait`, `wp_wordOsWait` -/

/-- The waiter at `w1` (`g`, out of the lock's code) goes `away` while it waits. -/
theorem waitAway (hE : L.Fits (E.prim L) P U ok) (hg : E.ph g = .w1) (hgo : L.ph g = .out)
    (G : ThreadId → γ) (rX : Res) (m : Mem) (hU : U (upd G t g) rX m)
    (hwL : L.WInv (L.pl (upd G t g)) m) :
    U (upd G t (L.set g .away rnil)) rX m := by
  obtain ⟨-, rY, rfl, hY⟩ := (hE.wRest rfl) _ _ _ hU
  have hI := hE.wInv _ _ _ hU
  have := hE.wStep (G := upd G t g) (rY := rY) (m := m) (m' := m) (t := t) (p := .w1)
    (q := .away) (h := rnil) rfl
    ⟨.inl ⟨.inl (by rw [upd_self]; exact hgo), .inr ⟨rfl, rfl⟩⟩, rfl, .same,
      .inl ⟨rfl, by rw [upd_self, hg]; trivial⟩⟩
    hU hwL hY
  rw [upd_self, upd_upd, set_of hg] at this
  exact this (hI.relabel (fun u hu => by rw [upd_ne _ _ hu, upd_ne _ _ hu])
    (by rw [upd_self, upd_self, hE.ph_l])
    (fun _ => .inr (.inr ⟨by rw [upd_self, hE.ph_l]; exact hg, by rw [upd_self, L.ph_set]⟩))
    (fun h => by rw [upd_self] at h ⊢; exact (hE.role_l true _ _ _).mpr h)
    (fun h => by rw [upd_self] at h ⊢; exact (hE.role_l false _ _ _).mpr h))

/-- The waiter asleep at `w1` is not in a deadlock: a set event's (`Fits.liveSet`), or by the
client's `hlive`. -/
theorem waitLive (hE : L.Fits (E.prim L) P U ok) (hg : E.ph g = .w1)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁) (G₁ : ThreadId → γ) (m₁ : Mem) (hg₁ : G₁ t = L.set g .away rnil)
    (hi₁ : P.inv G₁ m₁) : P.Live t G₁ m₁ := by
  have hga : E.ph (L.set g .away rnil) = .w1 := by rw [hE.ph_l]; exact hg
  by_cases hs : E.IsSet m₁
  · obtain ⟨rX, hL, hU⟩ := (hE.inv _ _).mp hi₁
    exact hE.liveSet (hE.wInv _ _ _ hU) hL (by rw [hg₁]; exact hga) hs
  · exact hlive G₁ m₁ (by rw [hg₁]; exact hga) (by rw [hg₁, L.ph_set]) hi₁ hs

/-- The waiter at `w1` sleeps: the word held `waiting`. -/
theorem waitSleep (hE : L.Fits (E.prim L) P U ok) {e : BitVec 32} (he : e = 1)
    (hg : E.ph g = .w1) (G₁ : ThreadId → γ) (rY : Res) (m₁ M : Mem)
    (hg₁ : G₁ t = L.set g .away rnil) (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁)
    (hwL : L.WInv (L.pl G₁) m₁)
    (hY : ∀ l, E.W.In l → rY.heap l = none) (_ : m₁.woken.contains t = false)
    (_ : m₁.waiters.any (·.1 == t) = false)
    (hw₀ : E.W.Ok { m₁ with current := t } (fun u => E.Live (G₁ u))) (hct : t < m₁.clocks.size)
    (hrecord : M = ({ m₁ with current := t } : Mem).recordAt E.W.b E.W.o 4 .atomicRead)
    (hf : M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg)
    (hh : E.W.hist M = E.W.hist m₁) (_ : E.W.Ok M (fun u => E.Live (G₁ u)))
    (hbl : M.blocks = m₁.blocks) (hU32 : E.W.Holds m₁ e) :
    U G₁ (rsum (E.W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, E.W.ptr) } := by
  have hop : FStepIn (fun _ => none) { m₁ with current := t } M := by
    rw [hrecord]
    exact Word.record_fstep hw₀ hct (fun _ _ _ => rfl)
  have hga : E.ph (L.set g .away rnil) = .w1 := by rw [hE.ph_l]; exact hg
  have hgq : ∀ q, L.set (E.set (L.set g .away rnil) .w1) q rnil = L.set g q rnil := fun q => by
    rw [set_of hga, L.set_set]
  have hI := hE.wInv _ _ _ hU
  have hw₁ := ((hE.wRest rfl) _ _ _ hU).1
  have hv : (E.newest m₁).Val (1 : BitVec 32) := by rw [he] at hU32; exact hw₁.holds_last.mp hU32
  have hst := hE.wStep (G := G₁) (rY := rY) (m := m₁) (t := t) (p := .w1) (q := .away)
    (h := rnil) rfl ⟨.inl ⟨.inr ⟨by rw [hg₁, L.ph_set], by rw [hg₁]; exact hga⟩, .inr ⟨rfl, rfl⟩⟩,
      rfl, .sleep (hw₀.single (hI.live (by rw [hg₁, hga]; exact .inr rfl))) hct hwL.csize hrecord hh,
      .inl ⟨hh, by rw [hg₁, hga]; trivial⟩⟩ hU hwL hY
  rw [hg₁, hgq, ← hg₁, upd_same, Word.cellsR_congr (W := E.W) (show
    ({ M with waiters := M.waiters.push (t, E.W.ptr) } : Mem).blocks = m₁.blocks from hbl)] at hst
  exact hst (hI.sleep (by rw [hg₁]; exact hga) hop.clock hop.waiters
    (Nat.le_of_eq (by rw [hop.threads])) hh hv
    (hI.fresh.of_eq hf.1 (Nat.le_of_eq hf.2.2.symm)))

/-- The kernel's compare at the word (`Os.futexWord`, an atomic read) by the waiter at `w1`, out
of the lock's code: it stays at `w1`. -/
theorem waitCompare (hE : L.Fits (E.prim L) P U ok) (hg : E.ph g = .w1) (hgo : L.ph g = .out)
    (G₁ : ThreadId → γ) (rY : Res) (m₁ m' : Mem) (hg₁ : G₁ t = g)
    (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁) (hwL : L.WInv (L.pl G₁) m₁)
    (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hh : E.W.hist m' = E.W.hist m₁) (hms : E.MStep t m₁ m')
    (hA : ∀ hF, (∀ x, E.W.o ≤ x → x < E.W.o + 4 → hF (E.W.b, x) = none) →
      FStepIn hF m₁ m')
    (hS : E.W.Fresh m₁ → E.W.Fresh m' ∧ ∀ u, E.W.ownPos m₁ u ≤ E.W.ownPos m' u)
    (hL : L.Inv G₁ (rsum (E.W.cellsR m') rY) m') : P.inv G₁ m' := by
  have hop := hA (fun _ => none) (fun _ _ _ => rfl)
  obtain ⟨hI, -, -⟩ := hE.atWord (.inl (by rw [hg₁]; exact hgo)) hU hop.waiters hL
  have := hE.backOut (p := .w1) hg₁ (.inl hgo) hU hwL hY hms (.inl ⟨hh, by rw [hg]; trivial⟩) hL (by
    rw [set_of hg, ← hg₁, upd_same]
    exact hI.frame (t := t) (fun _ _ => rfl) rfl rfl hh hop.waiters hop.clock
      (Nat.le_of_eq (by rw [hop.threads])) id id
      (hS hI.fresh).1)
  rwa [set_of hg, ← hg₁, upd_same] at this

/-- An interrupt's delivery (`Os.takeInterrupt`) by the current thread `t`, out of the lock's code,
keeps the protocol's invariant (`Fits.wOs`). -/
theorem waitOs (hE : L.Fits (E.prim L) P U ok) (hgo : L.ph g = .out) (G₁ : ThreadId → γ)
    (m₁ : Mem) (o : OsState) (hg₁ : G₁ t = g) (hc : m₁.current = t) (hi : P.inv G₁ m₁) :
    P.inv G₁ { m₁ with os := o } :=
  hE.wOs rfl (fun G' m' o' hI => hI.frame (t := t) (m' := { m' with os := o' })
     (fun _ _ => rfl) rfl rfl rfl rfl (fun _ => VClock.le_refl _) (Nat.le_refl _) id id hI.fresh)
    (show L.ph (G₁ t) = .out by rw [hg₁]; exact hgo) hc hi o

/-- The waiter is back at `w1`, out of the lock's code: after the kernel's read, a wake that was
pending, or a spurious return. -/
theorem waitBack (hE : L.Fits (E.prim L) P U ok) (hg : E.ph g = .w1) (hgo : L.ph g = .out)
    (hheld : L.held g = rnil) (G₁ : ThreadId → γ) (rY : Res) (m₁ M : Mem)
    (hg₁ : G₁ t = L.set g .away rnil) (hU : U G₁ (rsum (E.W.cellsR m₁) rY) m₁)
    (hwL : L.WInv (L.pl G₁) m₁)
    (hY : ∀ l, E.W.In l → rY.heap l = none) (_ : m₁.waiters.any (·.1 == t) = false)
    (hf : M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg)
    (hM : M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
      (E.W.Ok { m₁ with current := t } (fun u => E.Live (G₁ u)) ∧ t < m₁.clocks.size ∧
        M = ({ m₁ with current := t } : Mem).recordAt E.W.b E.W.o 4 .atomicRead ∧
        E.W.hist M = E.W.hist m₁ ∧ E.W.Ok M (fun u => E.Live (G₁ u)) ∧ M.blocks = m₁.blocks)) :
    U (upd G₁ t g) (rsum (E.W.cellsR m₁) rY) M := by
  have hga : E.ph (L.set g .away rnil) = .w1 := by rw [hE.ph_l]; exact hg
  have hms : E.MStep t m₁ M := by
    rcases hM with rfl | rfl | ⟨hw₀, hct, hr, hh, -, _⟩
    · exact .woken
    · exact .resume
    · exact .op (hw₀.single ((hE.wInv _ _ _ hU).live (by rw [hg₁, hga]; exact .inr rfl))) hct
        hwL.csize (.inr (.inr (.inr (.inr hr)))) (.inl hh)
  have hwait : M.waiters = m₁.waiters := by
    rcases hM with rfl | rfl | ⟨_, _, hr, _, _, _⟩
    · rfl
    · rfl
    · rw [hr]; rfl
  have hclk := hms.clocks
  have hgq : ∀ q, L.set (E.set (L.set g .away rnil) .w1) q rnil = L.set g q rnil := fun q => by
    rw [set_of hga, L.set_set]
  have hgo' : L.set g .out rnil = g := by
    have := L.set_self g; rwa [hgo, hheld] at this
  · have hI := hE.wInv _ _ _ hU
    have hbl : M.blocks = m₁.blocks := by
      rcases hM with rfl | rfl | ⟨-, -, -, -, -, hb⟩
      · rfl
      · rfl
      · exact hb
    have hst := hE.wStep (G := G₁) (rY := rY) (m := m₁) (m' := M) (t := t) (p := .w1)
      (q := .out) (h := rnil) rfl
        ⟨.inl ⟨.inr ⟨by rw [hg₁, L.ph_set], by rw [hg₁]; exact hga⟩, .inl rfl⟩, rfl, ?_, ?_⟩ hU hwL hY
    · rw [hg₁, hgq, hgo'] at hst
      rw [Word.cellsR_congr (W := E.W) hbl] at hst
      refine hst (hI.move (G' := upd G₁ t g) (fun u hu => upd_ne _ _ hu) ?_ ?_ ?_
        (Nat.le_of_eq (by rw [hms.threads])) (by rw [upd_self, hg₁, hga, hg]; exact id) (by rw [upd_self, hg]; intro h; cases h)
        (fun _ => ?_) (by rw [hg₁, hga, upd_self, hg])
        (fun _ => .inl (by rw [upd_self]; exact hgo))
        (fun w hw e => ⟨fun _ => hI.qw w hw (by rw [e, hg₁]; exact hga),
          fun hp => by rw [upd_self]; exact hg⟩)
        (fun h => by rw [upd_self]; rw [hg₁] at h; exact (hE.role_l true _ _ _).mp h)
        (fun h => by rw [upd_self, hg] at h; rcases h with h | h <;> cases h)
        (hI.fresh.of_eq hf.1 (Nat.le_of_eq hf.2.2.symm)))
      · exact Word.hist_congr hf.1 hbl
      · exact hwait
      · exact hclk
      · obtain ⟨i, hi, hv, hc⟩ := hI.seen t (by rw [hg₁]; exact hga)
        refine ⟨i, hi, hv, VClock.le_trans hc ?_⟩
        exact hclk t
    · exact hms
    · exact .inl ⟨Word.hist_congr hf.1 hbl, by rw [hg₁, hga]; trivial⟩

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
    P.WP t ((futexWaitC io E.W.ptr e : CM Tgt σ Unit).run s) Q G m n :=
  FLock.wp_wordWait hE (hE.wRest rfl) (hE.wAp rfl) hgo hi (waitAway hE hg hgo G · m)
    (waitLive hE hg hlive) (waitSleep hE he hg) (waitBack hE hg hgo (hE.heldOut hgo hi)) h
    (hlv := hE.live_l.mpr (hE.liveWaiter hi (.inr hg)))

/-- **The waiter's untimed OS futex wait** (`Os.futexWait`, OSF-01; std's translated
`Thread.Futex.wait`) at the word with the value `waiting`, at `w1`, the current thread: it goes on
at `w1` with a result other than `timedOut`. A set event's sleeper is not in a deadlock
(`Fits.liveSet`); for an event that is not set, the client shows it (`hlive`). -/
theorem wp_osWait (hE : L.Fits (E.prim L) P U ok) {e : BitVec 32} (he : e = 1)
    (hg : E.ph g = .w1) (hgo : L.ph g = .out) (hc : m.current = t) (hi : P.inv (upd G t g) m)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    {Q : Os.WaitResult → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ d, d < n → ∀ r G₁ m', m'.current = t → r ≠ .timedOut → P.inv (upd G₁ t g) m' →
      Q r G₁ m' d)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Os.futexWait E.W.ptr e false : ConcM Tgt Os.WaitResult) Q G m n :=
  FLock.wp_wordOsWait hE (hE.wRest rfl) (hE.wAp rfl) hgo hc hi (waitOs hE hgo)
    (hlv := hE.liveWaiter hi (.inr hg)) (hlva := hE.live_l.mpr (hE.liveWaiter hi (.inr hg)))
    (fun G₁ rY m₁ m' hg₁ hc₁ hU hwL hY hh _ hw₀ hct hrun hA hS hL =>
      waitCompare hE hg hgo G₁ rY m₁ m' hg₁
        hU hwL hY hh (by
        refine .op (by rw [FEvent.cur_eq hc₁]; exact hw₀.single (hg₁ ▸ hE.liveWaiter hi (.inr hg)))
          hct hwL.csize ?_ (.inl hh)
        rw [FEvent.cur_eq hc₁]
        exact (by rcases hrun with ⟨c, v, hr⟩; exact .inl ⟨c, _, _, hr⟩)) hA hS hL) (waitAway hE hg hgo) (waitLive hE hg hlive) (waitSleep hE he hg)
    (waitBack hE hg hgo (hE.heldOut hgo hi)) h

/-- **The setter's OS futex wake** (`Os.futexWake`, OSF-02; std's translated `Thread.Futex.wake`)
of up to `w ≥ 1` waiters (or all) at the word, at `sw`: after a wake it is done (`sd`; the event
is set);
after a spurious `EINTR` (macOS; nobody woken) it is still at `sw` (std wakes again). -/
theorem wp_osWake (hE : L.Fits (E.prim L) P U ok) {w : Option Nat}
    (hw : ∀ k, w = some k → 1 ≤ k) {spurious : Bool} (hg : E.ph g = .sw)
    (hgo : L.ph g = .out ∨ L.ph g = .gone)
    (hi : P.inv (upd G t g) m) {Q : Option Nat → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ r G₁ m', m'.current = t →
      ((∃ j, r = some j) ∧ E.IsSet m' ∧ P.inv (upd G₁ t (E.set g .sd)) m' ∨
       spurious = true ∧ r = none ∧ P.inv (upd G₁ t g) m') → Q r G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Os.futexWake E.W.ptr w spurious : ConcM Tgt (Option Nat)) Q G m n :=
  FLock.wp_wordOsWake hE (hE.wAp rfl) hi fun k hk G₁ rX m₁ hg₁ hU hwL =>
    ⟨fun cs m' hr hL => by
      obtain ⟨c, hc, hr'⟩ := Os.futexWake_pos (m := { m₁ with current := t }) hw hr
      obtain ⟨h1, h2, h3⟩ := hE.afterWake hg₁ hg hgo hc hU hwL hr' hL
      exact h k hk _ G₁ m' h1 (.inl ⟨⟨_, rfl⟩, h2, h3⟩),
     fun hs hic => h k hk none G₁ _ rfl (.inr ⟨hs, rfl, hic⟩)⟩

/-- The native event reconstruction shared by ordinary and cur-aware caller-part steps.
The native producer retains the ACTUAL complete rest, word history and ownership. -/
private theorem liftPartPost (hE : L.Fits (E.prim L) P U ok) {rY r' : Res} {m' : Mem}
    (hgo : L.ph g = .out) (hc : m.current = t)
    (hU : U (upd G t g) (rsum (E.W.cellsR m) rY) m)
    (hL : L.Inv (upd G t g) (rsum (E.W.cellsR m) rY) m)
    (hY : ∀ l, E.W.In l → rY.heap l = none)
    (hs : FStepIn (rsum (L.wordR m) (rsum (E.W.cellsR m) rY)).heap.erase m m')
    (hcW : ∀ l, E.W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm)
    (hw' : E.W.Ok m' (fun u => E.Live (upd G t g u))) (hh : E.W.hist m' = E.W.hist m)
    (hL' : L.Inv (upd G t (L.setPart g r')) (rsum (E.W.cellsR m') rY) m') :
    P.inv (upd G t (L.setPart g r')) m' := by
  have hw := ((hE.wRest rfl) _ _ _ hU).1
  have hwF : ∀ x, E.W.o ≤ x → x < E.W.o + 4 →
      (rsum (L.wordR m) (rsum (E.W.cellsR m) rY)).heap.erase (E.W.b, x) ≠ none := by
    intro x h1 h2
    have := cellsAt_some (W := E.W.In) (l := (E.W.b, x)) ⟨rfl, h1, h2⟩
      (hw.cellIn ⟨rfl, h1, h2⟩) (m := m)
    simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
      Option.or_eq_none_iff, not_and]
    intro _ h; exact absurd h this
  have hI' : E.Inv L (upd G t (L.setPart g r')) m' :=
    (hE.wInv _ _ _ hU).frame (t := t) (fun u hu => by rw [upd_ne _ _ hu, upd_ne _ _ hu])
      (by rw [upd_self, upd_self, hE.ph_part]) (by rw [upd_self, upd_self, L.ph_setPart])
      hh hs.waiters hs.clock (Nat.le_of_eq (by rw [hs.threads]))
      (fun h => by rw [upd_self] at h ⊢; exact (hE.role_part true _ _).mpr h)
      (fun h => by rw [upd_self] at h ⊢; exact (hE.role_part false _ _).mpr h)
      ((hE.wInv _ _ _ hU).fresh.fstep hs hwF (fun i l hl => (hw.loc i l hl).1))
  have hU' := hE.wOwn (G := upd G t g) (t := t) (r := r') rfl
    (by rw [upd_self]; exact hgo) hU hL hY hc hs hcW hw' hh
    (by rw [upd_self, upd_upd]; exact hL') (by rw [upd_self, upd_upd]; exact hI')
  rw [upd_self, upd_upd] at hU'
  exact (hE.inv _ _).mpr ⟨_, hL', hU'⟩

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
    (fun a m' r' rY hr hq hc' hU hL hY hs hcW hw' hh hL' => by
      exact h a m' r' hr hq hc' hh (liftPartPost hE hgo hc hU hL hY hs hcW hw' hh hL')) hret

/-- A cur-aware local step on the event caller's actual part. The same native reconstruction
handles ordinary and stack-budgeted steps; cur is removed before the invariant is returned. -/
theorem wp_liftPartCur (hE : L.Fits (E.prim L) P U ok) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple (Pa ⋆ cur t) x (fun a => Qa a ⋆ cur t)) (hp : Pa (L.part g))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      E.W.hist m' = E.W.hist m → P.inv (upd G t (L.setPart g r')) m' → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns (Pa ⋆ cur t) x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n :=
  FLock.wp_liftPartWCur hE (hE.wRest rfl) (.inl hgo) hi hc htt hp
    (fun a m' r' rY hr hq hc' hU hL hY hs hcW hw' hh hL' => by
      exact h a m' r' hr hq hc' hh (liftPartPost hE hgo hc hU hL hY hs hcW hw' hh hL')) hret

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

/-- The cur-aware caller-part rule for a generated `liftM` step. -/
theorem wp_liftPartCurM (hE : L.Fits (E.prim L) P U ok) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple (Pa ⋆ cur t) x (fun a => Qa a ⋆ cur t)) (hp : Pa (L.part g))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      E.W.hist m' = E.W.hist m → P.inv (upd G t (L.setPart g r')) m' → Q (a, s) G m' n)
    (hret : P.Partial ∨ FTTReturns (Pa ⋆ cur t) x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((liftM x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (wp_liftPartCur hE hgo hi hc htt hp (fun a m' r' hr hq hc' hh hi' =>
    WP.pure' (h a m' r' hr hq hc' hh hi')) hret)

end FEvent

/-- **An event implementation** in generated code: its `wait` and `set`, with the rules that a
client uses, for every protocol that has the event next to a lock (`L.Fits (E.prim L) P U ok`)
and counts no turns.

- `wait_wp`: a thread out of the event's and the lock's code, with a ghost value that may wait
  (`FEvent.wx`), that waits returns when the event is set. It enters only as the only waiter (no
  other thread at `w0`/`w1`), after every `waiting` write (`hone`, `hhb`; the scope of the module
  doc), and the client shows
   that its sleep at an event that is not set is not a deadlock (`hlive`). The implementation
   proves its actual caller-resource admission, including owned stack room when it keeps a
   deadline block. A Plain caller has a permanent exact-part specialization; unmetered alone
   neither supplies stack room nor bounds retries. The waiter returns synchronized with a set
   (`FEvent.Synced`: it read an `is_set` write with acquire), so what happened before the set
   happened before the waiter's next step: a set that writes orders memory, not only control.
- `set_wp`: a thread out of the event's code, with a ghost value that may set (`FEvent.sx`), that
   sets it returns with the event set, done (`sd`), and its exact caller part, whatever that part
   holds. Its steps are the event's (`FEvent.prim`, `FEvent.Next`): at most one write, a release
   `is_set` from `out`, so a client that tracks a clock below the setter's sees it in that write
   (the write's `clock`, below its release clock: `Inv.rel`) and, with `Inv.synced_first`, below
   the waiter's after its `wait`. A set that finds the event set already (0.15.2's peek,
   `Fits.doneSet`) writes nothing: a client with several setters shows which write is the first.
   To set or wait again, the client moves the thread from `sd` back to `out` by its own ghost
   step (`Inv.toOut`), which puts it in the word's live set again (`FEvent.Live`). The setter is out of the lock's code, or it left the lock for
   good (`gone`: a task after its last access to the lock's resource, a detached thread). `set`
   ticks in no implementation (`Io.Event` and `Thread.ResetEvent`: a store and a futex wake), so
   the contract demands no caller resource, as `MutexImpl.unlock_wp`.

`wait_wp_resource` states caller parts the same way as the mutex and condition (`LockRules`,
"Caller parts of composite operations"). Its post is about the actual caller part, not an
assertion implicitly closed under adding or removing resources. -/
structure EventImpl (Tgt : Type) where
  wait : Ptr → Io → ConcM Tgt Unit
  set : Ptr → Io → ConcM Tgt Unit
  wait_pre : ThreadId → FAssn
  wait_post : ThreadId → Res → FAssn
  wait_plain_pre : ∀ (t : ThreadId) (r : Res), r.Plain → wait_pre t r
  wait_plain_post : ∀ (t : ThreadId) (r r' : Res), r.Plain → wait_post t r r' → r' = r
  wait_wp_resource : ∀ {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, L.Fits (E.prim L) P U ok →
    P.cost = none → ∀ {p : Ptr}, p = E.W.ptr → ∀ (t : ThreadId) (g : γ), E.ph g = .out →
    L.ph g = .out → E.wx g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat),
    (∀ u, u ≠ t → ¬ (E.ph (G u)).Waiting) →
    (∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true) →
    (∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁) →
    wait_pre t (L.part g) → P.inv (upd G t g) m →
    P.WP t (wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      E.Synced t m' ∧ ∃ r', wait_post t (L.part g) r' ∧ P.inv (upd G' t (L.setPart g r')) m')
      G m d
  set_wp : ∀ {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, L.Fits (E.prim L) P U ok →
    P.cost = none → ∀ {p : Ptr}, p = E.W.ptr → ∀ (t : ThreadId) (g : γ), E.ph g = .out →
    (L.ph g = .out ∨ L.ph g = .gone) → E.sx g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat),
    P.inv (upd G t g) m →
    P.WP t (set p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      P.inv (upd G' t (E.set g .sd)) m') G m d

namespace EventImpl

/-- The exact-part wait rule for a concrete Plain caller, derived from the implementation's
actual endpoint entailments. Its intermediate deadline/stack resources remain genuine. -/
theorem wait_wp (I : EventImpl Tgt) {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}
    (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = E.W.ptr)
    (t : ThreadId) (g : γ) (hg : E.ph g = .out) (hgo : L.ph g = .out) (hwx : E.wx g)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → ¬ (E.ph (G u)).Waiting)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ →
      ¬ E.IsSet m₁ → P.Live t G₁ m₁)
    (hplain : (L.part g).Plain) (hi : P.inv (upd G t g) m) :
    P.WP t (I.wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ E.IsSet m' ∧
      E.Synced t m' ∧ P.inv (upd G' t g) m') G m d := by
  refine WP.mono ?_ (I.wait_wp_resource hE hcost hp t g hg hgo hwx io G m d
    hone hhb hlive (I.wait_plain_pre t (L.part g) hplain) hi)
  rintro _ G' m' d' ⟨hd, hc, hset, hsy, r', hr, hi'⟩
  have he := I.wait_plain_post t (L.part g) r' hplain hr
  subst r'
  exact ⟨hd, hc, hset, hsy, by simpa only [L.setPart_self] using hi'⟩

end EventImpl

end Full
end Zig
