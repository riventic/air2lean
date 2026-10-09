import ZigLean.Conc.Spec.Sys

/-!
# The mutex contract (`MutexSpec`): lock, tryLock, unlock and ownership transfer

What a client of `std.Io.Mutex` (and of `Io.Threaded`'s private `mutexLock`/`mutexUnlock`) may
assume, for every implementation that is proved against it (`docs/thread-specs.md`).

**Views.** The mutex protects a resource whose values have a type `X`. Each thread sees the
resource through its own **view** `cur t : X`; `val : X` (ghost) is the resource's real value.
Views move between threads only through the implementation's shared state: an atomic word
carries a message view (`AWord`), a release write publishes the writer's view in it, an acquire
read adopts it (`AWord.rmw`). This is the abstraction of the RC11 happens-before order of
`ZigLean/Mem/Thread.lean` that matters for a lock: a thread that sees a stale view did not
synchronise with the last writer. A futex op moves no view (`FutexSpec`: no happens-before
edge).

**The most general client** (`mgc I X`). Any number of threads; each one, at any time, is idle,
holds the lock, or runs an op of the implementation `I`:

* an idle thread calls `lock` or `tryLock`; a holder calls `unlock`;
* a holder writes the resource (`write x`: its view and the real value become `x`);
* a thread in an op takes an atomic step of `I` (`I.step`), which may read and change the shared
  state and the thread's view; when the op is done (`I.done`) it returns: `lock` and a
  successful `tryLock` make the thread a holder, `unlock` and a failed `tryLock` make it idle.

**The contract** (`MutexSpec I`), for every resource type `X` and in every reachable state:

| clause | statement |
|---|---|
| `excl` | at most one thread holds the lock |
| `view` | a holder's view is the real value: **ownership transfer** — the thread that returns from `lock` sees every write of the previous holders (the release of `unlock`, the acquire of `lock`) |
| `live` | no deadlock: if a thread runs an op and no thread holds the lock, some thread that runs an op can step |

`view` subsumes `excl` for a resource with two values (two holders cannot both see a write of one
of them) but both are stated. A resource predicate `R` (CSL's lock invariant) follows: in a
client that keeps `R`, the thread that returns from `lock` sees a value satisfying `R`
(`MutexSpec.resource`). `live` is the repo's notion of deadlock freedom (strict mode,
`Conc.Proto.Live`); like it, it does not exclude a livelock, which needs a fairness premise
(THR-09).

`ZigLean/Conc/Spec/MutexToy.lean`: a spin mutex satisfies the contract, and one whose `unlock`
writes with `monotonic` instead of `release` does not. `ZigLean/Conc/Spec/IoMutex.lean`: the
std 0.16.0 `Io.Mutex` satisfies it over every futex that satisfies `FutexSpec`.
-/

namespace Zig
namespace Spec

/-! ## Atomic words that carry views -/

/-- A 32-bit atomic word (its value as a `Nat`) and the view of its newest message. -/
structure AWord (X : Type) where
  val : Nat
  msg : X

namespace AWord

variable {X : Type}

/-- A read-modify-write of `w` by a thread with view `v` that writes `new`: the value read, the
word after it, the thread's view after it. With `acq` the thread adopts the message's view;
with `rel` the new message carries the thread's view, else it keeps the old one (a release
sequence goes on through an RMW). -/
def rmw (acq rel : Bool) (w : AWord X) (v : X) (new : Nat) : Nat × AWord X × X :=
  (w.val, ⟨new, if rel then v else w.msg⟩, if acq then w.msg else v)

end AWord

/-! ## Implementations and the most general client -/

/-- The ops of a mutex. -/
inductive MOp where
  | lock
  | tryLock
  | unlock
  deriving DecidableEq, Repr

/-- A mutex implementation: its shared state for a resource type `X` (atomic words with views,
a futex, …), the threads' places in its code, and its atomic steps. -/
structure MutexImpl where
  Sh : Type → Type
  /-- The shared state at the start, when every view is `x₀`. -/
  init : {X : Type} → X → Sh X → Prop
  Loc : Type
  /-- The place where an op starts. -/
  start : MOp → Loc
  /-- An atomic step of thread `t` at `l` with view `v`: the new place, shared state and view. -/
  step : {X : Type} → Tid → Loc → Sh X → X → Loc → Sh X → X → Prop
  /-- The op at `l` has returned `b`. -/
  done : Loc → Option Bool

/-- What a thread of the most general client is. -/
inductive Ctl (L : Type) where
  | idle
  | holds
  | run (op : MOp) (l : L)
  deriving DecidableEq

/-- What a thread is after op `op` returned `b`. -/
def MOp.after {L : Type} : MOp → Bool → Ctl L
  | .lock, _ => .holds
  | .tryLock, b => if b then .holds else .idle
  | .unlock, _ => .idle

/-- A state of the most general client. -/
structure MState (I : MutexImpl) (X : Type) where
  sh : I.Sh X
  ctl : Tid → Ctl I.Loc
  /-- The threads' views of the resource. -/
  cur : Tid → X
  /-- The real value of the resource (ghost). -/
  val : X

/-- A step of thread `t` of the most general client (module doc). -/
inductive MStep (I : MutexImpl) {X : Type} (t : Tid) : MState I X → MState I X → Prop
  | call {s : MState I X} (op : MOp) (hop : op ≠ .unlock) (h : s.ctl t = .idle) :
      MStep I t s { s with ctl := tset s.ctl t (.run op (I.start op)) }
  | unlock {s : MState I X} (h : s.ctl t = .holds) :
      MStep I t s { s with ctl := tset s.ctl t (.run .unlock (I.start .unlock)) }
  | write {s : MState I X} (x : X) (h : s.ctl t = .holds) :
      MStep I t s { s with cur := tset s.cur t x, val := x }
  | exec {s : MState I X} {op : MOp} {l l' : I.Loc} {sh' : I.Sh X} {v' : X}
      (h : s.ctl t = .run op l) (hs : I.step t l s.sh (s.cur t) l' sh' v') :
      MStep I t s { s with sh := sh', ctl := tset s.ctl t (.run op l'), cur := tset s.cur t v' }
  | ret {s : MState I X} {op : MOp} {l : I.Loc} {b : Bool}
      (h : s.ctl t = .run op l) (hd : I.done l = some b) :
      MStep I t s { s with ctl := tset s.ctl t (op.after b) }

/-- The most general client of `I` with the resource type `X`. -/
abbrev mgc (I : MutexImpl) (X : Type) : Sys where
  St := MState I X
  init s := ∃ x₀, I.init x₀ s.sh ∧ (∀ t, s.ctl t = .idle) ∧ (∀ t, s.cur t = x₀) ∧ s.val = x₀
  step t s s' := MStep I t s s'

/-- A deadlock: a thread runs an op, no thread holds the lock, and no thread that runs an op can
step. -/
def Stuck (I : MutexImpl) {X : Type} (s : MState I X) : Prop :=
  (∃ t op l, s.ctl t = .run op l) ∧ (∀ t, s.ctl t ≠ .holds) ∧
    ∀ t op l, s.ctl t = .run op l → ¬ (mgc I X).Enabled t s

/-- The mutex contract (module doc). -/
structure MutexSpec (I : MutexImpl) : Prop where
  excl : ∀ X, (mgc I X).Invariant fun s => ∀ t u, s.ctl t = .holds → s.ctl u = .holds → t = u
  view : ∀ X, (mgc I X).Invariant fun s => ∀ t, s.ctl t = .holds → s.cur t = s.val
  live : ∀ X, (mgc I X).Invariant fun s => ¬ Stuck I s

/-! ## Lemmas for proofs of implementations -/

/-- At most one thread has `p`. -/
def AtMostOne {β : Type} (p : β → Prop) (f : Tid → β) : Prop := ∀ t u, p (f t) → p (f u) → t = u

theorem AtMostOne.set {β : Type} {p : β → Prop} {f : Tid → β} (h : AtMostOne p f) {t : Tid}
    {c : β} (hc : p c → p (f t) ∨ ∀ u, ¬ p (f u)) : AtMostOne p (tset f t c) := by
  intro a b ha hb
  by_cases hat : a = t <;> by_cases hbt : b = t
  · rw [hat, hbt]
  · rw [hat, tset_self] at ha; rw [tset_ne _ _ hbt] at hb
    rcases hc ha with ht | hn
    · exact hat.trans (h t b ht hb)
    · exact absurd hb (hn b)
  · rw [hbt, tset_self] at hb; rw [tset_ne _ _ hat] at ha
    rcases hc hb with ht | hn
    · exact (h a t ha ht).trans hbt.symm
    · exact absurd ha (hn a)
  · rw [tset_ne _ _ hat] at ha; rw [tset_ne _ _ hbt] at hb
    exact h a b ha hb

/-- A step of the most general client from a state where an op runs is an `exec` or a `ret`. -/
theorem MStep.run_cases {I : MutexImpl} {X : Type} {t : Tid} {s s' : MState I X} {op : MOp}
    {l : I.Loc} (hc : s.ctl t = .run op l) (h : MStep I t s s') :
    (∃ l' sh' v', I.step t l s.sh (s.cur t) l' sh' v' ∧
      s' = { s with sh := sh', ctl := tset s.ctl t (.run op l'), cur := tset s.cur t v' }) ∨
    (∃ b, I.done l = some b ∧ s' = { s with ctl := tset s.ctl t (op.after b) }) := by
  cases h with
  | call _ _ h => rw [hc] at h; cases h
  | unlock h => rw [hc] at h; cases h
  | write _ h => rw [hc] at h; cases h
  | exec h hs => rw [hc] at h; cases h; exact .inl ⟨_, _, _, hs, rfl⟩
  | ret h hd => rw [hc] at h; cases h; exact .inr ⟨_, hd, rfl⟩

/-- A thread in an op whose op is done can return. -/
theorem enabled_ret {I : MutexImpl} {X : Type} {t : Tid} {s : MState I X} {op : MOp} {l : I.Loc}
    {b : Bool} (hc : s.ctl t = .run op l) (hd : I.done l = some b) : (mgc I X).Enabled t s :=
  ⟨_, MStep.ret hc hd⟩

/-- A thread in an op that the implementation can step can step. -/
theorem enabled_exec {I : MutexImpl} {X : Type} {t : Tid} {s : MState I X} {op : MOp}
    {l l' : I.Loc} {sh' : I.Sh X} {v' : X} (hc : s.ctl t = .run op l)
    (hs : I.step t l s.sh (s.cur t) l' sh' v') : (mgc I X).Enabled t s :=
  ⟨_, MStep.exec hc hs⟩

/-- The clients that write only values satisfying `R` and start with one (CSL's lock invariant
`R`, in its simplest discipline). -/
abbrev RClient (I : MutexImpl) (X : Type) (R : X → Prop) : Sys where
  St := MState I X
  init s := (mgc I X).init s ∧ R s.val
  step t s s' := MStep I t s s' ∧ R s'.val

theorem RClient.reach {I : MutexImpl} {X : Type} {R : X → Prop} {s : (RClient I X R).St}
    (hs : (RClient I X R).Reach s) : (mgc I X).Reach s ∧ R s.val := by
  induction hs with
  | init h => exact ⟨.init h.1, h.2⟩
  | step t _ h ih => exact ⟨.step t ih.1 h.1, h.2⟩

/-- **The resource invariant**: in a client that keeps `R`, a holder's view satisfies `R`, so
the thread that returns from `lock` gets the resource with its invariant. -/
theorem MutexSpec.resource {I : MutexImpl} (h : MutexSpec I) {X : Type} (R : X → Prop) :
    (RClient I X R).Invariant fun s => ∀ t, s.ctl t = .holds → R (s.cur t) := by
  intro s hs t ht
  obtain ⟨hm, hR⟩ := RClient.reach hs
  rw [h.view X s hm t ht]; exact hR

end Spec
end Zig
