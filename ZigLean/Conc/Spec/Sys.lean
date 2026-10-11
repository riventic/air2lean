/-!
# Systems of threads and their invariants (the logic of the generic sync specs)

The generic specifications of the sync layer (`FutexSpec`, `MutexSpec`, `EventSpec`,
`WaitGroupSpec`, `CondSpec`; `docs/thread-specs.md`) are stated over an abstract **system**: a
type of global states, the initial states, and the atomic steps of each thread. A proof over
all schedules is an **inductive invariant**: it holds initially and every atomic step of every
thread keeps it. This is the rely–guarantee form of `ZigLean/Conc/Logic.lean` with the global
invariant `Proto.inv` (each thread's steps keep it: the guarantee; the other threads may do any
step that keeps it: the rely), with the ghost values folded into the state.

The specs are independent of `Mem` and of the scheduler: the futex, the memory words and the
threads' views are abstract here, so the concrete OS rows (T2, `codex/thread-os-prims`) and the
translated std code (T3/T5) instantiate them without depending on how the concrete model
evolves.

* `Sys.Reach`: the reachable states; `Sys.Inductive`: an inductive invariant; `Sys.Invariant`:
  a property of every reachable state.
* `Sys.Enabled t s`: thread `t` can take a step. A blocked thread (asleep at a futex) cannot.
-/

namespace Zig
namespace Spec

/-- A thread id (the same `Nat` as `Zig.ThreadId`). -/
abbrev Tid := Nat

/-- The thread map `f` with `x` for thread `t`. -/
def tset {β : Type} (f : Tid → β) (t : Tid) (x : β) : Tid → β :=
  fun u => if u = t then x else f u

@[simp] theorem tset_self {β : Type} (f : Tid → β) (t : Tid) (x : β) : tset f t x t = x := by
  simp [tset]

theorem tset_ne {β : Type} (f : Tid → β) {t u : Tid} (x : β) (h : u ≠ t) : tset f t x u = f u := by
  simp [tset, h]

/-- `p` of the threads after thread `t` changed to `c` with `p c = p (f t)`. -/
theorem tset_same {β γ : Type} (p : β → γ) (f : Tid → β) (t : Tid) (c : β) (h : p c = p (f t)) :
    (fun u => p (tset f t c u)) = fun u => p (f u) := by
  funext u; by_cases hu : u = t
  · rw [hu, tset_self, h]
  · rw [tset_ne _ _ hu]

theorem tset_id {β : Type} (f : Tid → β) (t : Tid) : tset f t (f t) = f := by
  funext u; by_cases hu : u = t
  · rw [hu, tset_self]
  · rw [tset_ne _ _ hu]

/-- A concurrent system: states, initial states and the atomic steps of each thread. -/
structure Sys where
  St : Type
  init : St → Prop
  step : Tid → St → St → Prop

namespace Sys

variable (S : Sys)

/-- The states that a run reaches. -/
inductive Reach : S.St → Prop
  | init {s : S.St} : S.init s → Reach s
  | step {s s' : S.St} (t : Tid) : Reach s → S.step t s s' → Reach s'

/-- An inductive invariant: it holds initially and every step of every thread keeps it. -/
def Inductive (I : S.St → Prop) : Prop :=
  (∀ s, S.init s → I s) ∧ ∀ t s s', I s → S.step t s s' → I s'

/-- A property of every reachable state. -/
def Invariant (P : S.St → Prop) : Prop := ∀ s, S.Reach s → P s

/-- Thread `t` can take a step from `s`. -/
def Enabled (t : Tid) (s : S.St) : Prop := ∃ s', S.step t s s'

variable {S}

theorem Inductive.reach {I : S.St → Prop} (h : S.Inductive I) {s : S.St} (hs : S.Reach s) : I s := by
  induction hs with
  | init hi => exact h.1 _ hi
  | step t _ hst ih => exact h.2 t _ _ ih hst

/-- An inductive invariant that implies `P` proves `P` of every reachable state. -/
theorem Inductive.invariant {I P : S.St → Prop} (h : S.Inductive I) (hP : ∀ s, I s → P s) :
    S.Invariant P :=
  fun _ hs => hP _ (h.reach hs)

/-- One more step of a reachable state. -/
theorem Reach.next {s s' : S.St} (hs : S.Reach s) (t : Tid) (h : S.step t s s') : S.Reach s' :=
  .step t hs h

end Sys

end Spec
end Zig
