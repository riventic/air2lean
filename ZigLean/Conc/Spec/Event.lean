import ZigLean.Conc.Spec.Mutex

/-!
# The event contract (`EventSpec`)

`std.Io.Event` (`lib/std/Io.zig:1766`) and `Io.Threaded`'s vtable-free `eventWait`/`eventSet`
(the `event` of `Threaded.WaitGroup`): a flag that is set once and waited for. Std documents:
"any memory accesses prior to a `set` call are released, so that if this `set` call causes
`isSet` to return `true` or a wait to finish, those tasks will be able to observe those memory
accesses". `reset` is only allowed with no pending wait; it is not part of this contract (the
uses in `Io.Threaded` never reset).

**The most general client** (`emgc I X`). Thread `0` is the producer: while no `set` has been
called it may write the resource (its view and the real value). Only the producer calls `set`;
any thread calls `wait` or `isSet`. A thread that returns from `wait`, or from `isSet` with
`true`, has **got** the event; it may forget it later.

**The contract** (`EventSpec I`):

| clause | statement |
|---|---|
| `view` | a thread that got the event sees the real value: the producer's writes before `set` |
| `live` | no deadlock: once a `set` returned, if a thread waits, some thread in an op can step |

`view` also says that `wait` does not return before `set` (the producer may write a new value
first). `spinEvent_spec`: a word set with a release store and polled with acquire loads
satisfies the contract.
-/

namespace Zig
namespace Spec

/-- The ops of an event. -/
inductive EOp where
  | isSet
  | wait
  | set
  deriving DecidableEq, Repr

/-- A thread of the event's most general client. -/
inductive ECtl (L : Type) where
  | idle
  /-- It got the event (`wait` returned, or `isSet` returned `true`). -/
  | got
  | run (op : EOp) (l : L)
  deriving DecidableEq

/-- What a thread is after op `op` returned `b`. -/
def EOp.after {L : Type} : EOp → Bool → ECtl L
  | .wait, _ => .got
  | .isSet, b => if b then .got else .idle
  | .set, _ => .idle

/-- A state of the event's most general client. -/
structure EState (I : Impl EOp) (X : Type) where
  sh : I.Sh X
  ctl : Tid → ECtl I.Loc
  cur : Tid → X
  val : X
  /-- The producer called `set` (ghost). -/
  called : Bool
  /-- A `set` returned (ghost). -/
  setDone : Bool

/-- A step of thread `t` of the event's most general client (module doc). -/
inductive EStep (I : Impl EOp) {X : Type} (t : Tid) : EState I X → EState I X → Prop
  | write {s : EState I X} (x : X) (h0 : t = 0) (hc : s.called = false) (h : s.ctl t = .idle) :
      EStep I t s { s with cur := tset s.cur t x, val := x }
  | call {s : EState I X} (op : EOp) (hop : op = .set → t = 0) (h : s.ctl t = .idle) :
      EStep I t s { s with
        ctl := tset s.ctl t (.run op (I.start op))
        called := s.called || (op == EOp.set) }
  | forget {s : EState I X} (h : s.ctl t = .got) : EStep I t s { s with ctl := tset s.ctl t .idle }
  | exec {s : EState I X} {op : EOp} {l l' : I.Loc} {sh' : I.Sh X} {v' : X}
      (h : s.ctl t = .run op l) (hs : I.step t l s.sh (s.cur t) l' sh' v') :
      EStep I t s { s with sh := sh', ctl := tset s.ctl t (.run op l'), cur := tset s.cur t v' }
  | ret {s : EState I X} {op : EOp} {l : I.Loc} {b : Bool}
      (h : s.ctl t = .run op l) (hd : I.done l = some b) :
      EStep I t s { s with ctl := tset s.ctl t (op.after b), setDone := s.setDone || (op == EOp.set) }

/-- The event's most general client with the resource type `X`. -/
abbrev emgc (I : Impl EOp) (X : Type) : Sys where
  St := EState I X
  init s := ∃ x₀, I.init x₀ s.sh ∧ (∀ t, s.ctl t = .idle) ∧ (∀ t, s.cur t = x₀) ∧ s.val = x₀ ∧
    s.called = false ∧ s.setDone = false
  step t s s' := EStep I t s s'

/-- A deadlock after a `set` returned: a thread waits and no thread in an op can step. -/
def EStuck (I : Impl EOp) {X : Type} (s : EState I X) : Prop :=
  s.setDone = true ∧ (∃ t l, s.ctl t = .run .wait l) ∧
    ∀ t op l, s.ctl t = .run op l → ¬ (emgc I X).Enabled t s

/-- The event contract (module doc). -/
structure EventSpec (I : Impl EOp) : Prop where
  view : ∀ X, (emgc I X).Invariant fun s => ∀ t, s.ctl t = .got → s.cur t = s.val
  live : ∀ X, (emgc I X).Invariant fun s => ¬ EStuck I s

/-! ## A spin event -/

/-- The places in the spin event's code. -/
inductive EL where
  /-- `isSet`'s acquire load. -/
  | load
  /-- `wait`'s acquire load, repeated until it reads `1`. -/
  | poll
  /-- `set`'s release store of `1`. -/
  | store
  | fin (b : Bool)
  deriving DecidableEq

/-- The atomic steps of the spin event. -/
inductive SpinEStep {X : Type} : EL → AWord X → X → EL → AWord X → X → Prop
  | loadSet {w : AWord X} {v : X} : w.val = 1 → SpinEStep .load w v (.fin true) w w.msg
  | loadUnset {w : AWord X} {v : X} : w.val ≠ 1 → SpinEStep .load w v (.fin false) w v
  | pollSet {w : AWord X} {v : X} : w.val = 1 → SpinEStep .poll w v (.fin true) w w.msg
  | pollUnset {w : AWord X} {v : X} : w.val ≠ 1 → SpinEStep .poll w v .poll w v
  | store {w : AWord X} {v : X} : SpinEStep .store w v (.fin true) ⟨1, v⟩ v

/-- The spin event (module doc). -/
abbrev spinEvent : Impl EOp where
  Sh X := AWord X
  init x₀ w := w = ⟨0, x₀⟩
  Loc := EL
  start
    | .isSet => .load
    | .wait => .poll
    | .set => .store
  step _ l w v l' w' v' := SpinEStep l w v l' w' v'
  done
    | .fin b => some b
    | _ => none

namespace SpinEPlace

/-- The places that a thread can be at. -/
def ok : ECtl EL → Bool
  | .idle | .got | .run .isSet .load | .run .isSet (.fin _) | .run .wait .poll
  | .run .wait (.fin true) | .run .set .store | .run .set (.fin true) => true
  | _ => false

/-- The thread has got the event, or is about to return from a `wait`/`isSet` that read `1`. -/
def seen : ECtl EL → Bool
  | .got | .run .isSet (.fin true) | .run .wait (.fin true) => true
  | _ => false

end SpinEPlace

open SpinEPlace

/-- The invariant of the spin event. -/
structure SpinEInv {X : Type} (s : EState spinEvent X) : Prop where
  ok : ∀ t, SpinEPlace.ok (s.ctl t) = true
  prod : s.cur 0 = s.val
  word : s.sh.val = 1 → s.sh.msg = s.val ∧ s.called = true
  seen : ∀ t, seen (s.ctl t) = true → s.cur t = s.val ∧ s.called = true
  /-- Only the producer runs `set`, after it called it. -/
  setter : ∀ t l, s.ctl t = .run .set l → t = 0 ∧ s.called = true

theorem spinEvent_inductive (X : Type) : (emgc spinEvent X).Inductive SpinEInv := by
  refine ⟨?_, ?_⟩
  · rintro ⟨sh, ctl, cur, val, called, sd⟩ ⟨x₀, hsh, hctl, hcur, hval, hc, -⟩
    dsimp only at hsh hctl hcur hval hc
    subst hsh hval hc
    constructor <;> dsimp only
    · intro t; rw [hctl]; rfl
    · exact hcur 0
    · intro h; cases h
    · intro t ht; rw [hctl] at ht; cases ht
    · intro t l ht; rw [hctl] at ht; cases ht
  · intro t s s' hi hs
    cases hs with
    | write x h0 hc h =>
      subst h0
      constructor <;> dsimp only
      · exact hi.ok
      · simp
      · intro h1; rw [(hi.word h1).2] at hc; cases hc
      · intro u hu; rw [(hi.seen u hu).2] at hc; cases hc
      · exact hi.setter
    | call op hop h =>
      constructor <;> dsimp only
      · intro u
        by_cases hu : u = t
        · rw [hu, tset_self]; cases op <;> rfl
        · rw [tset_ne _ _ hu]; exact hi.ok u
      · exact hi.prod
      · intro h1; obtain ⟨hm, hc⟩ := hi.word h1; exact ⟨hm, by rw [hc]; rfl⟩
      · intro u hu
        have hu' : seen (s.ctl u) = true := by
          by_cases hut : u = t
          · rw [hut, tset_self] at hu; cases op <;> cases hu
          · rwa [tset_ne _ _ hut] at hu
        obtain ⟨hv, hc⟩ := hi.seen u hu'
        exact ⟨hv, by rw [hc]; rfl⟩
      · intro u l hu
        by_cases hut : u = t
        · subst hut; rw [tset_self] at hu; cases hu
          exact ⟨hop rfl, by simp⟩
        · rw [tset_ne _ _ hut] at hu
          obtain ⟨h0, hc⟩ := hi.setter u l hu
          exact ⟨h0, by rw [hc]; rfl⟩
    | forget h =>
      constructor <;> dsimp only
      · intro u
        by_cases hu : u = t
        · rw [hu, tset_self]; rfl
        · rw [tset_ne _ _ hu]; exact hi.ok u
      · exact hi.prod
      · exact hi.word
      · intro u hu
        by_cases hut : u = t
        · rw [hut, tset_self] at hu; cases hu
        · rw [tset_ne _ _ hut] at hu; exact hi.seen u hu
      · intro u l hu
        by_cases hut : u = t
        · rw [hut, tset_self] at hu; cases hu
        · rw [tset_ne _ _ hut] at hu; exact hi.setter u l hu
    | ret h hd =>
      rename_i op l b
      have hok : SpinEPlace.ok (.run op l) = true := by rw [← h]; exact hi.ok t
      cases l with
      | fin b' =>
        cases hd
        constructor <;> dsimp only
        · intro u
          by_cases hu : u = t
          · rw [hu, tset_self]; cases op <;> cases b <;> rfl
          · rw [tset_ne _ _ hu]; exact hi.ok u
        · exact hi.prod
        · exact hi.word
        · intro u hu
          by_cases hut : u = t
          · subst hut
            rw [tset_self] at hu
            have hs : seen (s.ctl u) = true := by
              rw [h]; cases op <;> cases b <;> first | rfl | exact absurd hok (by decide) | cases hu
            exact hi.seen u hs
          · rw [tset_ne _ _ hut] at hu; exact hi.seen u hu
        · intro u l hu
          by_cases hut : u = t
          · rw [hut, tset_self] at hu; cases op <;> cases b <;> cases hu
          · rw [tset_ne _ _ hut] at hu; exact hi.setter u l hu
      | _ => cases hd
    | exec h hstep =>
      rename_i op l l' sh' v'
      have hok : SpinEPlace.ok (.run op l) = true := by rw [← h]; exact hi.ok t
      -- the other threads keep their places and views
      have hother : ∀ u, u ≠ t → seen (tset s.ctl t (.run op l') u) = true →
          tset s.cur t v' u = s.val ∧ s.called = true := by
        intro u hut hu
        rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut]; exact hi.seen u hu
      have hset : ∀ u l₂, tset s.ctl t (.run op l') u = .run .set l₂ → u = 0 ∧ s.called = true := by
        intro u l₂ hu
        by_cases hut : u = t
        · subst hut; rw [tset_self] at hu; cases hu; exact hi.setter u l h
        · rw [tset_ne _ _ hut] at hu; exact hi.setter u l₂ hu
      cases hstep with
      | loadSet h1 | pollSet h1 =>
        obtain ⟨hm, hc⟩ := hi.word h1
        constructor <;> dsimp only
        · intro u
          by_cases hu : u = t
          · rw [hu, tset_self]; cases op <;> first | rfl | exact absurd hok (by decide)
          · rw [tset_ne _ _ hu]; exact hi.ok u
        · by_cases h0 : t = 0
          · subst h0; rw [tset_self]; exact hm
          · rw [tset_ne _ _ (Ne.symm h0)]; exact hi.prod
        · exact hi.word
        · intro u hu
          by_cases hut : u = t
          · subst hut; rw [tset_self]; exact ⟨hm, hc⟩
          · exact hother u hut hu
        · exact hset
      | loadUnset h1 | pollUnset h1 =>
        rw [tset_id]
        constructor <;> dsimp only
        · intro u
          by_cases hu : u = t
          · rw [hu, tset_self]; cases op <;> first | rfl | exact absurd hok (by decide)
          · rw [tset_ne _ _ hu]; exact hi.ok u
        · exact hi.prod
        · exact hi.word
        · intro u hu
          by_cases hut : u = t
          · subst hut; rw [tset_self] at hu
            cases op <;> first | cases hu | exact absurd hok (by decide)
          · rw [tset_ne _ _ hut] at hu; exact hi.seen u hu
        · exact hset
      | store =>
        rw [tset_id]
        cases op <;> try exact absurd hok (by decide)
        obtain ⟨h0, hc⟩ := hi.setter t _ h
        subst h0
        constructor <;> dsimp only
        · intro u
          by_cases hu : u = 0
          · rw [hu, tset_self]; rfl
          · rw [tset_ne _ _ hu]; exact hi.ok u
        · exact hi.prod
        · intro _; exact ⟨hi.prod, hc⟩
        · intro u hu
          by_cases hut : u = 0
          · subst hut; rw [tset_self] at hu; cases hu
          · rw [tset_ne _ _ hut] at hu; exact hi.seen u hu
        · exact hset

/-- No deadlock: a thread in the spin event's code can always step. -/
theorem spinEvent_enabled {X : Type} {s : EState spinEvent X} {t : Tid} {op : EOp} {l : EL}
    (h : s.ctl t = .run op l) : (emgc spinEvent X).Enabled t s := by
  cases l with
  | fin b => exact ⟨_, EStep.ret (I := spinEvent) h rfl⟩
  | load =>
    by_cases hw : s.sh.val = 1
    · exact ⟨_, EStep.exec (I := spinEvent) h (SpinEStep.loadSet hw)⟩
    · exact ⟨_, EStep.exec (I := spinEvent) h (SpinEStep.loadUnset hw)⟩
  | poll =>
    by_cases hw : s.sh.val = 1
    · exact ⟨_, EStep.exec (I := spinEvent) h (SpinEStep.pollSet hw)⟩
    · exact ⟨_, EStep.exec (I := spinEvent) h (SpinEStep.pollUnset hw)⟩
  | store => exact ⟨_, EStep.exec (I := spinEvent) h SpinEStep.store⟩

theorem spinEvent_spec : EventSpec spinEvent where
  view X := (spinEvent_inductive X).invariant fun s hi t ht => (hi.seen t (by rw [ht]; rfl)).1
  live X := fun s _ ⟨_, ⟨t, l, h⟩, hn⟩ => hn t _ l h (spinEvent_enabled h)

end Spec
end Zig
