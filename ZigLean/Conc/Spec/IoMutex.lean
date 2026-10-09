import ZigLean.Conc.Spec.Mutex
import ZigLean.Conc.Spec.FutexToy

/-!
# `std.Io.Mutex` satisfies `MutexSpec` over every futex that satisfies `FutexSpec`

The algorithm of Zig 0.16.0 `std.Io.Mutex` (`lib/std/Io.zig:1587`; `Io.Threaded.mutexLock`/
`mutexUnlock` are the same code without the vtable), with the word `0` (unlocked), `1`
(`locked_once`), `2` (`contended`):

```
lock:    if cmpxchg(0 → 1, acquire) fails with r:
           if r == 2: futexWait(word, 2)
           while xchg(2, acquire) != 0: futexWait(word, 2)
tryLock: cmpxchg(0 → 1, acquire) == null
unlock:  if xchg(0, release) == 2: futexWake(word, 1)
```

`ioMutex Fx` is this code over an abstract futex `Fx` whose memory is the word's value
(`wordView`): every wait has no timeout and is uncancelable (`lockUncancelable`; `lock`'s
`Canceled` belongs to IoSpec, T5).

`ioMutex_spec (hF : FutexSpec wordView Fx) : MutexSpec (ioMutex Fx)`: mutual exclusion,
ownership transfer (the acquire `cmpxchg`/`xchg` adopts the view that `unlock`'s release put in
the word) and no deadlock. The proof uses only the futex contract, so spurious returns,
interrupts and any choice of woken thread are covered. The invariant (`IoInv`) is the abstract
form of `Lock.Inv` of `ZigLean/Conc/Lock.lean`: the word is `0` iff no thread owns the lock; the
free lock's message carries the real value; the threads in the futex queue are asleep in
`lock`; and if the queue is not empty, a thread not in it is **busy** (it will take the lock or
wake a waiter: `Lock.Inv.wit`), so a sleeping waiter is never the last one.

The two clauses of the futex contract that this needs are necessary:
`lazyWake_deadlock` (the wake never wakes) and `noRecheck_deadlock` (the wait sleeps on a
changed word) are runs of two threads that end in a deadlock.
-/

namespace Zig
namespace Spec

/-- The futex's view of the memory: the word at the one address. -/
def wordView (n : Nat) (_ : Unit) : Option (BitVec 32) := some (BitVec.ofNat 32 n)

/-- The places in `Io.Mutex`'s code. -/
inductive IL where
  /-- `lock`'s first `cmpxchg`. -/
  | cas
  /-- `lock`'s `xchg(2)`. -/
  | xchg
  /-- `lock`'s futex wait for `2`, before the futex op. -/
  | wait
  /-- In `lock`'s futex wait: the thread went to sleep. -/
  | asleep
  /-- `tryLock`'s `cmpxchg`. -/
  | attempt
  /-- `unlock`'s `xchg(0)`. -/
  | rel
  /-- `unlock`'s futex wake of one waiter. -/
  | wake
  /-- The op returned `b`. -/
  | fin (b : Bool)
  deriving DecidableEq

/-- The atomic steps of `Io.Mutex`'s code over the futex `Fx`, by thread `t` with view `v`; the
word is `w` and the futex `f`. -/
inductive IoStep (Fx : Futex Nat Unit) {X : Type} (t : Tid) :
    IL → AWord X → Fx.F → X → IL → AWord X × Fx.F → X → Prop
  | casOk {w : AWord X} {f : Fx.F} {v : X} :
      w.val = 0 → IoStep Fx t .cas w f v (.fin true) (⟨1, w.msg⟩, f) w.msg
  | casWait {w : AWord X} {f : Fx.F} {v : X} : w.val = 2 → IoStep Fx t .cas w f v .wait (w, f) v
  | casSpin {w : AWord X} {f : Fx.F} {v : X} :
      w.val ≠ 0 → w.val ≠ 2 → IoStep Fx t .cas w f v .xchg (w, f) v
  | tryOk {w : AWord X} {f : Fx.F} {v : X} :
      w.val = 0 → IoStep Fx t .attempt w f v (.fin true) (⟨1, w.msg⟩, f) w.msg
  | tryFail {w : AWord X} {f : Fx.F} {v : X} :
      w.val ≠ 0 → IoStep Fx t .attempt w f v (.fin false) (w, f) v
  | xchgOk {w : AWord X} {f : Fx.F} {v : X} :
      w.val = 0 → IoStep Fx t .xchg w f v (.fin true) (⟨2, w.msg⟩, f) w.msg
  | xchgWait {w : AWord X} {f : Fx.F} {v : X} :
      w.val ≠ 0 → IoStep Fx t .xchg w f v .wait (⟨2, w.msg⟩, f) w.msg
  | sleep {w : AWord X} {f f' : Fx.F} {v : X} :
      Fx.wait t () 2 false w.val f none f' → IoStep Fx t .wait w f v .asleep (w, f') v
  | back {w : AWord X} {f f' : Fx.F} {v : X} {r : WaitRet} :
      Fx.wait t () 2 false w.val f (some r) f' → IoStep Fx t .wait w f v .xchg (w, f') v
  | resume {w : AWord X} {f f' : Fx.F} {v : X} {r : WaitRet} :
      Fx.resume t false f r f' → IoStep Fx t .asleep w f v .xchg (w, f') v
  | relWake {w : AWord X} {f : Fx.F} {v : X} :
      w.val = 2 → IoStep Fx t .rel w f v .wake (⟨0, v⟩, f) v
  | relDone {w : AWord X} {f : Fx.F} {v : X} :
      w.val ≠ 2 → IoStep Fx t .rel w f v (.fin false) (⟨0, v⟩, f) v
  | wake {w : AWord X} {f f' : Fx.F} {v : X} {k : Nat} :
      Fx.wake t () 1 f k f' → IoStep Fx t .wake w f v (.fin false) (w, f') v

/-- `std.Io.Mutex` over the futex `Fx` (module doc). -/
abbrev ioMutex (Fx : Futex Nat Unit) : MutexImpl where
  Sh X := AWord X × Fx.F
  init x₀ sh := sh.1 = ⟨0, x₀⟩ ∧ Fx.init sh.2
  Loc := IL
  start
    | .lock => .cas
    | .tryLock => .attempt
    | .unlock => .rel
  step t l sh v l' sh' v' := IoStep Fx t l sh.1 sh.2 v l' sh' v'
  done
    | .fin b => some b
    | _ => none

namespace IoPlace

/-- The places that a thread of the most general client can be at. -/
def ok : Ctl IL → Bool
  | .idle | .holds | .run .lock .cas | .run .lock .xchg | .run .lock .wait | .run .lock .asleep
  | .run .lock (.fin true) | .run .tryLock .attempt | .run .tryLock (.fin _) | .run .unlock .rel
  | .run .unlock .wake | .run .unlock (.fin false) => true
  | _ => false

/-- The thread owns the lock. -/
def own : Ctl IL → Bool
  | .holds | .run .lock (.fin true) | .run .tryLock (.fin true) | .run .unlock .rel => true
  | _ => false

/-- The thread is in the code and will take the lock or wake a waiter (if not asleep). -/
def busy : Ctl IL → Bool
  | .run .lock .xchg | .run .lock .wait | .run .lock .asleep | .run .unlock .wake => true
  | _ => false

end IoPlace

open IoPlace

/-- A witness of the futex queue: an owner while the word is `2`, or a busy thread. -/
def WitOk (c : Ctl IL) (w : Nat) : Prop := (own c = true ∧ w = 2) ∨ busy c = true

/-- A witness stays one when ownership is kept and the place was not busy. -/
theorem WitOk.of_own {c c' : Ctl IL} {w : Nat} (ho : own c = true → own c' = true)
    (hb : busy c = false) (h : WitOk c w) : WitOk c' w := by
  rcases h with ⟨h1, h2⟩ | h1
  · exact .inl ⟨ho h1, h2⟩
  · rw [hb] at h1; cases h1

variable {Fx : Futex Nat Unit}

/-- The invariant of `Io.Mutex` (module doc). -/
structure IoInv {X : Type} (s : MState (ioMutex Fx) X) : Prop where
  ok : ∀ t, IoPlace.ok (s.ctl t) = true
  excl : AtMostOne (fun c => own c = true) s.ctl
  bound : s.sh.1.val ≤ 2
  word : s.sh.1.val = 0 ↔ ∀ t, own (s.ctl t) = false
  view : ∀ t, own (s.ctl t) = true → s.cur t = s.val
  msg : (∀ t, own (s.ctl t) = false) → s.sh.1.msg = s.val
  qwf : (Fx.queue s.sh.2).WF
  qloc : ∀ u a, (u, a) ∈ Fx.queue s.sh.2 → s.ctl u = .run .lock .asleep
  wit : Fx.queue s.sh.2 ≠ [] → ∃ v, (Fx.queue s.sh.2).has v = false ∧ WitOk (s.ctl v) s.sh.1.val

namespace IoInv

variable {X : Type} {s : MState (ioMutex Fx) X}

theorem op_ok (hi : IoInv s) {t : Tid} {op : MOp} {l : IL} (h : s.ctl t = .run op l) :
    IoPlace.ok (.run op l) = true := by
  rw [← h]; exact hi.ok t

/-- A thread that is not asleep in `lock` is not in the queue. -/
theorem not_has (hi : IoInv s) {t : Tid} (h : s.ctl t ≠ .run .lock .asleep) :
    (Fx.queue s.sh.2).has t = false :=
  Queue.has_eq_false.mpr fun a ha => h (hi.qloc t a ha)

/-- The owners after thread `t` changed to `c` with the same ownership. -/
theorem own_same (s : MState (ioMutex Fx) X) {t : Tid} {c : Ctl IL} (ho : own c = own (s.ctl t))
    (u : Tid) : own (tset s.ctl t c u) = own (s.ctl u) :=
  congrFun (tset_same own s.ctl t c ho) u

/-- If no thread owns the lock, the word is `0`, and conversely. -/
theorem none_of_zero (hi : IoInv s) (h : s.sh.1.val = 0) : ∀ u, own (s.ctl u) = false :=
  hi.word.mp h

theorem exists_own (hi : IoInv s) (h : s.sh.1.val ≠ 0) : ∃ u, own (s.ctl u) = true := by
  refine Classical.byContradiction fun hn => h (hi.word.mpr fun u => ?_)
  cases hu : own (s.ctl u)
  · rfl
  · exact absurd ⟨u, hu⟩ hn

/-- A step that changes only thread `t`'s place (not asleep before), to one with the same
ownership that is a witness if `t` was one. -/
theorem place (hi : IoInv s) {t : Tid} {c : Ctl IL} (hok : IoPlace.ok c = true)
    (ho : own c = own (s.ctl t)) (hq : s.ctl t ≠ .run .lock .asleep) (hw : WitOk (s.ctl t) s.sh.1.val → WitOk c s.sh.1.val) :
    IoInv { s with ctl := tset s.ctl t c } := by
  have hown := IoInv.own_same s ho
  have hnt := hi.not_has hq
  constructor <;> dsimp only
  · intro u
    by_cases hu : u = t
    · rw [hu, tset_self]; exact hok
    · rw [tset_ne _ _ hu]; exact hi.ok u
  · intro a b ha hb
    (try dsimp only at ha hb)
    rw [hown] at ha hb
    exact hi.excl a b ha hb
  · exact hi.bound
  · simp only [hown]; exact hi.word
  · intro u hu; rw [hown] at hu; exact hi.view u hu
  · intro hn; exact hi.msg fun u => by rw [← hown u]; exact hn u
  · exact hi.qwf
  · intro u a ha
    have hut : u ≠ t := fun e => by
      rw [e] at ha; exact absurd hnt (by rw [Queue.has_eq_true.mpr ⟨a, ha⟩]; simp)
    rw [tset_ne _ _ hut]; exact hi.qloc u a ha
  · intro hne
    obtain ⟨v, hv, hwv⟩ := hi.wit hne
    refine ⟨v, hv, ?_⟩
    by_cases hvt : v = t
    · rw [hvt, tset_self]; rw [hvt] at hwv; exact hw hwv
    · rw [tset_ne _ _ hvt]; exact hwv

/-- `place` for a thread that was not busy. -/
theorem place' (hi : IoInv s) {t : Tid} {c : Ctl IL} (hok : IoPlace.ok c = true)
    (ho : own c = own (s.ctl t)) (hq : s.ctl t ≠ .run .lock .asleep)
    (hb : busy (s.ctl t) = false) : IoInv { s with ctl := tset s.ctl t c } :=
  hi.place hok ho hq (WitOk.of_own (fun h => ho ▸ h) hb)

end IoInv

/-! ## The invariant is inductive -/

theorem bv_two {n : Nat} (hn : n ≤ 2) (h : wordView n () = some 2) : n = 2 := by
  have h' := congrArg BitVec.toNat (Option.some.inj h)
  simp only [BitVec.toNat_ofNat] at h'
  have : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  have h2 : (2 : BitVec 32).toNat = 2 := rfl
  omega

section
variable (hF : FutexSpec wordView Fx)
include hF

theorem ioMutex_init {X : Type} {s : MState (ioMutex Fx) X} (h : (mgc (ioMutex Fx) X).init s) :
    IoInv s := by
  obtain ⟨x₀, ⟨hw, hf⟩, hctl, -, hval⟩ := h
  have hq := hF.init _ hf
  constructor
  · intro t; rw [hctl]; rfl
  · intro a b ha; (try dsimp only at ha); rw [hctl] at ha; cases ha
  · rw [hw]; exact Nat.zero_le _
  · rw [hw]; exact ⟨fun _ t => by rw [hctl]; rfl, fun _ => rfl⟩
  · intro t ht; rw [hctl] at ht; cases ht
  · intro _; rw [hw, hval]
  · rw [hq]; exact Queue.WF.nil
  · intro u a ha; rw [hq] at ha; cases ha
  · intro hne; exact absurd hq hne

theorem ioMutex_step {X : Type} {t : Tid} {s s' : MState (ioMutex Fx) X} (hi : IoInv s)
    (hs : MStep (ioMutex Fx) t s s') : IoInv s' := by
  cases hs with
  | call op hop h =>
    cases op
    · exact hi.place' rfl (by rw [h]; rfl) (by rw [h]; simp) (by rw [h]; rfl)
    · exact hi.place' rfl (by rw [h]; rfl) (by rw [h]; simp) (by rw [h]; rfl)
    · exact absurd rfl hop
  | unlock h =>
    refine hi.place rfl (by rw [h]; rfl) (by rw [h]; simp) fun hw => ?_
    rw [h] at hw
    rcases hw with ⟨-, h2⟩ | h1
    · exact .inl ⟨rfl, h2⟩
    · cases h1
  | write x h =>
    have ht : own (s.ctl t) = true := by rw [h]; rfl
    constructor <;> dsimp only
    · exact hi.ok
    · exact hi.excl
    · exact hi.bound
    · exact hi.word
    · intro u hu
      have := hi.excl u t hu ht; subst this
      simp
    · intro hn; exact absurd (hn t) (by rw [ht]; simp)
    · exact hi.qwf
    · exact hi.qloc
    · exact hi.wit
  | ret h hd =>
    rename_i op l b
    have hok := hi.op_ok h
    cases l with
    | fin b' =>
      cases hd
      cases op <;> cases b <;> try exact absurd hok (by decide)
      all_goals (try simp only [MOp.after, ↓reduceIte, Bool.false_eq_true])
      all_goals exact hi.place' rfl (by rw [h]; rfl) (by rw [h]; simp) (by rw [h]; rfl)
    | _ => cases hd
  | exec h hstep =>
    rename_i op l l' sh' v'
    have hok := hi.op_ok h
    cases hstep with
    | casWait hw | casSpin hw _ | tryFail hw =>
      rw [tset_id]
      cases op <;> try exact absurd hok (by decide)
      all_goals exact hi.place' rfl (by rw [h]; rfl) (by rw [h]; simp) (by rw [h]; rfl)
    | casOk hw | tryOk hw | xchgOk hw =>
      cases op <;> try exact absurd hok (by decide)
      all_goals
        have hno := hi.none_of_zero hw
        have hown : ∀ (c : Ctl IL) u, own (tset s.ctl t c u) = true → u = t := by
          intro c u hu
          refine Classical.byContradiction fun hut => ?_
          rw [tset_ne _ _ hut, hno u] at hu; cases hu
        constructor <;> dsimp only
        · intro u
          by_cases hu : u = t
          · rw [hu, tset_self]; rfl
          · rw [tset_ne _ _ hu]; exact hi.ok u
        · intro a b ha hb; exact (hown _ a ha).trans (hown _ b hb).symm
        · decide
        · exact ⟨fun h => absurd h (by decide), fun h => absurd (h t) (by rw [tset_self]; decide)⟩
        · intro u hu; rw [hown _ u hu, tset_self]; exact hi.msg hno
        · intro hn; exact absurd (hn t) (by rw [tset_self]; decide)
        · exact hi.qwf
        · intro u a ha
          have hut : u ≠ t := fun e => by have hq := hi.qloc u a ha; rw [e, h] at hq; cases hq
          rw [tset_ne _ _ hut]; exact hi.qloc u a ha
        · intro hne
          obtain ⟨v, hv, hwv⟩ := hi.wit hne
          refine ⟨v, hv, ?_⟩
          by_cases hvt : v = t
          · subst hvt; rw [h] at hwv
            rcases hwv with ⟨h1, -⟩ | h1
            · cases h1
            · first | (rw [tset_self]; exact .inl ⟨rfl, rfl⟩) | cases h1
          · rw [tset_ne _ _ hvt]
            rcases hwv with ⟨h1, -⟩ | h1
            · rw [hno v] at h1; cases h1
            · exact .inr h1
    | xchgWait hw =>
      cases op <;> try exact absurd hok (by decide)
      have hown := IoInv.own_same s (t := t) (c := .run .lock .wait) (by rw [h]; rfl)
      obtain ⟨o, ho⟩ := hi.exists_own hw
      constructor <;> dsimp only
      · intro u
        by_cases hu : u = t
        · rw [hu, tset_self]; rfl
        · rw [tset_ne _ _ hu]; exact hi.ok u
      · intro a b ha hb
        (try dsimp only at ha hb)
        rw [hown] at ha hb
        exact hi.excl a b ha hb
      · decide
      · constructor
        · intro h; cases h
        · intro h; have := h o; rw [hown, ho] at this; cases this
      · intro u hu
        rw [hown] at hu
        have hut : u ≠ t := fun e => by rw [e, h] at hu; cases hu
        rw [tset_ne _ _ hut]; exact hi.view u hu
      · intro hn; exact absurd (hn o) (by rw [hown, ho]; simp)
      · exact hi.qwf
      · intro u a ha
        have hut : u ≠ t := fun e => by have hq := hi.qloc u a ha; rw [e, h] at hq; cases hq
        rw [tset_ne _ _ hut]; exact hi.qloc u a ha
      · intro hne
        obtain ⟨v, hv, hwv⟩ := hi.wit hne
        refine ⟨v, hv, ?_⟩
        by_cases hvt : v = t
        · rw [hvt, tset_self]; exact .inr rfl
        · rw [tset_ne _ _ hvt]
          rcases hwv with ⟨h1, -⟩ | h1
          · exact .inl ⟨h1, rfl⟩
          · exact .inr h1
    | sleep hfw =>
      rw [tset_id]
      cases op <;> try exact absurd hok (by decide)
      have hown := IoInv.own_same s (t := t) (c := .run .lock .asleep) (by rw [h]; rfl)
      have hnt := hi.not_has (t := t) (by rw [h]; simp)
      have h2 : s.sh.1.val = 2 := bv_two hi.bound (hF.sleep_word hfw)
      obtain ⟨o, ho⟩ := hi.exists_own (by omega)
      have hot : o ≠ t := fun e => by rw [e, h] at ho; cases ho
      have hmem := hF.mem_wait hfw
      constructor <;> dsimp only
      · intro u
        by_cases hu : u = t
        · rw [hu, tset_self]; rfl
        · rw [tset_ne _ _ hu]; exact hi.ok u
      · intro a b ha hb
        (try dsimp only at ha hb)
        rw [hown] at ha hb
        exact hi.excl a b ha hb
      · exact hi.bound
      · simp only [hown]; exact hi.word
      · intro u hu; rw [hown] at hu; exact hi.view u hu
      · intro hn; exact hi.msg fun u => by rw [← hown u]; exact hn u
      · exact hF.wf_wait hi.qwf hnt hfw
      · intro u a ha
        rcases (hmem (u, a)).mp ha with ha | ⟨-, he⟩
        · have hut : u ≠ t := fun e => by
            rw [e] at ha; exact absurd hnt (by rw [Queue.has_eq_true.mpr ⟨a, ha⟩]; simp)
          rw [tset_ne _ _ hut]; exact hi.qloc u a ha
        · cases he; rw [tset_self]
      · intro _
        refine ⟨o, Queue.has_eq_false.mpr fun a ha => ?_, ?_⟩
        · rcases (hmem (o, a)).mp ha with ha | ⟨-, he⟩
          · have := hi.qloc o a ha; rw [this] at ho; cases ho
          · cases he; exact hot rfl
        · rw [tset_ne _ _ hot]; exact .inl ⟨ho, h2⟩
    | back hfw =>
      rw [tset_id]
      cases op <;> try exact absurd hok (by decide)
      have hown := IoInv.own_same s (t := t) (c := .run .lock .xchg) (by rw [h]; rfl)
      have hnt := hi.not_has (t := t) (by rw [h]; simp)
      have hmem := hF.mem_wait hfw
      constructor <;> dsimp only
      · intro u
        by_cases hu : u = t
        · rw [hu, tset_self]; rfl
        · rw [tset_ne _ _ hu]; exact hi.ok u
      · intro a b ha hb
        (try dsimp only at ha hb)
        rw [hown] at ha hb
        exact hi.excl a b ha hb
      · exact hi.bound
      · simp only [hown]; exact hi.word
      · intro u hu; rw [hown] at hu; exact hi.view u hu
      · intro hn; exact hi.msg fun u => by rw [← hown u]; exact hn u
      · exact hF.wf_wait hi.qwf hnt hfw
      · intro u a ha
        rcases (hmem (u, a)).mp ha with ha | ⟨he, -⟩
        · have hut : u ≠ t := fun e => by
            rw [e] at ha; exact absurd hnt (by rw [Queue.has_eq_true.mpr ⟨a, ha⟩]; simp)
          rw [tset_ne _ _ hut]; exact hi.qloc u a ha
        · cases he
      · intro hne
        have hne' : Fx.queue s.sh.2 ≠ [] := by
          intro he; apply hne
          exact List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
            rcases (hmem x).mp hx with hx | ⟨he', -⟩
            · rw [he] at hx; cases hx
            · cases he'
        obtain ⟨v, hv, hwv⟩ := hi.wit hne'
        refine ⟨v, Queue.has_eq_false.mpr fun a ha => ?_, ?_⟩
        · rcases (hmem (v, a)).mp ha with ha | ⟨he, -⟩
          · exact Queue.has_eq_false.mp hv a ha
          · cases he
        · by_cases hvt : v = t
          · rw [hvt, tset_self]; exact .inr rfl
          · rw [tset_ne _ _ hvt]; exact hwv
    | resume hfr =>
      rw [tset_id]
      cases op <;> try exact absurd hok (by decide)
      have hown := IoInv.own_same s (t := t) (c := .run .lock .xchg) (by rw [h]; rfl)
      have hmem := hF.mem_resume hfr
      constructor <;> dsimp only
      · intro u
        by_cases hu : u = t
        · rw [hu, tset_self]; rfl
        · rw [tset_ne _ _ hu]; exact hi.ok u
      · intro a b ha hb
        (try dsimp only at ha hb)
        rw [hown] at ha hb
        exact hi.excl a b ha hb
      · exact hi.bound
      · simp only [hown]; exact hi.word
      · intro u hu; rw [hown] at hu; exact hi.view u hu
      · intro hn; exact hi.msg fun u => by rw [← hown u]; exact hn u
      · exact hF.wf_resume hi.qwf hfr
      · intro u a ha
        obtain ⟨ha, hut⟩ := (hmem (u, a)).mp ha
        rw [tset_ne _ _ hut]; exact hi.qloc u a ha
      · intro hne
        have hne' : Fx.queue s.sh.2 ≠ [] := by
          intro he; apply hne
          exact List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
            have := ((hmem x).mp hx).1; rw [he] at this; cases this
        obtain ⟨v, hv, hwv⟩ := hi.wit hne'
        refine ⟨v, Queue.has_eq_false.mpr fun a ha => ?_, ?_⟩
        · exact Queue.has_eq_false.mp hv a ((hmem (v, a)).mp ha).1
        · by_cases hvt : v = t
          · rw [hvt, tset_self]; exact .inr rfl
          · rw [tset_ne _ _ hvt]; exact hwv
    | relWake hw =>
      cases op <;> try exact absurd hok (by decide)
      all_goals
        have hot : own (s.ctl t) = true := by rw [h]; rfl
        have hno' : ∀ (c : Ctl IL), own c = false → ∀ u, own (tset s.ctl t c u) = false := by
          intro c hc u
          by_cases hu : u = t
          · rw [hu, tset_self]; exact hc
          · rw [tset_ne _ _ hu]
            cases hb : own (s.ctl u)
            · rfl
            · exact absurd (hi.excl u t hb hot) hu
        have hno := hno' (.run .unlock .wake) rfl
        constructor <;> dsimp only
        · intro u
          by_cases hu : u = t
          · rw [hu, tset_self]; rfl
          · rw [tset_ne _ _ hu]; exact hi.ok u
        · intro a b ha; (try dsimp only at ha); rw [hno a] at ha; cases ha
        · decide
        · exact ⟨fun _ => hno, fun _ => rfl⟩
        · intro u hu; rw [hno u] at hu; cases hu
        · intro _; exact hi.view t hot
        · exact hi.qwf
        · intro u a ha
          have hut : u ≠ t := fun e => by have hq := hi.qloc u a ha; rw [e, h] at hq; cases hq
          rw [tset_ne _ _ hut]; exact hi.qloc u a ha
        · intro hne
          obtain ⟨v, hv, hwv⟩ := hi.wit hne
          refine ⟨v, hv, ?_⟩
          by_cases hvt : v = t
          · subst hvt; rw [h] at hwv
            rcases hwv with ⟨-, h2⟩ | h1
            · first | (rw [tset_self]; exact .inr rfl) | exact absurd h2 hw
            · cases h1
          · rw [tset_ne _ _ hvt]
            rcases hwv with ⟨h1, -⟩ | h1
            · exact absurd (hi.excl v t h1 hot) hvt
            · exact .inr h1
    | relDone hw =>
      cases op <;> try exact absurd hok (by decide)
      all_goals
        have hot : own (s.ctl t) = true := by rw [h]; rfl
        have hno' : ∀ (c : Ctl IL), own c = false → ∀ u, own (tset s.ctl t c u) = false := by
          intro c hc u
          by_cases hu : u = t
          · rw [hu, tset_self]; exact hc
          · rw [tset_ne _ _ hu]
            cases hb : own (s.ctl u)
            · rfl
            · exact absurd (hi.excl u t hb hot) hu
        have hno := hno' (.run .unlock (.fin false)) rfl
        constructor <;> dsimp only
        · intro u
          by_cases hu : u = t
          · rw [hu, tset_self]; rfl
          · rw [tset_ne _ _ hu]; exact hi.ok u
        · intro a b ha; (try dsimp only at ha); rw [hno a] at ha; cases ha
        · decide
        · exact ⟨fun _ => hno, fun _ => rfl⟩
        · intro u hu; rw [hno u] at hu; cases hu
        · intro _; exact hi.view t hot
        · exact hi.qwf
        · intro u a ha
          have hut : u ≠ t := fun e => by have hq := hi.qloc u a ha; rw [e, h] at hq; cases hq
          rw [tset_ne _ _ hut]; exact hi.qloc u a ha
        · intro hne
          obtain ⟨v, hv, hwv⟩ := hi.wit hne
          refine ⟨v, hv, ?_⟩
          by_cases hvt : v = t
          · subst hvt; rw [h] at hwv
            rcases hwv with ⟨-, h2⟩ | h1
            · first | (rw [tset_self]; exact .inr rfl) | exact absurd h2 hw
            · cases h1
          · rw [tset_ne _ _ hvt]
            rcases hwv with ⟨h1, -⟩ | h1
            · exact absurd (hi.excl v t h1 hot) hvt
            · exact .inr h1
    | wake hfk =>
      rw [tset_id]
      cases op <;> try exact absurd hok (by decide)
      have hown := IoInv.own_same s (t := t) (c := .run .unlock (.fin false)) (by rw [h]; rfl)
      have hnt := hi.not_has (t := t) (by rw [h]; simp)
      constructor <;> dsimp only
      · intro u
        by_cases hu : u = t
        · rw [hu, tset_self]; rfl
        · rw [tset_ne _ _ hu]; exact hi.ok u
      · intro a b ha hb
        (try dsimp only at ha hb)
        rw [hown] at ha hb
        exact hi.excl a b ha hb
      · exact hi.bound
      · simp only [hown]; exact hi.word
      · intro u hu; rw [hown] at hu; exact hi.view u hu
      · intro hn; exact hi.msg fun u => by rw [← hown u]; exact hn u
      · exact hF.wf_wake hi.qwf hfk
      · intro u a ha
        have ha := hF.mem_wake hi.qwf hfk ha
        have hut : u ≠ t := fun e => by
          rw [e] at ha; exact absurd hnt (by rw [Queue.has_eq_true.mpr ⟨a, ha⟩]; simp)
        rw [tset_ne _ _ hut]; exact hi.qloc u a ha
      · intro hne
        have hne' : Fx.queue s.sh.2 ≠ [] := by
          intro he; apply hne
          exact List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
            have := hF.mem_wake hi.qwf hfk hx; rw [he] at this; cases this
        obtain ⟨v, hv, hwv⟩ := hi.wit hne'
        by_cases hvt : v = t
        · -- the waker was the witness: a thread that it woke is the new one
          obtain ⟨⟨u, ⟨⟩⟩, hu⟩ := List.exists_mem_of_ne_nil _ hne'
          obtain ⟨-, v', hv', hv'q⟩ := hF.wake_one hi.qwf hfk (Nat.le_refl 1) hu
          have hloc := hi.qloc v' () hv'
          have hv't : v' ≠ t := fun e => by rw [e, h] at hloc; cases hloc
          refine ⟨v', hv'q, ?_⟩
          rw [tset_ne _ _ hv't, hloc]; exact .inr rfl
        · refine ⟨v, Queue.has_eq_false.mpr fun a ha => ?_, ?_⟩
          · exact Queue.has_eq_false.mp hv a (hF.mem_wake hi.qwf hfk ha)
          · rw [tset_ne _ _ hvt]; exact hwv

/-- The invariant of `Io.Mutex` is inductive over every futex that satisfies the contract. -/
theorem ioMutex_inductive (X : Type) : (mgc (ioMutex Fx) X).Inductive IoInv :=
  ⟨fun _ h => ioMutex_init hF h, fun _ _ _ hi hs => ioMutex_step hF hi hs⟩

/-- No deadlock: a thread in `Io.Mutex`'s code that is not asleep in the futex queue can step. -/
theorem ioMutex_enabled {X : Type} {s : MState (ioMutex Fx) X} (hi : IoInv s) {t : Tid}
    {op : MOp} {l : IL} (h : s.ctl t = .run op l) (hq : (Fx.queue s.sh.2).has t = false) :
    (mgc (ioMutex Fx) X).Enabled t s := by
  have ex : ∀ {l' : IL} {sh' : AWord X × Fx.F} {v' : X},
      IoStep Fx t l s.sh.1 s.sh.2 (s.cur t) l' sh' v' → (mgc (ioMutex Fx) X).Enabled t s :=
    fun hs => enabled_exec (I := ioMutex Fx) h hs
  cases l with
  | fin b => exact enabled_ret h rfl
  | cas =>
    by_cases h0 : s.sh.1.val = 0
    · exact ex (IoStep.casOk h0)
    · by_cases h2 : s.sh.1.val = 2
      · exact ex (IoStep.casWait h2)
      · exact ex (IoStep.casSpin h0 h2)
  | attempt =>
    by_cases h0 : s.sh.1.val = 0
    · exact ex (IoStep.tryOk h0)
    · exact ex (IoStep.tryFail h0)
  | xchg =>
    by_cases h0 : s.sh.1.val = 0
    · exact ex (IoStep.xchgOk h0)
    · exact ex (IoStep.xchgWait h0)
  | wait =>
    obtain ⟨r, f', hw⟩ := hF.wait_total t () 2 false s.sh.1.val s.sh.2 _ rfl hq
    cases r with
    | none => exact ex (IoStep.sleep hw)
    | some r => exact ex (IoStep.back hw)
  | asleep =>
    obtain ⟨r, f', hr⟩ := hF.resume_total t false s.sh.2 hq
    exact ex (IoStep.resume hr)
  | rel =>
    by_cases h2 : s.sh.1.val = 2
    · exact ex (IoStep.relWake h2)
    · exact ex (IoStep.relDone h2)
  | wake =>
    obtain ⟨k, f', hk⟩ := hF.wake_total t () 1 s.sh.2 hi.qwf
    exact ex (IoStep.wake hk)

/-- **`std.Io.Mutex` satisfies the mutex contract over every futex that satisfies the futex
contract.** -/
theorem ioMutex_spec : MutexSpec (ioMutex Fx) where
  excl X := (ioMutex_inductive hF X).invariant fun s hi t u ht hu =>
    hi.excl t u (by rw [ht]; rfl) (by rw [hu]; rfl)
  view X := (ioMutex_inductive hF X).invariant fun s hi t ht => hi.view t (by rw [ht]; rfl)
  live X := (ioMutex_inductive hF X).invariant fun s hi ⟨⟨t, op, l, h⟩, hnh, hn⟩ => by
    -- every thread in the code is disabled, so each one is asleep in the queue
    have hall : ∀ u op l, s.ctl u = .run op l → (Fx.queue s.sh.2).has u = true := by
      intro u op l hu
      cases hq : (Fx.queue s.sh.2).has u
      · exact absurd (ioMutex_enabled hF hi hu hq) (hn u op l hu)
      · rfl
    obtain ⟨a, ha⟩ := Queue.has_eq_true.mp (hall t op l h)
    obtain ⟨v, hv, hwv⟩ := hi.wit (List.ne_nil_of_mem ha)
    rcases hwv with ⟨ho, -⟩ | hb
    · cases hc : s.ctl v with
      | idle => rw [hc] at ho; cases ho
      | holds => exact hnh v hc
      | run op' l' => rw [hall v op' l' hc] at hv; cases hv
    · cases hc : s.ctl v with
      | idle => rw [hc] at hb; cases hb
      | holds => exact hnh v hc
      | run op' l' => rw [hall v op' l' hc] at hv; cases hv

end

end Spec
end Zig
