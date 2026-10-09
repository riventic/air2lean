import ZigLean.Conc.Spec.Mutex

/-!
# A spin mutex that satisfies `MutexSpec`, and one that does not

`spin rel`: one atomic word, `0` (free) or `1` (held).

* `lock`: `cmpxchg(0 → 1)` with acquire, repeated until it succeeds (a spin lock; no futex).
* `tryLock`: one `cmpxchg(0 → 1)` with acquire.
* `unlock`: `xchg(0)`, with release if `rel`, else monotonic.

`spin_spec : MutexSpec (spin true)`: mutual exclusion, ownership transfer and no deadlock (a
spinning thread can always step). `relaxed_not_spec : ¬ MutexSpec (spin false)`: without the
release, the next holder adopts the message of an older `unlock` and does not see the previous
holder's write (a run of two threads, `view` fails). Mutual exclusion alone does not catch
this; the views do.
-/

namespace Zig
namespace Spec

/-- The places in the spin mutex's code. -/
inductive SL where
  | cas
  | attempt
  | rel
  | fin (b : Bool)
  deriving DecidableEq

/-- The atomic steps of the spin mutex (`rel`: `unlock` writes with release). -/
inductive SpinStep {X : Type} (rel : Bool) : SL → AWord X → X → SL → AWord X → X → Prop
  | casOk {w : AWord X} {v : X} : w.val = 0 → SpinStep rel .cas w v (.fin true) ⟨1, w.msg⟩ w.msg
  | casFail {w : AWord X} {v : X} : w.val ≠ 0 → SpinStep rel .cas w v .cas w v
  | tryOk {w : AWord X} {v : X} : w.val = 0 → SpinStep rel .attempt w v (.fin true) ⟨1, w.msg⟩ w.msg
  | tryFail {w : AWord X} {v : X} : w.val ≠ 0 → SpinStep rel .attempt w v (.fin false) w v
  | unlock {w : AWord X} {v : X} :
      SpinStep rel .rel w v (.fin false) ⟨0, if rel then v else w.msg⟩ v

/-- The spin mutex (module doc). -/
abbrev spin (rel : Bool) : MutexImpl where
  Sh X := AWord X
  init x₀ w := w = ⟨0, x₀⟩
  Loc := SL
  start
    | .lock => .cas
    | .tryLock => .attempt
    | .unlock => .rel
  step _ l w v l' w' v' := SpinStep rel l w v l' w' v'
  done
    | .fin b => some b
    | _ => none

namespace SpinPlace

/-- The places that a thread of the most general client can be at. -/
def ok : Ctl SL → Bool
  | .idle | .holds | .run .lock .cas | .run .lock (.fin true) | .run .tryLock .attempt
  | .run .tryLock (.fin _) | .run .unlock .rel | .run .unlock (.fin false) => true
  | _ => false

/-- The thread owns the lock: it holds it, or it is in `lock`/`tryLock` after the successful
`cmpxchg`, or in `unlock` before its `xchg`. -/
def own : Ctl SL → Bool
  | .holds | .run .lock (.fin true) | .run .tryLock (.fin true) | .run .unlock .rel => true
  | _ => false

end SpinPlace

open SpinPlace

/-- The invariant of the spin mutex. -/
structure SpinInv {rel : Bool} {X : Type} (s : MState (spin rel) X) : Prop where
  ok : ∀ t, SpinPlace.ok (s.ctl t) = true
  excl : AtMostOne (fun c => own c = true) s.ctl
  word : (s.sh.val = 0 ∧ ∀ t, own (s.ctl t) = false) ∨ (s.sh.val = 1 ∧ ∃ t, own (s.ctl t) = true)
  view : ∀ t, own (s.ctl t) = true → s.cur t = s.val
  msg : (∀ t, own (s.ctl t) = false) → s.sh.msg = s.val

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

/-- A step that changes only thread `t`'s place, to one with the same ownership, and keeps the
shared state and the views. -/
theorem SpinInv.place {rel : Bool} {X : Type} {s : MState (spin rel) X} (hi : SpinInv s)
    {t : Tid} {c : Ctl SL} (hok : SpinPlace.ok c = true) (ho : own c = own (s.ctl t)) :
    SpinInv { s with ctl := tset s.ctl t c } := by
  have hown : ∀ u, own (tset s.ctl t c u) = own (s.ctl u) := fun u =>
    congrFun (tset_same own s.ctl t c ho) u
  constructor <;> dsimp only
  · intro u
    by_cases hu : u = t
    · rw [hu, tset_self]; exact hok
    · rw [tset_ne _ _ hu]; exact hi.ok u
  · intro a b ha hb
    try dsimp only at ha hb
    rw [hown] at ha hb
    exact hi.excl a b ha hb
  · simp only [hown]; exact hi.word
  · intro u hu; rw [hown] at hu; exact hi.view u hu
  · intro hn; exact hi.msg fun u => by rw [← hown u]; exact hn u

/-- The thread `t` at `l` in op `op`: the pair is one of the places of the code. -/
theorem SpinInv.op_ok {rel : Bool} {X : Type} {s : MState (spin rel) X} (hi : SpinInv s)
    {t : Tid} {op : MOp} {l : SL} (h : s.ctl t = .run op l) : SpinPlace.ok (.run op l) = true := by
  rw [← h]; exact hi.ok t

theorem spin_inductive (rel : Bool) (hrel : rel = true) (X : Type) :
    (mgc (spin rel) X).Inductive SpinInv := by
  refine ⟨?_, ?_⟩
  · rintro ⟨sh, ctl, cur, val⟩ ⟨x₀, hsh, hctl, hcur, hval⟩
    dsimp only at hsh hctl hcur hval
    subst hsh hval
    constructor <;> dsimp only
    · intro t; rw [hctl]; rfl
    · intro a b ha; (try dsimp only at ha); rw [hctl] at ha; cases ha
    · exact .inl ⟨rfl, fun t => by rw [hctl]; rfl⟩
    · intro t ht; rw [hctl] at ht; cases ht
    · intro _; rfl
  · intro t s s' hi hs
    cases hs with
    | call op hop h =>
      refine hi.place ?_ ?_ <;> cases op <;> first | exact absurd rfl hop | (rw [h]; rfl) | rfl
    | unlock h => exact hi.place rfl (by rw [h]; rfl)
    | write x h =>
      have ht : own (s.ctl t) = true := by rw [h]; rfl
      constructor <;> dsimp only
      · exact hi.ok
      · exact hi.excl
      · exact hi.word
      · intro u hu
        have := hi.excl u t hu ht; subst this
        simp
      · intro hn; exact absurd (hn t) (by rw [ht]; simp)
    | ret h hd =>
      rename_i op l b
      have hok := hi.op_ok h
      cases l with
      | fin b' =>
        cases hd
        refine hi.place ?_ ?_ <;> (try rw [h]) <;> cases op <;> cases b <;>
          first | rfl | exact absurd hok (by decide)
      | _ => cases hd
    | exec h hstep =>
      rename_i op l l' sh' v'
      have hok := hi.op_ok h
      cases hstep with
      | casFail hw | tryFail hw =>
        rw [tset_id]
        refine hi.place ?_ ?_ <;> (try rw [h]) <;> cases op <;>
          first | rfl | exact absurd hok (by decide)
      | casOk hw | tryOk hw =>
        have hlk : own (tset s.ctl t (.run op (.fin true)) t) = true := by
          rw [tset_self]; cases op <;> first | rfl | exact absurd hok (by decide)
        have hno : ∀ u, own (s.ctl u) = false := by
          rcases hi.word with ⟨-, hn⟩ | ⟨h1, -⟩
          · exact hn
          · rw [hw] at h1; cases h1
        have hown : ∀ u, own (tset s.ctl t (.run op (.fin true)) u) = true → u = t := by
          intro u hu
          refine Classical.byContradiction fun hut => ?_
          rw [tset_ne _ _ hut, hno u] at hu; cases hu
        constructor <;> dsimp only
        · intro u
          by_cases hu : u = t
          · rw [hu, tset_self]; cases op <;> first | rfl | exact absurd hok (by decide)
          · rw [tset_ne _ _ hu]; exact hi.ok u
        · intro a b ha hb; exact (hown a ha).trans (hown b hb).symm
        · exact .inr ⟨rfl, t, hlk⟩
        · intro u hu; rw [hown u hu, tset_self]; exact hi.msg hno
        · intro hn; exact absurd (hn t) (by rw [hlk]; simp)
      | unlock =>
        have hown0 : own (s.ctl t) = true := by
          rw [h]; cases op <;> first | rfl | exact absurd hok (by decide)
        have hno : ∀ u, own (tset s.ctl t (.run op (.fin false)) u) = false := by
          intro u
          by_cases hu : u = t
          · rw [hu, tset_self]; cases op <;> rfl
          · rw [tset_ne _ _ hu]
            cases hb : own (s.ctl u)
            · rfl
            · exact absurd (hi.excl u t hb hown0) hu
        constructor <;> dsimp only
        · intro u
          by_cases hu : u = t
          · rw [hu, tset_self]; cases op <;> first | rfl | exact absurd hok (by decide)
          · rw [tset_ne _ _ hu]; exact hi.ok u
        · intro a b ha; (try dsimp only at ha); rw [hno a] at ha; cases ha
        · exact .inl ⟨rfl, hno⟩
        · intro u hu; rw [hno u] at hu; cases hu
        · intro _; subst hrel; exact hi.view t hown0

/-- No deadlock: a thread in the spin mutex's code can always step. -/
theorem spin_enabled {rel : Bool} {X : Type} {s : MState (spin rel) X} {t : Tid} {op : MOp}
    {l : SL} (h : s.ctl t = .run op l) : (mgc (spin rel) X).Enabled t s := by
  cases l with
  | fin b => exact enabled_ret h rfl
  | cas =>
    by_cases hw : s.sh.val = 0
    · exact enabled_exec (I := spin rel) h (SpinStep.casOk hw)
    · exact enabled_exec (I := spin rel) h (SpinStep.casFail hw)
  | attempt =>
    by_cases hw : s.sh.val = 0
    · exact enabled_exec (I := spin rel) h (SpinStep.tryOk hw)
    · exact enabled_exec (I := spin rel) h (SpinStep.tryFail hw)
  | rel => exact enabled_exec (I := spin rel) h SpinStep.unlock

theorem spin_spec : MutexSpec (spin true) where
  excl X := (spin_inductive true rfl X).invariant fun s hi t u ht hu =>
    hi.excl t u (by rw [ht]; rfl) (by rw [hu]; rfl)
  view X := (spin_inductive true rfl X).invariant fun s hi t ht => hi.view t (by rw [ht]; rfl)
  live X := fun s _ ⟨⟨t, op, l, h⟩, _, hn⟩ => hn t op l h (spin_enabled h)

/-- An `unlock` without release breaks ownership transfer: thread 0 locks, writes `true`,
unlocks with a monotonic `xchg`; thread 1 locks and sees the initial `false`. -/
theorem relaxed_not_spec : ¬ MutexSpec (spin false) := by
  intro h
  have r0 : (mgc (spin false) Bool).Reach
      (⟨⟨0, false⟩, fun _ => .idle, fun _ => false, false⟩ : MState (spin false) Bool) :=
    .init ⟨false, rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  have r1 := r0.next 0 (MStep.call (I := spin false) .lock (by decide) (by decide))
  have r2 := r1.next 0 (MStep.exec (I := spin false) (op := .lock) (l := .cas) (by decide)
    (SpinStep.casOk (rel := false) (v := false) rfl))
  have r3 := r2.next 0 (MStep.ret (I := spin false) (op := .lock) (l := .fin true) (b := true) (by decide) rfl)
  have r4 := r3.next 0 (MStep.write (I := spin false) true (by decide))
  have r5 := r4.next 0 (MStep.unlock (I := spin false) (by decide))
  have r6 := r5.next 0 (MStep.exec (I := spin false) (op := .unlock) (l := .rel) (by decide)
    (SpinStep.unlock (rel := false)))
  have r7 := r6.next 1 (MStep.call (I := spin false) .lock (by decide) (by decide))
  have r8 := r7.next 1 (MStep.exec (I := spin false) (op := .lock) (l := .cas) (by decide)
    (SpinStep.casOk (rel := false) rfl))
  have r9 := r8.next 1 (MStep.ret (I := spin false) (op := .lock) (l := .fin true) (b := true) (by decide) rfl)
  have := h.view Bool _ r9 1 rfl
  exact absurd this (by decide)

end Spec
end Zig
