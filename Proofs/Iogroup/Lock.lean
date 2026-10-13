import Proofs.Iogroup.Gen
import ZigLean.Sep.Full.Mutex

/-!
# `Io.Mutex` of `examples/iogroup` as a mutex (`MutexImpl`)

The per-item obligation of `Io.Mutex` (Zig 0.16.0's std code) in this program's generated code:
its `lockUncancelable` and `unlock` satisfy the mutex contract (`ZigLean/Sep/Full/Mutex.lean`)
for every protocol that has the lock (`FLock.FitsOn`). The steps are the rules of a lock's code
(`ZigLean/Sep/Full/LockRules.lean`); this file follows the generated control flow only.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FLock

namespace Iogroup

/-- The states of `Io.Mutex`. -/
def mutexS : LockWord.States Io_Mutex_State where
  unl := .unlocked
  one := .locked_once
  two := .contended
  c := 2
  bits0 := rfl
  bits1 := rfl
  bits2 := rfl
  dec0 := rfl
  dec1 := rfl
  dec2 := rfl
  ne01 := by decide
  ne02 := by decide
  ne12 := by decide

namespace IoMutex

variable {γ : Type} {L : FLock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
  {ok : γ → Prop}

/-- `lock`'s loop invariant: thread `t` is at `spin`. -/
def lockInv (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Io_Mutex_lockUncancelableLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t (L.set g .spin rnil)) m

/-- `lock`'s loop ends when thread `t` holds the mutex. -/
def lockPost (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Io_Mutex_lockUncancelableExit × Io_Mutex_lockUncancelableLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) : Prop :=
  r.1 = .br22 ∧ d < D ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

/-- One repeat of `lock`'s loop: `xchg(contended)`; the thread holds the mutex, or it waits at
the futex (a stop, so the depth gets smaller). -/
theorem loop23_body (hP : L.FitsOn P U ok) (hcost : P.cost = none) (hS : mutexS.c = L.c)
    (t : ThreadId) (g : γ)
    (hok : ok g) (D : Nat) (io : Io) (s : Io_Mutex_lockUncancelableLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (h : lockInv P L t g D s G m d) :
    P.WP t ((Io_Mutex_lockUncancelable.loop23 L.ptr io).run s) (fun r G' m' d' =>
      if Io_Mutex_lockUncancelable.again23 r.1 then lockInv P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Mutex_lockUncancelableLocals) => 0) s)
      else lockPost P L t g D r G' m' d') G m d := by
  obtain ⟨hD, -, hi⟩ := h
  unfold Io_Mutex_lockUncancelable.loop23
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (wp_xchgLockOn hP mutexS hS (g := L.set g .spin rnil) (L.ph_set _ _ _)
    ((hP.ok_set _ _ _).mpr hok) hi fun k hk G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, rL, hi₁⟩ | ⟨hr, hi₁⟩
  · simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Mutex_lockUncancelable.again23, Bool.false_eq_true, ↓reduceIte]
    rw [L.set_set] at hi₁
    exact ⟨rfl, by omega, hc₁, rL, hi₁⟩
  · have hne : (r != Io_Mutex_State.unlocked) = true := by simpa [mutexS] using hr
    simp only [StateT.run_pure, pure_bind, hne, ↓reduceIte, StateT.run_bind, bind_assoc]
    rw [L.set_set] at hi₁
    refine WP.bind (wp_waitOn hP mutexS hS (g := L.set g .wait rnil) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Mutex_lockUncancelable.again23, ↓reduceIte]
    rw [L.set_set] at hi₂
    exact ⟨⟨by omega, hc₂, hi₂⟩, .inl (by omega)⟩

/-- `lock` by thread `t` at `out` (`g`): it holds the mutex, with a resource `rL`. -/
theorem lock_wp (hP : L.FitsOn P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr) (hS : L.c = mutexS.c)
    (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (io : Io) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Mutex_lockUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp
  have hS : mutexS.c = L.c := hS.symm
  unfold Io_Mutex_lockUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (wp_casOn hP mutexS hS (g := g) hg hok hi fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  -- the loop, from `spin`
  have hloop : ∀ G₃ m₃ d₃, lockInv P L t g d default G₃ m₃ d₃ →
      P.WP t ((do
          let __do_lift ← loop (Io_Mutex_lockUncancelable.loop23 L.ptr io)
            Io_Mutex_lockUncancelable.again23
          match __do_lift with
          | Io_Mutex_lockUncancelableExit.br22 => pure Io_Mutex_lockUncancelableExit.ret
          | e => pure e : CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit).run
          default)
        (fun a G₄ m₄ d₄ => P.WP t (match a.1 with
          | Io_Mutex_lockUncancelableExit.ret => pure ()
          | _ => throw Error.panic)
          (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
            ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G₄ m₄ d₄)
        G₃ m₃ d₃ := by
    intro G₃ m₃ d₃ h₃
    simp only [StateT.run_bind]
    refine WP.bind (WP.mono ?_ (WP.loop _ _ (lockInv P L t g d) (fun _ => 0) (lockPost P L t g d)
      (loop23_body hP hcost hS t g hok d io) default G₃ m₃ d₃ h₃))
    rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', rL, hi'⟩
    simp only [StateT.run_pure]
    exact WP.pure' (WP.pure' ⟨hd', hc', rL, hi'⟩)
  rcases hcase with ⟨rfl, rL, hi₁⟩ | ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨by omega, hc₁, rL, hi₁⟩)
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    simp only [StateT.run_pure, pure_bind, mutexS, beq_iff_eq, reduceCtorEq, ↓reduceIte]
    exact hloop G₁ m₁ k₁ ⟨by omega, hc₁, hi₁⟩
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    simp only [StateT.run_pure, pure_bind, mutexS, beq_self_eq_true, ↓reduceIte, StateT.run_bind,
      bind_assoc]
    refine WP.bind (wp_waitOn hP mutexS hS (g := L.set g .wait rnil) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    rw [L.set_set] at hi₂
    exact hloop G₂ m₂ k₂ ⟨by omega, hc₂, hi₂⟩

/-- `unlock` by the holder `t` (`g`): it goes to `out`. -/
theorem unlock_wp (hP : L.FitsOn P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr) (hS : L.c = mutexS.c)
    (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (hok : ok g) (io : Io) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Mutex_unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d := by
  subst hp
  have hS : mutexS.c = L.c := hS.symm
  unfold Io_Mutex_unlock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (wp_xchgUnlockOn hP mutexS hS (g := g) hg hok hi fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [mutexS, StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨by omega, hc₁, hi₁⟩)
  · simp only [mutexS, StateT.run_bind, bind_assoc, pure_bind]
    refine WP.bind (wp_wakeOn hP (g := L.set g .wake rnil) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    rw [L.set_set] at hi₂
    exact WP.pure' (WP.pure' ⟨by omega, hc₂, hi₂⟩)

end IoMutex

/-- **`Io.Mutex` of this program is a mutex** (`MutexImpl`). -/
def ioMutex : MutexImpl Tgt where
  lock := Io_Mutex_lockUncancelable
  unlock := Io_Mutex_unlock
  c := mutexS.c
  lock_wp := IoMutex.lock_wp
  unlock_wp := IoMutex.unlock_wp

end Iogroup
