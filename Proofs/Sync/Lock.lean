import Proofs.Sync.Gen
import ZigLean.Conc.LockRules

/-!
# `lock` and `unlock` of the translated `Io.Mutex`

The control flow of the generated `Io_Mutex_lockUncancelable` and `Io_Mutex_unlock`
(`examples/sync`), with the rules of a lock (`ZigLean/Conc/LockRules.lean`), for every protocol
that has the lock (`Lock.Fits`). `Proofs/Sync/Mutex.lean` and `Proofs/Sync/Handoff.lean` use them.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock

namespace Sync

/-- The states of `Io.Mutex`. -/
def mutexS : States Io_Mutex_State where
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

namespace MutexOps

variable {γ : Type} {L : Lock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Mem → Prop} {ok : γ → Prop}

/-- `lock`'s loop invariant: thread `t` is at `spin`. -/
def lockInv (P : Proto Tgt γ) (L : Lock γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Io_Mutex_lockUncancelableLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t (L.set g .spin Heap.empty)) m

/-- `lock`'s loop ends when thread `t` holds the mutex. -/
def lockPost (P : Proto Tgt γ) (L : Lock γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Io_Mutex_lockUncancelableExit × Io_Mutex_lockUncancelableLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) : Prop :=
  r.1 = .br22 ∧ d < D ∧ m.current = t ∧ ∃ hL, P.inv (upd G t (L.set g .holds hL)) m

/-- One repeat of `lock`'s loop: `xchg(contended)`; the thread holds the mutex, or it waits at
the futex (a stop, so the depth gets smaller). -/
theorem loop23_body (hP : L.FitsOn P U ok) {p : Ptr} (hp : (p.add 0).add 0 = L.ptr) (hS : mutexS.c = L.c) (t : ThreadId)
    (g : γ) (hok : ok g) (D : Nat) (io : Io) (s : Io_Mutex_lockUncancelableLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (h : lockInv P L t g D s G m d) :
    P.WP t ((Io_Mutex_lockUncancelable.loop23 p io).run s) (fun r G' m' d' =>
      if Io_Mutex_lockUncancelable.again23 r.1 then lockInv P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Mutex_lockUncancelableLocals) => 0) s)
      else lockPost P L t g D r G' m' d') G m d := by
  obtain ⟨hD, -, hi⟩ := h
  unfold Io_Mutex_lockUncancelable.loop23
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [hp]
  refine WP.bind (wp_xchgLockOn hP mutexS hS (g := L.set g .spin Heap.empty) (L.ph_set _ _ _)
    ((hP.ok_set _ _ _).mpr hok) hi
    fun k hk G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hL, hi₁⟩ | ⟨hr, hi₁⟩
  · simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Mutex_lockUncancelable.again23, Bool.false_eq_true, ↓reduceIte]
    rw [L.set_set] at hi₁
    exact ⟨rfl, by omega, hc₁, hL, hi₁⟩
  · have hne : (r != mutexS.unl) = true := by simpa using hr
    simp only [StateT.run_pure, pure_bind]
    simp only [show (r != Io_Mutex_State.unlocked) = true from hne, ↓reduceIte, StateT.run_bind,
      bind_assoc, pure_bind]
    rw [L.set_set] at hi₁
    refine WP.bind (wp_waitOn hP mutexS hS (g := L.set g .wait Heap.empty) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Mutex_lockUncancelable.again23, ↓reduceIte]
    rw [L.set_set] at hi₂
    exact ⟨⟨by omega, hc₂, hi₂⟩, .inl (by omega)⟩

/-- `lock` by thread `t` at `out` (`g`): it holds the mutex, with a resource `hL`. -/
theorem lock_specOn (hP : L.FitsOn P U ok) {p : Ptr} (hp : (p.add 0).add 0 = L.ptr) (hS : mutexS.c = L.c) (t : ThreadId)
    (g : γ) (hg : L.ph g = .out) (hok : ok g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Mutex_lockUncancelable p io) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G m d := by
  unfold Io_Mutex_lockUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [hp]
  refine WP.bind (wp_casOn hP mutexS hS (g := g) hg hok hi fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  -- the loop, from `spin`
  have hloop : ∀ G₃ m₃ d₃, lockInv P L t g d default G₃ m₃ d₃ →
      P.WP t ((do
          let __do_lift ← loop (Io_Mutex_lockUncancelable.loop23 p io)
            Io_Mutex_lockUncancelable.again23
          match __do_lift with
          | Io_Mutex_lockUncancelableExit.br22 => pure Io_Mutex_lockUncancelableExit.ret
          | e => pure e : CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit).run
          default)
        (fun a G₄ m₄ d₄ => P.WP t (match a.1 with
          | Io_Mutex_lockUncancelableExit.ret => pure ()
          | _ => throw Error.panic)
          (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
            ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G₄ m₄ d₄)
        G₃ m₃ d₃ := by
    intro G₃ m₃ d₃ h₃
    simp only [StateT.run_bind]
    refine WP.bind (WP.mono ?_ (WP.loop _ _ (lockInv P L t g d) (fun _ => 0) (lockPost P L t g d)
      (loop23_body hP hp hS t g hok d io) default G₃ m₃ d₃ h₃))
    rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', hL, hi'⟩
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    exact WP.pure' ⟨hd', hc', hL, hi'⟩
  rcases hcase with ⟨rfl, hL, hi₁⟩ | ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    exact WP.pure' ⟨by omega, hc₁, hL, hi₁⟩
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    simp only [StateT.run_pure, pure_bind]
    simp only [mutexS, beq_iff_eq, reduceCtorEq, ↓reduceIte, pure_bind]
    exact hloop G₁ m₁ k₁ ⟨by omega, hc₁, hi₁⟩
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    simp only [StateT.run_pure, pure_bind]
    simp only [mutexS, beq_self_eq_true, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (wp_waitOn hP mutexS hS (g := L.set g .wait Heap.empty) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    rw [L.set_set] at hi₂
    exact hloop G₂ m₂ k₂ ⟨by omega, hc₂, hi₂⟩

/-- `unlock` by the holder `t` (`g`), the current thread: the owner check passes
(`Inv.ownerCheck`), and it goes to `out`. -/
theorem unlock_specOn (hP : L.FitsOn P U ok) {p : Ptr} (hp : (p.add 0).add 0 = L.ptr) (hS : mutexS.c = L.c) (t : ThreadId)
    (g : γ) (hg : L.ph g = .holds) (hok : ok g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) (hcur : m.current = t := by first | assumption | rfl) :
    P.WP t (Io_Mutex_unlock p io) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = t ∧ P.inv (upd G' t (L.set g .out Heap.empty)) m') G m d := by
  unfold Io_Mutex_unlock
  have hp' : p = L.ptr := by rw [← hp]; cases p; simp [Ptr.add]
  have hrun := ((hP.inv _ _).mp hi).1.ownerCheck (by rw [upd_self]; exact hg) hcur
  rw [← hp'] at hrun
  refine WP.ownerCheck hrun ?_
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [hp]
  refine WP.bind (wp_xchgUnlockOn hP mutexS hS (g := g) hg hok hi fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [mutexS, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    exact WP.pure' ⟨by omega, hc₁, hi₁⟩
  · simp only [mutexS, StateT.run_bind, bind_assoc, pure_bind]
    refine WP.bind (wp_wakeOn hP (g := L.set g .wake Heap.empty) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    rw [L.set_set] at hi₂
    exact WP.pure' ⟨by omega, hc₂, hi₂⟩

/-- `lock` by thread `t` at `out` (`g`): it holds the mutex, with a resource `hL`. -/
theorem lock_spec (hP : L.Fits P U) {p : Ptr} (hp : (p.add 0).add 0 = L.ptr) (hS : mutexS.c = L.c)
    (t : ThreadId) (g : γ) (hg : L.ph g = .out) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Mutex_lockUncancelable p io) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G m d :=
  lock_specOn hP.on hp hS t g hg trivial io G m d hi

/-- `unlock` by the holder `t` (`g`), the current thread: it goes to `out`. -/
theorem unlock_spec (hP : L.Fits P U) {p : Ptr} (hp : (p.add 0).add 0 = L.ptr) (hS : mutexS.c = L.c)
    (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) (hcur : m.current = t := by first | assumption | rfl) :
    P.WP t (Io_Mutex_unlock p io) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = t ∧ P.inv (upd G' t (L.set g .out Heap.empty)) m') G m d :=
  unlock_specOn hP.on hp hS t g hg trivial io G m d hi hcur

end MutexOps
end Sync
