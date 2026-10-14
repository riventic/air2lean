import ZigLean.Sep.Full.Mutex

/-!
# `Io.Mutex` as a mutex (`MutexImpl`), once for every program

`Io.Mutex`'s `lockUncancelable` and `unlock` (Zig 0.16.0's std code; 0.17.0 translates to the same
code) are the same code in every program that uses them: only the names differ (each program's
`Gen` defines its own `Io_Mutex_State`, exits and locals). `IoMutexCode Tgt` is that code passed
as parameters: the functions of a program's `Gen` with their unfolding equations, stated over the
code's normal form (`bind_assoc`, `pure_bind`, `ite_bind`). What stays of the generated code's
matches on its own exits is a continuation (`kL`, `fin`, `kX`, `kU`, `ufin`), of which the proof
uses only its value at the exit it takes. `IoMutexCode.impl` proves the mutex contract
(`ZigLean/Sep/Full/Mutex.lean`) once from the rules of a lock's code
(`ZigLean/Sep/Full/LockRules.lean`); a program instantiates it with its names and `rfl`/`simp`
proofs of the equations (`Proofs/Iogroup/Lock.lean`, `Proofs/Sync/IoMutex.lean`).
-/

namespace Zig
namespace Full

open Conc Proto LockWord

namespace IoMutexCode

variable {Tgt S σ E : Type} [Packed S 32] [DecidableEq S] [Inhabited σ]

/-- `lockUncancelable`'s loop body, in normal form: `xchg(contended)`, and the futex wait if the
word was not `unlocked`. -/
def bodyOf (st : States S) (rep stop : E) (p : Ptr) (io : Io) : CM Tgt σ E := do
  let x ← atomicRmwAsC .xchg .acquire 4 p st.two
  if x != st.unl then do
    futexWaitC io p st.two
    pure rep
  else pure stop

/-- `lockUncancelable` in normal form: `cmpxchg(unlocked → locked_once)`; if it fails, the futex
wait if the word was `contended`, then the loop. `kL` is the generated match after the loop,
`fin` the one on the function's exit. -/
def lockOf (st : States S) (body : Ptr → Io → CM Tgt σ E) (again : E → Bool) (ret : E)
    (kL : E → CM Tgt σ E) (fin : E → ConcM Tgt Unit) (p : Ptr) (io : Io) : ConcM Tgt Unit := do
  let e ← StateT.run' (do
      let x ← cmpxchgAsC .acquire .relaxed 4 p st.unl st.one
      if x.isSome then do
        let v ← liftM (optPayload x)
        if v == st.two then do
          futexWaitC io p st.two
          let y ← loop (body p io) again
          kL y
        else do
          let y ← loop (body p io) again
          kL y
      else pure ret) default
  fin e

/-- `unlock` in normal form: `xchg(unlocked)`, then the generated match on the old value (`kX`:
nothing for `locked_once`, a futex wake for `contended`), on its exit (`kU`) and on the
function's exit (`ufin`). -/
def unlockOf {μ ν : Type} [Inhabited μ] (st : States S) (kX : Ptr → Io → S → CM Tgt μ ν)
    (kU : ν → CM Tgt μ ν) (ufin : ν → ConcM Tgt Unit) (p : Ptr) (io : Io) : ConcM Tgt Unit := do
  let e ← StateT.run' (do
      let v ← atomicRmwAsC .xchg .release 4 p st.unl
      let y ← kX p io v
      kU y) default
  ufin e

end IoMutexCode

/-- `Io.Mutex`'s code in a program's generated code (module doc). -/
structure IoMutexCode (Tgt : Type) where
  /-- `Io.Mutex.State`. -/
  S : Type
  [pk : Packed S 32]
  [deq : DecidableEq S]
  /-- Its values `unlocked`, `locked_once`, `contended`. -/
  st : States S
  /-- `lockUncancelable`'s locals and exits. -/
  σ : Type
  [inh : Inhabited σ]
  E : Type
  /-- The exits: the function's return, the loop's end, the loop's repeat. -/
  ret : E
  stop : E
  rep : E
  again : E → Bool
  again_rep : again rep = true
  again_stop : again stop = false
  /-- The loop body. -/
  body : Ptr → Io → CM Tgt σ E
  body_eq : ∀ p io, body p io = IoMutexCode.bodyOf st rep stop p io
  /-- `lockUncancelable`. -/
  lock : Ptr → Io → ConcM Tgt Unit
  lock_eq : ∃ (kL : E → CM Tgt σ E) (fin : E → ConcM Tgt Unit),
    (∀ p io, lock p io = IoMutexCode.lockOf st body again ret kL fin p io) ∧
    kL stop = pure ret ∧ fin ret = pure ()
  /-- `unlock`'s locals and exits: the end of the match on the old value, the return. -/
  μ : Type
  [uinh : Inhabited μ]
  ν : Type
  umid : ν
  uret : ν
  /-- `unlock`. -/
  unlock : Ptr → Io → ConcM Tgt Unit
  unlock_eq : ∃ (kX : Ptr → Io → S → CM Tgt μ ν) (kU : ν → CM Tgt μ ν) (ufin : ν → ConcM Tgt Unit),
    (∀ p io, unlock p io = IoMutexCode.unlockOf st kX kU ufin p io) ∧
    (∀ p io, kX p io st.one = pure umid) ∧
    (∀ p io, kX p io st.two = do futexWakeC io p (1 : BitVec 32); pure umid) ∧
    kU umid = pure uret ∧ ufin uret = pure ()

namespace IoMutexCode

attribute [instance] IoMutexCode.pk IoMutexCode.deq IoMutexCode.inh IoMutexCode.uinh

open FLock

variable (C : IoMutexCode Tgt) {γ : Type} {L : FLock γ} {K : FPrim γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- `lock`'s loop invariant: thread `t` is at `spin`. -/
def lockInv (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat) (_ : C.σ)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t (L.set g .spin rnil)) m

/-- `lock`'s loop ends at `stop` when thread `t` holds the mutex. -/
def lockPost (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat) (r : C.E × C.σ)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = C.stop ∧ d < D ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

/-- One repeat of `lock`'s loop: `xchg(contended)`; the thread holds the mutex, or it waits at
the futex (a stop, so the depth gets smaller). -/
theorem body_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) (hS : C.st.c = L.c)
    (t : ThreadId) (g : γ) (hok : ok g) (D : Nat) (io : Io) (s : C.σ) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (h : C.lockInv P L t g D s G m d) :
    P.WP t ((C.body L.ptr io).run s) (fun r G' m' d' =>
      if C.again r.1 then C.lockInv P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : C.σ) => 0) s)
      else C.lockPost P L t g D r G' m' d') G m d := by
  obtain ⟨hD, -, hi⟩ := h
  rw [C.body_eq, bodyOf, StateT.run_bind]
  refine WP.bind (wp_xchgLockOn hP C.st hS (g := L.set g .spin rnil) (L.ph_set _ _ _)
    ((hP.ok_set _ _ _).mpr hok) hi fun k hk G₁ m₁ r hc₁ hcase => ?_)
  simp only [L.set_set] at hcase
  rcases hcase with ⟨rfl, rL, hi₁⟩ | ⟨hr, hi₁⟩
  · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    refine WP.pure' ?_
    simp only [C.again_stop, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, by omega, hc₁, rL, hi₁⟩
  · have hne : (r != C.st.unl) = true := by simpa using hr
    simp only [hne, ↓reduceIte, StateT.run_bind]
    refine WP.bind (wp_waitOn hP C.st hS (g := L.set g .wait rnil) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    rw [StateT.run_pure]
    refine WP.pure' ?_
    simp only [C.again_rep, ↓reduceIte]
    rw [L.set_set] at hi₂
    exact ⟨⟨by omega, hc₂, hi₂⟩, .inl (by omega)⟩

/-- `lock` by thread `t` at `out` (`g`): it holds the mutex, with a resource `rL`. -/
theorem lock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hS : L.c = C.st.c) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (C.lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp
  have hS : C.st.c = L.c := hS.symm
  obtain ⟨kL, fin, hlock, hkL, hfin⟩ := C.lock_eq
  rw [hlock, lockOf]
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  rw [StateT.run_bind]
  refine WP.bind (wp_casOn hP C.st hS (g := g) hg hok hi fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  -- the loop, from `spin`
  have hloop : ∀ G₃ m₃ d₃, C.lockInv P L t g d default G₃ m₃ d₃ →
      P.WP t ((do let y ← loop (C.body L.ptr io) C.again; kL y : CM Tgt C.σ C.E).run default)
        (fun a G₄ m₄ d₄ => P.WP t (fin a.1) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
          ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G₄ m₄ d₄) G₃ m₃ d₃ := by
    intro G₃ m₃ d₃ h₃
    rw [StateT.run_bind]
    refine WP.bind (WP.mono ?_ (WP.loop _ _ (C.lockInv P L t g d) (fun _ => 0)
      (C.lockPost P L t g d) (C.body_wp hP hcost hS t g hok d io) default G₃ m₃ d₃ h₃))
    rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', rL, hi'⟩
    rw [hkL, StateT.run_pure]
    exact WP.pure' (by rw [hfin]; exact WP.pure' ⟨hd', hc', rL, hi'⟩)
  rcases hcase with ⟨rfl, rL, hi₁⟩ | ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    exact WP.pure' (by rw [hfin]; exact WP.pure' ⟨by omega, hc₁, rL, hi₁⟩)
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    have hne : (C.st.one == C.st.two) = false := beq_false_of_ne C.st.ne12
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact hloop G₁ m₁ k₁ ⟨by omega, hc₁, hi₁⟩
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    simp only [beq_self_eq_true, ↓reduceIte, StateT.run_bind]
    refine WP.bind (wp_waitOn hP C.st hS (g := L.set g .wait rnil) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    rw [L.set_set] at hi₂
    exact hloop G₂ m₂ k₂ ⟨by omega, hc₂, hi₂⟩

/-- `unlock` by the holder `t` (`g`): it goes to `out`. -/
theorem unlock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hS : L.c = C.st.c) (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) (_hcur : m.current = t) :
    P.WP t (C.unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d := by
  subst hp
  have hS : C.st.c = L.c := hS.symm
  obtain ⟨kX, kU, ufin, hunlock, hone, htwo, hkU, hfin⟩ := C.unlock_eq
  rw [hunlock, unlockOf]
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  rw [StateT.run_bind]
  refine WP.bind (wp_xchgUnlockOn hP C.st hS (g := g) hg hok hi fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · rw [StateT.run_bind, hone, StateT.run_pure, pure_bind, hkU, StateT.run_pure]
    exact WP.pure' (by rw [hfin]; exact WP.pure' ⟨by omega, hc₁, hi₁⟩)
  · rw [StateT.run_bind, htwo, StateT.run_bind, bind_assoc]
    refine WP.bind (wp_wakeOn hP (g := L.set g .wake rnil) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    rw [L.set_set] at hi₂
    simp only [StateT.run_pure, pure_bind, hkU]
    exact WP.pure' (by rw [hfin]; exact WP.pure' ⟨by omega, hc₂, hi₂⟩)

/-- **`Io.Mutex` is a mutex** (`MutexImpl`), in every program whose code it is. -/
def impl : MutexImpl Tgt where
  lock := C.lock
  unlock := C.unlock
  c := C.st.c
  lock_wp := C.lock_wp
  unlock_wp := C.unlock_wp

end IoMutexCode

end Full
end Zig
