import Proofs.Iogroup.Gen
import ZigLean.Sep.Full.LockRules
import ZigLean.Sep.Full.AutoWP

/-!
# `fsym` on `Io.Mutex` (Zig 0.16.0's std code) as a mutex, in every protocol with the lock

The generated `lockUncancelable` and `unlock` of `examples/iogroup` walked by `fsym`'s `WP`
backend against the rules of a lock's code (`ZigLean/Sep/Full/LockRules.lean`), for every
protocol that has the lock (`FLock.Fits`): the statements of `Proofs/Iogroup/Lock.lean`
(`codex/mig-sync-iogroup2`), whose proofs walk the same code by hand (`WP.bind`, `simp only`
normal forms, `rcases` of each stop's cases). Here the proofs name the lock's rules with the
lock's states, the loop's invariant, and the `FLock` laws as simp terms; the walk is `fsym`'s.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FLock Iogroup

namespace SepAuto.WPMutex

attribute [local irreducible] Proto.WP

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

variable {γ : Type} {L : FLock γ} {K : FPrim γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

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
the futex. -/
theorem loop23_body (hP : L.Fits K P U ok) (hcost : P.cost = none) (hS : mutexS.c = L.c)
    (t : ThreadId) (g : γ)
    (hok : ok g) (D : Nat) (io : Io) (s : Io_Mutex_lockUncancelableLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (h : lockInv P L t g D s G m d) :
    P.WP t ((Io_Mutex_lockUncancelable.loop23 L.ptr io).run s) (fun r G' m' d' =>
      if Io_Mutex_lockUncancelable.again23 r.1 then lockInv P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Mutex_lockUncancelableLocals) => 0) s)
      else lockPost P L t g D r G' m' d') G m d := by
  fsym [wp_xchgLockOn hP mutexS hS, wp_waitOn hP mutexS hS, L.ph_set, L.set_set, hP.ok_set,
    Io_Mutex_lockUncancelable.again23, mutexS]

/-- `lock` by thread `t` at `out` (`g`): it holds the mutex, with a resource `rL`. -/
theorem lock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hS : L.c = mutexS.c) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Mutex_lockUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  have hS : mutexS.c = L.c := hS.symm
  fsym [wp_casOn hP mutexS hS, wp_waitOn hP mutexS hS,
    WP.loop _ _ (lockInv P L t g d) (fun _ => 0) (lockPost P L t g d)
      (loop23_body hP hcost hS t g hok d io),
    L.ph_set, L.set_set, hP.ok_set, mutexS]

/-- `unlock` by the holder `t` (`g`): it goes to `out`. -/
theorem unlock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hS : L.c = mutexS.c) (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Mutex_unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d := by
  have hS : mutexS.c = L.c := hS.symm
  fsym [wp_xchgUnlockOn hP mutexS hS, wp_wakeOn hP, L.ph_set, L.set_set, hP.ok_set, mutexS]

end SepAuto.WPMutex
