import ZigLean.Sep.Full.Seq
import ZigLean.Sep.Full.Logic
import ZigLean.Conc.Call
import ZigLean.Conc.AtomicWord
import ZigLean.Conc.PtrAtomic
import ZigLean.Sep.AllocSpec.Norm

/-!
# Full-state triples for concurrent functions read in one thread

A call of a concurrent function (`ConcM`, a tree of sync ops) from a sequential caller runs in
the caller's thread: each stop is answered as a single thread answers it (`Sched.soloResp`: the
oracle's choice `0`, as the sequential atomic rules assume), in the memory the thread stopped
with. `Sched.soloRun fuel x` is that reading as a `MemM` program, at the depth `fuel`.
Unlike `Sched.seqRun` (`Seq.lean`) it keeps the caller's thread id and does not end the thread
(no `checkJoinedByChild`), so it is a call, not a whole program.

`CTriple P x Q` is `FTriple P (soloRun n x) Q` at every depth `n`. Its rules follow the
structure of the generated code: `bind`, `liftMem` (an `FTriple` of the `MemM` part), `pick_bind`
(an atomic op's choice is `0`), and the structural rules. The `cnorm` simp set pushes
`StateT.run` through the body monad `CM` of a generated concurrent function (as `gen_norm` does
for `MM`).
-/

namespace Zig
namespace Sched

variable {Tgt α β γ : Type}

/-- The in-thread reading of a run (module doc). -/
def soloTree : {n : Nat} → CoN Tgt (α × Mem) n → Out α
  | _, .leaf r => r
  | _, .sync op m k => soloTree (k (soloResp op) m)

/-- A call of `x` read in the caller's thread, at depth `fuel`. -/
def soloRun (fuel : Nat) (x : ConcM Tgt α) : MemM α := fun m => ExceptT.mk (soloTree (x fuel m))

theorem soloTree_bind : ∀ {n : Nat} (t : CoN Tgt (γ × Mem) n)
    (G : γ × Mem → (k : Nat) → CoN Tgt (α × Mem) k),
    (soloTree t = none ∧ soloTree (t.bind G) = none) ∨
    (∃ e, soloTree t = some (.error e) ∧ soloTree (t.bind G) = some (.error e)) ∨
    (∃ b k, soloTree t = some (.ok b) ∧ soloTree (t.bind G) = soloTree (G b k))
  | _, .leaf none, _ => .inl ⟨rfl, rfl⟩
  | _, .leaf (some (.error e)), _ => .inr (.inl ⟨e, rfl, rfl⟩)
  | n, .leaf (some (.ok b)), _ => .inr (.inr ⟨b, n, rfl, rfl⟩)
  | _, .sync op m k, G => soloTree_bind (k (soloResp op) m) G

end Sched

namespace Full

open Sched FAssn

variable {Tgt α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {x : ConcM Tgt α}

/-- A full-state triple for a concurrent function read in one thread (module doc). -/
def CTriple (P : FAssn) (x : ConcM Tgt α) (Q : α → FAssn) : Prop :=
  ∀ n, FTriple P (soloRun n x) Q

namespace CTriple

theorem run_eq (n : Nat) (m : Mem) : ((soloRun n x).run m).run = soloTree (x n m) := rfl

theorem bind {S : β → FAssn} {f : α → ConcM Tgt β} (hx : CTriple P x Q)
    (hf : ∀ a, CTriple (Q a) (f a) S) : CTriple P (x >>= f) S := by
  intro n m r rF hh hp hs
  have h1 := hx n m r rF hh hp hs
  rw [run_eq] at h1
  show match soloTree ((x n m).bind fun (a, m') k => f a k m') with
    | none => True
    | some (.error _) => False
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ S v r' ∧ m'.FSeq
  rcases soloTree_bind (x n m) (fun (a, m') k => f a k m') with ⟨-, h2⟩ | ⟨e, he, -⟩ |
    ⟨⟨a, m'⟩, k, he, h2⟩
  · rw [h2]; trivial
  · rw [he] at h1; exact h1.elim
  · rw [he] at h1
    obtain ⟨r', hh', hq, hs'⟩ := h1
    rw [h2]
    have := hf a k m' r' rF hh' hq hs'
    rw [run_eq] at this
    exact this

theorem liftMem {c : MemM α} (h : FTriple P c Q) : CTriple P (ConcM.liftMem c : ConcM Tgt α) Q :=
  fun _ => h

theorem ret (v : α) : CTriple (Q v) (pure v : ConcM Tgt α) Q := fun _ => FTriple.ret v

theorem ret' (v : α) (hq : ∀ r, P r → Q v r) : CTriple P (pure v : ConcM Tgt α) Q :=
  fun _ => FTriple.ret' v hq

/-- An atomic op's choice of the oracle: `0` in one thread. -/
theorem pick_bind {count : Mem → Nat} {f : Nat → ConcM Tgt α} (h : CTriple P (f 0) Q) :
    CTriple P ((ConcM.sync (.pick count) : ConcM Tgt Nat) >>= f) Q := by
  intro n m r rF hh hp hs
  cases n with
  | zero => trivial
  | succ n => exact h n m r rF hh hp hs

theorem conseq (ht : CTriple P x Q) (hp : ∀ r, P' r → P r) (hq : ∀ v r, Q v r → Q' v r) :
    CTriple P' x Q' := fun n => (ht n).conseq hp hq

theorem pre (ht : CTriple P x Q) (hp : ∀ r, P' r → P r) : CTriple P' x Q :=
  fun n => (ht n).pre hp

theorem post (ht : CTriple P x Q) (hq : ∀ v r, Q v r → Q' v r) : CTriple P x Q' :=
  fun n => (ht n).post hq

theorem frame (ht : CTriple P x Q) : CTriple (P ⋆ R) x (fun v => Q v ⋆ R) :=
  fun n => (ht n).frame

theorem frameL (ht : CTriple P x Q) : CTriple (R ⋆ P) x (fun v => R ⋆ Q v) :=
  fun n => (ht n).frameL

theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ y, CTriple (P y) x Q) : CTriple (FAssn.ex P) x Q :=
  fun n => FTriple.ex fun y => h y n

theorem lift {φ : Prop} (h : φ → CTriple P x Q) : CTriple (⟪φ⟫ ⋆ P) x Q :=
  fun n => FTriple.lift fun hφ => h hφ n

/-- A fact that the precondition implies. -/
theorem of_pure {φ : Prop} (hφ : ∀ r, P r → φ) (h : φ → CTriple P x Q) : CTriple P x Q :=
  fun n m r rF hh hp hs => h (hφ r hp) n m r rF hh hp hs

/-- **Knowledge from ownership** (`FTriple.know_intro`). -/
theorem know_intro {b : BlockId} {A : Nat}
    (hc : ∀ r, P r → ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A)
    (ht : CTriple (P ⋆ known b A) x Q) : CTriple P x Q :=
  fun n => FTriple.know_intro hc (ht n)

/-- Knowledge and ghost state (anything that owns no bytes) in the precondition can be forgotten. -/
theorem forget {K : FAssn} (hK : ∀ r, K r → r.heap = FHeap.empty) (ht : CTriple P x Q) :
    CTriple (P ⋆ K) x Q := by
  intro n m r rF hh hp hs
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hp
  have e := hK _ h2
  have hh₁ : Holds m r₁ rF := by
    obtain ⟨hd', hm, hk, hkF, hg⟩ := hh
    simp only [e, FHeap.union_empty] at hd' hm
    exact ⟨hd', hm, hk.left, hkF, Ghost.Ok.mono hg⟩
  exact ht n m r₁ rF hh₁ h1 hs

/-- A legacy total triple of a `Tame` step, with a full-state frame `H` (`FTotalTriple.ofTotal`). -/
theorem step {H : FAssn} {X : Assn} {c : MemM α} {Y : α → Assn} {f : α → ConcM Tgt β}
    {S : β → FAssn} (ht : TotalTriple X c Y) (hc : Tame c)
    (hf : ∀ v, CTriple (H ⋆ up (Y v)) (f v) S) :
    CTriple (H ⋆ up X) (ConcM.liftMem c >>= f) S :=
  bind (liftMem (FTotalTriple.ofTotal ht hc).toPartial.frameL) hf

end CTriple

end Full

/-! ## Normalizing the body of a generated concurrent function -/

namespace CNorm

variable {Tgt σ α β : Type}

theorem run_callC (x : ConcM Tgt α) (s : σ) :
    (callC x : CM Tgt σ α).run s = x >>= fun a => pure (a, s) := rfl

theorem run_callMC (x : MemM α) (s : σ) :
    (callMC x : CM Tgt σ α).run s = ConcM.liftMem x >>= fun a => pure (a, s) := rfl

theorem run_callRC (x : Result α) (s : σ) :
    (callRC x : CM Tgt σ α).run s = ConcM.liftMem (StateT.lift x) >>= fun a => pure (a, s) := rfl

theorem run_liftR (x : Result α) (s : σ) :
    (liftM x : CM Tgt σ α).run s = ConcM.liftMem (StateT.lift x) >>= fun a => pure (a, s) := rfl

theorem run_pickC (count : Mem → Nat) (s : σ) :
    (pickC count : CM Tgt σ Nat).run s =
      (ConcM.sync (.pick count) : ConcM Tgt Nat) >>= fun (a : Nat) => pure (a, s) := rfl

theorem run_ite {c : Prop} [Decidable c] (x y : CM Tgt σ α) (s : σ) :
    (if c then x else y).run s = if c then x.run s else y.run s := by split <;> rfl

theorem run_throw (e : Error) (s : σ) : (throw e : CM Tgt σ α).run s = throw e := rfl

theorem throw_bind (e : Error) (f : α → ConcM Tgt β) : (throw e : ConcM Tgt α) >>= f = throw e :=
  rfl

theorem run_get (s : σ) : (get : CM Tgt σ σ).run s = pure (s, s) := rfl

theorem run_modify (f : σ → σ) (s : σ) : (modify f : CM Tgt σ Unit).run s = pure ((), f s) := rfl

/-- `bind_assoc` at an oracle pick (whose result type `SyncOp.Resp (.pick _)` is `Nat` only up to
unfolding, so `bind_assoc` does not match it in `simp`). -/
theorem pick_assoc {γ : Type} (count : Mem → Nat) (f : Nat → ConcM Tgt β) (g : β → ConcM Tgt γ) :
    ((ConcM.sync (.pick count) : ConcM Tgt Nat) >>= f) >>= g =
      (ConcM.sync (.pick count) : ConcM Tgt Nat) >>= fun a => f a >>= g :=
  bind_assoc _ _ _

theorem liftMem_pure (v : α) : (ConcM.liftMem (pure v : MemM α) : ConcM Tgt α) = pure v := rfl

theorem liftMem_lift_pure (v : α) :
    (ConcM.liftMem (StateT.lift (pure v : Result α)) : ConcM Tgt α) = pure v := rfl

theorem liftMem_lift_throw (e : Error) :
    (ConcM.liftMem (StateT.lift (throw e : Result α)) : ConcM Tgt α) = throw e := rfl

end CNorm

/-- Normalize the body of a generated concurrent function to a `ConcM` program of `liftMem`
steps, oracle picks and `pure`/`if` (module doc). -/
macro "conc_norm" : tactic => `(tactic| (
  simp only [atomicLoadUnorderedEncC, cmpxchgPtrC, StateT.run'_eq, StateT.run_bind, StateT.run_pure, CNorm.run_callC,
    CNorm.run_callMC, CNorm.run_callRC, CNorm.run_liftR, CNorm.run_pickC, CNorm.run_ite,
    Norm.ite_bind, CNorm.run_throw, CNorm.throw_bind, CNorm.run_get, CNorm.run_modify,
    CNorm.pick_assoc, CNorm.liftMem_pure, CNorm.liftMem_lift_pure, CNorm.liftMem_lift_throw, Norm.sub_zero,
    Norm.elem_zero, Norm.add_zero_ptr, bind_assoc, pure_bind, map_pure, bind_map_left, map_bind,
    Norm.beq_true_iff, bind_pure_unit, Bool.not_false, Bool.not_true, ↓reduceIte,
    Bool.false_eq_true]))

end Zig
