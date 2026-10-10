import ZigLean.Conc.Sched

/-!
# A one-thread scheduler run is a sequential run

A concurrent function (`ConcM`, `ZigLean/Conc/Basic.lean`) is a tree of sync ops. When it only
stops at ops that a single thread answers by itself (`yield`, a `choose`, a `pick` of the
oracle: every atomic op) and the oracle always answers `0`, the scheduler's run
(`Sched.run`) is the tree read sequentially: each stop answered with `0` (or `()`), in the
memory the thread stopped with, as thread `0` (`seqTree`). This is how the `alloc` entry of the
translated `std.heap.PageAllocator` (a `ConcM` function: its hint is an atomic) becomes a
`MemM` program for `AllocSpec` (`seqTree_run`): `Sched.run dispatch fuel (fun _ => 0) main m`
is `seqRun fuel main m` (`run_solo`), given that the tree is `ThreadFree`
(`ConcM.ThreadFree`, closed under `pure`, `bind`, `liftMem` and solo sync ops).
-/

namespace Zig
namespace Sched

variable {Tgt α β : Type}

/-- A sync op that a single thread answers by itself. -/
def SyncOp.Solo : SyncOp Tgt → Bool
  | .yield | .choose _ | .pick _ => true
  | _ => false

/-- The answer of a one-thread run with the oracle `0`. -/
def soloResp : (op : SyncOp Tgt) → op.Resp
  | .yield => ()
  | .choose _ => (0 : Nat)
  | .pick _ => (0 : Nat)
  | .spawn _ => (0 : Nat)
  | .join _ => ()
  | .wait .. => ()
  | .wake .. => ()

/-- Every stop of the tree is a solo op. -/
def ThreadFree : {n : Nat} → CoN Tgt β n → Prop
  | _, .leaf _ => True
  | _, .sync op _ k => SyncOp.Solo op = true ∧ ∀ r m, ThreadFree (k r m)

/-- The sequential reading of a run of thread `0` (module doc). -/
def seqTree : {n : Nat} → CoN Tgt (α × Mem) n → Out α
  | _, .leaf none => none
  | _, .leaf (some (.error e)) => some (.error e)
  | _, .leaf (some (.ok (v, m))) =>
    match ((Thread.checkJoinedByChild 0).run m).run with
    | some (.ok (_, m')) => some (.ok (v, m'))
    | some (.error e) => some (.error e)
    | none => none
  | _, .sync op m k => seqTree (k (soloResp op) { m with current := 0 })

theorem canGo_solo {s : State Tgt α} {op : SyncOp Tgt} (h : SyncOp.Solo op = true) :
    canGo s 0 op = true := by
  cases op <;> simp_all [SyncOp.Solo, canGo]

theorem leaf_solo (d : Tgt → ConcM Tgt Unit) (f n : Nat) (v : α) (m : Mem) (s : State Tgt α) :
    (match settle 0 s (CoN.leaf (some (.ok (v, m))) : CoN Tgt (α × Mem) n) with
      | .error e => outOf e
      | .ok (_, some v, s') => some (.ok (v, s'.mem))
      | .ok (ts, none, s') => (go d (fun _ => 0) f { s' with main := ts }).1) =
      seqTree (CoN.leaf (some (.ok (v, m))) : CoN Tgt (α × Mem) n) := by
  simp only [settle, seqTree]
  cases hc : ((Thread.checkJoinedByChild 0).run m).run with
  | none => rfl
  | some x =>
    cases x with
    | error e => rfl
    | ok x => obtain ⟨_, m'⟩ := x; rfl

/-- After a settle of thread `0`, the scheduler (with the oracle `0`, no other thread) reads the
rest of the tree sequentially. -/
theorem step_solo (d : Tgt → ConcM Tgt Unit) :
    ∀ (f dep : Nat), dep ≤ f → ∀ (t : CoN Tgt (α × Mem) dep), ThreadFree t →
      ∀ (s : State Tgt α), s.kids = #[] →
      (match settle 0 s t with
        | .error e => outOf e
        | .ok (_, some v, s') => some (.ok (v, s'.mem))
        | .ok (ts, none, s') => (go d (fun _ => 0) f { s' with main := ts }).1) = seqTree t := by
  intro f
  induction f with
  | zero =>
    intro dep hdep t _ s _
    cases t with
    | leaf r =>
      rcases r with _ | (e | ⟨v, m⟩)
      · rfl
      · rfl
      · exact leaf_solo d _ _ _ _ _
    | sync op m k => omega
  | succ f ih =>
    intro dep hdep t ht s hk
    cases t with
    | leaf r =>
      rcases r with _ | (e | ⟨v, m⟩)
      · rfl
      · rfl
      · exact leaf_solo d _ _ _ _ _
    | sync op m k =>
      rename_i n
      obtain ⟨hsolo, hrest⟩ := ht
      obtain ⟨main, kids, mem, step, trace⟩ := s
      simp only at hk
      subst hk
      simp only [settle]
      unfold go
      have hready : (State.mk (TS.paused ⟨n, op, k⟩) #[] m step trace : State Tgt α).ready =
          #[0] := by
        simp [State.ready, canGo_solo hsolo]
        rfl
      simp only [hready]
      simp only [show (#[0] : Array ThreadId).isEmpty = false from rfl, Bool.false_eq_true,
        ↓reduceIte, State.choose, show (#[0] : Array ThreadId).size = 1 from rfl, ite_self,
        show (#[0] : Array ThreadId)[0]! = 0 from rfl, turn]
      cases op with
      | yield =>
        have := ih n (by omega) (k () { m with current := 0 }) (hrest _ _)
          ⟨TS.paused ⟨n, .yield, k⟩, #[], { m with current := 0 }, step + 1, trace.push 1⟩ rfl
        simp only [turnTrace, seqTree, soloResp]
        rw [← this]
        generalize settle 0 _ _ = x
        rcases x with e | ⟨ts, _ | v, s'⟩ <;> rfl
      | choose c =>
        have := ih n (by omega) (k (0 : Nat) { m with current := 0 }) (hrest _ _)
          ⟨TS.paused ⟨n, .choose c, k⟩, #[], { m with current := 0 }, step + 1 + 1,
            (trace.push 1).push c⟩ rfl
        simp only [turnTrace, seqTree, soloResp, State.choose, Nat.zero_mod, ite_self]
        rw [← this]
        generalize settle 0 _ _ = x
        rcases x with e | ⟨ts, _ | v, s'⟩ <;> rfl
      | pick count =>
        have := ih n (by omega) (k (0 : Nat) { m with current := 0 }) (hrest _ _)
          ⟨TS.paused ⟨n, .pick count, k⟩, #[], { m with current := 0 }, step + 1 + 1,
            (trace.push 1).push (count { m with current := 0 })⟩ rfl
        simp only [turnTrace, seqTree, soloResp, State.choose, Nat.zero_mod, ite_self]
        rw [← this]
        generalize settle 0 _ _ = x
        rcases x with e | ⟨ts, _ | v, s'⟩ <;> rfl
      | spawn _ => simp [SyncOp.Solo] at hsolo
      | join _ => simp [SyncOp.Solo] at hsolo
      | wait _ _ => simp [SyncOp.Solo] at hsolo
      | wake _ _ => simp [SyncOp.Solo] at hsolo

/-- **A one-thread run with the oracle `0` is the sequential reading of its tree.** -/
theorem run_solo (d : Tgt → ConcM Tgt Unit) (fuel : Nat) (main : ConcM Tgt α) (m0 : Mem)
    (ht : ThreadFree (main fuel { m0 with current := 0 })) :
    (run d fuel (fun _ => 0) main m0).run = seqTree (main fuel { m0 with current := 0 }) := by
  have := step_solo d fuel fuel (Nat.le_refl _) _ ht
    { main := .done, kids := #[], mem := { m0 with current := 0 }, step := 0, trace := #[] } rfl
  simp only [run, runTrace, ExceptT.mk, ExceptT.run]
  rw [← this]
  split <;> simp_all

/-! ## Thread-free concurrent functions -/

/-- Every run of `x`, at every depth and from every memory, stops only at solo ops. -/
def _root_.Zig.ConcM.ThreadFree (x : ConcM Tgt β) : Prop := ∀ n m, Sched.ThreadFree (x n m)

namespace ThreadFreeC

theorem pure' (v : β) : ConcM.ThreadFree (pure v : ConcM Tgt β) := by
  intro _ _; exact trivial

theorem throw (e : Error) : ConcM.ThreadFree (throw e : ConcM Tgt β) := by
  intro _ _; exact trivial

theorem liftMem (x : MemM β) : ConcM.ThreadFree (ConcM.liftMem x : ConcM Tgt β) := by
  intro _ _; exact trivial

theorem sync {op : SyncOp Tgt} (h : SyncOp.Solo op = true) : ConcM.ThreadFree (ConcM.sync op) := by
  unfold ConcM.ThreadFree
  intro n m
  cases n with
  | zero => exact trivial
  | succ n => exact And.intro h fun _ _ => trivial

theorem bind_tree {γ : Type} : ∀ {n : Nat} (t : CoN Tgt γ n) (f : γ → (k : Nat) → CoN Tgt β k),
    ThreadFree t → (∀ a k, ThreadFree (f a k)) → ThreadFree (t.bind f)
  | _, .leaf none, _, _, _ => trivial
  | _, .leaf (some (.error _)), _, _, _ => trivial
  | _, .leaf (some (.ok a)), _, _, hf => hf a _
  | _, .sync _ _ k, f, ht, hf =>
    And.intro ht.1 fun r m => bind_tree (k r m) f (ht.2 r m) hf

theorem bind {γ : Type} {x : ConcM Tgt γ} {f : γ → ConcM Tgt β} (hx : ConcM.ThreadFree x)
    (hf : ∀ a, ConcM.ThreadFree (f a)) : ConcM.ThreadFree (x >>= f) :=
  fun n m => bind_tree (x n m) _ (hx n m) fun am k => hf am.1 k am.2

end ThreadFreeC

/-- The sequential reading of `main` as a `MemM` program (thread `0`, oracle `0`). -/
def seqRun (fuel : Nat) (main : ConcM Tgt α) : MemM α :=
  fun m => ExceptT.mk (seqTree (main fuel { m with current := 0 }))

/-- **A one-thread scheduler run of a thread-free function is its sequential reading.** -/
theorem run_eq_seqRun (d : Tgt → ConcM Tgt Unit) (fuel : Nat) {main : ConcM Tgt α}
    (ht : ConcM.ThreadFree main) (m : Mem) :
    run d fuel (fun _ => 0) main m = (seqRun fuel main).run m := by
  have := run_solo d fuel main m (ht _ _)
  simp only [seqRun, StateT.run]
  exact congrArg ExceptT.mk this

end Sched
end Zig
