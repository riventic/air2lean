import IdleLoop.Basic

/-!
# Memory steps that always give a result

A `MemM` step can give a value, an error, or no result (`none`). Safety rules exclude errors;
a progress proof must also exclude `none`. `NN x` says that `x` gives a value or an error from
every memory. The atomic load and store of the client are `NN`, so with their no-error facts
they give a value.
-/

namespace IdleLoop.Client

open Zig

/-- `x` gives a value or an error from every memory. -/
def NN {α : Type} (x : MemM α) : Prop := ∀ m, (x.run m).run ≠ none

theorem nn_pure {α : Type} (a : α) : NN (pure a : MemM α) := by
  intro m h
  simp [StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at h

theorem nn_bind {α β : Type} {x : MemM α} {f : α → MemM β} (hx : NN x) (hf : ∀ a, NN (f a)) :
    NN (x >>= f) := by
  intro m h
  rw [StateT.run_bind, ExceptT.run_bind] at h
  match hr : (x.run m).run, h with
  | none, _ => exact hx m hr
  | some (.error _), h => simp [pure] at h
  | some (.ok (a, m')), h => exact hf a m' (by simpa [hr] using h)

theorem nn_get : NN (get : MemM Mem) := by
  intro m h
  simp [get, getThe, MonadStateOf.get, StateT.get, StateT.run, pure, ExceptT.pure,
    ExceptT.mk, ExceptT.run] at h

theorem nn_set (x : Mem) : NN (set x : MemM PUnit) := by
  intro m h
  simp [set, StateT.set, StateT.run, pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at h

theorem nn_modify (f : Mem → Mem) : NN (modify f : MemM PUnit) := by
  intro m h
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, pure,
    ExceptT.pure, ExceptT.mk, ExceptT.run] at h

theorem nn_throw {α : Type} (e : Error) : NN (throw e : MemM α) := by
  intro m h
  simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.run, ExceptT.run,
    ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont] at h

theorem nn_lift {α : Type} {r : Result α} (hr : r.run ≠ none) : NN (StateT.lift r : MemM α) := by
  intro m h
  simp only [StateT.run, StateT.lift, ExceptT.run_bind] at h
  match hr' : r.run, h with
  | none, _ => exact hr hr'
  | some (.error _), h => simp [pure, ExceptT.pure, ExceptT.mk] at h
  | some (.ok _), h => simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at h

theorem rnn_pure {α : Type} (a : α) : (pure a : Result α).run ≠ none := by
  simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

theorem rnn_throw {α : Type} (e : Error) : (throw e : Result α).run ≠ none := by
  simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.run]

theorem rnn_bind {α β : Type} {r : Result α} {f : α → Result β} (hr : r.run ≠ none)
    (hf : ∀ a, (f a).run ≠ none) : (r >>= f).run ≠ none := by
  rw [ExceptT.run_bind]
  match h : r.run with
  | none => exact absurd h hr
  | some (.error _) => simp [pure]
  | some (.ok a) => simpa using hf a

theorem rnn_access (m : Mem) (p : Ptr) (n a : Nat) : (m.access p n a).run ≠ none := by
  unfold Mem.access
  split
  · exact rnn_throw _
  · split
    · exact rnn_throw _
    · split
      · exact rnn_pure _
      · exact rnn_throw _

theorem rnn_accessW (m : Mem) (p : Ptr) (n a : Nat) : (m.accessW p n a).run ≠ none := by
  unfold Mem.accessW
  refine rnn_bind (rnn_access m p n a) fun r => ?_
  split
  · exact rnn_throw _
  · exact rnn_pure _

theorem rnn_intOfBytes (n : Nat) (bs : Array Byte) (trunc : Bool) :
    (intOfBytes n bs trunc).run ≠ none := by
  unfold intOfBytes
  rw [← Array.foldr_toList]
  generalize (bs.extract 0 ((n + 7) / 8)).zipIdx.toList = l
  induction l with
  | nil => exact rnn_pure _
  | cons x xs ih =>
    obtain ⟨b, i⟩ := x
    simp only [List.foldr_cons]
    refine rnn_bind ih fun hi => ?_
    split
    · exact rnn_pure _
    · exact rnn_throw _

/-- One step of the `NN` search: a leaf, a bind, a branch. -/
macro "nn_step" : tactic => `(tactic| first
  | exact nn_pure _ | exact nn_throw _ | exact nn_set _ | exact nn_modify _ | exact nn_get
  | exact nn_lift (rnn_access _ _ _ _) | exact nn_lift (rnn_accessW _ _ _ _)
  | exact nn_lift (rnn_intOfBytes _ _ _)
  | refine nn_bind ?_ fun _ => ?_
  | split
  | (dsimp only))

theorem nn_recordAccess (b o len : Nat) (k : AccessKind) : NN (recordAccess b o len k) := by
  unfold recordAccess
  repeat nn_step

theorem nn_locIdx (b o len : Nat) : NN (locIdx b o len) := by
  unfold locIdx
  repeat nn_step

theorem nn_loadPrep (n : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) (rmw : Bool) :
    NN (loadPrep n ord align p rmw) := by
  unfold loadPrep
  refine nn_bind nn_get fun m => ?_
  refine nn_bind ?_ fun r => ?_
  · split
    · exact nn_lift (rnn_accessW _ _ _ _)
    · exact nn_lift (rnn_access _ _ _ _)
  · obtain ⟨b, _, o⟩ := r
    refine nn_bind (nn_recordAccess _ _ _ _) fun _ => nn_bind (nn_locIdx _ _ _) fun li => ?_
    exact nn_bind nn_get fun _ => nn_pure _

theorem nn_atomicLoadAt {n : Nat} (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    NN (atomicLoadAt (n := n) c ord align p) := by
  unfold atomicLoadAt
  refine nn_bind (nn_loadPrep _ _ _ _ _) fun r => ?_
  obtain ⟨li, opts⟩ := r
  dsimp only
  split
  · refine nn_bind nn_get fun m => nn_bind (nn_modify _) fun _ => ?_
    split
    · exact nn_bind (nn_modify _) fun _ => nn_lift (rnn_intOfBytes _ _ _)
    · exact nn_lift (rnn_intOfBytes _ _ _)
  · exact nn_throw _

theorem nn_storePrep (n : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    NN (storePrep n ord align p) := by
  unfold storePrep
  refine nn_bind nn_get fun m => ?_
  refine nn_bind (nn_lift (rnn_accessW _ _ _ _)) fun r => ?_
  obtain ⟨b, _, o⟩ := r
  refine nn_bind (nn_recordAccess _ _ _ _) fun _ => nn_bind (nn_locIdx _ _ _) fun li => ?_
  exact nn_bind nn_get fun _ => nn_pure _

theorem nn_atomicStoreAt {n : Nat} (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr)
    (v : BitVec n) : NN (atomicStoreAt c ord align p v) := by
  unfold atomicStoreAt
  refine nn_bind (nn_storePrep _ _ _ _) fun r => ?_
  obtain ⟨li, slots⟩ := r
  dsimp only
  split
  · exact nn_bind nn_get fun m => nn_bind (nn_modify _) fun _ => nn_modify _
  · exact nn_throw _

/-- A step that gives a result and no error gives a value. -/
theorem ok_of {α : Type} {x : MemM α} {m : Mem} (hn : NN x)
    (he : ∀ e, (x.run m).run ≠ some (.error e)) : ∃ a m', (x.run m).run = some (.ok (a, m')) := by
  match h : (x.run m).run with
  | none => exact absurd h (hn m)
  | some (.error e) => exact absurd h (he e)
  | some (.ok (a, m')) => exact ⟨a, m', rfl⟩

end IdleLoop.Client
