import IdleLoop.Basic

/-!
# Memory steps that always give a result

A `MemM` step can give a value, an error, or no result (`none`). Safety rules exclude errors;
a progress proof must also exclude `none`. `NN x` says that `x` gives a value or an error from
every memory. These facts specialize the general `ZigLean` semantic lemmas without walking
the memory model in the fixture. With the client's no-error facts, its atomic steps give a value.
-/

namespace IdleLoop.Client

open Zig

/-- `x` gives a value or an error from every memory. -/
def NN {α : Type} (x : MemM α) : Prop := ∀ m, (x.run m).run ≠ none

theorem nn_pure {α : Type} (a : α) : NN (pure a : MemM α) :=
  M.pure_run_ne_none a

theorem nn_bind {α β : Type} {x : MemM α} {f : α → MemM β} (hx : NN x) (hf : ∀ a, NN (f a)) :
    NN (x >>= f) :=
  M.bind_run_ne_none hx hf

theorem nn_get : NN (get : MemM Mem) := M.get_run_ne_none

theorem nn_set (x : Mem) : NN (set x : MemM PUnit) := M.set_run_ne_none x

theorem nn_modify (f : Mem → Mem) : NN (modify f : MemM PUnit) := M.modify_run_ne_none f

theorem nn_throw {α : Type} (e : Error) : NN (throw e : MemM α) := M.throw_run_ne_none e

theorem nn_lift {α : Type} {r : Result α} (hr : r.run ≠ none) : NN (StateT.lift r : MemM α) :=
  M.lift_run_ne_none hr

theorem rnn_pure {α : Type} (a : α) : (pure a : Result α).run ≠ none :=
  Result.pure_run_ne_none a

theorem rnn_throw {α : Type} (e : Error) : (throw e : Result α).run ≠ none :=
  Result.throw_run_ne_none e

theorem rnn_bind {α β : Type} {r : Result α} {f : α → Result β} (hr : r.run ≠ none)
    (hf : ∀ a, (f a).run ≠ none) : (r >>= f).run ≠ none :=
  Result.bind_run_ne_none hr hf

theorem rnn_access (m : Mem) (p : Ptr) (n a : Nat) : (m.access p n a).run ≠ none :=
  m.access_run_ne_none p n a

theorem rnn_accessW (m : Mem) (p : Ptr) (n a : Nat) : (m.accessW p n a).run ≠ none :=
  m.accessW_run_ne_none p n a

theorem rnn_intOfBytes (n : Nat) (bs : Array Byte) (trunc : Bool) :
    (intOfBytes n bs trunc).run ≠ none :=
  intOfBytes_run_ne_none n bs trunc

theorem nn_recordAccess (b o len : Nat) (k : AccessKind) : NN (recordAccess b o len k) :=
  recordAccess_run_ne_none b o len k

theorem nn_retireAt (b o len : Nat) : NN (retireAt b o len) := retireAt_run_ne_none b o len

theorem nn_locIdx (b o len : Nat) : NN (locIdx b o len) := locIdx_run_ne_none b o len

theorem nn_loadPrep (n : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) (rmw : Bool) :
    NN (loadPrep n ord align p rmw) :=
  loadPrep_run_ne_none n ord align p rmw

theorem nn_atomicLoadAt {n : Nat} (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    NN (atomicLoadAt (n := n) c ord align p) :=
  atomicLoadAt_run_ne_none c ord align p

theorem nn_storePrep (n : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    NN (storePrep n ord align p) :=
  storePrep_run_ne_none n ord align p

theorem nn_atomicStoreAt {n : Nat} (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr)
    (v : BitVec n) : NN (atomicStoreAt c ord align p v) :=
  atomicStoreAt_run_ne_none c ord align p v

/-- A step that gives a result and no error gives a value. -/
theorem ok_of {α : Type} {x : MemM α} {m : Mem} (hn : NN x)
    (he : ∀ e, (x.run m).run ≠ some (.error e)) : ∃ a m', (x.run m).run = some (.ok (a, m')) := by
  obtain ⟨⟨a, m'⟩, h⟩ := Result.exists_ok_of_run_ne_none (hn m) he
  exact ⟨a, m', h⟩

end IdleLoop.Client
