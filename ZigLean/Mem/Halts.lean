import ZigLean.Mem.Thread

/-!
# Steps that have a result

A run in `MemM` gives a value, an error, or no result (`none`: a loop that does not end, by
`partial_fixpoint`). `MemM.Halts x`: from every memory, `x` gives a value or an error. The
memory primitives (`load`, `store`, `alloc`, `free`, `ptrProject`, the bounds checks), the
atomic ops (`atomicLoadAt`, `atomicStoreAt`, `atomicRmwAt`, `cmpxchgAt`) and the scheduler's
parts of the sync ops (`Thread.fork`, `Thread.join`, `Thread.futexWake`,
`Thread.checkJoinedByChild`) halt; `bind`, `pure`, `throw`, `get`, `set`, `modify` and lifts
of a halting `Result` keep it. `halts` proves it for a straight-line composition of these.

This is the termination half of a step only: a step may still throw (`.illegal`, a race).
Concurrent termination (`ZigLean/Conc/Stops.lean`) counts turns between such steps.
-/

namespace Zig

variable {α β : Type}

/-- `r` has a result: a value or an error, not "no result". -/
def Result.Halts (r : Result α) : Prop := r.run ≠ none

/-- From every memory, `x` gives a value or an error. -/
def MemM.Halts (x : MemM α) : Prop := ∀ m, (x.run m).Halts

namespace Result.Halts

theorem pure' (a : α) : (pure a : Result α).Halts := by
  simp [Result.Halts, pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

theorem throw' (e : Error) : (throw e : Result α).Halts := by
  simp [Result.Halts, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.run]

theorem bind' {r : Result α} {f : α → Result β} (hr : r.Halts) (hf : ∀ a, (f a).Halts) :
    (r >>= f).Halts := by
  unfold Result.Halts at *
  rw [ExceptT.run_bind]
  match h : r.run, hr with
  | some (.error _), _ => simp [pure]
  | some (.ok a), _ => simpa using hf a

theorem map' {r : Result α} {f : α → β} (hr : r.Halts) : (f <$> r).Halts := by
  unfold Result.Halts at *
  rw [ExceptT.run_map]
  match h : r.run, hr with
  | some _, _ => simp

end Result.Halts

namespace MemM.Halts

variable {x : MemM α} {f : α → MemM β}

theorem pure' (a : α) : (pure a : MemM α).Halts := fun _ => by
  simp [Result.Halts, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

theorem bind' (hx : x.Halts) (hf : ∀ a, (f a).Halts) : (x >>= f).Halts := fun m => by
  unfold Result.Halts
  rw [StateT.run_bind, ExceptT.run_bind]
  have := hx m
  unfold Result.Halts at this
  match h : (x.run m).run, this with
  | some (.error _), _ => simp [pure]
  | some (.ok (a, m')), _ =>
    have := hf a m'
    unfold Result.Halts at this
    simpa using this

theorem map' (hx : x.Halts) {g : α → β} : (g <$> x).Halts := by
  rw [map_eq_pure_bind]; exact bind' hx fun _ => pure' _

theorem seq' {y : MemM β} (hx : x.Halts) (hy : y.Halts) : (x *> y).Halts := by
  rw [seqRight_eq_bind]; exact bind' hx fun _ => hy

theorem get' : (get : MemM Mem).Halts := fun _ => by
  simp [Result.Halts, get, getThe, MonadStateOf.get, StateT.get, StateT.run, pure,
    ExceptT.pure, ExceptT.mk, ExceptT.run]

theorem set' (m' : Mem) : (set m' : MemM PUnit).Halts := fun _ => by
  simp [Result.Halts, set, StateT.set, StateT.run, pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

theorem modify' (g : Mem → Mem) : (modify g : MemM PUnit).Halts := fun _ => by
  simp [Result.Halts, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run,
    pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

theorem throw' (e : Error) : (throw e : MemM α).Halts := fun _ => by
  simp [Result.Halts, throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift,
    ExceptT.mk, ExceptT.run, ExceptT.bind, ExceptT.bindCont, bind, Option.bind]

theorem lift' {r : Result α} (hr : r.Halts) : MemM.Halts (StateT.lift r : MemM α) := fun _ => by
  unfold Result.Halts at *
  simp only [StateT.run, StateT.lift, ExceptT.run_bind]
  match h : r.run, hr with
  | some (.error _), _ => simp [pure]
  | some (.ok _), _ => simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

theorem liftM' {r : Result α} (hr : r.Halts) : MemM.Halts (liftM r : MemM α) := lift' hr

theorem monadLift' {r : Result α} (hr : r.Halts) : MemM.Halts (monadLift r : MemM α) := lift' hr

theorem ite' {c : Prop} [Decidable c] {x y : MemM α} (hx : x.Halts) (hy : y.Halts) :
    (if c then x else y).Halts := by
  split <;> assumption

theorem of_fun {g : Mem → Result (α × Mem)} (h : ∀ m, (g m).Halts) : MemM.Halts (α := α) g := h

end MemM.Halts

/-! ## Primitives -/

/-- Decoding a value always gives a value or an error. -/
class EncHalts (α : Type) [Enc α] : Prop where
  decode_halts : ∀ bs, (Enc.decode bs : Result α).Halts

theorem intOfBytes_halts (n : Nat) (bs : Array Byte) (trunc : Bool) :
    (intOfBytes n bs trunc).Halts := by
  unfold intOfBytes
  generalize (bs.extract 0 ((n + 7) / 8)).zipIdx = l
  rw [← Array.foldr_toList]
  induction l.toList with
  | nil => exact Result.Halts.pure' _
  | cons x xs ih =>
    rw [List.foldr_cons]
    refine Result.Halts.bind' ih fun hi => ?_
    split
    · exact Result.Halts.pure' _
    · exact Result.Halts.throw' _

instance {n : Nat} : EncHalts (BitVec n) := ⟨fun bs => intOfBytes_halts n bs false⟩

instance : EncHalts Ptr where
  decode_halts bs := by
    show (match (bs[0]? : Option Byte) with
      | some (.ptrFrag p _) =>
        if bs.extract 0 8 == (Array.finRange 8).map (.ptrFrag p) then pure p else throw .unspecified
      | some (.int _) => do
        let n ← intOfBytes 64 bs
        pure ⟨none, n.toNat⟩
      | _ => throw .unspecified : Result Ptr).Halts
    split
    · split
      · exact Result.Halts.pure' _
      · exact Result.Halts.throw' _
    · exact Result.Halts.bind' (intOfBytes_halts _ _ _) fun _ => Result.Halts.pure' _
    · exact Result.Halts.throw' _

theorem decodeLoad_halts {T : Type} [Enc T] [EncHalts T] (blocks : Array Block) (bs : Array Byte) :
    (decodeLoad (α := T) blocks bs).Halts := by
  unfold decodeLoad Result.Halts
  simp only [ExceptT.run_mk]
  split
  · split
    · exact EncHalts.decode_halts _
    · simp
  · rename_i r hr
    intro h
    exact EncHalts.decode_halts (α := T) bs (by rw [ExceptT.run] at *; simp_all)

/-- A halting leaf step: extend with `macro_rules | `(tactic| halts_leaf) => ...`. -/
syntax "halts_leaf" : tactic

macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact Result.Halts.pure' _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact Result.Halts.throw' _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact MemM.Halts.pure' _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact MemM.Halts.get')
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact MemM.Halts.set' _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact MemM.Halts.modify' _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact MemM.Halts.throw' _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact intOfBytes_halts _ _ _)

/-- `halts`: a straight-line composition of halting steps halts (`halts_leaf` for the leaves). -/
syntax "halts" : tactic

macro_rules
  | `(tactic| halts) => `(tactic| repeat (first
      | halts_leaf
      | assumption
      | (with_reducible apply MemM.Halts.bind' <;> try intro)
      | with_reducible apply MemM.Halts.map'
      | with_reducible apply MemM.Halts.lift'
      | with_reducible apply MemM.Halts.liftM'
      | with_reducible apply MemM.Halts.monadLift'
      | (with_reducible apply Result.Halts.bind' <;> try intro)
      | with_reducible apply Result.Halts.map'
      | dsimp only
      | split))

theorem access_halts (m : Mem) (p : Ptr) (n a : Nat) : (m.access p n a).Halts := by
  unfold Mem.access; halts

theorem accessW_halts (m : Mem) (p : Ptr) (n a : Nat) : (m.accessW p n a).Halts := by
  unfold Mem.accessW
  exact Result.Halts.bind' (access_halts _ _ _ _) fun _ => by halts

theorem recordAccess_halts (b o n : Nat) (k : AccessKind) : (recordAccess b o n k).Halts := by
  unfold recordAccess; halts

theorem loadBytes_halts (p : Ptr) (n a : Nat) (k : AccessKind) : (loadBytes p n a k).Halts := by
  unfold loadBytes
  refine MemM.Halts.bind' MemM.Halts.get' fun m => ?_
  refine MemM.Halts.bind' (MemM.Halts.lift' (access_halts _ _ _ _)) fun _ => ?_
  exact MemM.Halts.bind' (recordAccess_halts _ _ _ _) fun _ => MemM.Halts.pure' _

theorem load_halts (T : Type) [Enc T] [EncHalts T] (a : Nat) (p : Ptr) : (load T a p).Halts := by
  unfold load
  refine MemM.Halts.bind' (loadBytes_halts _ _ _ _) fun bs => ?_
  exact MemM.Halts.bind' MemM.Halts.get' fun m => MemM.Halts.lift' (decodeLoad_halts (T := T) _ _)

theorem storeBytes_halts (p : Ptr) (a : Nat) (bs : Array Byte) (k : AccessKind) :
    (storeBytes p a bs k).Halts := by
  unfold storeBytes
  refine MemM.Halts.bind' MemM.Halts.get' fun m => ?_
  refine MemM.Halts.bind' (MemM.Halts.lift' (accessW_halts _ _ _ _)) fun _ => ?_
  exact MemM.Halts.bind' (recordAccess_halts _ _ _ _) fun _ => by halts

theorem store_halts {T : Type} [Enc T] (a : Nat) (p : Ptr) (v : T) : (store a p v).Halts :=
  storeBytes_halts _ _ _ _

theorem storeUndef_halts (T : Type) [Enc T] (a : Nat) (p : Ptr) : (storeUndef T a p).Halts :=
  storeBytes_halts _ _ _ _

theorem alloc_halts (k : BlockKind) (size a : Nat) : (alloc k size a).Halts := by
  unfold alloc; halts

theorem allocStack_halts (size a : Nat) : (allocStack size a).Halts := alloc_halts _ _ _

theorem free_halts (p : Ptr) : (free p).Halts := by
  unfold free; halts

theorem ptrProject_halts (p : Ptr) (f : Ptr → Ptr) : (ptrProject p f).Halts := by
  intro m
  unfold ptrProject
  simp only [StateT.run]
  split
  · exact MemM.Halts.pure' _ m
  · exact MemM.Halts.throw' _ m

theorem checkIndex_halts {n : Nat} (len i : BitVec n) : (checkIndex len i).Halts := by
  unfold checkIndex; halts

theorem checkSliceEnd_halts (len start l : BitVec 64) (e : Nat) :
    (checkSliceEnd len start l e).Halts := by
  unfold checkSliceEnd; halts

/-! ## Atomic ops and the scheduler's part of the sync ops -/

macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact access_halts _ _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact accessW_halts _ _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact recordAccess_halts _ _ _ _)

theorem locIdx_halts (b o n : Nat) : (locIdx b o n).Halts := by
  unfold locIdx; halts

macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact locIdx_halts _ _ _)

theorem loadPrep_halts (n : Nat) (ord : AtomicOrder) (a : Nat) (p : Ptr) (rmw : Bool) :
    (loadPrep n ord a p rmw).Halts := by
  unfold loadPrep; halts

theorem storePrep_halts (n : Nat) (ord : AtomicOrder) (a : Nat) (p : Ptr) :
    (storePrep n ord a p).Halts := by
  unfold storePrep; halts

theorem casReadPrep_halts (n a : Nat) (p : Ptr) : (casReadPrep n a p).Halts := by
  unfold casReadPrep; halts

theorem rmwWrite_halts {n : Nat} (li pos : Nat) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) :
    (rmwWrite li pos ord rd new).Halts := by
  unfold rmwWrite acquireClock insertMsg observe; halts

macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact loadPrep_halts _ _ _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact storePrep_halts _ _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact casReadPrep_halts _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact rmwWrite_halts _ _ _ _ _)

theorem atomicLoadAt_halts {n : Nat} (c : Nat) (ord : AtomicOrder) (a : Nat) (p : Ptr) :
    (atomicLoadAt (n := n) c ord a p).Halts := by
  unfold atomicLoadAt observe acquireClock; halts

theorem atomicStoreAt_halts {n : Nat} (c : Nat) (ord : AtomicOrder) (a : Nat) (p : Ptr)
    (v : BitVec n) : (atomicStoreAt c ord a p v).Halts := by
  unfold atomicStoreAt insertMsg observe; halts

theorem atomicRmwAt_halts {n : Nat} (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
    (a : Nat) (p : Ptr) (v : BitVec n) : (atomicRmwAt c op signed ord a p v).Halts := by
  unfold atomicRmwAt; halts

theorem cmpxchgAt_halts {n : Nat} (c : Nat) (succ fail : AtomicOrder) (a : Nat) (p : Ptr)
    (e new : BitVec n) : (cmpxchgAt c succ fail a p e new).Halts := by
  unfold cmpxchgAt casPrep casMarkWrite observe acquireClock; halts

theorem fork_halts : Thread.fork.Halts := by
  unfold Thread.fork Thread.forkWith; halts

theorem forkGated_halts : Thread.forkGated.Halts := by
  unfold Thread.forkGated Thread.forkWith; halts

theorem join_halts (tid : ThreadId) : (Thread.join tid).Halts := by
  unfold Thread.join; halts

theorem futexWake_halts (p : Ptr) (n : Nat) (cs : List Nat) : (Thread.futexWake p n cs).Halts := by
  unfold Thread.futexWake; halts

theorem checkJoinedByChild_halts (t : ThreadId) : (Thread.checkJoinedByChild t).Halts := by
  unfold Thread.checkJoinedByChild; halts

macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact load_halts _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact store_halts _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact storeUndef_halts _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact allocStack_halts _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact alloc_halts _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact free_halts _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact ptrProject_halts _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact checkIndex_halts _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact checkSliceEnd_halts _ _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact atomicLoadAt_halts _ _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact atomicStoreAt_halts _ _ _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact atomicRmwAt_halts _ _ _ _ _ _ _)
macro_rules | `(tactic| halts_leaf) => `(tactic| with_reducible exact cmpxchgAt_halts _ _ _ _ _ _ _)

end Zig
