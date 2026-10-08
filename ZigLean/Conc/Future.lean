import ZigLean.Conc.Spawn

/-!
# `std.Io.Future` (Zig 0.16.0)

The qualified future API is `Io.async(function, args)`, `Future(T).await(io)`,
`Future(T).cancel(io)` and the cancelation point `Io.checkCancel(io)`
(`docs/futures.md`). `Io.Group` is a separate model (`ZigLean/Conc/Call.lean`); its support
does not extend to futures, and the two are qualified separately.

- **Task states.** A future is *pending* while its `any_future` handle names a runtime record
  (`task = some slot`): the task is a thread of the model, *running* until it ends and
  *completed* once it has written its result into the record. `await`/`cancel` *consume* the
  record: they join the thread, copy the result into `Future.result`, free the record and set
  `any_future = null` (`task = none`). A future that `Io.async` ran in the caller (the
  fallible policy's eager branch) is born consumed.
- **Await** joins the task and returns its complete result, so an error union result
  (`E!T`) propagates its error to the awaiter unchanged.
- **Cancel** first records a cancelation request for the task (`Mem.cancels`), then awaits it.
  The task observes the request only at a cancelation point (`checkCancelC`), which acknowledges
  it and returns `error.Canceled`; a task that completes without reaching one returns its
  ordinary result. A request that is never acknowledged is dropped when `cancel` returns.
- **Idempotence.** As in std, `await` and `cancel` on a consumed future return the stored
  `result` again; they do not touch the task.
- **Not threadsafe.** Both operations read and write the `Future` value with plain accesses, so
  two threads that await or cancel one future concurrently race (`.illegal`). Only the thread
  that called `Io.async` may consume the future: the join of another thread is `.illegal`
  (`Thread.join`).
- **A future must be consumed.** The runtime record and the task are released only by
  `await`/`cancel` (`Io.Threaded` destroys its `Future` there). The task is a thread of its
  spawner, so a spawner that ends with an unconsumed future fails `checkJoinedByChild`
  (`.illegal`).
- **Ownership.** The task receives its by-value argument tuple as a spawn target and owns the
  result cells of the runtime record until the join returns them to the awaiter
  (`Zig.Conc.Capture`, `Zig.Conc.Transfer`).

The runtime record (`Io.AnyFuture`) has the layout of the future itself: the task's thread id
where `any_future` is, the result at `Future.resultOff`.
-/

namespace Zig

/-- `std.Io.Future(T)`: `any_future: ?*AnyFuture` (the model's runtime record) and `result: T`,
whose bytes are undefined (`none`) until the task has been consumed or ran eagerly. -/
structure Future (α : Type) where
  task : Option Ptr
  result : Option α
  deriving Repr, Inhabited

namespace Future

variable (α : Type) [Enc α]

/-- The offset of `result`: after the 8-byte `any_future`. -/
def resultOff : Nat := alignUp 8 (Enc.align α)

def align : Nat := Nat.max 8 (Enc.align α)

def size : Nat := alignUp (resultOff α + Enc.size α) (align α)

variable {α}

/-- The bytes of a future: `any_future`, then the result if it is defined. -/
def bytes (f : Future α) : Array Byte :=
  let bs := writeBytes (Array.replicate (size α) .undef) 0 (Enc.encode f.task)
  match f.result with
  | some r => writeBytes bs (resultOff α) (Enc.encode r)
  | none => bs

/-- A result whose bytes are all undefined is `none`; a zero-sized result is always defined. -/
def decodeResult (bs : Array Byte) : Result (Option α) :=
  if Enc.size α ≠ 0 ∧ bs.all (· == .undef) then pure none else some <$> Enc.decode bs

instance instEnc : Enc (Future α) where
  size := size α
  align := align α
  encode := bytes
  decode bs := do
    let task ← (Enc.decode (bs.extract 0 8) : Result (Option Ptr))
    let result ← decodeResult (bs.extract (resultOff α) (resultOff α + Enc.size α))
    pure { task, result }

/-- The stored result of a consumed future: undefined bytes are `.unspecified`. -/
def settled (f : Future α) : Result α :=
  match f.result with
  | some r => pure r
  | none => throw .unspecified

/-- `Io.Threaded.Future.create`: a runtime record for a task with result type `α`. -/
def slotAlloc (α : Type) [Enc α] : MemM Ptr := alloc .heap (size α) (align α)

/-- The task's last step: `result_casted.* = @call(function, args)` into the runtime record. -/
def complete (slot : Ptr) (r : α) : MemM Unit :=
  store (Enc.align α) (slot.add (resultOff α)) r

/-- `@memcpy(result, future.resultPointer()); future.destroy(gpa)`: the result, then the record
is freed. -/
def take (α : Type) [Enc α] (slot : Ptr) : MemM α := do
  let r ← load α (Enc.align α) (slot.add (resultOff α))
  free slot
  pure r

/-- A cancelation request for the task `tid` (idempotent). -/
def requestCancel (tid : ThreadId) : MemM Unit := modify fun m =>
  if m.cancels.contains tid then m else { m with cancels := m.cancels.push tid }

/-- `cancel` returns: a request that the task did not acknowledge is dropped. -/
def dropCancel (tid : ThreadId) : MemM Unit := modify fun m =>
  { m with cancels := m.cancels.erase tid }

/-- A cancelation point of the current thread: an outstanding request is acknowledged and
becomes `error.Canceled`; later points do not signal it again. -/
def takeCancel : MemM (Except ErrName Unit) := do
  let m ← get
  if m.cancels.contains m.current then
    set { m with cancels := m.cancels.erase m.current }
    pure (.error "Canceled")
  else pure (.ok ())

end Future

instance {α : Type} [Enc α] : Enc (Future α) := Future.instEnc

variable {Tgt σ α : Type} [Enc α]

/-- `Io.async(function, args)` when a unit of concurrency is assigned: a runtime record, then a
spawn of the task `mk slot` (the generated target writes the worker's result with
`Future.complete slot`). The spawner writes the task's id into the record. -/
def asyncC (mk : Ptr → Tgt) : CM Tgt σ (Future α) := do
  let slot ← callMC (Future.slotAlloc α)
  let tid : ThreadId ← StateT.lift (ConcM.sync (.spawn (mk slot)))
  callMC (store 8 slot tid)
  pure { task := some slot, result := none }

/-- The caller's eager execution (`start(context.ptr, result.ptr)` before `async` returns): the
future is born consumed, with no record, thread or ownership transfer. -/
def asyncEagerC (eager : ConcM Tgt α) : CM Tgt σ (Future α) := do
  let r ← callC eager
  pure { task := none, result := some r }

/-- Choice zero assigns a unit of concurrency; any other runs the task in the caller. -/
def asyncOutcomeC (choice : Nat) (mk : Ptr → Tgt) (eager : ConcM Tgt α) : CM Tgt σ (Future α) :=
  if choice = 0 then asyncC mk else asyncEagerC eager

/-- `available` assumes the runtime assigns every task; `fallible` also covers the audited
`Io.Threaded.async` fallbacks (record allocation failure, the async limit, a failed worker
spawn, single-threaded builds), each of which runs the task in the caller. -/
def asyncWithPolicyC (policy : SpawnPolicy) (mk : Ptr → Tgt) (eager : ConcM Tgt α) :
    CM Tgt σ (Future α) := do
  match policy with
  | .available => asyncC mk
  | .fallible =>
    let choice ← pickC (fun _ => 2)
    asyncOutcomeC choice mk eager

/-- Consume the pending task of the future at `p`: join it, take its result, free the record
and store the consumed future. -/
def consumeC (p : Ptr) (slot : Ptr) (tid : ThreadId) : CM Tgt σ α := do
  joinC tid
  let r ← callMC (Future.take α slot)
  callMC (store (Future.align α) p ({ task := none, result := some r } : Future α))
  pure r

/-- `Future(T).await(io)` on the future at `p`. -/
def awaitC (_ : Io) (p : Ptr) : CM Tgt σ α := do
  let f ← callMC (load (Future α) (Future.align α) p)
  match f.task with
  | none => callRC f.settled
  | some slot =>
    let tid ← callMC (load ThreadId 8 slot)
    consumeC p slot tid

/-- `Future(T).cancel(io)` on the future at `p`: a cancelation request, then as `await`. The
request is an atomic update of the task's status in `Io.Threaded`, so like every atomic op of
the model it follows a scheduling point: the task may reach its cancelation point first. -/
def cancelC (_ : Io) (p : Ptr) : CM Tgt σ α := do
  let f ← callMC (load (Future α) (Future.align α) p)
  match f.task with
  | none => callRC f.settled
  | some slot =>
    let tid ← callMC (load ThreadId 8 slot)
    StateT.lift (discard (ConcM.sync (Tgt := Tgt) .yield))
    callMC (Future.requestCancel tid)
    let r ← consumeC p slot tid
    callMC (Future.dropCancel tid)
    pure r

/-- `Io.checkCancel(io)`: a scheduling point, then the current thread's cancelation point. -/
def checkCancelC (_ : Io) : CM Tgt σ (Except ErrName Unit) := do
  StateT.lift (discard (ConcM.sync (Tgt := Tgt) .yield))
  callMC Future.takeCancel

open Lean.Order in
@[partial_fixpoint_monotone]
theorem monotone_asyncWithPolicyC {γ : Type} [PartialOrder γ]
    (policy : SpawnPolicy) (mk : Ptr → Tgt)
    (f : γ → ConcM Tgt α) (hmono : monotone f) :
    monotone (fun x => (asyncWithPolicyC policy mk (f x) : CM Tgt σ (Future α))) := by
  cases policy with
  | available => exact monotone_const _
  | fallible =>
    unfold asyncWithPolicyC
    apply monotone_bind _ _ _ (monotone_const _)
    apply monotone_of_monotone_apply
    intro choice
    by_cases hc : choice = 0
    · simpa only [asyncOutcomeC, if_pos hc] using
        (monotone_const (asyncC mk : CM Tgt σ (Future α)) :
          monotone (fun _ : γ => (asyncC mk : CM Tgt σ (Future α))))
    · simp only [asyncOutcomeC, if_neg hc, asyncEagerC]
      exact monotone_bind _ _ _ (monotone_callC f hmono) (monotone_const _)

end Zig
