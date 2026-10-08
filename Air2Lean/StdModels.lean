import Std.Data.HashMap

/-! # Built-in std model registry

The single table of qualified standard-library names that the translator recognizes
(`docs/std-models.md`, `docs/external-models.md`). `Check.lean`, `Emit.lean`, `Memory.lean`,
`Diagnose.lean` and the project registry (`ModelRegistry.lean`) consult it through
`stdModel?` and the typed projections below; none of them carries its own name table.

Each entry records the typed model it selects, its Zig-version qualification (empty: every
audited version; the checked AIR profile still applies), and its semantic dependencies: the
`ZigLean` declarations the emitter may reference for it. `tests/roadmap/models/StdModels.lean`
checks that every dependency exists in the `ZigLean` environment. Adding a model means one row
here, one typed signature case in `checkModelSignature` and one emission case; no name test. -/
namespace Air2Lean

/-- A function of `std.mem.Allocator` that the model has (`ZigLean/Mem/Alloc.lean`). -/
inductive AllocFn where
  | create | destroy | alloc | alignedAlloc | allocSentinel | free | dupe | remap | realloc
  deriving BEq, Repr

/-- `std.Thread.spawn`/`.join`/`.detach`, modelled like `AllocFn` (`ZigLean/Mem/Thread.lean`). -/
inductive ThreadFn where
  | spawn | join
  /-- `Thread.detach` (C07): the handle is consumed and the thread runs on (`Zig.detachC`). -/
  | detach
  /-- Progress hints: scheduler opportunity, with no fairness guarantee. -/
  | yield | spinLoopHint
  /-- `Io.futexWait` (cancelable), `Io.futexWaitUncancelable`, `Io.futexWake` (0.16.0). -/
  | futexWait | futexWaitU | futexWake
  /-- `Thread.Futex.wait`, `Thread.Futex.wake`. -/
  | threadFutexWait | threadFutexWake
  /-- `Thread.Mutex.DarwinImpl.lock`, `.unlock`, `.tryLock` (0.15.2 on macOS): each is one call of
  `os_unfair_lock_*`, a C function (the exporter does not name an `extern` function). -/
  | osLock | osUnlock | osTryLock
  /-- `time.Timer.start`, `time.Timer.read`, `Thread.Futex.timedWait`: a clock, which the model
  does not have. `Thread.Futex.Deadline` reaches them only with a timeout, so a call is
  `.unsupportedTimer` at run time (distinct from `.unspecified`), not a rejection. Each has its
  own runtime signature (`checkModelSignature`). -/
  | timerStart | timerRead | futexTimedWait
  /-- `Io.Group.async`, `.concurrent`, `.await`, `.cancel` (0.16.0): a task is a thread. -/
  | groupAsync | groupConcurrent | groupAwait | groupCancel
  /-- `Io.async`, `Io.Future(T).await`, `Io.Future(T).cancel`, `Io.checkCancel` (0.16.0 only;
  `ZigLean/Conc/Future.lean`, `docs/futures.md`): a future's task is a thread with a result. -/
  | futureAsync | futureAwait | futureCancel | checkCancel
  deriving BEq, Repr

/-- What a recognized std name selects: an allocator or thread model, or an explicit
rejection (outside the fork-join subset) with its reason. -/
inductive StdModelKind where
  | alloc (fn : AllocFn)
  | thread (fn : ThreadFn)
  | rejected (reason : String)
  deriving BEq, Repr

structure StdModel where
  /-- The qualified std name; an instance `<symbol>__anon_<n>` selects the same model. -/
  symbol : String
  kind : StdModelKind
  /-- Zig versions this model is qualified for; empty means every audited version. -/
  zigVersions : Array String := #[]
  /-- `ZigLean` declarations the emitted term may reference (the semantic dependencies). -/
  dependencies : Array String := #[]
  deriving Repr

def StdModel.qualifies (m : StdModel) (zigVersion : String) : Bool :=
  m.zigVersions.isEmpty || m.zigVersions.contains zigVersion

private def allocModel (symbol : String) (fn : AllocFn) (deps : Array String)
    (zigVersions : Array String := #[]) : StdModel :=
  { symbol, kind := .alloc fn, zigVersions, dependencies := deps.map ("Zig.Allocator." ++ ·) }
private def threadModel (symbol : String) (fn : ThreadFn) (deps : Array String)
    (zigVersions : Array String := #[]) : StdModel :=
  { symbol, kind := .thread fn, zigVersions, dependencies := deps.map ("Zig." ++ ·) }

/-- The reason of an async API outside the qualified future subset (`docs/futures.md`). -/
private def asyncReason (symbol reason : String) : String :=
  s!"{symbol} is not a qualified async API: {reason} (docs/futures.md)"

/-- The one table of built-in std models. -/
def stdModels : Array StdModel := #[
  allocModel "mem.Allocator.create" .create #["create"],
  allocModel "mem.Allocator.destroy" .destroy #["destroy"],
  allocModel "mem.Allocator.alloc" .alloc #["alloc"],
  allocModel "mem.Allocator.alignedAlloc" .alignedAlloc #["alloc"],
  allocModel "mem.Allocator.allocSentinel" .allocSentinel #["allocSentinel"] #["0.16.0"],
  allocModel "mem.Allocator.free" .free #["free", "freeSentinel"],
  allocModel "mem.Allocator.dupe" .dupe #["dupe"],
  allocModel "mem.Allocator.remap" .remap #["remap"],
  allocModel "mem.Allocator.realloc" .realloc #["realloc"] #["0.16.0"],
  threadModel "Thread.spawn" .spawn #["spawnC", "spawnWithPolicyC"],
  threadModel "Thread.join" .join #["joinC"],
  threadModel "Thread.detach" .detach #["detachC"] #["0.16.0"],
  threadModel "Thread.yield" .yield #["threadYieldC"],
  threadModel "atomic.spinLoopHint" .spinLoopHint #["spinLoopHintC"],
  threadModel "Thread.spinLoopHint" .spinLoopHint #["spinLoopHintC"],
  threadModel "Io.futexWait" .futexWait #["futexWaitCancelableC"],
  threadModel "Io.futexWaitUncancelable" .futexWaitU #["futexWaitC"],
  threadModel "Io.futexWake" .futexWake #["futexWakeC"],
  threadModel "Thread.Futex.wait" .threadFutexWait #["threadFutexWaitC"],
  threadModel "Thread.Futex.wake" .threadFutexWake #["threadFutexWakeC"],
  threadModel "Thread.Mutex.DarwinImpl.lock" .osLock #["osUnfairLockC"],
  threadModel "Thread.Mutex.DarwinImpl.unlock" .osUnlock #["osUnfairUnlockC"],
  threadModel "Thread.Mutex.DarwinImpl.tryLock" .osTryLock #["osUnfairTryLockC"],
  threadModel "time.Timer.start" .timerStart #["callRC", "Error.unsupportedTimer"],
  threadModel "time.Timer.read" .timerRead #["callRC", "Error.unsupportedTimer"],
  threadModel "Thread.Futex.timedWait" .futexTimedWait #["callRC", "Error.unsupportedTimer"],
  threadModel "Io.Group.async" .groupAsync #["groupAsyncC", "groupAsyncWithPolicyC"],
  threadModel "Io.Group.concurrent" .groupConcurrent #["groupConcurrentC", "groupConcurrentWithPolicyC"],
  threadModel "Io.Group.await" .groupAwait #["groupAwaitC"],
  threadModel "Io.Group.cancel" .groupCancel #["groupCancelC"],
  threadModel "Io.async" .futureAsync #["asyncC", "asyncWithPolicyC", "Future.complete"] #["0.16.0"],
  threadModel "Io.Future.await" .futureAwait #["awaitC"] #["0.16.0"],
  threadModel "Io.Future.cancel" .futureCancel #["cancelC"] #["0.16.0"],
  threadModel "Io.checkCancel" .checkCancel #["checkCancelC"] #["0.16.0"],
  { symbol := "Io.concurrent",
    kind := .rejected (asyncReason "Io.concurrent" "its guaranteed unit of concurrency and ConcurrencyUnavailable outcome are not modelled for futures") },
  { symbol := "Io.recancel",
    kind := .rejected (asyncReason "Io.recancel" "re-arming an acknowledged cancelation is not modelled") },
  { symbol := "Io.swapCancelProtection",
    kind := .rejected (asyncReason "Io.swapCancelProtection" "cancel protection is not modelled") },
  { symbol := "Io.Select.async",
    kind := .rejected (asyncReason "Io.Select.async" "Select queues task results; only Io.async futures are qualified") },
  { symbol := "Io.Select.concurrent",
    kind := .rejected (asyncReason "Io.Select.concurrent" "Select queues task results; only Io.async futures are qualified") },
  { symbol := "Io.Select.await",
    kind := .rejected (asyncReason "Io.Select.await" "Select queues task results; only Io.async futures are qualified") },
  { symbol := "Io.Select.cancel",
    kind := .rejected (asyncReason "Io.Select.cancel" "Select queues task results; only Io.async futures are qualified") },
  { symbol := "Io.Select.cancelDiscard",
    kind := .rejected (asyncReason "Io.Select.cancelDiscard" "Select queues task results; only Io.async futures are qualified") },
  { symbol := "Io.Batch.awaitAsync",
    kind := .rejected (asyncReason "Io.Batch.awaitAsync" "Io operations and batches are not modelled") },
  { symbol := "Io.Batch.awaitConcurrent",
    kind := .rejected (asyncReason "Io.Batch.awaitConcurrent" "Io operations and batches are not modelled") },
  { symbol := "Io.Batch.cancel",
    kind := .rejected (asyncReason "Io.Batch.cancel" "Io operations and batches are not modelled") },
  { symbol := "Io.operate",
    kind := .rejected (asyncReason "Io.operate" "Io operations and batches are not modelled") },
  { symbol := "Io.operateTimeout",
    kind := .rejected (asyncReason "Io.operateTimeout" "Io operations and batches are not modelled") },
  { symbol := "Io.sleep",
    kind := .rejected (asyncReason "Io.sleep" "it has no clock") },
  { symbol := "Io.futexWaitTimeout",
    kind := .rejected "Io.futexWaitTimeout is outside the model: it has no clock" }]
  -- The cancelation points of the model (`docs/std-models.md` §Cancelation, C05/C08):
  -- `Io.futexWait` (and the std code over it), `Io.Group.await` and `Io.checkCancel`; the
  -- requests come from `Io.Group.cancel` and `Io.Future.cancel`. Every other cancelable `std.Io`
  -- API above is rejected with its reason.

private def stdModelIndex : Std.HashMap String StdModel :=
  stdModels.foldl (fun index m => index.insert m.symbol m) {}

/-- The qualified std name of `name`: an instance `<fn>__anon_<n>` names its generic `<fn>`, and
a method of an instantiated generic type `Io.Future(T).<fn>` or `Io.Select(U).<fn>` names
`Io.Future.<fn>` or `Io.Select.<fn>` (the type argument is everything up to the last `).`). -/
def stdModelBase (name : String) : String :=
  let base := (name.splitOn "__anon_").head!
  let generic (ty : String) : Option String := do
    unless base.startsWith (ty ++ "(") do none
    let parts := base.splitOn ")."
    unless parts.length ≥ 2 do none
    some s!"{ty}.{parts.getLast!}"
  ((generic "Io.Future").orElse fun _ => generic "Io.Select").getD base

/-- The built-in std model (modelled or rejected) that the function `name` is an instance of. -/
def stdModel? (name : String) : Option StdModel := stdModelIndex[stdModelBase name]?

private def stdKind? (name : String) : Option StdModelKind := (stdModel? name).map (·.kind)

/-- The allocator function that the function `name` is an instance of
(`mem.Allocator.<fn>__anon_<n>`). -/
def allocFn? (name : String) : Option AllocFn :=
  match stdKind? name with
  | some (.alloc fn) => some fn
  | _ => none

/-- The `Thread` function that the function `name` is an instance of
(`Thread.spawn__anon_<n>`, `Thread.join`, `Thread.detach`). -/
def threadFn? (name : String) : Option ThreadFn :=
  match stdKind? name with
  | some (.thread fn) => some fn
  | _ => none

/-- A thread or sync primitive outside the fork-join subset (`docs/std-models.md` §Thread
model): `Check.lean` rejects a call to one of these, with this reason. -/
def rejectedThreadFn? (name : String) : Option String :=
  match stdKind? name with
  | some (.rejected reason) => some reason
  | _ => none

/-- `name` selects an allocator or thread model (not a rejection). -/
def modelledStdFn (name : String) : Bool :=
  match stdKind? name with
  | some (.alloc _) | some (.thread _) => true
  | _ => false

end Air2Lean
