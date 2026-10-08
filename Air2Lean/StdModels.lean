import Std.Data.HashMap

/-! # Built-in std model registry

The single table of qualified standard-library names that the translator recognizes
(`docs/std-models.md`, `docs/external-models.md`). `Check.lean`, `Emit.lean`, `Memory.lean`,
`Diagnose.lean` and the project registry (`ModelRegistry.lean`) consult it through
`stdModel?` and the typed projections below; none of them carries its own name table.

Each entry records the typed model it selects, its Zig-version qualification (empty: every
version in `baseZigVersions`; the checked AIR profile still applies), and its semantic dependencies: the
`ZigLean` declarations the emitter may reference for it. `tests/roadmap/models/StdModels.lean`
checks that every dependency exists in the `ZigLean` environment. Adding a model means one row
here, one typed signature case in `checkModelSignature` and one emission case; no name test. -/
namespace Air2Lean

/-- A function of `std.mem.Allocator` that the model has (`ZigLean/Mem/Alloc.lean`). -/
inductive AllocFn where
  | create | destroy | alloc | alignedAlloc | allocSentinel | free | dupe | remap | realloc
  deriving BEq, Repr

/-- `std.Thread.spawn`/`.join`, modelled like `AllocFn` (`ZigLean/Mem/Thread.lean`). -/
inductive ThreadFn where
  | spawn | join
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
  `.unspecified` at run time (the diff test pins that count), not a rejection. Each has its
  own runtime signature (`checkModelSignature`). -/
  | timerStart | timerRead | futexTimedWait
  /-- `Io.Group.async`, `.concurrent`, `.await`, `.cancel` (0.16.0): a task is a thread. -/
  | groupAsync | groupConcurrent | groupAwait | groupCancel
  deriving BEq, Repr

/-- What a recognized std name selects: an allocator or thread model, or an explicit
rejection (outside the fork-join subset) with its reason. -/
inductive StdModelKind where
  | alloc (fn : AllocFn)
  | thread (fn : ThreadFn)
  | rejected (reason : String)
  deriving BEq, Repr

/-- The Zig versions that a row without an explicit `zigVersions` is qualified for. A later
version is fail-closed: a row qualifies for it only by listing it, after its std source was
re-audited for that version (`docs/std-models.md` §Zig 0.17.0 audit). -/
def baseZigVersions : Array String := #["0.14.1", "0.15.2", "0.16.0"]

/-- `baseZigVersions` and 0.17.0: a row whose std source (name, signature and semantics) did not
change from 0.16.0 to 0.17.0. -/
private def through017 : Array String := baseZigVersions.push "0.17.0"

structure StdModel where
  /-- The qualified std name; an instance `<symbol>__anon_<n>` selects the same model. -/
  symbol : String
  kind : StdModelKind
  /-- Zig versions this model is qualified for; empty means `baseZigVersions`. -/
  zigVersions : Array String := #[]
  /-- `ZigLean` declarations the emitted term may reference (the semantic dependencies). -/
  dependencies : Array String := #[]
  deriving Repr

/-- The Zig versions `m` is qualified for. -/
def StdModel.qualifiedVersions (m : StdModel) : Array String :=
  if m.zigVersions.isEmpty then baseZigVersions else m.zigVersions

/-- A rejection holds in every version; a model only in its qualified versions. -/
def StdModel.qualifies (m : StdModel) (zigVersion : String) : Bool :=
  match m.kind with
  | .rejected _ => true
  | _ => m.qualifiedVersions.contains zigVersion

private def allocModel (symbol : String) (fn : AllocFn) (deps : Array String)
    (zigVersions : Array String := #[]) : StdModel :=
  { symbol, kind := .alloc fn, zigVersions, dependencies := deps.map ("Zig.Allocator." ++ ·) }
private def threadModel (symbol : String) (fn : ThreadFn) (deps : Array String)
    (zigVersions : Array String := #[]) : StdModel :=
  { symbol, kind := .thread fn, zigVersions, dependencies := deps.map ("Zig." ++ ·) }

/-- The one table of built-in std models. Rows without 0.17.0 are 0.17.0-unqualified on purpose
(`docs/std-models.md` §Zig 0.17.0 audit): the `Thread.Futex`, `Thread.Mutex.DarwinImpl`,
`time.Timer` and `Thread.spinLoopHint` rows name std declarations that 0.16.0 and 0.17.0 no
longer have. -/
def stdModels : Array StdModel := #[
  allocModel "mem.Allocator.create" .create #["create"] through017,
  allocModel "mem.Allocator.destroy" .destroy #["destroy"] through017,
  allocModel "mem.Allocator.alloc" .alloc #["alloc"] through017,
  allocModel "mem.Allocator.alignedAlloc" .alignedAlloc #["alloc"] through017,
  allocModel "mem.Allocator.allocSentinel" .allocSentinel #["allocSentinel"] #["0.16.0", "0.17.0"],
  allocModel "mem.Allocator.free" .free #["free", "freeSentinel"] through017,
  allocModel "mem.Allocator.dupe" .dupe #["dupe"] through017,
  allocModel "mem.Allocator.remap" .remap #["remap"] through017,
  threadModel "Thread.spawn" .spawn #["spawnC", "spawnWithPolicyC"] through017,
  threadModel "Thread.join" .join #["joinC"] through017,
  threadModel "Thread.yield" .yield #["threadYieldC"] through017,
  threadModel "atomic.spinLoopHint" .spinLoopHint #["spinLoopHintC"] through017,
  allocModel "mem.Allocator.realloc" .realloc #["realloc"] #["0.16.0"],
  threadModel "Thread.spinLoopHint" .spinLoopHint #["spinLoopHintC"],
  threadModel "Io.futexWait" .futexWait #["futexWaitCancelableC"] through017,
  threadModel "Io.futexWaitUncancelable" .futexWaitU #["futexWaitC"] through017,
  threadModel "Io.futexWake" .futexWake #["futexWakeC"] through017,
  threadModel "Thread.Futex.wait" .threadFutexWait #["threadFutexWaitC"],
  threadModel "Thread.Futex.wake" .threadFutexWake #["threadFutexWakeC"],
  threadModel "Thread.Mutex.DarwinImpl.lock" .osLock #["osUnfairLockC"],
  threadModel "Thread.Mutex.DarwinImpl.unlock" .osUnlock #["osUnfairUnlockC"],
  threadModel "Thread.Mutex.DarwinImpl.tryLock" .osTryLock #["osUnfairTryLockC"],
  threadModel "time.Timer.start" .timerStart #["callRC", "Error.unspecified"],
  threadModel "time.Timer.read" .timerRead #["callRC", "Error.unspecified"],
  threadModel "Thread.Futex.timedWait" .futexTimedWait #["callRC", "Error.unspecified"],
  threadModel "Io.Group.async" .groupAsync #["groupAsyncC", "groupAsyncWithPolicyC"] through017,
  threadModel "Io.Group.concurrent" .groupConcurrent #["groupConcurrentC", "groupConcurrentWithPolicyC"] through017,
  threadModel "Io.Group.await" .groupAwait #["groupAwaitC"] through017,
  threadModel "Io.Group.cancel" .groupCancel #["groupCancelC"] through017,
  { symbol := "Io.futexWaitTimeout",
    kind := .rejected "Io.futexWaitTimeout is outside the model: it has no clock" },
  { symbol := "Thread.detach",
    kind := .rejected "Thread.detach is outside the fork-join subset: every spawned thread must be joined" }]

private def stdModelIndex : Std.HashMap String StdModel :=
  stdModels.foldl (fun index m => index.insert m.symbol m) {}

/-- The qualified std name of `name`: an instance `<fn>__anon_<n>` names its generic `<fn>`. -/
def stdModelBase (name : String) : String := (name.splitOn "__anon_").head!

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
(`Thread.spawn__anon_<n>`, `Thread.join`). -/
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
