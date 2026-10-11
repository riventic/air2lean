import Std.Data.HashMap

/-! # Built-in std model registry

The single table of qualified standard-library names that the translator recognizes
(`docs/std-models.md`, `docs/external-models.md`). `Check.lean`, `Emit.lean`, `Memory.lean`,
`Diagnose.lean` and the project registry (`ModelRegistry.lean`) consult it through
`stdModel?` and the typed projections below; none of them carries its own name table.

Each entry records the typed model it selects, its Zig-version qualification, and its
semantic dependencies: the `ZigLean` declarations the emitter may reference for it. The
qualification is the explicit list of reviewed std sources (`StdReview`): one Zig version and
the SHA-256 of the std file that defines the symbol, reviewed against the model. A version that
is not listed (a new Zig release, or an empty list) is rejected, never assumed
(`tests/roadmap/models/test_std_sources.py` rechecks the hashes against the std sources). `tests/roadmap/models/StdModels.lean`
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
  /-- `Io.Group.async` (a thread, the caller or deferred), `.concurrent`, `.await`, `.cancel` (0.16.0). -/
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

/-- One reviewed std source of a model row: the Zig version, the std file (relative to
`lib/std`) and its SHA-256 at review time. -/
structure StdReview where
  zigVersion : String
  file : String
  sha256 : String
  deriving Repr

structure StdModel where
  /-- The qualified std name; an instance `<symbol>__anon_<n>` selects the same model. -/
  symbol : String
  kind : StdModelKind
  /-- The std sources this model was reviewed against, one per qualified Zig version. Empty:
  qualified for no version (the row only rejects). -/
  reviewed : Array StdReview := #[]
  /-- `ZigLean` declarations the emitted term may reference (the semantic dependencies). -/
  dependencies : Array String := #[]
  deriving Repr

/-- The Zig versions this model is qualified for: exactly the reviewed ones. -/
def StdModel.zigVersions (m : StdModel) : Array String := m.reviewed.map (·.zigVersion)

/-- Fail closed: a version without a reviewed std source is not qualified. -/
def StdModel.qualifies (m : StdModel) (zigVersion : String) : Bool :=
  m.zigVersions.contains zigVersion

/-- Reviewed std file hashes (`sha256` of `lib/std/<file>` in the release tarball). Each row
below cites the files whose definition of its symbol was compared with the model. -/
private def review (file : String) (hashes : List (String × String)) : Array StdReview :=
  (hashes.map fun (zigVersion, sha256) => { zigVersion, file, sha256 }).toArray
/-- 0.17.0 rows: the std source (name, signature and semantics) did not change from 0.16.0 for
the models that list 0.17.0 (`docs/std-models.md` §Zig 0.17.0 audit). -/
private def allocatorZig (versions : List String := ["0.14.1", "0.15.2", "0.16.0", "0.17.0"]) : Array StdReview :=
  review "mem/Allocator.zig" <| [
    ("0.14.1", "2abc46d48236f1914c5cb9f1a8d526210c1159613bdf19bb57dda054c4f408b5"),
    ("0.15.2", "679b9ca1d9314e138a7c7303bce1520c7a8fd7de7cfaf3d47659e23c3ae3aa77"),
    ("0.16.0", "f6ad8a10185701ef1399350f127692ed5e89141773ea3c7e5ccc54a652120397"),
    ("0.17.0", "25099a1aaed1fe80b811e1eaedf8c3e2059a3fe7b6c29db868a68da3085b7997")].filter
    (versions.contains ·.1)
private def threadZig : Array StdReview := review "Thread.zig" [
  ("0.14.1", "6cc77eb377153ac08394e7422984bbb684c1ba7b0118dee33c9be50b6184f12d"),
  ("0.15.2", "d5c5453d21967d531575ae2809aeda8848468a9d202aad4c4d2596e746a46f8a"),
  ("0.16.0", "14260c03063b52821c5369fc09ec32456062b0366a8e1510c0f853a204ff7eeb"),
  ("0.17.0", "36dab581ad0a30b2ac9fc3321db6b071331c3893f3811f1ec6628d59020c7f87")]
private def atomicZig : Array StdReview := review "atomic.zig" [
  ("0.14.1", "5765a0e92346ae81cae3034d1d58ba4fc2c3e800fb59f80e87b7694c9b810f72"),
  ("0.15.2", "8421886c8789d9cf7619b40f81ea9e24f7af8c31beaf8a93ba610fcc21bba269"),
  ("0.16.0", "1f53df09898b7c88f8ad3ffff60b22e5656c0ea1a7c84663c6a0b8466c139c22"),
  ("0.17.0", "85b467837478ff64aba29bf52cf9eef9b973ddb3ec6b5472901500a8e4a925c5")]
/-- `std.Io` has the futex and `Group` API only from 0.16.0 (0.14.1/0.15.2 `Io.zig` is the
reader/writer namespace). -/
private def ioZig : Array StdReview := review "Io.zig" [
  ("0.16.0", "2d452f28cbeca10280f471b8e1962cdfe2a01000535050af6f6ebcc1a56365d6"),
  ("0.17.0", "382a4e343017183eff88e311f983066f88306e7bfcd85a890723b3697f4b2732")]
/-- `std.Thread.Futex` is removed in 0.16.0 (replaced by `Io.futex*`). -/
private def futexZig : Array StdReview := review "Thread/Futex.zig" [
  ("0.14.1", "f1f8fd850c94e0eb99a9332a2e51dd793f4057e35b6e8f7a04efd46a65c04960"),
  ("0.15.2", "0b03207ea341c962122d4410cb52b52379a3e202be4556c6766efc74587a51b6")]
/-- Byte-identical in 0.14.1 and 0.15.2; `Thread.Mutex` is removed in 0.16.0. -/
private def mutexZig : Array StdReview := review "Thread/Mutex.zig" [
  ("0.14.1", "6916d64495922ac3b61386b659248c7fc0002edabc489f4a4fb64f973c754bcc"),
  ("0.15.2", "6916d64495922ac3b61386b659248c7fc0002edabc489f4a4fb64f973c754bcc")]
/-- `std.time.Timer` is removed in 0.16.0. -/
private def timeZig : Array StdReview := review "time.zig" [
  ("0.14.1", "3dcf1c3db1d8f99b8b4d0f6da6dbc7ad916ef62765a1fede977517587523d7ed"),
  ("0.15.2", "b8b686d5ecaa81cb25b3234229a85cf0ff99c5bd6153283b272fe586c558d7f1")]

private def allocModel (symbol : String) (fn : AllocFn) (deps : Array String)
    (reviewed : Array StdReview := allocatorZig) : StdModel :=
  { symbol, kind := .alloc fn, reviewed, dependencies := deps.map ("Zig.Allocator." ++ ·) }
private def threadModel (symbol : String) (fn : ThreadFn) (deps : Array String)
    (reviewed : Array StdReview) : StdModel :=
  { symbol, kind := .thread fn, reviewed, dependencies := deps.map ("Zig." ++ ·) }

/-- `reviewed` restricted to the Zig versions in `versions` (a model qualified for fewer versions
than the std file exists in). -/
private def only (versions : List String) (reviewed : Array StdReview) : Array StdReview :=
  reviewed.filter (versions.contains ·.zigVersion)

/-- The reason of an async API outside the qualified future subset (`docs/futures.md`). -/
private def asyncReason (symbol reason : String) : String :=
  s!"{symbol} is not a qualified async API: {reason} (docs/futures.md)"

/-- The one table of built-in std models. Rows without a 0.17.0 review are 0.17.0-unqualified on
purpose (`docs/std-models.md` §Zig 0.17.0 audit): the `Thread.Futex`, `Thread.Mutex.DarwinImpl`,
`time.Timer` and `Thread.spinLoopHint` rows name std declarations that 0.17.0 no longer has. -/
def stdModels : Array StdModel := #[
  allocModel "mem.Allocator.create" .create #["create"],
  allocModel "mem.Allocator.destroy" .destroy #["destroy"],
  allocModel "mem.Allocator.alloc" .alloc #["alloc"],
  allocModel "mem.Allocator.alignedAlloc" .alignedAlloc #["alloc"],
  allocModel "mem.Allocator.allocSentinel" .allocSentinel #["allocSentinel"] (allocatorZig ["0.16.0", "0.17.0"]),
  allocModel "mem.Allocator.free" .free #["free", "freeSentinel"],
  allocModel "mem.Allocator.dupe" .dupe #["dupe"],
  allocModel "mem.Allocator.remap" .remap #["remap"],
  allocModel "mem.Allocator.realloc" .realloc #["realloc"] (allocatorZig ["0.16.0"]),
  threadModel "Thread.spawn" .spawn #["spawnC", "spawnWithPolicyC"] threadZig,
  threadModel "Thread.join" .join #["joinC"] threadZig,
  threadModel "Thread.detach" .detach #["detachC"] (only ["0.16.0"] threadZig),
  threadModel "Thread.yield" .yield #["threadYieldC"] threadZig,
  threadModel "atomic.spinLoopHint" .spinLoopHint #["spinLoopHintC"] atomicZig,
  threadModel "Io.futexWait" .futexWait #["futexWaitCancelableC"] ioZig,
  threadModel "Io.futexWaitUncancelable" .futexWaitU #["futexWaitC"] ioZig,
  threadModel "Io.futexWake" .futexWake #["futexWakeC"] ioZig,
  threadModel "Thread.Futex.wait" .threadFutexWait #["threadFutexWaitC"] futexZig,
  threadModel "Thread.Futex.wake" .threadFutexWake #["threadFutexWakeC"] futexZig,
  threadModel "Thread.Mutex.DarwinImpl.lock" .osLock #["osUnfairLockC"] mutexZig,
  threadModel "Thread.Mutex.DarwinImpl.unlock" .osUnlock #["osUnfairUnlockC"] mutexZig,
  threadModel "Thread.Mutex.DarwinImpl.tryLock" .osTryLock #["osUnfairTryLockC"] mutexZig,
  threadModel "time.Timer.start" .timerStart #["callRC", "Error.unsupportedTimer"] timeZig,
  threadModel "time.Timer.read" .timerRead #["callRC", "Error.unsupportedTimer"] timeZig,
  threadModel "Thread.Futex.timedWait" .futexTimedWait #["callRC", "Error.unsupportedTimer"] futexZig,
  threadModel "Io.Group.async" .groupAsync #["groupAsyncWithPolicyC", "groupAsyncC", "groupDeferC"] ioZig,
  threadModel "Io.Group.concurrent" .groupConcurrent #["groupConcurrentC", "groupConcurrentWithPolicyC"] ioZig,
  threadModel "Io.Group.await" .groupAwait #["groupAwaitC"] ioZig,
  threadModel "Io.Group.cancel" .groupCancel #["groupCancelC"] ioZig,
  threadModel "Io.async" .futureAsync #["asyncWithPolicyC", "asyncC", "Future.complete"] (only ["0.16.0"] ioZig),
  threadModel "Io.Future.await" .futureAwait #["awaitC"] (only ["0.16.0"] ioZig),
  threadModel "Io.Future.cancel" .futureCancel #["cancelC"] (only ["0.16.0"] ioZig),
  threadModel "Io.checkCancel" .checkCancel #["checkCancelC"] (only ["0.16.0"] ioZig),
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
    kind := .rejected "Io.futexWaitTimeout is outside the model: it has no clock" },
  { symbol := "Thread.spinLoopHint",
    kind := .rejected "Thread.spinLoopHint is not a std declaration in any audited Zig version; std.atomic.spinLoopHint is the modelled hint" }]
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

/-- Translated std functions whose generated definition starts with the owner check of a mutex
unlock (`Zig.mutexOwnerCheck p0`, `ZigLean/Conc/Call.lean`): `.illegal` unless the current thread
made the most recent successful acquire of the mutex word, at offset 0 of the first argument.
They are translated, not modelled; the check is ghost (it reads no byte and writes nothing).
`Thread.Mutex.FutexImpl.unlock` (0.14.1, 0.15.2): std makes an unlock from another thread undefined
behavior. `Io.Mutex.unlock` (0.16.0, 0.17.0) is not listed: std names no owner, so an unlock by
another thread of a held `Io.Mutex` is legal (`docs/std-models.md` §Thread model). -/
def ownerCheckedUnlocks : Array String := #["Thread.Mutex.FutexImpl.unlock"]

/-- `name` selects an allocator or thread model (not a rejection). -/
def modelledStdFn (name : String) : Bool :=
  match stdKind? name with
  | some (.alloc _) | some (.thread _) => true
  | _ => false

/-- The top-level namespaces of `lib/std` (its files and directories) in Zig 0.14.1, 0.15.2 and
0.16.0. A fully qualified AIR name whose first component is one of these names std code. -/
def stdNamespaces : Array String := #[
  "BitStack", "Build", "DoublyLinkedList", "Io", "Progress", "Random", "RingBuffer",
  "SemanticVersion", "SinglyLinkedList", "Target", "Thread", "Uri", "array_hash_map",
  "array_list", "ascii", "atomic", "base64", "bit_set", "bounded_array", "buf_map", "buf_set",
  "builtin", "c", "coff", "compress", "crypto", "debug", "deque", "dwarf", "dynamic_library",
  "elf", "enums", "fifo", "fmt", "fs", "gpu", "hash", "hash_map", "heap", "http", "io", "json",
  "leb128", "linked_list", "log", "macho", "math", "mem", "meta", "multi_array_list", "net",
  "once", "os", "pdb", "pie", "posix", "priority_dequeue", "priority_queue", "process",
  "segmented_list", "simd", "sort", "start", "static_string_map", "std", "tar", "testing",
  "time", "treap", "tz", "unicode", "valgrind", "wasm", "zig", "zip", "zon"]

/-- The std functions a project registry may bind (W4, `docs/external-models.md`): OS primitives
only, the trusted base of the allocators-from-OS-primitives design (class A of
`docs/architecture-audit/models.md`). Every other std function is translated from its source or
modelled by a reviewed `stdModels` row; a project cannot hand-model it. -/
def osPrimitiveBindings : Array String := #[
  "os.linux.read", "os.linux.write", "os.linux.close", "os.linux.mmap", "os.linux.munmap",
  "os.linux.mremap", "os.linux.clock_gettime", "os.linux.futex_3arg", "os.linux.futex_4arg",
  "os.linux.futex_wait", "os.linux.futex_wake", "os.linux.sched_yield",
  "posix.mmap", "posix.munmap", "posix.mremap"]

/-- Why a project registry binding of `symbol` is rejected as a hand model of std code, if it is.
`module` is the callee's module identity (`Air2Lean/Air/Identity.lean`, B1): the binding is std
code exactly when that module is `std`, so a user module named like a std namespace
(`posix.zig`, key `posix.helper` of module `root`) may be bound. Without module identity (a
legacy export, `module = none`) the first name component is matched against `stdNamespaces`,
which also refuses such a user module (fail closed). -/
def projectStdBinding? (symbol : String) (module : Option String := none) : Option String :=
  let base := stdModelBase symbol
  let std := match module with
    | some m => m == "std"
    | none => stdNamespaces.contains ((base.splitOn ".").head!)
  if std && !osPrimitiveBindings.contains base then
    some s!"model '{symbol}' hand-models std code: a project registry may bind only the OS primitives {", ".intercalate osPrimitiveBindings.toList} in a std namespace; translate the std function instead"
  else none

end Air2Lean
