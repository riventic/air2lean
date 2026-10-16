import Std.Data.HashMap
import Air2Lean.Air.Op
import Air2Lean.Air.Dialect

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
  /-- `Io.futexWait` (cancelable), `Io.futexWaitUncancelable`, `Io.futexWake` (0.16.0). -/
  | futexWait | futexWaitU | futexWake
  /-- `Thread.Futex.wait`, `Thread.Futex.wake`. -/
  | threadFutexWait | threadFutexWake
  /-- `Thread.Mutex.DarwinImpl.lock`, `.unlock`, `.tryLock` (0.15.2 on macOS): each is one call of
  `os_unfair_lock_*`, a C function (the exporter does not name an `extern` function). -/
  | osLock | osUnlock | osTryLock
  /-- `Io.Group.async` (a thread, the caller or deferred), `.concurrent`, `.await`, `.cancel` (0.16.0). -/
  | groupAsync | groupConcurrent | groupAwait | groupCancel
  /-- `Io.async`, `Io.Future(T).await`, `Io.Future(T).cancel`, `Io.checkCancel` (0.16.0 only;
  `ZigLean/Conc/Future.lean`, `docs/futures.md`): a future's task is a thread with a result. -/
  | futureAsync | futureAwait | futureCancel | checkCancel
  deriving BEq, Repr

/-- The trusted OS primitives (`ZigLean/Os/`, `docs/os-threads.md`). The page-mapping ones of
`--allocator-model translated` (`ZigLean/Os/Mmap.lean`, premise OSM-01) are cut at `posix.*`,
above the syscall/libc layer, on Linux and macOS alike; the others at the named OS wrapper
(Linux: the `os.linux.*` function above `syscallN`; libc: the `extern` symbol). -/
inductive OsFn where
  | mmap | munmap | mremap
  /-- `os.linux.sched_yield() usize` (OSY-01, `Zig.Os.Linux.sched_yield`). -/
  | schedYield
  /-- libc `sched_yield() c_int` (OSY-01, macOS, `Zig.Os.Darwin.sched_yield`). -/
  | cSchedYield
  /-- libc `__error() *c_int` (OSK-02, macOS, `Zig.Os.Darwin.__error`): the thread's `errno`
  cell, which `c.errno` reads after a failing libc call. -/
  | cErrno
  /-- `os.linux.clock_gettime(clk_id: clockid_t, tp: *timespec) usize` (OSK-01,
  `Zig.Os.Linux.clock_gettime`). -/
  | clockGettime
  /-- libc `clock_gettime(clk_id: clockid_t, tp: *timespec) c_int` (OSK-01, macOS,
  `Zig.Os.Darwin.clock_gettime`). -/
  | cClockGettime
  /-- `os.linux.futex_4arg(uaddr, futex_op: FUTEX_OP, val: u32, timeout: ?*const timespec) usize`
  (OSF-01, `Zig.Os.Linux.futex_4arg`; 0.15.2 on). -/
  | futex4
  /-- `os.linux.futex_wait(uaddr: *const i32, futex_op: u32, val: i32, timeout: ?*const timespec)
  usize` (OSF-01, 0.14.1): the same `futex` system call as `futex_4arg`, so the same model. -/
  | futexWaitRaw
  /-- libc `__ulock_wait2(op: UL, addr, val: u64, timeout_ns: u64, val2: u64) c_int` (OSF-01,
  macOS ≥ 11, `Zig.Os.Darwin.__ulock_wait2`). -/
  | ulockWait2
  /-- libc `__ulock_wait(op: UL, addr, val: u64, timeout_us: u32) c_int` (OSF-01, macOS before 11,
  `Zig.Os.Darwin.__ulock_wait`). -/
  | ulockWait
  deriving BEq, Repr

/-- The OS primitive lets another thread run: a call of it is a sync op (`Func.syncLocally`), so
its caller is a concurrent function. -/
def OsFn.sync : OsFn → Bool
  | .schedYield | .cSchedYield | .clockGettime | .cClockGettime | .futex4 | .futexWaitRaw
  | .ulockWait2 | .ulockWait => true
  | .mmap | .munmap | .mremap | .cErrno => false

/-- The OS primitive's model takes the OS environment (`Zig.Os.Env`): a generated definition
that reaches it takes `[Zig.Os.HasEnv]` (`envFunctions`, `docs/os-threads.md` §Environment). -/
def OsFn.env : OsFn → Bool
  | .clockGettime | .cClockGettime => true
  | _ => false

/-- What a recognized std name selects: an allocator, thread or OS model, or an explicit
rejection (outside the fork-join subset) with its reason. -/
inductive StdModelKind where
  | alloc (fn : AllocFn)
  | thread (fn : ThreadFn)
  | os (fn : OsFn)
  | rejected (reason : String)
  deriving BEq, Repr

/-- One reviewed std source of a model row: the Zig version, the std file (relative to
`lib/std`) and its SHA-256 at review time. -/
structure StdReview where
  zigVersion : ZigVersion
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
  /-- The `--allocator-model` this row is active in; `none`: every mode. Allocator rows are
  `std`-only (translated mode translates `mem.Allocator.*` from its AIR); OS rows are
  `translated`-only. -/
  allocatorModel : Option AllocatorModel := none
  /-- The premise (`docs/premises.md`) that a claim relying on this model lists: `OSM-01` for an
  OS primitive; `STD-<nn>` for a hand-written model of std code, which is transitional and is
  deleted with its premise once the std code is translated (`docs/std-models.md` §Retiring the
  hand models). `none` for a rejected row. -/
  premise : Option String := none
  deriving Repr

/-- The Zig versions this model is qualified for: exactly the reviewed ones. -/
def StdModel.zigVersions (m : StdModel) : Array ZigVersion := m.reviewed.map (·.zigVersion)

/-- Fail closed: a version without a reviewed std source is not qualified. -/
def StdModel.qualifies (m : StdModel) (zigVersion : ZigVersion) : Bool :=
  m.zigVersions.contains zigVersion

/-- Reviewed std file hashes (`sha256` of `lib/std/<file>` in the release tarball). Each row
below cites the files whose definition of its symbol was compared with the model. -/
private def review (file : String) (hashes : List (ZigVersion × String)) : Array StdReview :=
  (hashes.map fun (zigVersion, sha256) => { zigVersion, file, sha256 }).toArray
/-- 0.17.0 rows: the std source (name, signature and semantics) did not change from 0.16.0 for
the models that list 0.17.0 (`docs/std-models.md` §Zig 0.17.0 audit). -/
private def allocatorZig (versions : List ZigVersion := ZigVersion.all) : Array StdReview :=
  review "mem/Allocator.zig" <| [
    (.v0_14_1, "2abc46d48236f1914c5cb9f1a8d526210c1159613bdf19bb57dda054c4f408b5"),
    (.v0_15_2, "679b9ca1d9314e138a7c7303bce1520c7a8fd7de7cfaf3d47659e23c3ae3aa77"),
    (.v0_16_0, "f6ad8a10185701ef1399350f127692ed5e89141773ea3c7e5ccc54a652120397"),
    (.v0_17_0, "25099a1aaed1fe80b811e1eaedf8c3e2059a3fe7b6c29db868a68da3085b7997")].filter
    (versions.contains ·.1)
private def threadZig : Array StdReview := review "Thread.zig" [
  (.v0_14_1, "6cc77eb377153ac08394e7422984bbb684c1ba7b0118dee33c9be50b6184f12d"),
  (.v0_15_2, "d5c5453d21967d531575ae2809aeda8848468a9d202aad4c4d2596e746a46f8a"),
  (.v0_16_0, "14260c03063b52821c5369fc09ec32456062b0366a8e1510c0f853a204ff7eeb"),
  (.v0_17_0, "36dab581ad0a30b2ac9fc3321db6b071331c3893f3811f1ec6628d59020c7f87")]
/-- `std.Io` has the futex and `Group` API only from 0.16.0 (0.14.1/0.15.2 `Io.zig` is the
reader/writer namespace). -/
private def ioZig : Array StdReview := review "Io.zig" [
  (.v0_16_0, "2d452f28cbeca10280f471b8e1962cdfe2a01000535050af6f6ebcc1a56365d6"),
  (.v0_17_0, "382a4e343017183eff88e311f983066f88306e7bfcd85a890723b3697f4b2732")]
/-- `std.Thread.Futex` is removed in 0.16.0 (replaced by `Io.futex*`). -/
private def futexZig : Array StdReview := review "Thread/Futex.zig" [
  (.v0_14_1, "f1f8fd850c94e0eb99a9332a2e51dd793f4057e35b6e8f7a04efd46a65c04960"),
  (.v0_15_2, "0b03207ea341c962122d4410cb52b52379a3e202be4556c6766efc74587a51b6")]
/-- Byte-identical in 0.14.1 and 0.15.2; `Thread.Mutex` is removed in 0.16.0. -/
private def mutexZig : Array StdReview := review "Thread/Mutex.zig" [
  (.v0_14_1, "6916d64495922ac3b61386b659248c7fc0002edabc489f4a4fb64f973c754bcc"),
  (.v0_15_2, "6916d64495922ac3b61386b659248c7fc0002edabc489f4a4fb64f973c754bcc")]
/-- `posix.mmap`, `posix.munmap`, `posix.mremap` (`--allocator-model translated`, OS-01): reviewed
for 0.16.0 only. -/
private def posixZig : Array StdReview := review "posix.zig" [
  (.v0_16_0, "5b1462b18db6757d984e118e09c532ac8b98cf1cc1ed48f18fcdbb362b75b5e0")]
/-- `os.linux.sched_yield` (`syscall0(.sched_yield)`), `os.linux.clock_gettime` (the vDSO
pointer, else `syscall2(.clock_gettime)`), `os.linux.futex_4arg` (0.15.2 on) and
`os.linux.futex_wait` (0.14.1) (`syscall4(.futex)`): unchanged signatures in every version. -/
private def linuxZig : Array StdReview := review "os/linux.zig" [
  (.v0_14_1, "36e1b68b9c747a426c110fa8ce588253ca8a895a5241ab1452e8340901ee7d81"),
  (.v0_15_2, "49e632c05b4b5e3333ed318b8ae9ad26997fd507bcea111d88cabc628ba748d3"),
  (.v0_16_0, "54d019f38778161dfd57e0da36fcf9ed0cd25e4ac792617dff2dc35b7513f185"),
  (.v0_17_0, "34f8a2301eb7f01c4747d70440c773790284dd074861086aab52bdaac75090a0")]
/-- libc's `extern "c" fn sched_yield() c_int`, `fn __error() *c_int` and
`fn clock_gettime(clk_id: clockid_t, tp: *timespec) c_int` (unchanged in every version). -/
private def cZig : Array StdReview := review "c.zig" [
  (.v0_14_1, "d4139b4464d840a2cb538970edbeffee386bee6ef3122512ef2d2410be69c5ef"),
  (.v0_15_2, "a8138d10955a61fae402e1235e81685732f46e4cacca1e922609034183824bb1"),
  (.v0_16_0, "f7062a55808aac78c515abd8bee5d36a596ee2de4116f61a51125107f84be158"),
  (.v0_17_0, "b1046cea3ed2f6310ba251b74da05faa323222779942ec7d11285979d48d71db")]
/-- macOS libc's `extern "c" fn __ulock_wait2(op: UL, addr: ?*const anyopaque, val: u64,
timeout_ns: u64, val2: u64) c_int` and `__ulock_wait(…, timeout_us: u32) c_int` (unchanged in
every version). -/
private def darwinZig : Array StdReview := review "c/darwin.zig" [
  (.v0_14_1, "ab9b468c43a73ab1ea9ae46911adf3c8cf2b049761cf4e5476ae50748e3885ac"),
  (.v0_15_2, "4565e4abbe32fa6cdbdcee67d52376dacee82aa7c489d0048e509663500358c9"),
  (.v0_16_0, "82eb9ed604a1adcf34be1e961caaa7395fd20d6ee90daec26af67f6a8c869be1"),
  (.v0_17_0, "cc262eee5afb345b3ff2628bcd0d645fa0bc95d81effc85524cb2bd8d9976fbc")]

/-- The row is active under `--allocator-model mode`. -/
def StdModel.activeIn (m : StdModel) (mode : AllocatorModel) : Bool :=
  match m.allocatorModel with
  | none => true
  | some only => only == mode

private def allocModel (symbol premise : String) (fn : AllocFn) (deps : Array String)
    (reviewed : Array StdReview := allocatorZig) : StdModel :=
  { symbol, kind := .alloc fn, reviewed, dependencies := deps.map ("Zig.Allocator." ++ ·),
    allocatorModel := some .std, premise }
private def threadModel (symbol premise : String) (fn : ThreadFn) (deps : Array String)
    (reviewed : Array StdReview) : StdModel :=
  { symbol, kind := .thread fn, reviewed, dependencies := deps.map ("Zig." ++ ·), premise }
/-- An OS primitive. The page-mapping rows are `--allocator-model translated`-only (std mode
models the allocator above them); the others are active in every mode. -/
private def osModel (symbol premise : String) (fn : OsFn) (deps : Array String)
    (reviewed : Array StdReview := posixZig)
    (allocatorModel : Option AllocatorModel := some .translated) : StdModel :=
  { symbol, kind := .os fn, reviewed, dependencies := deps.map ("Zig.Os." ++ ·), allocatorModel,
    premise }

/-- `reviewed` restricted to the Zig versions in `versions` (a model qualified for fewer versions
than the std file exists in). -/
private def only (versions : List ZigVersion) (reviewed : Array StdReview) : Array StdReview :=
  reviewed.filter (versions.contains ·.zigVersion)

/-- The reason of an async API outside the qualified future subset (`docs/futures.md`). -/
private def asyncReason (symbol reason : String) : String :=
  s!"{symbol} is not a qualified async API: {reason} (docs/futures.md)"

/-- The one table of built-in std models. Rows without a 0.17.0 review are 0.17.0-unqualified on
purpose (`docs/std-models.md` §Zig 0.17.0 audit): the `Thread.Futex`, `Thread.Mutex.DarwinImpl`,
`time.Timer` and `Thread.spinLoopHint` rows name std declarations that 0.17.0 no longer has. -/
def stdModels : Array StdModel := #[
  allocModel "mem.Allocator.create" "STD-01" .create #["create"],
  allocModel "mem.Allocator.destroy" "STD-01" .destroy #["destroy"],
  allocModel "mem.Allocator.alloc" "STD-01" .alloc #["alloc"],
  allocModel "mem.Allocator.alignedAlloc" "STD-01" .alignedAlloc #["alloc"],
  allocModel "mem.Allocator.allocSentinel" "STD-01" .allocSentinel #["allocSentinel"] (allocatorZig [.v0_16_0, .v0_17_0]),
  allocModel "mem.Allocator.free" "STD-01" .free #["free", "freeSentinel"],
  allocModel "mem.Allocator.dupe" "STD-01" .dupe #["dupe"],
  allocModel "mem.Allocator.remap" "STD-01" .remap #["remap"],
  allocModel "mem.Allocator.realloc" "STD-01" .realloc #["realloc"] (allocatorZig [.v0_16_0]),
  threadModel "Thread.spawn" "STD-02" .spawn #["spawnC", "spawnWithPolicyC"] threadZig,
  threadModel "Thread.join" "STD-02" .join #["joinC"] threadZig,
  threadModel "Thread.detach" "STD-03" .detach #["detachC"] (only [.v0_16_0] threadZig),
  threadModel "Io.futexWait" "STD-05" .futexWait #["futexWaitCancelableC"] ioZig,
  threadModel "Io.futexWaitUncancelable" "STD-05" .futexWaitU #["futexWaitC"] ioZig,
  threadModel "Io.futexWake" "STD-05" .futexWake #["futexWakeC"] ioZig,
  threadModel "Thread.Futex.wait" "STD-05" .threadFutexWait #["threadFutexWaitC"] futexZig,
  threadModel "Thread.Futex.wake" "STD-05" .threadFutexWake #["threadFutexWakeC"] futexZig,
  threadModel "Thread.Mutex.DarwinImpl.lock" "STD-06" .osLock #["osUnfairLockC"] mutexZig,
  threadModel "Thread.Mutex.DarwinImpl.unlock" "STD-06" .osUnlock #["osUnfairUnlockC"] mutexZig,
  threadModel "Thread.Mutex.DarwinImpl.tryLock" "STD-06" .osTryLock #["osUnfairTryLockC"] mutexZig,
  threadModel "Io.Group.async" "STD-08" .groupAsync #["groupAsyncWithPolicyC", "groupAsyncC", "groupDeferC"] ioZig,
  threadModel "Io.Group.concurrent" "STD-08" .groupConcurrent #["groupConcurrentC", "groupConcurrentWithPolicyC"] ioZig,
  threadModel "Io.Group.await" "STD-08" .groupAwait #["groupAwaitC"] ioZig,
  threadModel "Io.Group.cancel" "STD-08" .groupCancel #["groupCancelC"] ioZig,
  threadModel "Io.async" "STD-09" .futureAsync #["asyncWithPolicyC", "asyncC", "Future.complete"] (only [.v0_16_0] ioZig),
  threadModel "Io.Future.await" "STD-09" .futureAwait #["awaitC"] (only [.v0_16_0] ioZig),
  threadModel "Io.Future.cancel" "STD-09" .futureCancel #["cancelC"] (only [.v0_16_0] ioZig),
  threadModel "Io.checkCancel" "STD-09" .checkCancel #["checkCancelC"] (only [.v0_16_0] ioZig),
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
  osModel "posix.mmap" "OSM-01" .mmap #["mmap", "Target.linux", "Target.macos"],
  osModel "posix.munmap" "OSM-01" .munmap #["munmap", "Target.linux", "Target.macos"],
  osModel "posix.mremap" "OSM-01" .mremap #["mremap", "Target.linux"],
  -- `Thread.yield` is translated from std (`posix.errno(posix.system.sched_yield())`) down to these.
  osModel "os.linux.sched_yield" "OSY-01" .schedYield #["Linux.sched_yield"] linuxZig none,
  osModel "extern:sched_yield" "OSY-01" .cSchedYield #["Darwin.sched_yield"] cZig none,
  osModel "extern:__error" "OSK-02" .cErrno #["Darwin.__error"] cZig none,
  -- `time.Timer`/`Instant` (0.14.1, 0.15.2) are translated from std (`posix.clock_gettime`) down
  -- to these; they take the OS environment (`OsFn.env`).
  osModel "os.linux.clock_gettime" "OSK-01" .clockGettime #["Linux.clock_gettime", "HasEnv.env"] linuxZig none,
  osModel "extern:clock_gettime" "OSK-01" .cClockGettime #["Darwin.clock_gettime", "HasEnv.env"] cZig none,
  -- `Thread.Futex.timedWait` (0.14.1, 0.15.2) is translated from std (`LinuxImpl.wait`,
  -- `DarwinImpl.wait`) down to these.
  osModel "os.linux.futex_4arg" "OSF-01" .futex4 #["Linux.futex_4arg"] (only [.v0_15_2, .v0_16_0, .v0_17_0] linuxZig) none,
  osModel "os.linux.futex_wait" "OSF-01" .futexWaitRaw #["Linux.futex_4arg"] (only [.v0_14_1] linuxZig) none,
  osModel "extern:__ulock_wait2" "OSF-01" .ulockWait2 #["Darwin.__ulock_wait2"] darwinZig none,
  osModel "extern:__ulock_wait" "OSF-01" .ulockWait #["Darwin.__ulock_wait"] darwinZig none,
  { symbol := "Io.futexWaitTimeout",
    kind := .rejected "Io.futexWaitTimeout is outside the model: it has no clock" },
  { symbol := "Thread.spinLoopHint",
    kind := .rejected "Thread.spinLoopHint is not a std declaration in any audited Zig version; std.atomic.spinLoopHint (inline: its pause/isb instruction) is the supported hint" }]
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

/-- The built-in std model (modelled or rejected) that the function `name` is an instance of,
among the rows active under `mode` (`StdModel.activeIn`). -/
def stdModel? (name : String) (mode : AllocatorModel := .std) : Option StdModel :=
  (stdModelIndex[stdModelBase name]?).filter (·.activeIn mode)

/-- The built-in std model row of `name` in any `--allocator-model`: the names that a project
binding (`ModelRegistry`) can never claim, the OS boundary included. -/
def anyStdModel? (name : String) : Option StdModel := stdModelIndex[stdModelBase name]?

private def stdKind? (name : String) (mode : AllocatorModel := .std) : Option StdModelKind :=
  (stdModel? name mode).map (·.kind)

/-- The allocator function that the function `name` is an instance of
(`mem.Allocator.<fn>__anon_<n>`). Std mode only. -/
def allocFn? (name : String) (mode : AllocatorModel := .std) : Option AllocFn :=
  match stdKind? name mode with
  | some (.alloc fn) => some fn
  | _ => none

/-- The trusted OS primitive that `name` selects. `--allocator-model translated` only. -/
def osFn? (name : String) (mode : AllocatorModel := .std) : Option OsFn :=
  match stdKind? name mode with
  | some (.os fn) => some fn
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

/-- `name` selects an allocator, thread or OS model (not a rejection) under `mode`. -/
def modelledStdFn (name : String) (mode : AllocatorModel := .std) : Bool :=
  match stdKind? name mode with
  | some (.alloc _) | some (.thread _) | some (.os _) => true
  | _ => false

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
legacy export, `module = none`) the namespace is matched against `Identity.stdNamespaces`,
which also refuses such a user module (fail closed). -/
def projectStdBinding? (symbol : String) (module : Option String := none) : Option String :=
  let base := stdModelBase symbol
  let std := match module with
    | some m => m == "std"
    | none => Identity.stdNamespaces.contains (Identity.namespaceOf base)
  if std && !osPrimitiveBindings.contains base then
    some s!"model '{symbol}' hand-models std code: a project registry may bind only the OS primitives {", ".intercalate osPrimitiveBindings.toList} in a std namespace; translate the std function instead"
  else none

end Air2Lean
