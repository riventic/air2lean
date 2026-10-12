import ZigLean.Os.Futex

/-!
# Threads: Linux `clone`, macOS `pthread_*`, ids, CPU count, yield, interrupts
(premises OST-01, OST-02, OST-03, OSY-01, OSG-01)

The OS rows of `std.Thread` and of `Io.Threaded`'s worker management (Zig 0.16.0;
`docs/thread-io-translation.md` §1.2, `docs/os-threads.md`). As for the futex rows
(`ZigLean/Os/Futex.lean`), each one is the named `os.linux.*` wrapper or the `extern "c"` symbol,
and a call that can reach another thread is a `ConcM` function over the existing scheduler.

**Create** (OST-01). The entry point of a new thread is a function pointer constant at each call
site (`Instance.entryFn`), so the translator builds the spawn target `t : Tgt` from it and its
argument, as for `std.Thread.spawn` today; `clone`/`pthread_create` take that target. The call
is the scheduler's `spawn t`: a new thread with a happens-before edge from the parent
(`Thread.fork`), or, under the run's spawn policy (`Zig.Env.spawn = fallible`, with
`Mem.spawnLimit`; `ZigLean/Conc/Sched.lean`), one of the declared failures, which the row returns
as Linux `-ENOMEM` (`OutOfMemory`) or `-EAGAIN` (the others), macOS `EAGAIN` (`Linux.spawnErrno`).
Its thread-local variables are new instances (C02: the
generated dispatcher's `tlsEnter`; the `tls` argument of `clone` and `tls.prepareArea` are part
of this row and not translated). Linux `PARENT_SETTID` writes the child's id to `ptid`; the
parent makes that write after the fork, so a child that reads `ptid` without synchronizing races
(stricter than the kernel; std's child never reads it). `pthread_create` writes the handle the
same way.

**Linux exit** (OST-02). The dispatcher of a `clone` target is `Linux.cloneThread entry ctid`:
the entry function, then the kernel's `CHILD_CLEARTID` in one turn (`cloneExit`): a release store
of `0` to the `i32` at `ctid`, which carries the thread's final clock, a wake of every waiter at
`ctid`, and the end of the join obligation (`ThreadRec.joined`, so `checkJoinedByChild` of the
parent passes only after the thread exited). Std's translated `LinuxThreadImpl.join` (a `seq_cst`
load loop and `futex_4arg` on `child_tid`) gets the join edge from the store; the scheduler's
`join` is not used on Linux. A detached thread's `freeAndExit` (inline `munmap` + `exit`) is not
modelled yet: it needs the OSM-01 `munmap` (`codex/alloc-translated-p2`).

**macOS join/detach** (OST-02). `pthread_join` is the scheduler's `join` (the edge from the end of
the thread); `pthread_detach` is `Thread.detach` (C07: the caller must own the handle; the handle
is consumed). A join or detach of a handle that the caller does
not own, or that is consumed, is `.illegal` (std: `unreachable`). A `pthread_t` is the model's
`ThreadId` (`Enc ThreadId`, 8 bytes).

**Ids and CPUs** (OST-03). Thread ids and the process id come from the environment (`Env.tid`,
`Env.pid`); the CPU count is `Env.cpus`, never a constant.

**Yield** (OSY-01) is the scheduler's `yield`; it always succeeds.

**Interrupts** (OSG-01). `tgkill`/`pthread_kill` of `SIG.IO` to a live thread `t` (std's
cancelation of a blocked syscall) wakes `t` if it sleeps in a futex wait, which then returns
`EINTR`; otherwise it leaves a pending interrupt, which `t`'s next futex wait or sleep delivers at
its start. It forces no `EINTR` (a signal that arrives before the syscall runs the handler and is
gone; the oracle `EINTR` of every wait and sleep covers the rest). The bit exists for liveness
arguments. Installing the no-op handler (`sigaction`) has no memory effect and is not a row here.
-/

namespace Zig
namespace Os

variable {Tgt : Type}

/-- The Linux errno of a `clone` that the run's environment failed (`SyncOp.spawn` returned the
declared error `e`): `ENOMEM` for `OutOfMemory`, else `EAGAIN`. Both are reachable under
`fallible`. -/
def Linux.spawnErrno (e : ErrName) : Nat := if e = "OutOfMemory" then Linux.E.NOMEM else Linux.E.AGAIN

/-- Thread `t` can be signaled: it exists, and it has not exited (Linux `cloneExit`) or been
joined (macOS); a detached macOS thread stays signalable (the model does not see its end, so a
signal to one that ended returns `0`, where POSIX leaves it undefined). Thread 0 is alive until
the run ends. -/
def _root_.Zig.Mem.threadAlive (m : Mem) (t : ThreadId) : Bool :=
  match m.threads[t]? with
  | some r => t == 0 || !r.joined || m.os.detached.contains t
  | none => false

/-- A signal to thread `t` (OSG-01): it wakes if it sleeps at a futex; the interrupt is pending
until its next futex wait or sleep delivers it. -/
def interrupt (t : ThreadId) : MemM Unit := modify fun m =>
  let asleep := m.waiters.any (·.1 == t)
  { m with
    os := { m.os with interrupts := if m.os.interrupts.contains t then m.os.interrupts
                                    else m.os.interrupts.push t }
    waiters := if asleep then m.waiters.filter (·.1 != t) else m.waiters
    woken := if asleep then m.woken.push t else m.woken }

/-- The current thread has exited: its join obligation ends (`checkJoinedByChild`). The exit is
no join: the owner synchronizes only through the `CHILD_CLEARTID` store (`ThreadRec.released`). -/
def markExited : MemM Unit := modify fun m =>
  { m with threads := m.threads.modify m.current fun r => { r with joined := true, released := true } }

/-! ## Linux (`std.os.linux`, x86_64) -/

namespace Linux

/-- `CLONE.{THREAD, DETACHED, VM, FS, FILES, PARENT_SETTID, CHILD_CLEARTID, SIGHAND, SYSVSEM,
SETTLS}`: the flags of `LinuxThreadImpl.spawn`, the only set in the model. -/
def stdCloneFlags : BitVec 32 := 0x7d0f00

/-- `os.linux.clone(func, stack: usize, flags: u32, arg: usize, ptid: ?*i32, tp: usize,
ctid: ?*i32) usize` (module doc). `t` is the spawn target of `(func, arg, ctid)`; its dispatcher
must be `cloneThread`. `stack` and `tp` are not used (the model's thread has its own frames; its
TLS instances are C02's). Returns the child's id, `-EAGAIN` or `-ENOMEM`. -/
def clone (env : Env) (t : Tgt) (_stack : BitVec 64) (flags : BitVec 32) (ptid : Option Ptr)
    (_tp : BitVec 64) (ctid : Option Ptr) : ConcM Tgt (BitVec 64) := do
  if flags ≠ stdCloneFlags ∨ ctid = none then throw .unspecified
  let some ptid := ptid | throw .unspecified
  match ← ConcM.sync (.spawn t) with
  | .ok child =>
    ConcM.liftMem (store 4 ptid (env.tid child))
    return (env.tid child).setWidth 64
  | .error e => return negErrno (spawnErrno e)

/-- The kernel's `CHILD_CLEARTID` when a `clone` thread exits (module doc): one turn. -/
def cloneExit (ctid : Ptr) : ConcM Tgt Unit := do
  let c ← pick (storeCount 32 .release 4 ctid)
  ConcM.liftMem do
    atomicStoreAt c .release 4 ctid (0 : BitVec 32)
    wakeAll ctid
    markExited

/-- The dispatcher of a `clone` target: the entry function, then the exit (module doc). -/
def cloneThread {α : Type} (entry : ConcM Tgt α) (ctid : Ptr) : ConcM Tgt Unit := do
  let _ ← entry
  cloneExit ctid

/-- `os.linux.gettid() pid_t`. -/
def gettid (env : Env) : MemM (BitVec 32) := do
  pure (env.tid (← get).current)

/-- `os.linux.getpid() pid_t`. -/
def getpid (env : Env) : MemM (BitVec 32) := pure env.pid

/-- `SIG.IO` on x86_64 Linux. -/
def SIG_IO : BitVec 32 := 29

/-- `os.linux.tgkill(tgid: pid_t, tid: pid_t, sig: SIG) usize` with `sig = .IO` (OSG-01): `0`, or
`-ESRCH` if no live thread of the process has the id. -/
def tgkill (env : Env) (tgid tid : BitVec 32) (sig : BitVec 32) : MemM (BitVec 64) := do
  if sig ≠ SIG_IO then throw .unspecified
  let m ← get
  if tgid ≠ env.pid then return negErrno E.SRCH
  match (List.range m.threads.size).find? (fun t => env.tid t == tid && m.threadAlive t) with
  | none => return negErrno E.SRCH
  | some t =>
    interrupt t
    return 0

/-- The bytes of a `cpu_set_t` of `size` bytes with the CPUs of `mask`. -/
def cpuSetBytes (mask size : Nat) : Array Byte :=
  (Array.range size).map fun i =>
    .int (if 8 * i < cpuSetBits then BitVec.ofNat 8 (mask >>> (8 * i)) else 0)

/-- `os.linux.sched_getaffinity(pid: pid_t, size: usize, set: *cpu_set_t) usize` for the calling
thread (`pid = 0`) and a set of at least 1024 bits, a multiple of 8 bytes (std's `cpu_set_t`):
writes the environment's mask, returns `0` (OST-03). -/
def sched_getaffinity (env : Env) (pid : BitVec 32) (size : BitVec 64) (set : Ptr) :
    MemM (BitVec 64) := do
  if pid ≠ 0 ∨ size.toNat < cpuSetBits / 8 ∨ size.toNat % 8 ≠ 0 then throw .unspecified
  storeBytes set 8 (cpuSetBytes env.cpuMask size.toNat)
  return 0

/-- `os.linux.sched_yield() usize` (OSY-01). -/
def sched_yield : ConcM Tgt (BitVec 64) := do
  ConcM.sync .yield
  return 0

end Linux

/-! ## macOS (`std.c`, aarch64) -/

namespace Darwin

/-- `sizeof(pthread_attr_t)` on macOS (`__sig` and 56 opaque bytes). -/
def pthreadAttrSize : Nat := 64

/-- `PTHREAD_STACK_MIN` and the page size of aarch64-macos. -/
def pthreadStackMin : Nat := 16384

/-- Libc writes `attr`'s opaque bytes: they are undefined to Zig code. -/
def writeAttr (attr : Ptr) : MemM Unit :=
  storeBytes attr 8 (Array.replicate pthreadAttrSize .undef)

/-- `pthread_attr_init(attr: *pthread_attr_t) E`: `0`. -/
def pthread_attr_init (attr : Ptr) : MemM (BitVec 16) := do
  writeAttr attr
  return 0

/-- `pthread_attr_destroy(attr: *pthread_attr_t) E`: `0`. -/
def pthread_attr_destroy (attr : Ptr) : MemM (BitVec 16) := do
  writeAttr attr
  return 0

/-- `pthread_attr_setstacksize(attr: *pthread_attr_t, stacksize: usize) E`: `0`, or `EINVAL`
below `PTHREAD_STACK_MIN` or off a page multiple. -/
def pthread_attr_setstacksize (attr : Ptr) (stacksize : BitVec 64) : MemM (BitVec 16) := do
  let _ ← loadBytes attr pthreadAttrSize 8
  if stacksize.toNat < pthreadStackMin ∨ stacksize.toNat % pthreadStackMin ≠ 0 then
    return BitVec.ofNat 16 E.INVAL
  writeAttr attr
  return 0

/-- `pthread_attr_setguardsize(attr: *pthread_attr_t, guardsize: usize) E`: `0`. -/
def pthread_attr_setguardsize (attr : Ptr) (_guardsize : BitVec 64) : MemM (BitVec 16) := do
  let _ ← loadBytes attr pthreadAttrSize 8
  writeAttr attr
  return 0

/-- `pthread_create(newthread: *pthread_t, attr: ?*const pthread_attr_t, start_routine, arg) E`
(module doc): `t` is the spawn target of `(start_routine, arg)`. Writes the handle; returns `0`,
or `EAGAIN` when the run's environment fails the spawn (`Zig.Env.spawn`). -/
def pthread_create (newthread : Ptr) (attr : Option Ptr) (t : Tgt) :
    ConcM Tgt (BitVec 16) := do
  if let some a := attr then let _ ← ConcM.liftMem (loadBytes a pthreadAttrSize 8)
  match ← ConcM.sync (.spawn t) with
  | .ok child =>
    ConcM.liftMem (store 8 newthread child)
    return 0
  | .error _ => return BitVec.ofNat 16 E.AGAIN

/-- `pthread_join(thread: pthread_t, arg_return: ?*?*anyopaque) E` with `arg_return = null`:
the scheduler's `join` (the edge from the end of `thread`); `0`. -/
def pthread_join (thread : ThreadId) (arg_return : Option Ptr) : ConcM Tgt (BitVec 16) := do
  if arg_return ≠ none then throw .unspecified
  ConcM.sync (.join thread)
  return 0

/-- `pthread_detach(thread: pthread_t) E`: the caller gives up its obligation to join `thread`
(`Thread.detach`, C07: the handle is consumed and `released`, so its accesses get no join
edge); the thread stays signalable (`OsState.detached`); `0`. -/
def pthread_detach (thread : ThreadId) : MemM (BitVec 16) := do
  Thread.detach thread
  modify fun m => { m with os := { m.os with detached := m.os.detached.push thread } }
  return 0

/-- `pthread_self() pthread_t`. -/
def pthread_self : MemM ThreadId := do pure (← get).current

/-- `pthread_threadid_np(thread: ?pthread_t, thread_id: *u64) c_int`: the id of `thread` (`null`:
the caller), `ESRCH` for a thread that is not alive. -/
def pthread_threadid_np (env : Env) (thread : Option ThreadId) (thread_id : Ptr) :
    MemM (BitVec 32) := do
  let m ← get
  let t := thread.getD m.current
  if !m.threadAlive t then return BitVec.ofNat 32 E.SRCH
  store 8 thread_id ((env.tid t).setWidth 64)
  return 0

/-- `SIG.IO` on macOS. -/
def SIG_IO : BitVec 32 := 23

/-- `pthread_kill(thread: pthread_t, sig: SIG) c_int` with `sig = .IO` (OSG-01): `0`, or `ESRCH`
for a thread that is not alive. -/
def pthread_kill (thread : ThreadId) (sig : BitVec 32) : MemM (BitVec 32) := do
  if sig ≠ SIG_IO then throw .unspecified
  if !(← get).threadAlive thread then return BitVec.ofNat 32 E.SRCH
  interrupt thread
  return 0

/-- The bytes of `"hw.logicalcpu"`. -/
def logicalCpuName : List (BitVec 8) := "hw.logicalcpu".toList.map fun c => BitVec.ofNat 8 c.toNat

/-- Read the NUL-terminated string at `p`, at most `max` bytes before the NUL: `none` if longer. -/
def readCString (p : Ptr) : Nat → MemM (Option (List (BitVec 8)))
  | 0 => pure none
  | max + 1 => do
    let b ← load (BitVec 8) 1 p
    if b = 0 then return some []
    match ← readCString (p.add 1) max with
    | none => return none
    | some bs => return some (b :: bs)

/-- `sysctlbyname(name: [*:0]const u8, oldp: ?*anyopaque, oldlenp: ?*usize, newp: ?*anyopaque,
newlen: usize) c_int` for `"hw.logicalcpu"` read into a `c_int` (OST-03): writes `Env.cpus` and
the length `4`; `0`. Any other name or use is outside the model. -/
def sysctlbyname (env : Env) (name : Ptr) (oldp oldlenp newp : Option Ptr) (newlen : BitVec 64) :
    MemM (BitVec 32) := do
  if (← readCString name 64) ≠ some logicalCpuName then throw .unspecified
  let (some old, some len, none) := (oldp, oldlenp, newp) | throw .unspecified
  if newlen ≠ 0 then throw .unspecified
  let cap ← load (BitVec 64) 8 len
  if cap.toNat < 4 then throw .unspecified
  store 4 old (BitVec.ofNat 32 env.cpus)
  store 8 len (4 : BitVec 64)
  return 0

/-- `sched_yield() c_int` (OSY-01). -/
def sched_yield : ConcM Tgt (BitVec 32) := do
  ConcM.sync .yield
  return 0

end Darwin

end Os
end Zig
