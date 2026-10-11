import ZigLean.Os.Env

/-!
# Futexes: Linux `futex_4arg`/`futex_3arg`, macOS `__ulock_wait2`/`__ulock_wait`/`__ulock_wake`
(premises OSF-01, OSF-02)

Std 0.16.0 reaches the kernel's wait queues only through these calls (`Io.Threaded.Thread.
futexWaitInner`/`futexWake`, `Thread.LinuxThreadImpl.join`; `docs/thread-io-translation.md` §1.2).
Under `--thread-model translated` the translator cuts the call graph at the named wrapper
(`os.linux.futex_4arg`, `os.linux.futex_3arg`) or the `extern "c"` symbol (`__ulock_*`) and calls
the definition below. Each one is a concurrent function (`ConcM`): it stops at sync ops of the
existing scheduler (`ZigLean/Conc/Sched.lean`), over the same memory and RC11-approximate atomics
(`ZigLean/Mem/Thread.lean`). The kernel's wait queue is `Mem.waiters`/`Mem.woken`, as for the
std-mode futex rows.

**Wait** (`futexWait`). One `pick`, then in the same turn the kernel's compare: an atomic read of
the `u32` at `p` that reads the newest message (`atomicLoadAt 0 .relaxed`: an atomic-read
footprint, so a racing plain write is `.illegal`, and `observe`, so the waiter's view moves on;
audit finding #14). A bad pointer (no live block, out of bounds, misaligned) is `.illegal` (std
treats `EFAULT` as an OS bug). If the word is not `expected`, the call returns `mismatch`
(`EAGAIN`). Otherwise the oracle picks one of:

* `0`, sleep: an untimed wait stops at the scheduler's `wait p expected`, which compares the word
  again and sleeps until a wake at `p` (if the word changed in between, the thread goes on: a
  spurious return with `0`, which Linux allows). A timed wait joins the queue and stops at a
  `yield` instead: it stays runnable, so the scheduler can resume it at any later turn — a wake
  in between makes it return `woken`, else it leaves the queue and returns `timedOut`. A timed
  wait never deadlocks;
* `1`, `EINTR` at once (a signal; any spurious return);
* `2` (timed only), `ETIMEDOUT` at once.

A sleeper that a `tgkill`/`pthread_kill` (`ZigLean/Os/Thread.lean`, OSG-01) woke returns
`interrupted`. A wake gives no happens-before edge: std reads the word again with an acquire.

**Wake** (`futexWake`). One `pick` among the subsets of `min n k` of the `k` threads queued at `p`
(audit finding #6: no FIFO order), which go on; the call returns their number. No memory access
(a private futex is keyed by its address). macOS `__ulock_wake` also has the option `EINTR`
with nobody woken (std retries).

The return conventions are the ABI's: a Linux wrapper returns the raw `usize` (`-errno` on
failure, decoded by the translated `linux.errno`); `__ulock_*` with `NO_ERRNO` return `-errno` as
a `c_int`. Arguments that std never passes (other futex commands, flags, `val2`) are outside the
model: `.unspecified`.
-/

namespace Zig
namespace Os

variable {Tgt : Type}

/-! ## Errno values -/

/-- `-e` as the `usize` of a raw Linux syscall result. -/
def negErrno (e : Nat) : BitVec 64 := -(BitVec.ofNat 64 e)

/-- `-e` as a `c_int` (`__ulock_*` with `NO_ERRNO`). -/
def negErrno32 (e : Nat) : BitVec 32 := -(BitVec.ofNat 32 e)

-- `std.os.linux.E` (x86_64).
namespace Linux.E
def SRCH : Nat := 3
def INTR : Nat := 4
def AGAIN : Nat := 11
def NOMEM : Nat := 12
def INVAL : Nat := 22
def TIMEDOUT : Nat := 110
end Linux.E

-- `std.c.E` on macOS.
namespace Darwin.E
def NOENT : Nat := 2
def SRCH : Nat := 3
def INTR : Nat := 4
def INVAL : Nat := 22
def AGAIN : Nat := 35
def TIMEDOUT : Nat := 60
end Darwin.E

/-! ## The kernel's part -/

/-- A choice of the oracle among `count m` options (`SyncOp.pick`). -/
def pick (count : Mem → Nat) : ConcM Tgt Nat := ConcM.sync (.pick count)

/-- How a futex wait returned. -/
inductive WaitResult where
  /-- A wake woke the thread, or a spurious return with `0`. -/
  | woken
  /-- The word was not the expected value (`EAGAIN`). -/
  | mismatch
  /-- `EINTR`: a signal, or a spurious return. -/
  | interrupted
  /-- `ETIMEDOUT`. -/
  | timedOut
  deriving DecidableEq, Repr, Inhabited

/-- The kernel's compare of a futex word: an atomic read of the newest message of the `u32` at
`p` (module doc). -/
def futexWord (p : Ptr) : MemM (BitVec 32) := atomicLoadAt 0 .relaxed 4 p

/-- The options of a wait at `p` for `e`: one (`mismatch`, or the read throws) unless the word is
`e`; then sleep and `EINTR`, and `ETIMEDOUT` if `timed`. -/
def waitCount (p : Ptr) (e : BitVec 32) (timed : Bool) (m : Mem) : Nat :=
  match ((futexWord p).run m).run with
  | some (.ok (v, _)) => if v = e then (if timed then 3 else 2) else 1
  | _ => 1

/-- The current thread's pending interrupt (OSG-01), which this call delivers: `true` if there
was one. -/
def takeInterrupt : MemM Bool := do
  let m ← get
  if m.os.interrupts.contains m.current then
    set { m with os := { m.os with interrupts := m.os.interrupts.erase m.current } }
    pure true
  else pure false

/-- A timed sleeper joins the queue at `p`. -/
def enqueue (p : Ptr) : MemM Unit := modify fun m => { m with waiters := m.waiters.push (m.current, p) }

/-- A timed sleeper resumes: an interrupt, a wake, or else the timeout; it leaves the queue. -/
def timedResume : MemM WaitResult := do
  let intr ← takeInterrupt
  let m ← get
  let me := m.current
  let woke := m.woken.contains me
  set { m with woken := m.woken.erase me, waiters := m.waiters.filter (·.1 != me) }
  pure (if intr then .interrupted else if woke then .woken else .timedOut)

/-- A futex wait at `p` for `e` (module doc). An interrupt pending at the call was delivered
before it (the signal handler ran first). -/
def futexWait (p : Ptr) (e : BitVec 32) (timed : Bool) : ConcM Tgt WaitResult := do
  let _ ← ConcM.liftMem takeInterrupt
  let c ← pick (waitCount p e timed)
  let v ← ConcM.liftMem (futexWord p)
  if v ≠ e then return .mismatch
  match c with
  | 0 =>
    if timed then
      ConcM.liftMem (enqueue p)
      ConcM.sync .yield
      ConcM.liftMem timedResume
    else
      ConcM.sync (.wait p e)
      return (if ← ConcM.liftMem takeInterrupt then .interrupted else .woken)
  | 1 => return .interrupted
  | _ => return .timedOut

/-- The `k`-element sublists of `xs`, in order. -/
def sublistsLen {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (sublistsLen k xs).map (x :: ·) ++ sublistsLen (k + 1) xs

/-- The threads queued at `p`, in queue order. -/
def _root_.Zig.Mem.waitersAt (m : Mem) (p : Ptr) : List ThreadId :=
  (m.waiters.toList.filter (·.2 == p)).map (·.1)

/-- The sets of threads that a wake of up to `n` waiters at `p` (`none`: all) can wake: every
subset of `min n k` of the `k` queued threads. -/
def wakeSets (m : Mem) (p : Ptr) (n : Option Nat) : List (List ThreadId) :=
  let ws := m.waitersAt p
  sublistsLen ((n.map (Nat.min · ws.length)).getD ws.length) ws

/-- The number of options of a wake. -/
def wakeCount (p : Ptr) (n : Option Nat) (m : Mem) : Nat := (wakeSets m p n).length

/-- The threads `ts` leave the queue and go on at their next turn. -/
def wakeThreads (ts : List ThreadId) : MemM Unit := modify fun m =>
  { m with waiters := m.waiters.filter (fun w => !ts.contains w.1), woken := m.woken ++ ts.toArray }

/-- Wake option `c` of up to `n` waiters at `p`: the number woken, or `none` (nobody woken) past
the last option. -/
def wakeAt (c : Nat) (p : Ptr) (n : Option Nat) : MemM (Option Nat) := do
  let some ts := (wakeSets (← get) p n)[c]? | return none
  wakeThreads ts
  return some ts.length

/-- A futex wake of up to `n` waiters at `p` (`none`: all of them; module doc). With `spurious`,
there is one more option, `none`: `EINTR`, nobody woken. -/
def futexWake (p : Ptr) (n : Option Nat) (spurious : Bool := false) : ConcM Tgt (Option Nat) := do
  let c ← pick fun m => wakeCount p n m + (if spurious then 1 else 0)
  ConcM.liftMem (wakeAt c p n)

/-- Wake every thread queued at `p` (the kernel's wake after `CHILD_CLEARTID`): no choice. -/
def wakeAll (p : Ptr) : MemM Unit := do
  wakeThreads ((← get).waitersAt p)

/-! ## `struct timespec` -/

/-- A `timespec` (`{ sec: isize, nsec: isize }`, 16 bytes, both targets) as the kernel reads it:
`none` if it is invalid (`EINVAL`: a negative second count, or nanoseconds outside
`[0, 10^9)`). -/
def readTimespec (p : Ptr) : MemM (Option Nat) := do
  let sec ← load (BitVec 64) 8 p
  let nsec ← load (BitVec 64) 8 (p.add 8)
  if sec.toInt < 0 ∨ nsec.toInt < 0 ∨ 1000000000 ≤ nsec.toInt then return none
  return some (sec.toNat * 1000000000 + nsec.toNat)

/-! ## Linux (`std.os.linux`, x86_64) -/

namespace Linux

/-- `FUTEX_OP{ .cmd = .WAIT }` and `FUTEX_OP{ .cmd = .WAKE }`; `.private = true` adds `0x80`. -/
def FUTEX_WAIT : BitVec 32 := 0
def FUTEX_WAKE : BitVec 32 := 1
def FUTEX_PRIVATE : BitVec 32 := 0x80

/-- `os.linux.futex_4arg(uaddr: *const anyopaque, futex_op: FUTEX_OP, val: u32,
timeout: ?*const timespec) usize` with `cmd = .WAIT` (private or not): `0` (woken),
`-EAGAIN`, `-EINTR`, `-ETIMEDOUT`, or `-EINVAL` for an invalid timeout (module doc).
`futex_op` is the `FUTEX_OP`'s bits. -/
def futex_4arg (uaddr : Ptr) (futex_op : BitVec 32) (val : BitVec 32) (timeout : Option Ptr) :
    ConcM Tgt (BitVec 64) := do
  if futex_op ≠ FUTEX_WAIT ∧ futex_op ≠ FUTEX_WAIT ||| FUTEX_PRIVATE then throw .unspecified
  if let some ts := timeout then
    if (← ConcM.liftMem (readTimespec ts)).isNone then return negErrno E.INVAL
  match ← futexWait uaddr val timeout.isSome with
  | .woken => return 0
  | .mismatch => return negErrno E.AGAIN
  | .interrupted => return negErrno E.INTR
  | .timedOut => return negErrno E.TIMEDOUT

/-- The `nr_wake` of `FUTEX_WAKE`: the kernel wakes at least one waiter for `val ≤ 0` (an
`int`). -/
def wakeLimit (val : BitVec 32) : Nat := if val.toInt ≤ 0 then 1 else val.toNat

/-- `os.linux.futex_3arg(uaddr: *const anyopaque, futex_op: FUTEX_OP, val: u32) usize` with
`cmd = .WAKE` (private or not): the number of threads woken (module doc). -/
def futex_3arg (uaddr : Ptr) (futex_op : BitVec 32) (val : BitVec 32) : ConcM Tgt (BitVec 64) := do
  if futex_op ≠ FUTEX_WAKE ∧ futex_op ≠ FUTEX_WAKE ||| FUTEX_PRIVATE then throw .unspecified
  let r ← futexWake uaddr (some (wakeLimit val))
  return BitVec.ofNat 64 (r.getD 0)

end Linux

/-! ## macOS (`std.c`, aarch64) -/

namespace Darwin

/-- `UL{ .op = .COMPARE_AND_WAIT, .NO_ERRNO = true }`'s bits; `WAKE_ALL` adds `0x100`. -/
def UL_COMPARE_AND_WAIT_NO_ERRNO : BitVec 32 := 0x01000001
def UL_WAKE_ALL : BitVec 32 := 0x100

/-- The shared part of `__ulock_wait2`/`__ulock_wait`: a non-negative result (`0`) for a wake, a
spurious return or a mismatch; `-EINTR`, `-ETIMEDOUT`. -/
def ulockWait (op : BitVec 32) (addr : Option Ptr) (value : BitVec 64) (timed : Bool) :
    ConcM Tgt (BitVec 32) := do
  if op ≠ UL_COMPARE_AND_WAIT_NO_ERRNO ∨ 2 ^ 32 ≤ value.toNat then throw .unspecified
  let some p := addr | throw .illegal
  match ← futexWait p (value.setWidth 32) timed with
  | .woken | .mismatch => return 0
  | .interrupted => return negErrno32 E.INTR
  | .timedOut => return negErrno32 E.TIMEDOUT

/-- `__ulock_wait2(op: UL, addr: ?*const anyopaque, val: u64, timeout_ns: u64, val2: u64) c_int`
(macOS ≥ 11): `timeout_ns = 0` waits without a timeout; `val2` must be `0`. -/
def __ulock_wait2 (op : BitVec 32) (addr : Option Ptr) (val timeout_ns val2 : BitVec 64) :
    ConcM Tgt (BitVec 32) := do
  if val2 ≠ 0 then throw .unspecified
  ulockWait op addr val (timeout_ns ≠ 0)

/-- `__ulock_wait(op: UL, addr: ?*const anyopaque, val: u64, timeout_us: u32) c_int` (before
macOS 11): `timeout_us = 0` waits without a timeout. -/
def __ulock_wait (op : BitVec 32) (addr : Option Ptr) (val : BitVec 64) (timeout_us : BitVec 32) :
    ConcM Tgt (BitVec 32) :=
  ulockWait op addr val (timeout_us ≠ 0)

/-- `__ulock_wake(op: UL, addr: ?*const anyopaque, val: u64) c_int`: wakes one waiter (oracle) or,
with `WAKE_ALL`, every waiter at `addr`: `0` if it woke one, `-ENOENT` if nobody waited, or
`-EINTR` with nobody woken (std retries). `val` must be `0`. -/
def __ulock_wake (op : BitVec 32) (addr : Option Ptr) (val : BitVec 64) : ConcM Tgt (BitVec 32) := do
  if (op ≠ UL_COMPARE_AND_WAIT_NO_ERRNO ∧ op ≠ UL_COMPARE_AND_WAIT_NO_ERRNO ||| UL_WAKE_ALL) ∨
      val ≠ 0 then
    throw .unspecified
  let some p := addr | throw .illegal
  match ← futexWake p (if op = UL_COMPARE_AND_WAIT_NO_ERRNO then some 1 else none)
      (spurious := true) with
  | none => return negErrno32 E.INTR
  | some 0 => return negErrno32 E.NOENT
  | some _ => return 0

end Darwin

end Os
end Zig
