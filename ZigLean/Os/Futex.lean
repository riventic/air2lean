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
audit finding #14). A bad pointer that passed address validation (no live block, out of bounds) is `.illegal` (std
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

**macOS wait results** (xnu-12377.121.6, `bsd/kern/sys_ulock.c`). A wait that returns without an
error (a wake, a spurious return or a mismatch) returns `*retval = --ull_nwaiters`
(`ulock_wait_cleanup`, :826): the number of other threads in a wait at the same key at that
moment, a non-negative `c_int` (asserted at :857). The word's `copyin` (:663) runs under the
ull spinlock, which makes any VM fault fail (:652–657), so a live word that is not resident
returns `-EFAULT` before the compare (std treats it as a spurious return). The model tracks
neither: after the wait the oracle picks `-EFAULT` or any value in `[0, 2^31)`
(`ulockResult`, one more stop). A bad pointer stays WAIT's conservative refusal (below). Other
paths:

* `ENOMEM` (:636) needs `ull_alloc`'s `zalloc_flags(ull_zone, Z_SET_NOT_EARLY)` to fail. That is
  a `Z_WAITOK` allocation, which never fails from a zone that is not exhaustible
  (`osfmk/kern/zalloc.h:383–390`). A zone is exhaustible only if `zone_set_exhaustible`
  (`zalloc.c:8805`) lowered its `z_wired_max` from `~0u` (`zalloc.c:8795`,
  `zalloc_internal.h:748–751`), and the kalloc-type zones of `KALLOC_TYPE_DEFINE`
  (`osfmk/kern/kalloc.c`) never call it. So it is unreachable.
* `EDOM` (:646; WAKE :1012) needs another opcode at the same key. Every ulock call of a row
  uses `COMPARE_AND_WAIT`, and any other op is `.unspecified`. The one other opcode in a run
  is `os_unfair_lock`'s `UL_UNFAIR_LOCK`, at a `std.Thread.Mutex` word on macOS, which the
  STD-06 hand rows model without the kernel. A ulock wait at such a lock word while a thread
  blocks in the lock is `-EDOM` natively but not in the model. That is a model gap (audit
  soundness-2026-10-14 §S6, finding 4).

**Address validation** happens before an interrupt, pick, word read or queue change. The
address the kernel receives is the pointer's numeric address as a `usize` (`futexAddr`).

* **Linux.** WAIT first copies and validates its optional timespec. Both rows then follow
  `get_futex_key` (Linux v6.16 `kernel/futex/core.c:521–628`, `Linux.futexKey`):
  - an address that is not a multiple of four returns `-EINVAL`;
  - then `access_ok` and the key. A private key needs a user address. A shared key (no
    `FUTEX_PRIVATE_FLAG`) needs a writable page: `get_user_pages_fast`, for anonymous memory a
    key of the address space and the address, distinct from the private key.

  The model forms the key only where it knows that the kernel forms it: at a live writable word
  of the model (`Mem.wordAt`), and, for a private key, at any address below the end of a block
  that the run placed (`Mem.userBelow`, premise SEM-07). It returns `-EFAULT` only where no
  `access_ok` passes: at an address with bits 63 and 55 set. That is a kernel address on x86_64,
  also with LAM (whose `untagged_addr` keeps an address with bit 63 set), and on aarch64, also
  under the tagged-address ABI (whose `untagged_addr` sign-extends bit 55). Any other address
  would need native mapping or address-space knowledge that the model leaves open, for example
  the read-only file-backed (inode) key of a shared request on a `const` global, an address above
  every block, or a tagged aarch64 address. That is a conservative `.illegal` refusal: the model
  says `.illegal` where native code returns `-EFAULT` or forms a key. Once the key forms, the
  queue still matches waiters by pointer, not by key (audit S6, premise OSF-02).
* **macOS** (xnu-12377.121.6, `bsd/kern/sys_ulock.c`). A WAIT with a null or unaligned address
  returns `-EINVAL`. A WAKE with a null address returns `-EINVAL`, and an unaligned WAKE looks up
  its key and finds no waiter. The key is the task and the address (`ULK_UADDR`). A live
  writable word of the model is never null (SEM-07).

Past validation, WAIT's word read keeps the existing conservative access failure. A bad
pointer is `.illegal` where native code returns `-EFAULT`.
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
def FAULT : Nat := 14
def INVAL : Nat := 22
def TIMEDOUT : Nat := 110
end Linux.E

-- `std.c.E` on macOS.
namespace Darwin.E
def NOENT : Nat := 2
def SRCH : Nat := 3
def INTR : Nat := 4
def FAULT : Nat := 14
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

/-! ## `struct timespec` -/

/-- A `timespec` (`{ sec: isize, nsec: isize }`, 16 bytes, both targets) as the kernel reads it:
`none` if it is invalid (`EINVAL`: a negative second count, or nanoseconds outside
`[0, 10^9)`). -/
def readTimespec (p : Ptr) : MemM (Option Nat) := do
  let sec ← load (BitVec 64) 8 p
  let nsec ← load (BitVec 64) 8 (p.add 8)
  if sec.toInt < 0 ∨ nsec.toInt < 0 ∨ 1000000000 ≤ nsec.toInt then return none
  return some (sec.toNat * 1000000000 + nsec.toNat)

/-! ## Address validation (module doc) -/

/-- The address that the kernel receives for a pointer with numeric address `a`: its `usize`. -/
def futexAddr (a : Int) : Nat := (a % 2 ^ 64).toNat

/-- `p` is a live writable `u32` of the model: four live bytes of one live block that is not
read-only, at an address that is a multiple of four (`Mem.accessW`). Natively it is a mapped,
writable user word (premise SEM-07). -/
def _root_.Zig.Mem.wordAt (m : Mem) (p : Ptr) : Bool :=
  match (m.accessW p 4 4).run with
  | some (.ok _) => true
  | _ => false

/-- The address `e - 1` is below the end of a block that the run placed, live or not: natively a
user address (premise SEM-07), so `access_ok` passes for every address below `e`. -/
def _root_.Zig.Mem.userBelow (m : Mem) (e : Nat) : Bool :=
  m.blocks.any fun blk => decide (0 < blk.bytes.size ∧ e ≤ blk.addr + blk.bytes.size)

/-! ## Linux (`std.os.linux`, x86_64) -/

namespace Linux

/-- `get_futex_key` (core.c:521–628) after the alignment check, at the pointer `p` with numeric
address `a`, for a shared or a private key: `none` once the kernel forms the key, `-EFAULT` for
an address that no `access_ok` admits (bits 63 and 55 set, module doc), `.illegal` where the native result
needs knowledge that the model leaves open (module doc). No state change. -/
def futexKey (p : Ptr) (a : Int) (shared : Bool) : MemM (Option (BitVec 64)) := do
  let m ← get
  let u := futexAddr a
  if m.wordAt p || (!shared && m.userBelow (u + 4)) then return none
  if 2 ^ 63 ≤ u && u.testBit 55 then return some (negErrno E.FAULT)
  throw .illegal

/-- `FUTEX_OP{ .cmd = .WAIT }` and `FUTEX_OP{ .cmd = .WAKE }`; `.private = true` adds `0x80`. -/
def FUTEX_WAIT : BitVec 32 := 0
def FUTEX_WAKE : BitVec 32 := 1
def FUTEX_PRIVATE : BitVec 32 := 0x80

/-- `os.linux.futex_4arg(uaddr: *const anyopaque, futex_op: FUTEX_OP, val: u32,
timeout: ?*const timespec) usize` with `cmd = .WAIT` (private or not): `0` (woken),
`-EAGAIN`, `-EINTR`, `-ETIMEDOUT`, `-EINVAL` for an invalid timeout or unaligned address, or
`-EFAULT` (`futexKey`). `futex_op` is the `FUTEX_OP`'s bits; without `FUTEX_PRIVATE` the key is
shared. -/
def futex_4arg (uaddr : Ptr) (futex_op : BitVec 32) (val : BitVec 32) (timeout : Option Ptr) :
    ConcM Tgt (BitVec 64) := do
  if futex_op ≠ FUTEX_WAIT ∧ futex_op ≠ FUTEX_WAIT ||| FUTEX_PRIVATE then throw .unspecified
  if let some ts := timeout then
    if (← ConcM.liftMem (readTimespec ts)).isNone then return negErrno E.INVAL
  let a ← ConcM.liftMem (ptrAddr uaddr)
  if a % 4 ≠ 0 then return negErrno E.INVAL
  if let some e ← ConcM.liftMem (futexKey uaddr a (futex_op = FUTEX_WAIT)) then return e
  match ← futexWait uaddr val timeout.isSome with
  | .woken => return 0
  | .mismatch => return negErrno E.AGAIN
  | .interrupted => return negErrno E.INTR
  | .timedOut => return negErrno E.TIMEDOUT

/-- The `nr_wake` of `FUTEX_WAKE`: the kernel wakes at least one waiter for `val ≤ 0` (an
`int`). -/
def wakeLimit (val : BitVec 32) : Nat := if val.toInt ≤ 0 then 1 else val.toNat

/-- `os.linux.futex_3arg(uaddr: *const anyopaque, futex_op: FUTEX_OP, val: u32) usize` with
`cmd = .WAKE` (private or not): the number of threads woken, `-EINVAL` for an unaligned
numeric address, or `-EFAULT` (`futexKey`; module doc). -/
def futex_3arg (uaddr : Ptr) (futex_op : BitVec 32) (val : BitVec 32) : ConcM Tgt (BitVec 64) := do
  if futex_op ≠ FUTEX_WAKE ∧ futex_op ≠ FUTEX_WAKE ||| FUTEX_PRIVATE then throw .unspecified
  let a ← ConcM.liftMem (ptrAddr uaddr)
  if a % 4 ≠ 0 then return negErrno E.INVAL
  if let some e ← ConcM.liftMem (futexKey uaddr a (futex_op = FUTEX_WAKE)) then return e
  let r ← futexWake uaddr (some (wakeLimit val))
  return BitVec.ofNat 64 (r.getD 0)

end Linux

/-! ## macOS (`std.c`, aarch64) -/

namespace Darwin

/-- `UL{ .op = .COMPARE_AND_WAIT, .NO_ERRNO = true }`'s bits; `WAKE_ALL` adds `0x100`. -/
def UL_COMPARE_AND_WAIT_NO_ERRNO : BitVec 32 := 0x01000001
def UL_WAKE_ALL : BitVec 32 := 0x100

/-- `sys_ulock.c`'s address check: the pointer, or `none` (`EINVAL`) for a null address (no
pointer, or one at address `0`) or, with `aligned`, one that is not a multiple of four (the
32-bit ops' `lock_size - 1`; the 64-bit ops stay `.unspecified` before this check). A live
writable word of the model passes without resolving its address: it is never null (SEM-07). -/
def ulockAddr (addr : Option Ptr) (aligned : Bool) : MemM (Option Ptr) := do
  let some p := addr | return none
  if (← get).wordAt p then return some p
  let u := futexAddr (← ptrAddr p)
  return if u = 0 ∨ (aligned ∧ u % 4 ≠ 0) then none else some p

/-- The number of non-negative `c_int`s, `[0, 2^31)`: the values of `--ull_nwaiters`. -/
def ulockWaiters : Nat := 2 ^ 31

/-- Option `c` of a wait's result pick: `0` is `-EFAULT`, `c + 1` is `--ull_nwaiters = c`. -/
def ulockCode (c : Nat) : BitVec 32 := if c = 0 then negErrno32 E.FAULT else BitVec.ofNat 32 (c - 1)

/-- The return code of a wait that ended with `r` (module doc). After a wake, a spurious return or
a mismatch the oracle picks option `0`, `-EFAULT` (a word that is not resident), or option
`c + 1`, `--ull_nwaiters = c` (`sys_ulock.c:826`, any non-negative `c_int`). Else `-EINTR` or
`-ETIMEDOUT`. -/
def ulockResult : WaitResult → ConcM Tgt (BitVec 32)
  | .woken | .mismatch => return ulockCode (← pick fun _ => ulockWaiters + 1)
  | .interrupted => return negErrno32 E.INTR
  | .timedOut => return negErrno32 E.TIMEDOUT

/-- The return codes `s` of a wait that ended with `r` (`ulockResult`): `-EFAULT` or any
non-negative `c_int` after a wake, a spurious return or a mismatch, else `-EINTR` or
`-ETIMEDOUT`. -/
def WaitCode : WaitResult → BitVec 32 → Prop
  | .woken, s | .mismatch, s => s = negErrno32 E.FAULT ∨ 0 ≤ s.toInt
  | .interrupted, s => s = negErrno32 E.INTR
  | .timedOut, s => s = negErrno32 E.TIMEDOUT

/-- The shared part of `__ulock_wait2`/`__ulock_wait`: the wait's `ulockResult`, or `-EINVAL`
for a null or unaligned address (module doc). -/
def ulockWait (op : BitVec 32) (addr : Option Ptr) (value : BitVec 64) (timed : Bool) :
    ConcM Tgt (BitVec 32) := do
  if op ≠ UL_COMPARE_AND_WAIT_NO_ERRNO ∨ 2 ^ 32 ≤ value.toNat then throw .unspecified
  let some p ← ConcM.liftMem (ulockAddr addr true) | return negErrno32 E.INVAL
  ulockResult (← futexWait p (value.setWidth 32) timed)

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
`-EINTR` with nobody woken (std retries), or `-EINVAL` for a null address (module doc). `val`
must be `0`. -/
def __ulock_wake (op : BitVec 32) (addr : Option Ptr) (val : BitVec 64) : ConcM Tgt (BitVec 32) := do
  if (op ≠ UL_COMPARE_AND_WAIT_NO_ERRNO ∧ op ≠ UL_COMPARE_AND_WAIT_NO_ERRNO ||| UL_WAKE_ALL) ∨
      val ≠ 0 then
    throw .unspecified
  let some p ← ConcM.liftMem (ulockAddr addr false) | return negErrno32 E.INVAL
  match ← futexWake p (if op = UL_COMPARE_AND_WAIT_NO_ERRNO then some 1 else none)
      (spurious := true) with
  | none => return negErrno32 E.INTR
  | some 0 => return negErrno32 E.NOENT
  | some _ => return 0

end Darwin

end Os
end Zig
