import ZigLean.Os.Thread

/-!
# Clocks and sleep: `clock_gettime`, Linux `clock_nanosleep`, macOS `nanosleep`
(premises OSK-01, OSK-02)

`Io.Threaded.now` and `sleep` (Zig 0.16.0) reach the OS through these calls
(`nowPosix`, `sleepPosix` on Linux, `sleepNanosleep` on macOS, which has no `clock_nanosleep`).

**Read** (OSK-01). A clock read is a scheduling point (`yield`): the reads of all threads form one
sequence, the order of the run, and the `i`-th read of clock `k` gives `Env.clock k i` nanoseconds
(`OsState.clockReads` counts the reads). `Env.Valid` makes `awake` and `boot` monotone along that
sequence, so a read that happens after another one never gives less; `real` is arbitrary. The
`timespec` is written as two plain `isize` stores. Clocks other than those std uses are outside the
model (`.unspecified`). The default scheduler has no notion of elapsed time: a value says nothing
about the turns between two reads (the opt-in timed scheduler, TMR-02, is separate).

**Sleep** (OSK-02). One oracle choice (a scheduling point, as `yield`): return at once with `0`,
or with `EINTR` (a signal). No duration is promised. An interrupted relative sleep writes the
whole request as the time left (the kernel writes some value up to it). An invalid request is
`EINVAL`. A pending interrupt (OSG-01) is delivered at the start.

**`errno`** (macOS). `nanosleep` reports `EINTR` as `-1` and `errno`. `__error()` gives the calling
thread's `errno` cell: a 4-byte block that the thread makes at its first use, `0` at first, never
freed (`OsState.errno`).
-/

namespace Zig
namespace Os

variable {Tgt : Type}

/-- The next clock read of clock `k` (module doc). -/
def readClock (env : Env) (k : Clock) : MemM Nat := do
  let m ← get
  set { m with os := { m.os with clockReads := m.os.clockReads + 1 } }
  pure (env.clock k m.os.clockReads)

/-- Store `ns` nanoseconds as a `timespec` (`sec`, then `nsec`, both `isize`). -/
def writeTimespec (tp : Ptr) (ns : Nat) : MemM Unit := do
  store 8 tp (BitVec.ofNat 64 (ns / 1000000000))
  store 8 (tp.add 8) (BitVec.ofNat 64 (ns % 1000000000))

/-- A clock read into `tp`: the scheduling point, then the read and the stores. -/
def clockRead (env : Env) (k : Clock) (tp : Ptr) : ConcM Tgt Unit := do
  ConcM.sync .yield
  ConcM.liftMem (do writeTimespec tp (← readClock env k))

/-- An interruptible sleep for the `timespec` at `request` (module doc): `none` for an invalid
request, `some true` if a signal interrupted it (`remain`, if any, gets the request). -/
def sleepFor (request : Ptr) (remain : Option Ptr) : ConcM Tgt (Option Bool) := do
  let some ns ← ConcM.liftMem (readTimespec request) | return none
  let _ ← ConcM.liftMem takeInterrupt
  let c ← pick fun _ => 2
  if c = 0 then return some false
  if let some r := remain then ConcM.liftMem (writeTimespec r ns)
  return some true

/-! ## Linux (`std.os.linux`, x86_64) -/

namespace Linux

/-- `clockid_t`: `REALTIME = 0`, `MONOTONIC = 1`, `BOOTTIME = 7`. -/
def clockOf (clk : BitVec 32) : Option Clock :=
  if clk = 0 then some .real else if clk = 1 then some .awake else if clk = 7 then some .boot
  else none

/-- `os.linux.clock_gettime(clk_id: clockid_t, tp: *timespec) usize` (OSK-01): `0`. The vDSO
pointer that std loads is part of this row. -/
def clock_gettime (env : Env) (clk_id : BitVec 32) (tp : Ptr) : ConcM Tgt (BitVec 64) := do
  let some k := clockOf clk_id | throw .unspecified
  clockRead env k tp
  return 0

/-- `os.linux.clock_nanosleep(clockid: clockid_t, flags: TIMER, request: *const timespec,
remain: ?*timespec) usize` (OSK-02): `0`, `-EINTR` or `-EINVAL`. `flags` is `TIMER`'s bits
(`ABSTIME = 1`); an absolute sleep writes no time left. -/
def clock_nanosleep (clockid : BitVec 32) (flags : BitVec 32) (request : Ptr)
    (remain : Option Ptr) : ConcM Tgt (BitVec 64) := do
  if clockOf clockid = none ∨ (flags ≠ 0 ∧ flags ≠ 1) then throw .unspecified
  match ← sleepFor request (if flags = 0 then remain else none) with
  | none => return negErrno E.INVAL
  | some false => return 0
  | some true => return negErrno E.INTR

end Linux

/-! ## macOS (`std.c`, aarch64) -/

namespace Darwin

/-- `clockid_t`: `REALTIME = 0`, `MONOTONIC_RAW = 4`, `MONOTONIC = 6`, `UPTIME_RAW = 8`. -/
def clockOf (clk : BitVec 32) : Option Clock :=
  if clk = 0 then some .real else if clk = 8 then some .awake
  else if clk = 4 ∨ clk = 6 then some .boot else none

/-- `clock_gettime(clk_id: clockid_t, tp: *timespec) c_int` (OSK-01): `0`. -/
def clock_gettime (env : Env) (clk_id : BitVec 32) (tp : Ptr) : ConcM Tgt (BitVec 32) := do
  let some k := clockOf clk_id | throw .unspecified
  clockRead env k tp
  return 0

/-- `__error() *c_int`: the calling thread's `errno` cell (module doc). -/
def __error : MemM Ptr := do
  let m ← get
  match m.os.errno.find? (·.1 == m.current) with
  | some (_, b) => pure ⟨some b, 0⟩
  | none =>
    let p ← alloc .global 4 4
    store 4 p (0 : BitVec 32)
    modify fun m' => { m' with os := { m'.os with errno := m'.os.errno.push (m.current, m.blocks.size) } }
    pure p

/-- `errno = e`, `-1`. -/
def failWith (e : Nat) : MemM (BitVec 32) := do
  store 4 (← __error) (BitVec.ofNat 32 e)
  return -1

/-- `nanosleep(rqtp: *const timespec, rmtp: ?*timespec) c_int` (OSK-02): `0`, or `-1` with
`errno` `EINTR` or `EINVAL`. -/
def nanosleep (rqtp : Ptr) (rmtp : Option Ptr) : ConcM Tgt (BitVec 32) := do
  match ← sleepFor rqtp rmtp with
  | none => ConcM.liftMem (failWith E.INVAL)
  | some false => return 0
  | some true => ConcM.liftMem (failWith E.INTR)

end Darwin

end Os
end Zig
