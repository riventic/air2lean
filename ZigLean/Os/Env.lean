import ZigLean.Conc.Spawn

/-!
# The OS environment of the thread primitives (premises OST-01, OST-03, OSK-01, OSM-02)

The trusted OS thread primitives (`docs/os-threads.md`) take an explicit environment record
`Os.Env`: what the operating system decides and the program cannot (user decision D2,
2026-10-09: the CPU count, the spawn policy and the allocator's thread safety are explicit
parameters or premises of every concurrent theorem, never constants of the model).

* `cpuMask`: the CPUs the process may run on (`sched_getaffinity`), so `cpus` is
  `std.Thread.getCpuCount()` and `Io.Threaded`'s `async_limit` is `cpus - 1`.
* `spawn`: whether thread creation (`clone`, `pthread_create`) may fail
  (`ZigLean/Conc/Spawn.lean`: `available` or `fallible`, with `Mem.spawnLimit`).
* `tid`, `pid`: the kernel's thread ids and process id. A model thread's id never changes.
* `clock`: the value of the `i`-th clock read of a run, per clock (`clock_gettime`).
* `mallocSlack`: the bytes `malloc` adds to request `n` at allocation attempt `i`
  (`malloc_size` reports them).

`Env.Valid` is the premise that a theorem states about the environment: at least one CPU, thread
ids that are distinct and positive, monotone clocks for `awake` and `boot`, and clock values that
fit a `timespec`. A theorem over every `env` with `env.Valid` covers every environment that the
premises allow. Libc's `malloc`/`free` are thread-safe (OSM-02): no allocator flag is needed for
them.
-/

namespace Zig
namespace Os

/-- The clocks that `std.Io.Clock` maps to (`Io.Threaded.clockToPosix`, Zig 0.16.0):
`real` is `CLOCK_REALTIME`; `awake` is Linux `CLOCK_MONOTONIC` and macOS `CLOCK_UPTIME_RAW` (it
stops while the system sleeps); `boot` is Linux `CLOCK_BOOTTIME` and macOS
`CLOCK_MONOTONIC_RAW`/`CLOCK_MONOTONIC` (it counts the time asleep). -/
inductive Clock where
  | real
  | awake
  | boot
  deriving DecidableEq, Repr, Inhabited

/-- The clock never goes back. `real` can be set, so it can. -/
def Clock.monotone : Clock → Bool
  | .real => false
  | .awake | .boot => true

/-- The bits of a Linux `cpu_set_t` (`[1024 / 64]usize`). -/
def cpuSetBits : Nat := 1024

/-- The OS environment (module doc). -/
structure Env where
  /-- Bit `i` set: CPU `i` is in the process's affinity mask. Bits from `cpuSetBits` on are
  ignored. -/
  cpuMask : Nat
  /-- Whether `clone`/`pthread_create` may fail. -/
  spawn : SpawnPolicy
  /-- The kernel thread id of model thread `t` (Linux `gettid`; macOS `pthread_threadid_np`,
  zero-extended). -/
  tid : ThreadId → BitVec 32
  /-- The process id (Linux `getpid`). -/
  pid : BitVec 32
  /-- `clock k i`: the nanoseconds that clock `k` reads at the `i`-th clock read of the run
  (`OsState.clockReads`). -/
  clock : Clock → Nat → Nat
  /-- `mallocSlack i n`: the bytes beyond `n` that `malloc(n)` at allocation attempt `i` makes
  usable. -/
  mallocSlack : Nat → Nat → Nat
  deriving Inhabited

/-- The CPU count: the CPUs of the affinity mask (`posix.CPU_COUNT`, `hw.logicalcpu`). -/
def Env.cpus (env : Env) : Nat := (List.range cpuSetBits).countP (env.cpuMask.testBit ·)

/-- One above the largest number of nanoseconds whose seconds fit the `i64` of a `timespec`. -/
def timespecLimit : Nat := 2 ^ 63 * 1000000000

/-- The premise on the environment (module doc). -/
structure Env.Valid (env : Env) : Prop where
  cpus_pos : 0 < env.cpus
  tid_inj : ∀ a b, env.tid a = env.tid b → a = b
  tid_pos : ∀ t, 0 < (env.tid t).toInt
  pid_pos : 0 < env.pid.toInt
  clock_mono : ∀ k, k.monotone = true → ∀ i j, i ≤ j → env.clock k i ≤ env.clock k j
  clock_lt : ∀ k i, env.clock k i < timespecLimit

/-- The environment of the runtime regressions and examples: CPUs 0–3, assignment always
succeeds, thread `t` has id `1000 + t`, a clock that ticks once per read, and no malloc slack. It
is not `Valid` (the ids wrap at `2^32`); theorems quantify over environments instead. -/
def Env.example : Env where
  cpuMask := 0xf
  spawn := .available
  tid t := BitVec.ofNat 32 (1000 + t)
  pid := 1000
  clock _ i := i
  mallocSlack _ _ := 0

end Os
end Zig
