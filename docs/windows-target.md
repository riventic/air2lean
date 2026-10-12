# Windows targets

This document plans Windows target support and records what Phase 1 implements: the
translator profile of **x86_64-windows-gnu** for pure computations, Zig 0.17.0 first, then
0.16.0, 0.15.2 and 0.14.1. aarch64-windows and the MSVC ABI come later (§Phases).

A Windows target is qualified the way the aarch64 targets were ([aarch64-abi.md](aarch64-abi.md)):
a row of `Target.qualified` (`Air2Lean/Air/Dialect.lean`) that holds the target's ABI facts, a
versioned probe record per Zig version that a Lean check compares with the model, golden AIR and
translations of the examples, and a native differential test. The OS layer (allocators, threads,
synchronization, `Io`) follows later, translated from the real std code down to explicit OS
premises, as on Linux and macOS ([CLAUDE.md](../CLAUDE.md) §Trusted base).

## Status (Phase 1)

| Piece | State |
| --- | --- |
| `Target.qualified` row `x86_64`/`windows`, ABI `gnu`, Zig 0.17.0/0.16.0/0.15.2/0.14.1 | done |
| Fail closed: OS-backed std models, `threadlocal`, Windows OS calls, `f80` x87 precision | done |
| `--assume-x87-extended` admission (header `x87-extended`) | done; its premise awaits approval (§Premises) |
| `scripts/check.sh` cross-target mode (`AIR2LEAN_TARGET`), `air-windows/` overlays, `Gen-windows.lean` | done: §Goldens |
| Diff harness on Windows (case child with restart, `tests/diff/common.zig`) | done |
| T04 probe for `x86_64-windows-gnu`, expected files for four versions, `Model.lean` table | done (recorded under Wine) |
| Native confirmation on a Windows host (CI `windows` job) | open: §Native evidence |
| OS layer, aarch64-windows, MSVC | later phases |

## ABI and layout differences

The facts come from the stock compilers (`@sizeOf`/`@alignOf`/`cTypeBitSize` at comptime, all
four versions) and the T04 probe.

| Fact | x86_64-linux (reference) | x86_64-windows-gnu | x86_64-windows-msvc |
| --- | --- | --- | --- |
| Baseline CPU | `x86_64` (no `cx16`) | same | same |
| Widest atomic | 64 bits | 64 bits | 64 bits |
| `c_long`/`c_ulong` | 64 bits | **32 bits** (LLP64) | 32 bits |
| `c_longdouble` | `f80`, 16/16 | `f80`, 16/16 (MinGW) | **`f64`**, 8/8 |
| `f80` layout | 16/16 | 16/16 | 16/16; **16/8 in 0.17.0** |
| `f80` arithmetic | x87 | x87, **per-thread precision control** (§x87) | **soft float** (compiler_rt), like aarch64 |
| `f128`, `u128`, `i128` | 16/16 | 16/16 | 16/16 |
| `wchar_t` (`c_ushort`) | 32-bit `wchar_t`, Zig has no `c_wchar` | 16 bits | 16 bits |
| C calling convention | SysV | Win64 (`x86_64_win`) | Win64 |
| TLS | ELF TLS | PE TLS directory, `_tls_index` | same |
| Object format | ELF | COFF | COFF |
| Cache line (`std.atomic.cache_line`) | 128 | 128 | 128 |

What reaches the translator:

- **Integer and float layouts** are the model's (`Zig.intSize`/`intAlign`, `Enc` of `f80`/`f128`):
  the probe's layout rows equal the kernel-checked table `T04.windowsGnu`.
- **`c_long`** is exported as the integer it is (`Type.intInfo` in `zig-patch/air-json/json.zig`
  is target-aware): a 32-bit `c_long` is an `i32` in AIR, so the translator needs no rule.
- **`c_longdouble`** is `f80` (`Target.longDoubleBits = 80`). The `f128` libcall rule of
  aarch64-linux (MTH-05) does not apply.
- **Calling convention, struct/union passing, `__chkstk`, compiler_rt libcall ABI (`i128` division
  by reference, `f128` in `xmm`)**: below AIR. The model makes no binary claim (TRU-03); the
  native differential test is the evidence that the lowering agrees. An `extern` call resolves to
  an `export fn` only when both declare the same calling convention (`resolveExternsCollect`),
  which is `x86_64_win` on both sides here.
- **Error sets and unions** have the target-independent layout of the type table (16-bit errors by
  default); nothing differs.
- **`-gnu` vs `-msvc` compiler_rt**: with `-gnu` and without `-lc`, Zig links its own compiler_rt
  for every libcall (`f80`/`f128` routines, `__udivti3`); with `-lc`, MinGW-w64's CRT also starts
  the process (`CRT_fp10.o`: `fninit`). With `-msvc`, `f80` is soft float (compiler_rt
  `__divxf3`, …), `long double` libm calls are `double` ones, and the UCRT supplies `fmod` and the
  transcendentals when libc is linked. The MSVC row therefore needs the aarch64 soft-`f80`
  float rules (`FloatRules`), a `longDoubleBits = 64` row and its own probe record (Phase 4).

### x87 precision control

The model computes `f80` arithmetic with a 64-bit significand, as the x87 does with its
precision control (bits 8-9 of the control word) at "extended". Windows does not keep that state
on every thread, and the probe shows it (all four versions, recorded under Wine; the CI row
must confirm it natively):

| Zig | Main thread (`x87 main`) | Thread from `std.Thread.spawn` (`x87 thread`) |
| --- | --- | --- |
| 0.15.2, 0.16.0, 0.17.0 | `0x037f`: 64 bits (`WinStartup`: `fninit` for the `gnu` ABI) | `0x027f`: **53 bits** |
| 0.14.1 | `0x027f`: **53 bits** (no `fninit`); 64 bits with `-lc` (MinGW `_fpreset`) | `0x027f`: 53 bits |
| any, `-msvc` | `0x027f`, but `f80` is soft float | same |

At 53 bits, `f80` `1/3` is `3ffdaaaaaaaaaaaaa800` instead of `…aaab`, and every op that computes
through `fadd`/`fsub`/`fmul`/`fdiv`/`fsqrt` rounds differently, including compiler_rt's `f80`
routines (`fmal`: the probe's `mulAdd(1+e,1-e,-1)` row). The translator cannot know which thread
runs a function, so on a target with `Target.x87ThreadPrecision` (x86_64-windows) the checker
rejects (`CheckCtx.checkX87Precision`) every `f80` arithmetic, division, `@sqrt`, rounding, libm,
`@mulAdd`, reduction and `f80`-integer conversion, unless `--assume-x87-extended` states that the
code runs with extended precision. The admission is recorded in the generated header
(`"admission": "x87-extended"`), only on such a target. `neg`, `abs`, comparisons, `@min`/`@max`,
bit casts and conversions between float types are admitted: they do not use the precision
control. The `floatops` example's Windows translation passes the admission
(`examples/floatops/translate-windows.args`).

The long-term fix is in the OS layer: when Windows threads are translated (Phase 3), the model
gets the per-thread precision control as thread state, set by the startup code and by
`NtCreateThreadEx`, and the `f80` ops read it, so no admission is needed.

## Goldens

`scripts/check.sh` with `AIR2LEAN_TARGET=x86_64-windows-gnu` exports each example for the target
(`-target x86_64-windows-gnu -mcpu=baseline`, cross-compiled from any host), compares the AIR
with the golden stack (shared, version, then `air-windows/` and `air-windows-x86_64/`), translates
it (with `examples/<ex>/translate-windows.args`) and compares the translation with
`Gen-windows-x86_64.lean`, `Gen-windows.lean`, the version's `Gen.lean` or `Proofs/<Ex>/Gen.lean`.

For the nine pure examples (`basic`, `recursion`, `options`, `floatops`, `floats`, `errors`,
`variants`, `pointers`, `layout`) and all four Zig versions, the Windows AIR is the x86_64-linux
AIR, except that 0.17.0 `floatops` needs Linux's two `f80`-aligned files
(`tests/golden/0.17.0/floatops/air-windows/`; the version's shared files are aarch64's 8-aligned
`f80`), and every translation equals the committed one: no `Gen-windows.lean` exists. `c_long`
does not occur in them; the windows-target gate covers it.

Zig 0.14.1 and 0.15.2 queue a DLL import library for every `extern "kernel32"`/`"ntdll"` function of
a Windows compilation, also without a binary, and the AIR-only compiler (no LLVM) cannot build one;
their `hook.patch` makes `addLinkLib` skip it when there is no binary ([zig-patch/README.md](../zig-patch/README.md)).

`tests/roadmap/windows-target/check.sh` translates recorded 0.17.0 Windows exports of small
sources and checks each rule: pure code with a 32-bit `c_long` and an `f80` `neg` is accepted; an
`f80` division is rejected, and accepted with `--assume-x87-extended` (header admission); a
`threadlocal` global, a `std.Thread.spawn` and a `kernel32` call are rejected with their reasons.

## std paths that change

The translated std code is the target's own: the exporter analyses std for the target, so the
Windows branches are what the translator sees. The paths below are the ones Phases 2-3 translate;
each ends in an ntdll/kernel32 call, which is an `extern` function and stays unbound (rejected)
until its premise is approved.

| std path | 0.14.1 | 0.15.2 | 0.16.0 / 0.17.0 |
| --- | --- | --- | --- |
| `heap.PageAllocator` | `kernel32.VirtualAlloc`/`VirtualFree` | `ntdll.NtAllocateVirtualMemory` (reserve placeholders, commit), `NtFreeVirtualMemory` | same as 0.15.2 (`.RESERVE_PLACEHOLDER`, `.PRESERVE_PLACEHOLDER`) |
| `Thread.Mutex` | `SRWLOCK` (`kernel32.AcquireSRWLockExclusive`, `TryAcquire…`, `Release…`) | same | `Io.Mutex` over the `Io` futex |
| `Thread.Futex` / `Io.futexWait`/`Wake` | `ntdll.RtlWaitOnAddress`, `RtlWakeAddressSingle`/`All` | same | `Io.Threaded`: a userland address table over `ntdll.NtWaitForAlertByThreadId` / `NtAlertThreadByThreadId` (thread parking; `RtlWaitOnAddress` is built the same way) |
| `Thread.spawn` / `join` | `kernel32.CreateThread`, `WaitForSingleObject` | same | `ntdll.NtCreateThreadEx`, `NtWaitForSingleObject` |
| `Thread.yield` | `kernel32.SwitchToThread` | same | `ntdll.NtYieldExecution` |
| `Io.Threaded` (0.16.0+) | — | — | Windows backend: thread pool on `NtCreateThreadEx`, futex as above, files via `NtCreateFile`/`NtReadFile`/`NtWriteFile`, clocks via `RtlQueryPerformanceCounter` |
| Clocks | `QueryPerformanceCounter` | same | `RtlQueryPerformanceCounter`, `RtlGetSystemTimePrecise` |

Phase 1 rejects all of it: the std thread, futex, `Io` and timer **models** (`ThreadFn`) need the
target's OS layer (`Target.osLayer = false` for Windows; diagnostic "the std model of … is outside
the x86_64-windows model"), `threadlocal` globals are rejected with the same reason, and a call
of an ntdll/kernel32 function is an unbound extern ("the OS primitives of x86_64-windows have no
model yet"). The allocator interface models (`mem.Allocator.*`, a caller-supplied allocator,
ALC-09) are OS-independent and stay admitted.

## Premises (proposed; for approval before use in proofs)

None of these is in [premises.md](premises.md) or `assurance/premises.json` yet: no theorem uses
a Windows translation, and the catalog admits no unused ID. Each is stated in the style of OSM-01
(trusted OS behaviour below a translated std boundary) and becomes a catalog entry with its
derivation rule when its phase starts.

| ID (proposed) | Kind | Statement | Phase |
| --- | --- | --- | --- |
| MTH-06 | environment | Every `f80` op of the translation runs with the x87 precision control at extended precision (64-bit significand): the main thread of a Zig ≥ 0.15.2 x86_64-windows-gnu program (`WinStartup`'s `fninit`) or of a program linked with the MinGW CRT, never a thread that `CreateThread`/`NtCreateThreadEx` made. Derived from the header admission `x87-extended`. | 1 (admission exists, premise pending) |
| OSW-01 | trusted | `ntdll.NtAllocateVirtualMemory`/`NtFreeVirtualMemory` (0.15.2+; `kernel32.VirtualAlloc`/`VirtualFree` on 0.14.1) with the arguments `heap.PageAllocator` passes: `MEM_RESERVE` (with or without `MEM_RESERVE_PLACEHOLDER`) then `MEM_COMMIT` of a page-aligned range returns zeroed pages at the placement's 64 KiB-aligned address (allocation granularity) or fails with no change; `MEM_RELEASE` of a whole region (or a placeholder split with `MEM_PRESERVE_PLACEHOLDER`) ends it; any other combination is outside the model. Page size 4 KiB, granularity 64 KiB, user space below `0x7FFF_FFFF_0000`. | 2 |
| OSW-02 | trusted | Thread creation and join: `NtCreateThreadEx` (0.16.0+) / `CreateThread` (0.14.1, 0.15.2) starts a model thread running the given start routine with its argument, or fails with no thread; `NtWaitForSingleObject`/`WaitForSingleObject` on its handle returns after the thread has ended and its writes are visible (synchronizes-with); `NtClose` releases the handle. The new thread starts with x87 control word `0x027f` and MXCSR `0x1f80`. | 3 |
| OSW-03 | trusted | Thread parking (0.16.0+): `NtWaitForAlertByThreadId(addr, timeout)` returns after an alert for this thread, spuriously, or at the timeout; `NtAlertThreadByThreadId(tid)` wakes it or makes its next wait return at once (one pending alert). With the translated `Io.Threaded` address table on top, this yields the futex contract of THR-05. | 3 |
| OSW-04 | trusted | Address waits (0.14.1, 0.15.2): `RtlWaitOnAddress(addr, cmp, size, timeout)` returns at once if `*addr != *cmp`, else after a `RtlWakeAddressSingle`/`All` on `addr`, spuriously, or at the timeout: the futex contract of THR-05 for a 4-byte cell. | 3 |
| OSW-05 | trusted | `SRWLOCK` (0.14.1, 0.15.2 `Thread.Mutex`): `AcquireSRWLockExclusive` blocks until the lock is free and takes it (acquire), `TryAcquireSRWLockExclusive` takes it iff free, `ReleaseSRWLockExclusive` by the owner frees it (release); release by a non-owner is `.illegal`. The analogue of THR-06 (Darwin `os_unfair_lock`). | 3 |
| OSW-06 | trusted | `NtYieldExecution`/`SwitchToThread`: a scheduler opportunity with no other effect (THR-07). | 3 |
| OSW-07 | trusted | Clocks: `RtlQueryPerformanceCounter` is monotonic, `RtlQueryPerformanceFrequency` constant and positive, `RtlGetSystemTimePrecise` a wall clock (the ENV-02 contract). | 3 |
| OSW-08 | trusted | PE thread-local storage: each thread's instance of a `threadlocal` variable is initialized from the `.tls` template before the thread runs Zig code, and is distinct per thread (the model's TLS semantics, `docs/generated-code.md` §Thread-local storage). | 3 |

## Native evidence

The rule ([CLAUDE.md](../CLAUDE.md)): local first, CI confirms; Wine is never OS evidence.

| Option | What it gives | Cost | Use |
| --- | --- | --- | --- |
| **Wine 10 in a `linux/amd64` container (Rosetta)**: `Dockerfile.wine`, `scripts/wine-run.sh` | Runs the real x86_64 PE binaries' computations: layouts, integer and float results, the x87 rows (Wine starts threads at `0x027f` like Windows), the diff harness | local, ~0.3 s per process start; the 9 pure examples' harnesses in minutes | **Local iteration**, pure computations only, labelled (`"native": false, "runner": …`) |
| **GitHub `windows-2025` runner** | Native Windows: everything, including OS behaviour (threads, futex, `NtAllocateVirtualMemory`) | CI minutes at 2× the Linux rate; the private repo's concurrent-job limit is shared with all other rows | **Authoritative confirmation**: one row per PR (T04 probe `check` natively for each version + the diff test of the pure examples) |
| Local Windows VM (UTM/Parallels, Windows 11 on Arm with x64 emulation, or an x86_64 host) | Native Windows locally; on Apple silicon x86_64 runs under Prism emulation, aarch64-windows natively | license and setup; Prism is an emulator too | Later, when available: the design keeps the runner pluggable (`AIR2LEAN_DIFF_RUNNER`, `aarch64-abi.py --runner`), so a VM is one more runner (`ssh` + `scp`) |

**Recommendation.** Iterate locally under Wine for pure computations (this phase); make the
GitHub Windows row the authoritative evidence for every Windows claim, OS behaviour included,
and the only source of OS evidence until a local VM exists. Phase 1 adds no CI row: the 2×
minute rate and the shared concurrency limit cost more than one row of confirmation is worth
before the OS layer exists; the row is ready to add (`scripts/aarch64-abi.py check --target
x86_64-windows-gnu` and `scripts/check.sh` with the Windows harness need no Wine there) and is
the first item of Phase 2.

What Wine showed, all to be confirmed natively: the four probe records (§x87 precision control;
`tests/roadmap/aarch64-abi/expected/<version>/x86_64-windows-gnu-ReleaseSafe.txt`), and the
`basic` harness output identical to the native aarch64-macos run of the same harness.

### Running it

```sh
docker build --platform linux/amd64 -f Dockerfile.wine -t air2lean-wine:amd64 .
# T04 probe (local, labelled; natively on Windows drop --runner):
python3 scripts/aarch64-abi.py check --zig ZIG --target x86_64-windows-gnu --runner scripts/wine-run.sh
lake env lean --run tests/roadmap/aarch64-abi/Model.lean x86_64-windows-gnu \
  tests/roadmap/aarch64-abi/expected/0.17.0/x86_64-windows-gnu-ReleaseSafe.txt
# Golden AIR, translation, Lean build and the Wine differential of the pure examples:
AIR2LEAN_TARGET=x86_64-windows-gnu AIR2LEAN_ZIG_VERSION=0.17.0 AIR2LEAN_ZIG=STOCK_ZIG \
  AIR2LEAN_DIFF_RUNNER=scripts/wine-run.sh \
  AIR2LEAN_EXAMPLES="basic recursion options floatops floats errors variants pointers layout" \
  scripts/check.sh
```

### The harness on Windows

Windows has no `fork`. `tests/diff/common.zig` runs the inputs of one function in a case child (the
harness itself, `--air2lean-child <ex>/<fn> <line>`), which writes each case's bytes as a forked
POSIX child does (`C`, `R`, the payload; `P<kind>` from the panic handler) on its standard output,
each case ended by `0x1e`. A case that ends the child (a safety panic, a CPU fault: its exception
code maps to the POSIX fault name, `compat.windowsFault`) is decoded with the child's exit code,
and a new child continues at the next input; a case without a record within the deadline is
killed and reported as a harness failure. One decoder (`decodeChild`) serves both OSes. The cases
of one child share a process, which is sound for functions without state that outlives a call:
the nine Windows examples have no mutable globals (an example with them needs one child per case,
the same mechanism with the start line advanced after every case).

## Phases

Estimates are agent-days of one Opus agent, local runs included.

| Phase | Content | Estimate |
| --- | --- | --- |
| 1 (this) | Design; `x86_64-windows-gnu` row; fail-closed rules; cross-target `check.sh`; Windows harness runner; T04 probe and `Model.lean` table; Wine evidence | 3 |
| 2 | CI `windows` row (native T04 + pure-example diff); `lanePtrProbe` after the native vector rows; then the allocator layer: translate `heap.PageAllocator`'s Windows path to OSW-01 (`ZigLean/Os/WinVirtualMemory.lean`, the analogue of OSM-01) and its `AllocSpec` proof | 5-8 |
| 3 | Threads and synchronization: translate `Thread.spawn`/`join`, `Io.Threaded`'s Windows futex and thread pool (0.16.0+), `SRWLOCK`/`RtlWaitOnAddress` (0.14.1/0.15.2) down to OSW-02…08; per-thread x87 state (replaces MTH-06); `threads`/`sync`/`iogroup` examples on Windows | 10-15 |
| 4 | `x86_64-windows-msvc`: `longDoubleBits = 64`, soft-`f80` float rules, 0.17.0 `f80` alignment 8, UCRT libm (rejected without `--assume-no-libc`), own probe record | 3-4 |
| 5 | `aarch64-windows` (gnu, then msvc): `c_longdouble` `f64`, aarch64 float rules, 0.17.0 `f80`/`f128` alignment 8, LSE atomics (`cx16` analogue), native evidence on a Windows-on-Arm runner or VM | 4-6 |
