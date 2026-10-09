# Environment-operation boundary (E03)

`ZigLean/Env.lean` (`Zig.Env`) is a selected interface for environment operations: clocks,
handle-based reads and writes with partial success, enumerated errors, and cleanup.
`Zig.Mem` carries one installed environment (`Mem.host : Zig.Env.Host`: operations over request
histories, the current state and an event log). Its default has no open handle, so programs
that never reach an I/O primitive are unaffected. The translator emits no built-in call to it.
Translated std I/O reaches it only through three bound Linux primitives
([Bound primitives](#bound-primitives)); everything above them is translated from AIR.

Environment-dependent behavior is parameterized. `Zig.Env.Ops σ` gives every result as a
function of an arbitrary state `σ`. The state may contain an oracle stream, so the model
fixes no host behavior. A client learns only what `Zig.Env.Contract ops errors` states. Each
theorem quantifies over every `σ`, every `Ops` and every allowed error list that satisfies
the contract. The installed host uses request histories as its state; `Ops.replay` installs
any `ops : Ops σ` with an initial state, and `Contract.replay` transfers the contract, so the
translated-code theorems cover every contracted `Ops σ` (`writeAllClose_spec_replay`).

```sh
lake build ZigLean ZigLean.Env.Linux air2lean
lake env lean tests/roadmap/env-boundaries/WriteAll.lean
python3 -B tests/roadmap/env-boundaries/test_env_boundaries.py
tests/roadmap/env-boundaries/check.sh      # translate std I/O, elaborate, check StdIo.lean
tests/roadmap/env-boundaries/export.sh     # fresh AIR with the patched 0.15.2/0.16.0 compilers
```

## Operations

The checker `tests/roadmap/env-boundaries/test_env_boundaries.py` requires one row per
`Ops` field, and requires that row to name a premise defined in [premises.md](premises.md).

| Operation | Contract fields | Premise |
|---|---|---|
| `monotonicNow` | `readMonotone`, `writeMonotone`, `closeMonotone` | ENV-02 |
| `wallNow` | none: no ordering, may decrease | ENV-02 |
| `isOpen` | `readFrame`, `writeFrame`, `closeReleases`, `closeFrame` | ENV-01 |
| `read` | `readBound`, `readError`, `readFrame`, `readMonotone` | ENV-01 |
| `write` | `writeProgress`, `writeError`, `writeFrame`, `writeMonotone` | ENV-01 |
| `close` | `closeReleases`, `closeFrame`, `closeMonotone` | ENV-01 |

Every contract clause covers an open handle only:

- **Partial write.** A write of a nonempty buffer returns either `.ok n` with
  `0 < n ≤ len` (the first `n` bytes were accepted) or `.error e`.
- **Reads.** `.ok bytes` has at most the requested length. `.ok []` for a positive request
  is end of input.
- **Errors.** `IoError` enumerates `wouldBlock`, `brokenPipe`, `noSpaceLeft`, `accessDenied`,
  `inputOutput` and `connectionReset`. A contract selects the allowed subset, and every
  returned error is in it. In `Zig.Env` these are model names; ENV-03 maps them to Linux
  errno values for the bound primitives ([Bound primitives](#bound-primitives)), and the
  translated std code maps those to its Zig error names.
- **Handles.** Reads and writes leave the set of open handles unchanged. `close` releases
  its handle and leaves other handles unchanged.
- **Clocks.** The monotonic and wall clocks are distinct observations in nanoseconds. No
  operation moves the monotonic clock backwards. The wall clock has no contract.
  `scripted_wall_runs_backwards` shows a contract instance whose wall clock decreases.
  This clock is separate from the scheduler-facing `Zig.Time.AwakeEnvironment` (TMR-02).
  No bridge between them is proved.

Behavior on a closed handle is unconstrained. The client wrappers `writeAll` and
`closeOnce` instead return `Fault.closedHandle` before calling the environment. A write
count outside the contract range is `Fault.contractBreach`: Zig's `writeAll` would loop
forever on 0 or slice out of bounds above the length.

## Client

`tests/roadmap/env-boundaries/WriteAll.lean` proves `writeAllClose_spec` from the contract
alone. `writeAllClose` retries partial writes, then closes the handle. From an open handle
it never faults, and:

- it either writes the whole buffer (the `wrote` events concatenate to it), or returns the
  first error, which is in the allowed list. In the error case, the bytes before the error
  form a proper prefix, and the `failed` event is the only non-write event before cleanup.
- on both paths, the log ends with exactly one `closed h`, `h` is no longer open, and
  other handles are unchanged.
- the monotonic clock does not decrease.

`scripted_contract` shows the contract is satisfiable. It uses an explicit result script
whose wall clock runs backwards. `demo_partial`, `demo_error` and `demo_closed` evaluate
the client on that oracle. They cover retried partial writes, a stop at the first error
with cleanup, and a fault on a closed handle.

## Bound primitives

The trusted base of translated std I/O is the raw Linux syscall wrappers that Zig's std calls on
`x86_64-linux` without libc (`std.posix.system` is `std.os.linux`). Each is one `syscall`
instruction, which the translator rejects (asm `memory` clobber, M21). A project binds them
through the external model registry ([external-models.md](external-models.md), E01) to the models
in `ZigLean/Env/Linux.lean`. `tests/roadmap/env-boundaries/fill_registry.py` fills a
`--model-registry-template` with these entries and nothing else; every binding is
`trust: proved`, and its evidence is checked when the generated file elaborates.

| Primitive | Model | Contract / evidence | Footprint | Safety errors | Premise |
|---|---|---|---|---|---|
| `os.linux.write` | `Zig.Env.Linux.write` | `writeContract` / `writeEvidence` | reads `[1]` | `illegal`, `unspecified` | ENV-03 |
| `os.linux.read` | `Zig.Env.Linux.read` | `readContract` / `readEvidence` | writes `[1]` | `illegal` | ENV-03 |
| `os.linux.close` | `Zig.Env.Linux.close` | `closeContract` / `closeEvidence` | none | `illegal` | ENV-03 |

Each model returns the Linux raw convention: a `usize` byte count, or `-errno` for a modelled
error (`wouldBlock` EAGAIN 11, `brokenPipe` EPIPE 32, `noSpaceLeft` ENOSPC 28, `accessDenied`
EACCES 13, `inputOutput` EIO 5, `connectionReset` ECONNRESET 104). A zero count returns 0
without a request. `write` reads its `count` source bytes through the checked memory model
(an undefined byte is `.unspecified`) and offers them to `Ops.write`. `read` asks `Ops.read`
for at most `count` bytes and stores them through the checked memory model. `close` calls
`Ops.close`. Each request appends its `wrote`, `received`, `failed` or `closed` event to the host
log. A descriptor that is negative or not open is `.illegal`. This is stricter than the
kernel, which returns `EBADF` or acts on a reused descriptor.

These are the only std names bound here, and they are OS primitives. No std function above
them has a model. The registry matches them by their AIR name. Two pending changes affect
this. A project registry may bind std names only from the OS-primitive allowlist
(`codex/fix-model-premises`), and that allowlist contains these three. Module-qualified
identity (`codex/fix-module-identity`) will qualify the names in the template, so
`fill_registry.py` must then match the std module identity. On libc targets (macOS),
`posix.system` is `std.c`, whose `write`/`read`/`close` are `extern "c"` functions. Binding
them needs the extern-call registry support (`codex/extern-calls`). Until then, no libc
target is covered.

## Translated std I/O

`tests/roadmap/env-boundaries/` holds two sources and their committed AIR closures
(`air/std15`, `air/std16`). `export.sh` re-exports the AIR with the patched compilers and
compares it with the committed AIR (`--update` rewrites it). `refresh-air.py` keeps the
direct-call closure of the roots without the three bound primitives and the `syscallN`
wrappers below them. `translate.sh` translates the closures with the filled registry and
compares the output with `expected/` and `registry/`. `check.sh` then elaborates the output
and checks `StdIo.lean`.

- **Zig 0.15.2** (`std_io15.zig`): `writeAllClose` (`defer file.close(); try
  file.writeAll(bytes)`) and `readAllClose`. The translated std code is `fs.File.writeAll`,
  `write`, `close`, `readAll` and `read`, plus `posix.write`, `read`, `close`, `errno` and
  `unexpectedErrno`.
- **Zig 0.16.0** (`std_io16.zig`): `readClose` (`defer std.Io.Threaded.closeFd(fd); return
  posix.read(fd, buf)`). The translated std code is `posix.read`, `os.linux.errno`,
  `Io.Threaded.closeFd` and `recoverableOsBugDetected`.

`StdIo.lean` proves these theorems on the generated code, from ENV-01 and the ENV-03 models
only. No std function has a hand-written model.

- `EnvStd15.Proofs.writeAllClose_spec`: on an open descriptor whose buffer bytes are in
  memory, in a single-threaded memory, the generated code never faults, and leaves memory
  blocks unchanged. It either writes the whole buffer (the `wrote` events concatenate to it),
  or returns the first error under std's Zig error name after a proper prefix. On both paths
  the handle is closed exactly once and last, is then no longer open, and other handles are
  unchanged. Partial writes are retried by the translated `fs.File.writeAll` loop. Each
  `write` offers at most `0x7ffff000` bytes (`posix.write`'s cap).
  `writeAllClose_spec_replay` restates it for any `Ops σ` through `Ops.replay`.
- `EnvStd16.Proofs.readClose_spec`: on an open descriptor and a nonempty writable buffer, the
  result is the received byte count, with those bytes now in the buffer, or the error's name
  in 0.16.0 `posix.read`'s switch. The handle is closed exactly once and last.
- Two `#guard` runs execute the generated `writeAllClose` against a scripted host. In the
  first, five bytes are accepted two at a time. In the second, a `brokenPipe` after the first
  write stops the loop, and the handle is still closed once.

## Zig 0.16.0 `std.Io`: what is rejected

The 0.16.0 high-level path is `Io.File.writeStreamingAll` → `Io.operate` (an `Io` vtable call)
→ `Io.Threaded.operate` → `fileWriteStreaming` / `fileReadStreamingPosix` → `Syscall.start` /
`finish` / `checkCancel` → `posix.system.writev` / `readv`. Buffered `Io.Writer` / `Io.Reader`
go through `File.Writer.drain` and `File.Reader.stream`, and `Io.File.close` goes through
`io.vtable.fileClose`. With an export of that path (probe: `writeStreamingAll`, a buffered
writer, a buffered reader, stdout through `Io.Threaded.global_single_threaded`, and
`Dir.createFile` / `openFile`), the translator reports these rejections:

- `Io.Threaded.Syscall.start`: `runtime_nav_ptr` to the `threadlocal` `Thread.current`
  (EXPORTER_UNSUPPORTED: TLS identity and lifetime are outside the model).
- `Syscall.finish` / `checkCancel`: a `noreturn` value in memory (the unreachable switch arms).
- `fileWriteStreaming`: `SinglyLinkedList.Node` is exported without fields (exporter gap, the
  same gap as the allocator P0 work). `Syscall.fail__anon_*`: AIR arguments do not match the
  non-OPV parameters.
- `Io.operate`, `Io.File.writeStreaming`, `Io.File.readStreaming`: the `Io.Operation` union
  (`Io.net.IncomingMessage` is unsupported), a `tuple` value in memory, and an opaque bitcast
  of error-union storage. The shared type `Io.Operation` is also inconsistent between
  functions.
- `Io.Writer.writeAll` and `Io.Reader.*`: the `Io.Writer.VTable` / `Io.Reader.VTable` types are
  unsupported. `File.Writer.drain`, `sendFile`, `File.Reader.stream`, `readVec` and `discard`
  have unresolved pointer-cast provenance (`@fieldParentPtr` from the interface).
  `File.Writer.initInterface` and `File.Reader.initInterface` have an unresolved global alias.
  `Io.Writer` / `Io.Reader` are also inconsistent shared types.
- `Threaded.io()` places every vtable function in a global initializer, so stdout through
  `global_single_threaded` pulls in about 640 functions. Diagnostics inspect at most 256
  input files.
- `os.linux.x86_64.syscall1` / `syscall3`: the asm `memory` clobber (M21). This is the
  intended boundary.

`writev` / `readv` are not bound yet. No translated path reaches them until `Syscall.*` and
the `Io` vtable dispatch translate. `posix.read` and `closeFd` call the bound
`read` / `close` directly.

## Premises

- [ENV-01](premises.md#env-01): the selected handle/read/write/close contract.
- [ENV-02](premises.md#env-02): distinct monotonic and wall clock observations.
- [ENV-03](premises.md#env-03): the Linux raw `read`/`write`/`close` behave as the bound
  models.

`scripts/premises.py` derives ENV-01 from the `ZigLean.Env` module mapping, ENV-01 and ENV-03
from `ZigLean.Env.Linux`, and ENV-02 from the `monotonicNow`/`wallNow` tokens. The generated
modules add TRU-02 and their profile premise. Translated clocks and timed waits remain
TMR-01/TMR-02 ([deadline-runtime.md](deadline-runtime.md)).

## Not claimed

These targets are outside the boundary. No theorem covers them without its own explicit,
stated contract:

- **CPython.** No CPython C-API, GIL, reference-counting, buffer-protocol or exception
  behavior is modelled. No Python/native boundary contract used by a production client is
  shipped yet.
- **Browser host imports.** No WASM host import, JavaScript glue, browser clock, or
  WASI/browser I/O behavior is modelled. No WASM correspondence is claimed (T05).
- **The operating system.** Beyond ENV-03's three Linux primitives, no correspondence is
  claimed. That excludes `writev`/`readv`, `openat`, libc (macOS `std.c`), Windows, errno values
  outside the six modelled ones, signals/`EINTR`, blocking or non-blocking modes, descriptor
  reuse after close, durability, and OS clocks (`CLOCK_MONOTONIC`, `CLOCK_REALTIME`, suspend
  behavior). ENV-03 itself is assumed, not verified against a kernel.
- **Translated Zig I/O.** Only the paths listed in [Translated std I/O](#translated-std-io)
  are translated and proved. Zig 0.16.0 `std.Io` (vtable dispatch, `Threaded` cancellation,
  buffered `Io.Writer`/`Io.Reader`, `Dir`) is rejected as listed above. Other unknown calls
  still fail translation.
- **Concurrency.** The interface is sequential. The proofs assume a single-threaded memory.
  No shared handles across threads, cancellation or reentrancy are covered.
