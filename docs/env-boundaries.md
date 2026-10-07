# Environment-operation boundary (E03)

`ZigLean/Env.lean` (`Zig.Env`) is an opt-in, selected interface for environment operations:
clocks, handle-based reads and writes with partial success, enumerated errors, and cleanup.
It is outside the runtime umbrella `ZigLean.lean`. The translator emits no call to it.
Translated Zig code cannot use it yet. It is a contract surface for hand-written clients
and for future model bindings.

Environment-dependent behavior is parameterized. `Zig.Env.Ops σ` gives every result as a
function of an arbitrary state `σ`. The state may contain an oracle stream, so the model
fixes no host behavior. A client learns only what `Zig.Env.Contract ops errors` states. Each
theorem quantifies over every `σ`, every `Ops` and every allowed error list that satisfies
the contract.

```sh
lake build ZigLean.Env
lake env lean tests/roadmap/env-boundaries/WriteAll.lean
python3 -B tests/roadmap/env-boundaries/test_env_boundaries.py
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
  returned error is in it. These are model names. They are not mapped to errno or Zig
  error-set values.
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

## Premises

- [ENV-01](premises.md#env-01): the selected handle/read/write/close contract.
- [ENV-02](premises.md#env-02): distinct monotonic and wall clock observations.

`scripts/premises.py` derives both IDs for the client theorems. It derives ENV-01 from the
`ZigLean.Env` module mapping and ENV-02 from the `monotonicNow`/`wallNow` tokens. Foreign
calls that translated code actually reaches still go through the model registry
([external-models.md](external-models.md), EXT-01/EXT-02). Translated clocks and timed
waits remain TMR-01/TMR-02 ([deadline-runtime.md](deadline-runtime.md)).

## Not claimed

These targets are outside the boundary. No theorem covers them without its own explicit,
stated contract:

- **CPython.** No CPython C-API, GIL, reference-counting, buffer-protocol or exception
  behavior is modelled. No Python/native boundary contract used by a production client is
  shipped yet.
- **Browser host imports.** No WASM host import, JavaScript glue, browser clock, or
  WASI/browser I/O behavior is modelled. No WASM correspondence is claimed (T05).
- **The operating system.** No correspondence is claimed to POSIX/Windows file
  descriptors, syscalls, errno values, signals/`EINTR`, blocking or non-blocking modes,
  descriptor reuse after close, durability, or OS clocks (`CLOCK_MONOTONIC`,
  `CLOCK_REALTIME`, suspend behavior).
- **Translated Zig I/O.** `std.Io`, `std.fs`, `std.posix` and `std.time` calls in
  translated code are not routed through `Zig.Env`. Unknown calls still fail translation.
- **Concurrency.** The interface is sequential. No shared handles across threads,
  cancellation or reentrancy are covered.
