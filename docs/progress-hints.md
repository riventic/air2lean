# Yield and spin hints (C03)

`std.Thread.yield()` is a modeled zero-argument call returning
`error{SystemCannotYield}!void` in Zig 0.14.1, 0.15.2 and the qualified 0.16.0
compiler snapshot. Generated code calls `Zig.threadYieldC`. The environment can
return success or `error.SystemCannotYield`; the latter is an ordinary Zig error
value, so `try`, `catch`, and error cleanup retain their source meaning. It is
not a `Zig.Error` panic. No syscall availability or eventual success is assumed.
The checker rejects a non-void payload, a result error set excluding
`SystemCannotYield`, runtime arguments, or a `noreturn` callee annotation.

The supported source spin API is `std.atomic.spinLoopHint()`, an inline function.
`std.Thread.spinLoopHint` is not a declaration in these versions. Its historical
model boundary name remains recognized, together with `atomic.spinLoopHint`,
with zero runtime arguments and a void result. Real source normally exports
assembly directly: exact volatile `pause` and `isb`, with a void result and no
inputs, outputs or clobbers, become `Zig.spinLoopHintC`. Identical user-written
assembly gets the same instruction semantics. Other assembly retains the
existing opaque model and restrictions; this change does not interpret generic
assembly as a hint or infer source provenance from a string.

These exact strings were audited against the three compiler libraries:

| Exported instruction | Source targets | Qualification |
| --- | --- | --- |
| `pause` | x86/x86_64; RISC-V with Zihintpause | Additional scheduler opportunity; no fence |
| `isb` | aarch64/aarch64_be | Additional scheduler opportunity; no data-memory acquire/release edge |
| other instructions, or no instruction | ARM, PowerPC, Hexagon, other profiles | No new spin-specific semantics; existing translation rules apply |

The current AIR format carries little-endian qualification but not a complete
CPU/OS profile. Recognition therefore rests on the trusted compiler/exporter
premise that the instruction is valid for the selected source target. It does
not qualify native execution on every architecture in this table. Big-endian
exports remain rejected by the existing parser. Windows 0.14.1/0.15.2 yield
always succeeds; conservatively keeping `SystemCannotYield` adds an outcome for
those targets. The 0.16.0 Windows implementation can return that error. POSIX
implementations map unsuccessful `sched_yield` calls to the same error in all
three versions. This model avoids narrowing those real outcomes.

The source audit used these std-library SHA-256 values, independent of the
compiler execution qualification:

| Zig library | `std/Thread.zig` | `std/atomic.zig` |
| --- | --- | --- |
| 0.14.1 | `6cc77eb377153ac08394e7422984bbb684c1ba7b0118dee33c9be50b6184f12d` | `5765a0e92346ae81cae3034d1d58ba4fc2c3e800fb59f80e87b7694c9b810f72` |
| 0.15.2 | `d5c5453d21967d531575ae2809aeda8848468a9d202aad4c4d2596e746a46f8a` | `8421886c8789d9cf7619b40f81ea9e24f7af8c31beaf8a93ba610fcc21bba269` |
| 0.16.0 snapshot | `14260c03063b52821c5369fc09ec32456062b0366a8e1510c0f853a204ff7eeb` | `1f53df09898b7c88f8ad3ffff60b22e5656c0ea1a7c84663c6a0b8466c139c22` |

Both hints stop at an existing scheduler operation. Any ready thread may run
next, including the current thread. Hints do not change memory bytes, race
footprints, vector clocks, atomic read views, or the futex queue themselves.
Other threads can change shared memory before the hint resumes. The scheduler
assumes no fairness, minimum delay, time passage, or guaranteed handoff.

`ZigLean/Conc/Progress.lean` supplies invariant-based weakest-precondition rules
for every permitted interference state and both yield returns. Existing
`Conc.Proto.run_safe` and `run_sound` lift such rules to arbitrary schedules.
Those are safety and partial-correctness claims: no-result executions remain
permitted. Depth zero and exhausted scheduler fuel give `none`; an idle loop
can continue indefinitely or starve a worker. Eventual completion needs a
separate fairness/environment contract and proof.

`tests/roadmap/progress/progress.zig` covers actual source hints, a yield error
handler and an atomic idle loop. `Runtime.lean` exercises both yield returns,
same-thread continuation, another-thread interference, unbounded idle-loop
no-result behavior and absence of hint-created access/clock edges.
`Pipeline.lean` checks modeled signatures, classifications, negative boundaries,
and writes generated Lean for separate elaboration. Assertions detect mutations
that make a hint pure, force yield success, or require a different thread to run.

Reproduce qualification from the repository root (select each patched compiler
explicitly; keep exports separate by version/target):

```sh
lake build ZigLean Air2Lean air2lean
lake env lean --run tests/roadmap/progress/Runtime.lean
lake env lean --run tests/roadmap/progress/Pipeline.lean /tmp/ProgressPipeline.lean
lake env lean /tmp/ProgressPipeline.lean
progress_air=$(mktemp -d /tmp/progress-air.XXXXXX)
ZIG_AIR_JSON_DIR="$progress_air" ZIG_AIR_JSON_FILTER='progress.' "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing tests/roadmap/progress/progress.zig
lake exe air2lean "$progress_air" -o /tmp/ProgressSource.lean --namespace ProgressSource --prefix progress.
lake env lean /tmp/ProgressSource.lean
```

Keep the fresh AIR directory, generated Lean, command logs and compiler/source
hashes with the qualification record; do not reuse a directory containing exports
from a previous version or target.

The source semantics audit is separate from successful execution of these
commands. Compiler runs, kernel checks and exported fixture evidence must be
recorded for the exact reviewed revision; this document alone is not a fresh
validation result. The compiler/exporter correspondence remains trusted.
