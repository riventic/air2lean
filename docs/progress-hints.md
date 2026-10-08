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
assembly gets the same instruction semantics. Both are entries of the reviewed asm
allowlist (`Air2Lean/AsmAllowlist.lean`, L13): `pause` for x86_64 and `isb` for aarch64. Other
assembly must be on that allowlist as an input-determined opaque or a declared device event, else
it is `ASM_VOLATILE_EFFECT` ([volatile-effects.md](volatile-effects.md#inline-asm)). This change
does not interpret generic assembly as a hint or infer source provenance from a string.

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

`ZigLean/Conc/Total.lean` separates guaranteed return with a postcondition through
`EventuallyReturns`: for every oracle there is a bound above which every fuel
budget produces a successful result. Its first client, `countdown_total`, covers
every finite hint count `n` and every oracle, with the uniform bound `n`. This
client starts from the default memory `{}` and has exactly one ready task, no
children, retries, blocking operations or memory accesses. Its remaining hint
count decreases at each scheduler turn; the singleton ready set requires no
fairness assumption. This proves completion of the model fragment, not a source
export or native program. The worker idle loop below terminates only under an
explicit fairness premise. General fork/join completion, other retry loops and
weak-CAS success assumptions remain open.

Two more interfaces sit beside it. `ReturnsWithin B` bounds the budget uniformly: every
oracle returns for every fuel of at least `B` turns (`countdown_within`). It implies
`EventuallyReturns`. `EventuallyReturnsUnder Fair` is the conditional form: only oracles
satisfying the explicit premise `Fair` must return. It follows from `EventuallyReturns` for
any premise, and with the premise `True` it is equivalent to it. Since `under_false` proves
it for any program under an unsatisfiable premise, it never implies an unconditional return;
`EventuallyReturnsUnder.discharge` needs a proof that every oracle satisfies the premise.
`stuck_not_eventuallyReturns` and `stuck_not_returnsWithin` refute both unconditional forms
for a program that never returns.
`tests/roadmap/progress/Total.lean` checks the positive theorem families and a
symbolic counterexample showing that readiness alone does not imply fair task
selection. CI kernel-checks it with plain `lake env lean` in full non-mutation rows.

<a id="worker-idle-loop"></a>
## Worker idle loop

`tests/roadmap/idle-loops` checks the translated `progress.idle` loop
(`while (@atomicLoad(u32, flag, .acquire) == 0) { spinLoopHint(); Thread.yield() catch {}; }`).
The AIR is the retained 0.16.0 `x86_64-linux` baseline `ReleaseSafe` export from
full progress-hint qualifications. Three clean revisions produced byte-identical AIR
(`provenance.json`). `IdleLoop/Gen.lean` is the unmodified translator output, and the
gate retranslates and compares it. `wLoop_eq` unfolds one iteration of the
generated loop: an acquire load (a `pick` stop), then on 0 the spin `yield` stop
and the two-outcome `Thread.yield` stop, then the loop again.

The translated module has no spawn target. A spawn-target `retarget` therefore runs
it as thread 1 of a hand-written harness. That harness is not translated source:
`main` spawns the worker, writes 42 to `data`, release-stores 1 to `flag` and joins.
After the loop, the worker reads `data` and panics on any value other than 42.
`data` and `flag` are zero-initialized globals.

| Theorem (`IdleLoop/Theorems.lean`) | Claim | Premises beyond the model |
| --- | --- | --- |
| `idle_safe` | For every oracle and fuel: no error (no panic, so no stale `data`; no race; no deadlock). No-result runs remain allowed. | none (only the model premises THR-01/07/08) |
| `idle_progress` | If `Cooperative o`, every fuel above a bound returns after `main` joins the worker, so the loop exited. | THR-09 |
| `idle_starves` | Under `favorWorker` (always run the worker while it is ready), no fuel gives a result. The worker spins and yields forever. | none |
| `progress_needs_premise`, `not_eventuallyReturns` | The progress conclusion fails for some legal oracle, so it is not a model theorem without THR-09. | none |
| `idle_total_under` | `idle_progress` through `EventuallyReturnsUnder Cooperative`: the premise is an explicit argument of the interface. | THR-09 |
| `cooperative_not_all` | Some legal oracle is not cooperative, so the premise cannot be discharged. | none |

`Cooperative o` (premise [THR-09](premises.md#thr-09)) says that from some oracle
index on, every choice is option 0. The scheduler then prefers the lowest-numbered
ready thread (the setter, `main`). Every atomic read reads the newest message. This
combines scheduler fairness with eventual store visibility, and the progress proof
needs both. A fair scheduler alone still lets the worker reread the stale 0 forever.
Fresh visibility alone still lets `favorWorker` starve the setter.
`favorWorker_not_cooperative` and `zero_cooperative` show that the premise excludes
the starving oracle and is satisfiable. The safety theorem has no premise. The
premise index records THR-09 for the progress theorems only.

Target qualification of the hints is unchanged from the table above. On x86 the
hint exports `pause`, and on aarch64 it exports `isb`. The checked export is
`x86_64-linux`, whose AIR has `pause`. Other targets have no spin-specific semantics.
On every target, `Thread.yield` may return `SystemCannotYield`; the loop discards
that error. Neither hint promises a handoff, a delay or visibility. `idle_starves`
is a kernel-checked schedule in which both hints execute every iteration and the
loop never exits. The client proofs cover the model, not native execution. The
compiler/exporter correspondence remains trusted (TRU-02), and source/model
correspondence is not proved.

```sh
lake build ZigLean air2lean
bash tests/roadmap/idle-loops/check.sh
```

The gate checks the AIR and source hashes, retranslates and byte-compares
`Gen.lean`, and compiles the proof modules. `Check.lean` restates the four claims and
uses `#guard_msgs` to require only `propext`, `Classical.choice` and `Quot.sound`. CI
runs the gate in full non-mutation rows.

`tests/roadmap/progress/progress.zig` covers actual source hints, a yield error
handler and an atomic idle loop. `Runtime.lean` exercises both yield returns,
same-thread continuation, another-thread interference, unbounded idle-loop
no-result behavior and absence of hint-created access/clock edges.
`Pipeline.lean` checks modeled signatures, classifications, negative boundaries,
and writes generated Lean for separate elaboration. Assertions detect mutations
that make a hint pure, force yield success, or require a different thread to run.

The portable default gate needs Lean and Python but no Zig compiler:

```sh
scripts/progress-hints.sh
```

It builds the runtime/translator, kernel-checks the safety contracts, executes the
runtime and signature regressions, elaborates fresh synthetic translations for
all three supported versions, and verifies that an isolated mutant removing the
spin scheduling operation is rejected by the scheduler-participation assertion.
The mutation must return assertion exit code 85 with its runtime marker; a parse
or compile error does not count.

Opt into source and native qualification with explicit 0.16.0 compilers:

```sh
AIR2LEAN_ZIG_AIR=/path/to/patched/zig AIR2LEAN_ZIG=/path/to/stock/zig scripts/progress-hints.sh full
```

Full mode exports all four `progress.*` source roots on `x86_64-linux` with baseline
CPU features, `ReleaseSafe`, and disabled error tracing. `Thread.yield` is a modeled
boundary, so its syscall implementation is not exported as another translated body.
The gate checks a fresh `ProgressSource.lean`, then runs 64 finite native hint/yield
calls on the stock compiler's native host target. It never executes `idle`. On a
non-Linux host, that native smoke check is a separate target observation and does
not qualify native execution of the Linux AIR. The kernel safety contracts concern
the model's hints; source translation compilation and finite native smoke checks
are additional evidence and do not prove source/model correspondence or liveness.

Each local invocation retains a fresh `.lake/progress-hints-*` directory even on
failure. `AIR2LEAN_PROGRESS_ARTIFACT_DIR` selects a different retention directory.
`report.json` records exact command arguments, stage statuses, durations, revision,
dirty-tree state, source/model hashes, Lean/Lake binaries, translator binary,
patched/stock compiler binaries and versions, complete Zig library hash manifests,
artifact hashes, target/build profile and explicit claim exclusions. Logs, AIR,
generated Lean, fixtures and finite native binary remain available. Compiler caches
are retained locally but excluded from artifact hashes. Per-command timeouts default
to 600 seconds (`AIR2LEAN_PROGRESS_TIMEOUT_SECONDS`); a timeout is a failed
qualification, never a proof of divergence. Artifact-only runs explicitly report
that source export and native execution were not run. The gate is suitable for
separate artifact-only and 0.16.0 full CI invocation. CI runs the portable gate
in its non-mutation version jobs and full qualification in its 0.16.0 job. Detailed
CI evidence stays under `RUNNER_TEMP` outside the `.lake` cache; no new upload step
is added.

The source semantics audit is separate from successful execution of these
commands. Compiler runs, kernel checks and exported fixture evidence must be
recorded for the exact reviewed revision; this document alone is not a fresh
validation result. The compiler/exporter correspondence remains trusted.
