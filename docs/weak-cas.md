# Weak CAS: the spurious-failure part of C11

`cmpxchg_weak` is emitted as `Zig.cmpxchgWeakC` or `Zig.cmpxchgWeakAsC` for Packed
pointees. `cmpxchg_strong` retains its existing model and wrappers. The qualified weak model
adds a failed read for every readable message whose value equals the expected value. A weak
operation can still succeed on such a message when the RMW insertion is permitted. Strong
choices come first; additional tagged failure choices follow. This ordering is a test convention,
not a source guarantee.

Preparation records one atomic-read footprint and performs the existing access/race/location
checks. Success records an atomic write and inserts an RMW message exactly as strong CAS does.
Failure returns the value read, observes its message, and acquires its release clock only when
the failure order is acquire (or stronger under the existing ordering abstraction). It does not
record an atomic write, insert a message, advance the modification order, or add an RMW edge.
The success order has no effect on a failed operation. A failed read may observe a readable
matching predecessor already followed by an RMW: only successful insertion must exclude it.
The read's existing coherence floor still applies.

`ZigLean/Conc/WeakCas.lean` exposes the resulting success/failure transition alternatives and a
concurrent WP rule quantified over all permitted choices. Its retry rule preserves an invariant
on every failure and requires the success postcondition on return. A retry can fail arbitrarily
many times, exhaust scheduler depth, or never return. The rules establish safety and partial
correctness, with no fairness or eventual-success assumption. Existing SC and RC11 compiler
adequacy limitations remain the ones documented by the concurrency model.

C11 remains partly open. A same-value plain write can still be omitted from atomic message
history; explicit plain-write event tracking is not implemented here. Overlapping atomic
locations of different sizes still return `.unspecified`. The new weak-CAS behavior does not
qualify those cases. Modification-order tests cover matching weak failures, successful RMWs and
failed reads of an RMW predecessor; they do not establish a general mixed-size model.

The checked-in generated stack and std synchronization clients use the weak wrappers at their
weak-CAS instructions. Their proof rules retain every failed read, including one equal to the
expected value. Stack retries preserve their existing invariant; condition signal/wait retries
preserve the waiter and epoch state; shared-lock retries use the parallel weak Word rule.
The strong rules remain available for strong-only clients. The qualification gate requires the
complete shipped `Proofs` aggregate to build before running the new fixtures, so a stale strong
proof or a broken matching-failure retry branch cannot count as a passing gate.
`tests/roadmap/weak-cas/generated-origins.json` records the hashes and exact version/host merge
selections of checked AIR used for the five changed generated modules. These are retranslations
of retained AIR; the fresh standalone source qualification below covers only Zig 0.16.

## Reproduce the gate

```sh
scripts/weak-cas.sh                      # Lean runtime, kernel, pipeline and mutation checks
AIR2LEAN_ZIG_AIR=/path/to/safe-patched16/zig \
AIR2LEAN_ZIG=/path/to/stock16/zig scripts/weak-cas.sh full
```

Artifact-only mode checks synthetic schema-11 AIR for all supported version labels, including
preservation of weak/strong tags, integer/Packed dispatch and actual emitted Lean elaboration.
Runtime tests check matching failures, successes, mismatches, correct failure-order acquire,
unchanged messages/write footprints, Packed values, and readable RMW predecessors. Preparation
regressions compare the shared preparation against its previous implementation for matching,
mismatching and consumed-predecessor reads, including exact choice arrays, memory events,
writable-access errors and generic option-count fallback. Kernel reduction covers both branches
and every success/failure sequence of a bounded three-attempt retry client. The generic retry WP rule supports arbitrary repeated failure through an
invariant obligation; the bounded enumeration is not an exhaustive unbounded program proof.
The mutation gate substitutes a strong operation for the weak matching-failure operation and
requires the dedicated assertion marker and exit 85. A compiler failure cannot satisfy it.

Full mode freshly exports `weakcas.weak`, `weakcas.strong`, `weakcas.weakBool` and `weakcas.retry`
from `tests/roadmap/weak-cas/weakcas.zig` with qualified 0.16 compilers. The AIR profile is
`x86_64-linux`, baseline CPU, ReleaseSafe, without error tracing. It elaborates the actual
emitted module, runs success and failure oracles and 256 bounded retry masks against allowed
source outcomes, and executes a native test importing that same source. Native weak CAS may
never fail spuriously; the comparison checks allowed outcomes rather than identical failure
frequency. Native results on another host target are a separately reported smoke test, not
cross-target correspondence. Full mode checks no 0.14/0.15 source exports.

Every invocation creates a fresh retained directory under `.lake/weak-cas-*` by default. Set
`AIR2LEAN_WEAK_CAS_ARTIFACT_DIR` to retain it elsewhere. `report.json` records revision/dirty
state, complete input/model source hashes, translator and compiler binaries, compiler library
hash manifests, versions, explicit profile/scope, commands, return codes and logs. Fresh AIR,
emitted Lean, appended source checks, native executable, mutation and logs remain locally.
CI retains this under `${RUNNER_TEMP}` outside cached `.lake` and adds no artifact-upload step.
The compiler/exporter and selected model remain trusted; these checks do not prove compiler
correspondence or validate the remaining C11 gaps.
