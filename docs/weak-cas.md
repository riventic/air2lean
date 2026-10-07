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

## Message precision and mixed sizes

Modification order holds write events. Every atomic write is a fresh message (id, clock, release
clock, RMW edge); a plain write to an atomic location becomes a message at the next atomic op
whenever it did not happen before the newest message (`Zig.plainSince` in `locIdx`), even if it
wrote the bytes the location already holds. Earlier the model compared bytes only and folded an
equal-valued plain write into the previous message; under the race check that write happened
after every earlier message, so no outcome changed, but the event was not tracked. The message of
a plain write carries the join of the plain writes' clocks and no release clock, so it ends a
release sequence. The proof invariants (`Word.Ok.plain`, `Lock.LocOk.plain`, and the
`FlagLoc`/`HeadLoc`/`CntOk` invariants of the atomic examples) carry `PlainLe`.

Mixed-size policy: an atomic location is one `(block, offset, size)`. An atomic load, store, RMW
or `cmpxchg` that overlaps an existing atomic location with another offset or size throws
`.unspecified` before it reads or writes a message, in either order of the accesses. Adjacent
non-overlapping atomic words are separate locations. Plain accesses of another size are not
atomic accesses: a plain write is a write event as above. A proof of "no error" therefore shows
that its program has no mixed-size atomic access; the model does not give such accesses a meaning.

`tests/roadmap/weak-cas/Messages.lean` (kernel reduction and runtime assertions) checks:

- ABA: `x = 0` (plain), then relaxed `1`, relaxed `0`, release `1` from another thread. The
  four messages are distinct events; an acquire read of the newest `1` synchronizes and one of
  the older `1` does not; the pairs of two relaxed reads are exactly the coherent pairs (10 of
  16), so `1, 0, 1` is observable and `1` (newest) then `0` is not; a strong `cmpxchg(1 → 2)` has
  one option per message and may succeed on the older `1`, inserting the RMW right after it.
  Weak CAS adds a read-only failure for each of the two `1` messages.
- Release sequence through equal values: a release `x = 1`, a relaxed `xchg(x, 1)` reading it
  and an unrelated relaxed `x = 1`. An acquire reader synchronizes through the release store or
  the RMW and reads the data; reading the equal-valued relaxed store (or the initial value) and
  then the data is a race (`.illegal`). The model's release sequence has RMWs only (C++20); RC11
  also includes same-thread later stores, so the model may synchronize less, never more.
- An equal-valued plain write after a join becomes a message with no release clock; a following
  RMW reads it. Without a plain write, an atomic op adds no message.
- Mixed sizes: `u8`, `u16` at another offset, `u64`, a 2-byte `cmpxchg` and a 1-byte RMW against
  a `u32` location, and a `u32` against an earlier `u16`, are all `.unspecified`; an adjacent
  `u32` is a second location; a plain byte store is read back by the next `u32` atomic load.

These are bounded litmus tests of the model, not a compiler correspondence argument.

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
`x86_64-linux`, baseline CPU, ReleaseSafe, without error tracing. Its combined
`source-kernel-and-allowed-outcomes` step elaborates the actual emitted module together with
its appended checks, then runs success and failure oracles and 256 bounded retry masks against
allowed source outcomes. A failure may arise during elaboration or execution; the retained log
identifies it. Full mode also executes a native test importing that same source. Native weak CAS may
never fail spuriously; the comparison checks allowed outcomes rather than identical failure
frequency. Native results on another host target are a separately reported smoke test, not
cross-target correspondence. Full mode checks no 0.14/0.15 source exports.

Every invocation creates a fresh retained directory under `.lake/weak-cas-*` by default. Set
`AIR2LEAN_WEAK_CAS_ARTIFACT_DIR` to retain it elsewhere. `report.json` records revision/dirty
state, complete input/model source hashes, translator and compiler binaries, compiler library
hash manifests, versions, explicit profile/scope, commands, return codes and logs. Fresh AIR,
emitted Lean, appended source checks, native executable, mutation and logs remain locally.
CI runs the complete gate in the non-mutation 0.16 job, including all three synthetic version
labels; the existing 0.14/0.15 golden and proof gates remain required. CI retains the report
under `${RUNNER_TEMP}` outside cached `.lake` and adds no artifact-upload step.
A timed-out subprocess receives TERM and then KILL for its entire process group before the
leader is reaped; bounded cleanup attempts and failures are recorded in its report step.
`python3 tests/roadmap/weak-cas/Harness.py` checks signal/reap ordering and failures without
compilers, plus one self-expiring TERM-ignoring child within a 32 MiB memory budget. The gate
runs and retains this fixture too.
The compiler/exporter and selected model remain trusted; these checks do not prove compiler
correspondence or validate the remaining C11 gaps.
