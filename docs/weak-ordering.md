# Weak-ordering litmus tests (T04)

The model's atomics (`ZigLean/Mem/Thread.lean`, `docs/std-models.md` §Thread model) are an
operational approximation of RC11 without promises: a relaxed read may read any message that is
not older than what the thread has seen or what happened before it, a release write publishes its
clock and an acquire read adopts it, and `seq_cst` has the rule of `acq_rel`. These tests check,
on the two aarch64 profiles, that every outcome the hardware shows for the classic litmus shapes is
an outcome of that model. A native outcome outside the model's set would be a soundness finding:
a theorem could exclude a behaviour that the compiled code has.

## Tests

`tests/roadmap/weak-ordering/litmus.zig` runs each test 100 000 times on fresh cells. The threads
of a round meet at a relaxed barrier first, so their operations race. Each line records the
outcomes (the registers as digits) and how often each occurred.

| Test | Threads | Forbidden by the model |
| --- | --- | --- |
| `mp relaxed` | `x=1; y=1` ‖ `r0=y; r1=x` (all relaxed) | nothing |
| `mp release_acquire` | `x=1; y=1 (release)` ‖ `r0=y (acquire); r1=x` | `10` |
| `sb relaxed` / `sb seq_cst` | `x=1; r0=y` ‖ `y=1; r1=x` | nothing (the model has no SC order) |
| `lb relaxed` | `r0=x; y=1` ‖ `r1=y; x=1` | `11` (no load buffering) |
| `corr relaxed` | `x=1; x=2` ‖ `r0=x; r1=x` | `10`, `20`, `21` (read-read coherence) |
| `wrc release_acquire` | `x=1 (release)` ‖ `r0=x (acquire); y=1 (release)` ‖ `r1=y (acquire); r2=x` | `110` (causality) |
| `iriw relaxed` / `iriw acquire` | `x=1` ‖ `y=1` ‖ `r0=x; r1=y` ‖ `r2=y; r3=x` | nothing |

`tests/roadmap/weak-ordering/Litmus.lean` computes the model's outcome set of each test by
running the same operations on the model's `atomicLoadAt`/`atomicStoreAt`: every interleaving and,
at each operation, every option the model offers (which message a load reads, where a store goes
in modification order), with the threads made by `Thread.fork` after the cells are zero. The
forbidden outcomes of the table are checked when the file is elaborated (`#guard`). Run with
observation files, it fails unless every observed outcome is a model outcome. The one exception is
`lb relaxed`: the translator rejects the relaxed load-buffering shape (`checkLoadBuffering`,
premise ORD-02), so an observed `11` would be printed as `rejected shape`, never as a match.
The model outcomes no file observed are printed as `unobserved`.

## Evidence

`scripts/weak-ordering.py observe` builds the litmus program with a stock compiler for the
profile (ReleaseSafe, LLVM, baseline CPU) and runs it on that profile's own host only;
`scripts/weak-ordering.py check` runs `Litmus.lean`. `tests/roadmap/weak-ordering/observed/`
holds one observation per profile and Zig version (0.14.1 to 0.17.0): aarch64-macos-none on
Apple silicon, aarch64-linux-gnu in a native `linux/arm64` container. CI observes again on every
run (the `aarch64-linux` job for all four versions, the `macos` job for its row's version) and
checks the fresh and the committed files; `test_weak.py` checks that a forbidden outcome, a
missing or duplicated line and an unknown test fail.

Observed on these hosts: the store-buffering outcome `00` with relaxed ordering (both profiles),
and on Apple silicon (aarch64-macos-none) also the weak message-passing outcome `10` and the
IRIW outcome `1010` with relaxed loads (each reader's two loads are unordered); no weak outcome with
release/acquire or `seq_cst`. Every observed
outcome is a model outcome. No load-buffering outcome was observed.

## Limits

The tests check the outcome sets of these shapes, not instruction-level ordering strength (which
fence or barrier the compiler emits), futex or mutex behaviour, atomics wider than 32 bits, or
non-baseline CPU features. A shape that was not observed proves nothing about the hardware; the
model is checked to allow at least what was observed.
