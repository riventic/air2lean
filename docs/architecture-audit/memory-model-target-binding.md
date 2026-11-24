# ORD-06 was not bound to the theorem's target

Audit of 2026-11-24 on main `fdf416baa`. Premise [ORD-06](../premises.md#ord-06) (memory-model
adequacy, trusted) says that on the theorem's target the compiled program has no behaviour the
model excludes. Its argument and evidence are per target, in the `memory_model` record of
`assurance/premises.json`. Nothing tied a theorem's target to that record.
[research/C12.md](../research/C12.md) said so: "today that binding is the translator's rejection
of atomics and threads on wasm32 and s390x". T03 then admitted atomics, futexes, threads and the
allocator model on the big-endian profile (s390x-linux and the new mips64-linux), and the record
and the premise text were not changed.

## Facts on main `fdf416baa`

- **Translator.** `checkBigEndian` (`Air2Lean/Check.lean`) admits integer atomics of at most 8
  bits or a whole number of bytes on a big-endian profile; generated code calls the `…COf .big`
  ops of `ZigLean/Conc/Endian.lean`. Spawn, join, futex wait and wake and the std allocator
  model are admitted. Only the OS-level models (`docs/os-threads.md`) and the listed constructs
  of `docs/profiles.md` §Byte order are rejected. `tests/roadmap/big-endian/concurrency.sh`
  requires the fresh translation of `concurrency.zig` for s390x-linux and mips64-linux (Zig
  0.17.1 and 0.15.2) to equal the retained `BigEndian/Conc/<version>/<target>/Gen.lean` byte
  for byte. wasm32 still rejects atomics, threads and futexes.
- **Record.** `memory_model.targets` had x86_64-linux, aarch64-macos and aarch64-linux.
  `memory_model.unqualified` said "s390x-linux: The translator rejects atomics on the
  big-endian profile", which is false, and had no mips64-linux entry. ORD-06 said "Targets in
  the record's `unqualified` list (wasm32, s390x) reject atomics and threads, so no theorem
  about them carries this premise", false for s390x and false for the index (finding 2).
- **Checks.** `scripts/premises.py` (`check`, `compiled`) failed a theorem or catalogue report
  with THR-01 or ORD-01 and without ORD-06, and a missing evidence file. `scripts/claims.py`
  listed ORD-06 in a concurrency claim's `premises`. Neither read the target of the generated
  module (the `target_triple` of its `-- air2lean-profile:` header).

## Finding 1: a concurrency theorem on s390x or mips64 was accepted under ORD-06

Failure scenario. The program is `tests/roadmap/big-endian/concurrency.zig`, function
`threadsAdd` (two threads `@atomicRmw(.Add)` into one `u32`, then an atomic load), target
s390x-linux, Zig 0.17.1. Its translation is the committed
`tests/roadmap/big-endian/BigEndian/Conc/V0_17_1/S390x/Gen.lean` (profile `abi64-be-v1`,
`target_triple` `s390x-linux.5.10...7.2-musl`). Add a theorem about it in the same directory:

```lean
import BigEndian.Conc.V0_17_1.S390x.Gen
open Zig BigEndian.Conc.V0_17_1.S390x
theorem threadsAdd_scenario (n : BitVec 32) : threadsAdd n = threadsAdd n := rfl
```

On `fdf416baa`, `scripts/premises.py explain threadsAdd_scenario` gives PRF-05, THR-01
("runtime module ZigLean.Conc.Basic", "ZigLean.Conc.Call") and ORD-06 ("implied by ORD-01;
implied by THR-01"), and `check` reports nothing about the theorem (run on that tree with the
file added; the file is not committed). The same holds for any theorem whose closure reaches
`threadsAdd`, and for the mips64-linux translation. `scripts/claims.py check_goal` had no
target input at all: a goal whose closure reaches the atomics model is accepted with
`premises: ["ORD-06"]` whatever its root's translation records.

The premise text that is false for it: "On the theorem's target, every behaviour of the compiled
program is one of the model's outcomes: the backend's lowering … and the hardware memory model
(x86-TSO on x86_64, ARMv8 on aarch64) produce no outcome that [the model] exclude[s] … The
argument per target, and its bounded qualification evidence, are the `memory_model` record". The
record has no hardware model, argument or evidence for s390x-linux or mips64-linux, and says of
s390x that such a theorem cannot exist. The report would name a premise and qualification
evidence that do not cover its target.

No committed theorem was in this state. The big-endian concurrency modules (`Run`, `Diff`,
`Futex`) are executable models compared with native output; they contain no theorem. Of the 6430
indexed theorems, the closure of 3530 gives ORD-06 itself: 2620 reach no generated module, 483
reach one without a recorded target (PRF-01, PRF-03), and 427 reach x86_64-linux translations.
None reaches an s390x, mips64 or wasm32 translation.

## Finding 2: the index lists ORD-06 for sequential theorems on unqualified targets

14 committed theorems are indexed with ORD-01 and ORD-06 although their translation is for a
target the record calls unqualified:

- 7 in `tests/roadmap/big-endian/BigEndian/Proofs.lean` (s390x-linux; for example
  `BigEndianClients.fieldFromBytes_orders`);
- 7 in `tests/roadmap/pointer-width/PointerWidth/Proofs.lean` (wasm32-freestanding, 5 of them
  also wasm32-wasi; for example `PointerWidth.Proofs.zeros_boundary`).

They are sequential. `explain` gives "ORD-03: closure token seqCst (source runtime fallback
ZigLean.Mem.Basic)": the source index adds the token rules of every reached runtime module and
of its imports, as an upper bound ([premise-source-closure.md](premise-source-closure.md):
"an over-approximation, not evidence that every added premise is a genuine dependency").
A listed premise that the theorem does not need makes the row weaker, not unsound. But the row
still cites ORD-06 for a target without a record, and it contradicts both the ORD-06 text and
the record's wasm32 entry ("no theorem carries a concurrency premise for it").

## Fix

One mechanism, for every target-qualified premise (`target_qualified` in
`assurance/premises.json`; today `memory_model`):

- `scripts/premises.py profile_target` reads `<arch>-<os>` from the generated module's profile
  header. `target_binding_problems` fails a theorem that carries a target-qualified premise
  over a translation whose target is not in the record's `targets`. `check` applies it to the
  source index and `compiled` to the kernel graph. `scripts/claims.py check` rejects a goal
  whose root translation records such a target. The translator's accept or reject decision is
  no longer part of the binding.
- A module that records no target (no header or the legacy profile, PRF-01; a gate-time module,
  PRF-03) is admitted only through the record's `unrecorded` entry, which says what the premise
  then means: the qualified targets only.
- The source index binds the premises the theorem's closure gives itself: its tokens, the
  runtime modules it names, markers, statement rules and what those imply. It lists but does
  not bind the source fallbacks (finding 2). A theorem about a concurrent translation always
  reaches the translation's own `atomic…COf`, `spawn…` and futex tokens, so finding 1 fails in
  the source index. `compiled` and `claims.py` bind every kernel-derived premise.
- s390x-linux and mips64-linux are `unqualified`, with the true reason and what is missing. No
  qualification entry was written, because no evidence for one exists: the proofs the argument
  cites (the RC11 mappings through IMM) cover x86-TSO, ARMv7, ARMv8, POWER and RISC-V, not
  z/Architecture or MIPS64; the retained `observed/concurrency-*-{s390x,mips64}-linux.txt` are
  schedule-independent results run under qemu user-mode emulation, which check the byte order
  of the atomic model and say nothing about the hardware's memory ordering. Adding either
  target widens a trusted premise and is a maintainer decision.
- The translator still translates big-endian atomics and threads (T03's model-against-native
  byte-order evidence is unchanged). What fails closed is the claim: no theorem and no
  `claims.py` goal can rest on ORD-06 for s390x-linux, mips64-linux or wasm32.

To lift it for a target: a `memory_model.targets` entry with (1) the hardware memory model,
(2) an argument that LLVM's lowering of atomics for it is a mapping proved sound for RC11, or
the named assumption that replaces the proof, (3) evidence files, the litmus programs of the
qualified targets (`tests/roadmap/architecture-audit/concurrency/native_litmus.zig`,
`tests/roadmap/weak-cas/native.zig`) run on that hardware.

Regressions: `tests/roadmap/premises/test_premises.py`
(`test_target_qualified_premise_needs_a_qualified_target`,
`test_target_qualified_premise_over_an_unrecorded_target`,
`test_target_binding_covers_every_target_qualified_record`,
`test_source_fallback_premise_is_not_bound`, `test_compiled_concurrency_needs_a_qualified_target`)
and `tests/roadmap/claims/test_claims.py`
(`test_concurrency_claim_needs_a_qualified_target`); mutants `premises-target-binding-dropped`
and `claims-target-binding-dropped` (`tests/roadmap/mutation-map/mutants.py`).

## Remaining

- Finding 2 stays visible in the index: the 14 rows still list ORD-06. Removing it needs a
  source closure that tells a concurrency dependency from a module's unrelated tokens (the
  precision question of [premise-source-closure.md](premise-source-closure.md)). A concurrency
  premise that only a source fallback finds is bound by `compiled`, not by the source index;
  `compiled` runs over the audited translation, which does not include `tests/roadmap`.
- `claims.py` binds the target of the root's generated module, not of every generated module in
  the theorem's closure.
- 483 concurrency theorems are over translations without a recorded target. Their ORD-06 is
  the conditional of `memory_model.unrecorded`; a recorded profile (PRF-02) would bind them.
