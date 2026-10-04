# Compiler-derived coverage inventory

`python3 scripts/coverage.py` inventories the actual Zig compiler sources, without
starting Zig, Lake or Lean. The checked inventories in `coverage/` record Zig
0.14.1, 0.15.2 and 0.16.0. Every AIR enum field, `std.builtin.Type` field,
`InternPool.Key` field and pointer `BaseAddr` field receives a named disposition.
InternPool keys include internal and comptime entries: this is an exhaustive
compiler representation list, not a claim that every key reaches executable AIR.

The parser tokenizes Zig, ignores comments, preserves escaped identifiers and
tracks nested braces, parentheses and brackets. It reads top-level enum/union
fields while skipping methods and nested declarations. Zig quoted identifiers
use Zig byte (`\xHH`) and Unicode scalar (`\u{...}`) escapes; malformed escapes
and invalid UTF-8/scalars fail. File bytes, decoded tokens, hashes and symbol
indices are cached within one invocation and refreshed on the next invocation. Unexpected syntax,
duplicate fields, missing files and malformed golden JSON fail the command.
It never substitutes a README or exporter tag list for missing compiler sources.

## Generate and check

Pass a source root containing `src/Air.zig`, `src/InternPool.zig` and
`lib/std/builtin.zig`. A patched source checkout is usable: the fingerprint will
record that exact checkout. The release label is supplied by the caller; source
fingerprints, rather than a compiler `--version` process, establish snapshot
identity. Review source provenance before publishing an inventory.

```sh
python3 scripts/coverage.py generate --version 0.16.0 \
  --source /path/to/zig-0.16.0 --os linux --inventory coverage/0.16.0.json
python3 scripts/coverage.py check --version 0.16.0 \
  --source /path/to/zig-0.16.0 --os linux --inventory coverage/0.16.0.json
python3 tests/roadmap/inventory/test_inventory.py
```

Repeat generation/check for every supported version. `check` exits 1 when a
compiler fingerprint, universe, disposition, model boundary, golden input or
project evidence changes. New and renamed tags cannot disappear through a
normalizer filter. Renaming appears as removal plus addition; the tool does not
infer equivalence. Exit 2 means invalid/inaccessible input. CI must provision the
compiler source root and run checks after generating any expected translations.
Regeneration records evidence; it does not itself qualify an upgrade.

The initial snapshots use these already available source directories:

| Zig | Source root | AIR tags | Type tags | Intern keys | Pointer bases |
| --- | --- | ---: | ---: | ---: | ---: |
| 0.14.1 | `/opt/dev/air2lean-build/0.14.1/zig-0.14.1-pristine` | 207 | 24 | 34 | 9 |
| 0.15.2 | `/opt/dev/air2lean-build/zig-0.15.2-pristine` | 212 | 24 | 34 | 9 |
| 0.16.0 | `/opt/dev/air2lean-build/zig-0.16.0-src` | 214 | 24 | 33 | 9 |

## Reading stage evidence

All inventories have `evidence_level` **source-inventory**. They make no new
compiler execution, differential agreement, proof checking or preservation claim.

* **Exporter:** an explicit `writeInst` switch arm is indexed separately from an
  arm containing an `unsupported` marker. A fallback is **unclassified**, since
  version-dependent `Compat` helpers can decode it. An explicit arm still needs
  operand and helper review. In particular, `assembly` is conditional on version;
  shuffle and new cast tags may be decoded through fallback helpers.
* **Normalization:** explicit tag branches and the call-prefix branch are indexed;
  `_optimized` is always classified as rejected fast math. Missing branches are
  unclassified/unknown, with diagnostic guidance to inspect `normalizeOp`.
* **Parser and checker:** generic schema parsing and conditional type/layout
  checking are source references. They do not establish acceptance of all
  operands or all representations of a tag.
* **Semantics/emission/proofs:** constructor-symbol occurrences provide reviewer
  navigation. A hit can occur in comments or unrelated code; it is explicitly a
  symbol index, not a semantic implementation or theorem-coverage assertion.
  A missing hit is not a proof that the operation is unsupported. No theorem
  strength, input domain, all-schedules claim or current kernel result is inferred.
* **Tests:** AIR instruction tags in selected golden inputs are indexed. Selection
  follows `check.sh`: shared files, then the version layer, then `--os` (default
  `linux`), with later layers replacing all anonymous instances of the same
  normalized filename. Examples excluded by `zig-versions` contribute no paths.
  Other OS layers and overridden files contribute no evidence. Shared fixture
  applicability does not establish an actual run for this version/OS. Presence
  does not mean the test was run, passed, covers boundaries or has a
  differential/proof contract. Missing golden paths remain explicit.
* **Types/constants:** type exporter arms require conditional checker review.
  All intern keys are listed with an explicit unclassified disposition pending
  `writeRef`/checker review. Pointer bases record conditional global resolution
  from the actual `writePtr` switch: explicit arms require conditional review;
  missing arms are marked by the actual unsupported fallback marker, or left
  unclassified if no such marker exists. No base names are hardcoded as
  supported. This does not qualify pointer provenance, fields or layouts.
* **Models:** names recognized/rejected by `allocFn?`, `threadFn?` and
  `rejectedThreadFn?` are extracted from `Memory.lean`, with its anonymous-instance
  recognition rule. Recognition is a model boundary, not verification. Timer
  recognition, for example, retains the documented unspecified clock behavior.
  Contracts, target/version restrictions and spawn/allocator assumptions remain
  in `docs/std-models.md` and the checker.

A `source-pipeline-candidate-unqualified` tag has explicit export and normalizer
arms, subject to the preceding restrictions. It is deliberately not called
fully supported or verified. L14's source-feature qualification still requires a
compiler-generated fixture and a checked contract for that source feature.

## Upgrade change impact

```sh
python3 scripts/coverage.py diff coverage/0.15.2.json coverage/0.16.0.json \
  --output /tmp/zig-upgrade-impact.json
```

The report lists added/removed AIR tags, type tags, intern keys and pointer bases;
changed tag evidence; model boundary changes; and changed translation, runtime,
proof and probe source files. Compiler fingerprints detect changes even when enum
names stay identical. Besides the three universe files, the selected upgrade
surface includes `Type.zig`, `Value.zig`, `Sema.zig`, LLVM codegen and the allocator,
Thread, Io and time std entry files (absent files are explicit nulls). These
fingerprints are a selected change detector, not a full compiler source closure;
other compiler or std files still require release diff review. All snapshot source paths are repository-relative; compiler
fingerprints use source-root-relative paths. Moving a checkout does not change a
snapshot.

The report names remaining upgrade obligations: review lowering/export operands,
rerun layout/float probes and differential fixtures for qualified targets, review
std models, regenerate translations, rebuild affected proofs and compare kernel
dependency reports. It detects source changes in these areas; it does not invent
probe results or theorem dependency results from hashes. Q07 remains a release
qualification process requiring those actual results.

The offline synthetic tests cover nested syntax, escaped identifiers, malformed
input rejection, all four compiler universes, unknown AIR tags, rename impact,
fingerprint-only changes, Zig escapes, shared/version/OS overlays, new pointer
source arms, invocation cache freshness, switch scoping and model recognition. They intentionally
invoke no compiler.
