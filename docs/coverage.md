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
project evidence changes. Both `generate` and `check` also exit 1 while any AIR
tag, type tag, intern key or pointer base lacks a named disposition (see
[Dispositions](#dispositions)); `generate` still writes the file so the
`unclassified-forbidden` rows can be reviewed. New and renamed tags cannot
disappear through a normalizer filter. Renaming appears as removal plus addition;
the tool does not infer equivalence. Exit 2 means invalid/inaccessible input,
including a translator source whose diagnostic gates the derivation can no
longer find. CI must provision the
compiler source root and check committed evidence before overwriting generated
proof modules.
Regeneration records evidence; it does not itself qualify an upgrade.

CI runs the offline regression suite in every matrix job. Each non-mutation job
then downloads its version's source archive using the existing `versions.toml`
URL and SHA-256 pins, verifies the archive, extracts a fresh temporary source root
and checks the committed Linux inventory. It cleans up the source root on exit.
This gate runs before compiler/proof pipelines overwrite generated proof modules,
and independently of the patched compiler cache. A new/renamed tag, changed
compiler fingerprint or stale project evidence fails the job. The source gate
invokes neither Zig nor Lean; later pipeline steps supply execution/proof evidence.

The snapshots are generated from the checksum-verified release source archives
pinned in `zig-patch/versions.toml` (the same archives the CI gate checks):

| Zig | AIR tags | Type tags | Intern keys | Pointer bases |
| --- | ---: | ---: | ---: | ---: |
| 0.14.1 | 207 | 24 | 34 | 9 |
| 0.15.2 | 212 | 24 | 34 | 9 |
| 0.16.0 | 214 | 24 | 33 | 9 |

## Dispositions

Every row carries one name from `DISPOSITIONS` in `scripts/coverage.py`; each
inventory embeds that vocabulary under `dispositions`, and per-category counts
under `summary` (AIR tags) and `category_summary`. Each row's `derivation`
records `mechanical` or `reviewed-override`.

**AIR tags.** Derived in pipeline order from the exporter's `writeInst` switch
(with comptime `Compat.vNN` branches resolved for the inventory's version),
`normalizeOp` and the emitter's instruction dispatch (`emitScalar`, `emitStmts`,
`emitTerminator`):

| Disposition | Mechanical rule |
| --- | --- |
| `rejected-fast-math` | The tag has the suffix that `normalizeOp` rejects first (`_optimized`). |
| `rejected-compiler-state-or-effect` | `runtimeTagReason?` gives the tag a specific diagnostic. |
| `rejected-exporter-unsupported` | The version-selected exporter arm writes only `"unsupported": true`, or the fallback writes it for every tag it does not name; `normalizeOp` rejects the marker. |
| `rejected-unknown-tag` | Exported, but no `normalizeOp` branch; the fallback rejects it as an unknown AIR tag. |
| `erased-at-emission` | Exported and normalized to constructors that `emitScalar` maps to `(env, none)` (line/debug metadata). |
| `emitted-unqualified` | Exported (explicit arm, or a fallback branch naming the tag directly or via a `Compat.is*` helper), normalized, and every constructor has an emitter dispatch arm. |
| `unreachable-at-export` | Reviewed override only. |
| `unclassified-forbidden` | Anything else: unknown version branches that disagree, data-dependent `unsupported` arms, a fallback without a marker, or a constructor without a dispatch arm. |

**Types** (`std.builtin.Type`): `exported-checker-restricted` (explicit
`writeTypeEntry` arm; `Check.lean` restrictions apply) or
`exported-as-other-rejected` (fallback writes kind `other`, which `checkTy`
rejects; pointer-to-fn/anyopaque children are checked separately).

**Intern keys** (`InternPool.Key`): `value-exported` (explicit `writeRef` arm, or a
fallback `Compat.is*` helper naming the key, such as 0.16 `bitpack`),
`type-key-via-type-table` (`*_type` keys are exported through the type table and
classified by the type rows) or `value-fallback-text-restricted` (fallback
writes formatted text; `parseLeafVal` accepts only int/bool/void/packed leaves).

**Pointer bases** (`BaseAddr`): `rejected-unsupported-pointer-base` when the
`resolvePtr` arm or fallback returns `.unsupported` and `Check.lean` rejects
`ptrOther` constants; `resolved-conditional` for other explicit arms.

**Reviewed overrides** (`OVERRIDES` in `scripts/coverage.py`) cover what source
structure cannot show: comptime-only types (`type`, `comptime_int`,
`comptime_float`, `undefined`, `null`, `enum_literal`) and intern keys
`enum_literal`, `memoized_call` and 0.14/0.15 `variable` are
`unreachable-at-export`; `undef` is `value-exported` through the fallback's
`isUndef` marker. Each override pins the mechanical disposition it was reviewed
against (`replaces`). If the derivation changes, the row becomes
`unclassified-forbidden` and generation fails until the override is re-reviewed.

A new or renamed compiler tag therefore fails CI twice: the universe/fingerprint
comparison reports it, and the row needs a named disposition. An unknown tag
reaching the exporter's unsupported fallback is classified
`rejected-exporter-unsupported` automatically; any tag the exporter starts to
decode needs a normalizer branch and emitter arm, or it stays forbidden.

## Reading stage evidence

All inventories have `evidence_level` **source-inventory**. They make no new
compiler execution, differential agreement, proof checking or preservation claim.
Dispositions describe which source stage accepts or rejects a tag; they are not
semantic support claims.

* **Exporter:** `exporter.status` is one of `explicit-arm`,
  `fallback-named-decoder`, `explicit-arm-unsupported-marker`,
  `fallback-unsupported-marker`, `explicit-arm-conditional-unsupported`,
  `version-conditional-unresolved` or `fallback-unclassified`. Version selection
  only resolves `Compat.vNN` tests; an explicit arm still needs operand and
  nested helper review. A version label that is not `0.N.P` keeps every branch,
  and a tag stays forbidden unless they agree.
* **Normalization:** explicit tag branches, the call-prefix branch, fast-math
  and runtime-reason rejections, and unknown-tag rejection are recorded with
  their returned constructors. The fast-math suffix, call prefix and the
  unsupported-marker and unknown-tag gates are read from `normalizeOp`.
* **Parser and checker:** generic schema parsing and conditional type/layout
  checking are source references. They do not establish acceptance of all
  operands or all representations of a tag.
* **Emission:** `dispatch-arm`, `erased-dispatch-arm`, `not-reached` (the tag is
  rejected earlier) or `missing-dispatch-arm`. A dispatch arm is a source match
  arm, not evidence that every operand type is emitted correctly.
* **Semantics/proofs:** constructor-symbol occurrences provide reviewer
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
* **Types/constants/pointer bases:** dispositions come from the actual
  `writeTypeEntry`, `writeRef` and `resolvePtr` switches plus the matching
  `Check.lean`/`Json.lean` rejection. No base names are hardcoded as supported.
  This does not qualify pointer provenance, fields or layouts.
* **Models:** names recognized/rejected by `allocFn?`, `threadFn?` and
  `rejectedThreadFn?` are extracted from `Memory.lean`, with its anonymous-instance
  recognition rule. Recognition is a model boundary, not verification. Timer
  recognition, for example, retains the documented unspecified clock behavior.
  Contracts, target/version restrictions and spawn/allocator assumptions remain
  in `docs/std-models.md` and the checker.

An `emitted-unqualified` tag passes every source stage, subject to the preceding
restrictions. It is deliberately not called fully supported or verified. L14's
source-feature qualification still requires a compiler-generated fixture and a
checked contract for that source feature.

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

## Upgrade qualification

`scripts/qualify-upgrade.py` turns the change-impact report into a qualification
record of explicit obligations and gates on their results:

```sh
python3 scripts/qualify-upgrade.py plan coverage/0.15.2.json coverage/0.16.0.json \
  --output qualification/0.16.0.json
python3 scripts/qualify-upgrade.py commands qualification/0.16.0.json   # list, run nothing
AIR2LEAN_ZIG=/path/to/stock/zig python3 scripts/qualify-upgrade.py run qualification/0.16.0.json
python3 scripts/qualify-upgrade.py record qualification/0.16.0.json model-boundary \
  --reviewer NAME --decision accepted --evidence docs/std-models.md
python3 scripts/qualify-upgrade.py check qualification/0.16.0.json \
  --before coverage/0.15.2.json --after coverage/0.16.0.json
```

`plan` runs `coverage.py diff` and derives the obligations:

| Obligation | When | Discharged by |
| --- | --- | --- |
| `support:<category>:<name>` | a tag, type or pointer-base disposition is new or ranks higher (an unknown disposition counts as expansion; narrowing does not) | accepted review with evidence |
| `model:<name>`, `model-boundary` | std model recognition or boundary sources (Memory.lean, std-models.md, selected std files) changed | accepted review with evidence |
| `universe:<category>`, `evidence:tags`, `compiler-sources` | universe additions/removals, changed tag rows, changed compiler fingerprints | accepted review |
| `probe:float`, `probe:layout:<profile>` | version or compiler change, or probe sources changed | `run` (`floatprobe.sh`, `abi-probe.py observe` per profile) |
| `translation:<example>` | every example on a version, compiler, translator, runtime or model change; otherwise examples whose goldens contain changed tags | `run` (`AIR2LEAN_CI=1 check.sh` per example, includes the differential test) |
| `proofs:<example>` | affected examples, changed proof sources, runtime model or version change | `run` (`assumptions.py --module ...`, kernel dependency audit per example) |

`run` executes pending command obligations from the repository root, writes a log per
obligation under `<record>.d/logs/` and records the exit code, log hash and Git HEAD after
each one, so an interrupted run resumes; passed obligations rerun only with `--rerun`.
`record` stores a review decision (`--reviewer`, `--decision accepted|rejected`) or an
externally produced result (`--status pass|fail --evidence ...`, e.g. a CI run). `check`
fails when an obligation has no result or a failing one, a review is not accepted, a support
expansion or model change has no review evidence, a run log is missing or edited, the
obligation list was edited after `plan` (digest), or, with `--before/--after`, the plan is
stale for those inventories. Comparing each new dependency audit with the previous release's
audit is part of the `proofs:` obligation; the driver records the audit, it does not diff it.
`tests/roadmap/upgrade-qualification/` covers the driver on synthetic inventories with stub
runners; a real `run` builds Zig probes, translations, differential tests and proofs.

The offline synthetic tests cover nested syntax, escaped identifiers, malformed
input rejection, all four compiler universes, unknown AIR tags, rename impact,
fingerprint-only changes, Zig escapes, shared/version/OS overlays, new pointer
source arms, invocation cache freshness, switch scoping, model recognition, Compat
version branches, named fallback decoders, emission dispatch/erasure, stale
overrides and the forbidden-disposition exit. They intentionally
invoke no compiler.
