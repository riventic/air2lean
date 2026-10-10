# Float-semantics labels of numerical theorems

Every numerical theorem states which float semantics it concerns. A theorem is *numerical*
when it is declared in a `ZigLean.Float.*` module, or when its checked dependency closure reaches
one. Each numerical theorem has exactly one label in `assurance/float-semantics.json`:

| Label | Concerns | Graph rule (checked) |
|---|---|---|
| `ieee` | The model's IEEE 754 semantics (`docs/floats.md` §Semantics): correctly rounded ops, comparisons, NaN classes. This is what `--float-semantics ieee` emits. It also covers ops that both modes share. | No `ZigLean.Float.CompilerRt` dependency |
| `compiler-rt@<versions>` | The ported compiler_rt helpers (`ZigLean/Float/CompilerRt.lean`, groups A, B and E–H) of the listed Zig versions. This is what `--float-semantics compiler-rt` emits. | Requires a `ZigLean.Float.CompilerRt` dependency |
| `abstract-spec` | An abstract numerical specification: formats, encodings, exact rational values and the rounding function. It selects no operation semantics. | No `ZigLean.Float.Ops` or `ZigLean.Float.CompilerRt` dependency |

A compiler-rt label lists the Zig versions it holds for, e.g.
`{"semantics": "compiler-rt", "zig_versions": ["0.14.1", "0.15.2", "0.16.0"], ...}`.

Every label also lists the target profiles whose float rules it holds for (`targets`, a
sorted subset of `aarch64-linux`, `aarch64-macos` and `x86_64-linux`; `docs/floats.md` §Targets). A theorem
about a model function used by both targets' translations, or about a translation for each
target (e.g. `op16_spec`, which reads the target off `Gen.lean`), lists both. A theorem whose
statement holds for one target's translation only names that target in a premise and lists
only it: `op80_spec` (`floatopsTarget = .x86_64`, the x87) lists `x86_64-linux`,
`op80_spec_aarch64` (`floatopsTarget ≠ .x86_64`, soft-float `f80`) lists both aarch64 targets. A theorem that names a
model function that only an aarch64 translation calls (`Zig.Float.softF80Chk`, `divXf3`,
`divTruncXf3`, `divFloorXf3`, `fmaFused`, `fmaRtFused`, `sqrtF80ViaF64`) must list an aarch64
target. This rule is checked on the source only: through its target premise, a theorem
stated for one target reaches both targets' rules in its dependency closure.
Each version must be a version in `zig-patch/versions.toml`. The `op*_spec` theorems of
`Proofs/Floatops` hold for all three versions; `op128_spec_full` does too, with the `f128`
division and `@sqrt` helpers of the translation's profile. `Float.floorRtLegacyChk_eq`,
`Float.ceilRtLegacyChk_eq` and the `Float.divRt_*` lemmas state the helpers that Zig used
before 0.16.0 (`compiler-rt@0.14.1,0.15.2`); the `Float.divRt016_*` lemmas state the 0.16.0
`f128` division (`compiler-rt@0.16.0`).

Every label also carries `"correspondence": "model"`. A label is a statement about the
Lean model only. It never claims that a compiled or shipped binary behaves the same way.
Any other value is rejected, e.g. `binary`, `native` or `bit-exact`, and so is a missing
value. The differential test (`scripts/diff.sh`) and the float probe
(`scripts/floatprobe.sh`) are test evidence on the reference target, not theorems.
Lean-generated companions are reported as `compiler-generated` and need no label of their
own: equation, `inj`/`injEq`, `sizeOf_spec`, sparse-case and abstracted `_proof_` lemmas.

`non_numerical` lists reviewed exemptions (`module::name` → reason). A theorem may be
exempt only if its closure does not reach the float model. `checks` lists Lean test files
outside `ZigLean/`/`Proofs/` that contain anonymous float `example`s, e.g.
`tests/review/Floats.lean`. Each entry gives the labels the file covers.

## Gates

| Command | Build | Rejects |
|---|---|---|
| `python3 scripts/float-semantics.py check` | none | a `theorem` in `ZigLean/Float/`, or one whose declaration mentions float types, with no label or exemption; a label that names no declared theorem; a theorem that mentions an aarch64-only model function and whose label lists no aarch64 target; an unlisted float check file; a compiler-rt helper in a check without a compiler-rt label; a compiler-rt label in a `Proofs/<Ex>` module whose translation (`Gen.lean` header, else `examples/<ex>/translate.args`) selects `ieee`; a generated header claiming correspondence other than `model`; any malformed or binary-correspondence label |
| `scripts/assumptions.sh` | yes | on the checked declaration graph: an unlabeled numerical theorem (`unlabeled-numerical-theorem`), a label that contradicts the graph rules above or an exempt theorem that is numerical (`float-semantics-mismatch`), and a label or exemption for an audited module that names no checked theorem or a non-numerical one (`stale-float-semantics-label`) |
| `python3 scripts/float-semantics.py check-report FILE...` | none | a report or receipt without a float-semantics summary, or with any `binary_correspondence`/`native_correspondence` other than `not_claimed`, `native_adequacy`/`source_correspondence` other than `not_attested`, or `correspondence` other than `model`. For an assumption report with its graph, it also recomputes every label and fails if one differs |

The source check is a fast pre-build filter: it reads declaration text, not the checked
environment. The audit gate is authoritative.

## Reports and receipts

`scripts/assumptions.py` adds `float_semantics` to every numerical theorem in the report.
A labeled theorem gets `scope: stated`, `label`, `semantics`, `targets`, and `zig_versions`
when the label is compiler-rt. A generated companion gets `scope: compiler-generated`. Both kinds
have `correspondence: model` and `binary_correspondence: not_claimed`. The top-level
`float_semantics` summary records the registry SHA256 and the number of stated theorems
per label. A label violation makes the audit fail (exit 1), like an unlisted axiom.

A proof receipt (`docs/proof-receipts.md`, receipt schema 2) copies that summary plus each
stated theorem's label. `assurance/float-semantics.json` and `scripts/float-semantics.py`
are guarded receipt inputs. Sealing and verification recompute the audit labels from the
graph and the registry. They fail if the receipt or audit differs from that recomputation,
or if either claims binary correspondence.

## What a label does not establish

A label says which semantics a theorem's statement concerns. It does not show that the
selected semantics matches a target. Target matching rests on the probe and differential
tests of the reference target (`docs/floats.md` §Reference target). Generated code records
its choice in its first-line profile (`float_semantics`, `correspondence: model`), and so
do project reports (`docs/project-workflow.md`). No gate here accepts a binary-equivalence
claim.

Regressions:

```sh
python3 -m unittest discover -s tests/roadmap/float-semantics -v
python3 scripts/float-semantics.py check
tests/roadmap/assurance/check.sh   # compiled fixture: unlabeled/mislabeled/binary controls
```
