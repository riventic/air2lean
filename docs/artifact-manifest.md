# Artifact manifests (I07)

An artifact manifest names exactly what one example's proofs are about and lets a reviewer
detect, link by link, when a retained proof no longer matches the bytes in the tree. It
complements the [proof receipt](proof-receipts.md): the receipt binds a guarded compiled
theorem audit; the manifest chains that receipt (optionally) to the Zig source, AIR, generated
Lean, compiler patch, runtime model, toolchain, build profile and theorem names.

The format is `air2lean-artifact-manifest-v1` (`schema: 1` inside that format). It is a
separate document: proof receipt schema 1 (`receipt.json`) and its `prepare`/`worker`/`seal`/
`verify` commands are unchanged. Feeding a receipt to `check-manifest` reports `invalid`.

## Record

```sh
python3 scripts/proof-receipt.py manifest "$OUT/basic.json" --example basic --zig-version 0.16.0
```

`scripts/artifact-manifest.py manifest|check-manifest ...` is the same command. Defaults for
`--example EX --zig-version V` are shown below; each can be overridden (`--source` and `--proof`
repeat). Paths may be repository-relative or absolute (for example a fresh `AIR2LEAN_OUT_DIR`
export or `.lake/check-reports` file). The output path must not exist; it is never overwritten.

| Link (chain order) | Bytes / value hashed | Stale diagnosis |
| --- | --- | --- |
| `source` | `--source` (default `examples/EX/`): tracked plus untracked-unignored files | wrong source |
| `compiler_patch` | `zig-patch/versions.toml` + parsed pin for V, `zig-patch/V/hook.patch`, `zig-patch/air-json/`, `build.sh`, `lock.sh` | changed compiler patch |
| `air` | `--air-dir` (default `tests/golden/V/EX/air/`) `*.json` | changed AIR |
| `profile` | the single validated profile shared by all AIR files and any `Gen.lean` header, its `profile_sha256`, Zig version and header scope | wrong profile |
| `translator` | `Air2Lean.lean`, `Air2Lean/`, `scripts/check.sh`, `translate.sh`, `normalize-generated.py`, `normalize-air.py` | changed translator |
| `generated` | `--generated` (default `Proofs/Ex/Gen.lean`) raw bytes plus body hash without the profile header | edited or regenerated Gen.lean |
| `runtime` | `ZigLean.lean`, `ZigLean/` | changed runtime semantics |
| `toolchain` | `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | changed toolchain/build configuration |
| `proofs` | `--proof` (default `Proofs/Ex/*.lean` except `Gen.lean`) | changed proof sources |
| `theorems` | namespace-qualified theorem names scanned from the proof files; with `--audit` or `--receipt`, also the compiled audit's theorem names, statuses and non-allowed names for those modules | changed theorem inventory |
| `receipt` | only with `--receipt ATTEMPT`: its `receipt.json`, `plan.json`, `audit.json` and `after.json` when present (`receipt.json` hash-binds the rest, so the multi-MB `after.json` may be omitted from a committed copy). Receipt schema 1 and 2 are both just hashed bytes. A receipt inside the repository is recorded repository-relative | changed proof receipt |
| `native` | only with `--native-binary`: stock-Zig build of the same source; target, mode, cpu, compiler version, compiler sha256, binary sha256, plus the current `source` and `profile` link digests and whether target/mode/Zig version agree with the proved profile | wrong native binary |

Each link digest is SHA-256 over canonical JSON of its `{files, value}`; each chain entry
is `sha256(previous || link || digest)` starting from the format name. A last `inputs_provenance`
entry binds the canonical `{inputs, provenance}`, and its chain value is `manifest_sha256`. Editing
any recorded hash, value, input, provenance field or chain entry, or dropping a link the inputs
imply, makes the manifest `invalid` (this detects edits; it does not authenticate the recorder).

Recording refuses inconsistent inputs instead of hiding them: AIR files with different profiles,
an AIR `zig_version` different from `--zig-version`, a `Gen.lean` profile header that differs from
the AIR profile, a missing pin, or any unreadable link. Schema < 12 AIR records the explicit
`legacy-abi64-le` profile with `unverified` target fields and `legacy-or-unannotated` scope.

### Dirty-tree provenance

`provenance` records `HEAD`, whether any tracked file is dirty, `modified_link_paths` (any path
under a link's named inputs that differs from `HEAD`, staged or not, including deletions),
`untracked_link_paths` (hashed link files not in the index) and `external_link_paths` (outside the
repository). `status` is `dirty` if any link path is modified, deleted or untracked. Content hashes still describe the recorded bytes, but such a manifest is not
reproducible from `HEAD`, so `check-manifest` rejects it unless `--allow-dirty` is given.

### Native-binary identity

```sh
... manifest OUT.json --example EX --zig-version V \
  --native-binary BIN --native-compiler STOCK_ZIG --native-compiler-version V \
  --native-target x86_64-linux --native-mode ReleaseSafe --native-cpu baseline
```

The binary itself is not stored, only its sha256. The compiler must be a stock Zig (a sibling
`zig-unlocked`, the AIR-only patched compiler, is refused). Build with `-fstrip`: otherwise the
debug info embeds a random cache path and the hash is not reproducible. At check time
`--native-binary BIN` (and optionally `--native-compiler`) ties a diff-tested binary to the
manifest: a different binary or compiler, or a source/profile change, makes `native` stale;
`--require-native-binary` fails when none is supplied; a build whose target, mode or Zig version
differs from the proved profile is a problem unless `--allow-native-mismatch`. This records which
binary was built from this source; it does not prove the binary matches the Lean model.

## Check

```sh
python3 scripts/proof-receipt.py check-manifest "$OUT/basic.json" \
  [--expect source=SHA256] [--expect profile=PROFILE_SHA256] [--expect zig_version=0.16.0] \
  [--allow-dirty] [--verify-receipt]
```

The JSON report lists every link with `status`, recorded and current digests and, when
stale, its diagnosis and `changed`/`added`/`removed` paths, `value_changed`, and for theorems
`theorems_added`/`theorems_removed`. `stale_links` names the failing links; `problems` lists
dirty provenance and failed expectations. Exit 0 means `status: current`; exit 2 means
`stale`, `invalid` or unavailable (stderr summarizes). Typical outcomes:

* edited `examples/EX/*.zig` -> `source`;
* re-export for another build mode/target -> `air` + `profile` (+ `generated` once regenerated);
  AIR changed but `Gen.lean` header not -> `profile` error "Gen.lean profile header differs";
* hand-edited or regenerated `Gen.lean` -> `generated`;
* changed `ZigLean/` -> `runtime`; changed hook/exporter/pin -> `compiler_patch`;
* renamed/added/removed theorem -> `proofs` + `theorems` with the names;
* `--expect profile=X` for a profile the manifest was not recorded with -> "proof is for another profile".

`--expect` lets a reviewer pin the source, profile, Zig version or any link digest they intend
to accept, so a manifest for another source or profile cannot be passed off. `--verify-receipt`
additionally runs the existing receipt `verify` on a chained attempt (needs that toolchain).

## What it establishes and what it does not

A current manifest means the recorded bytes are still present. It does **not** rebuild AIR from
source, rerun the translator, recheck proofs, authenticate anyone, or prove source-to-AIR,
AIR-to-Lean or Lean-to-native correspondence: those links are recorded identities of a run, not
re-derived relations. The source-scan theorem list is lexical (not compiler-checked); bind a
receipt or audit for the compiled inventory. Directory links include tracked and
untracked-unignored files, so new scratch files in a linked directory make it stale.

Offline fixture regressions (no Zig/Lake/Lean):

```sh
python3 tests/roadmap/artifact-manifest/test_manifest.py
```

## Committed receipt-chained fixtures

Two fixtures are committed, each a genuine fresh run chaining every link including the `native` build:

| `--fixture` | Directory | Source | Target | Proofs |
| --- | --- | --- | --- | --- |
| `provenance` (default) | `assurance/provenance/` | `src/provenance.zig` (`add`, `double`) | x86_64-linux musl, ReleaseSafe | `Proofs/Provenance/` |
| `gap` | `assurance/provenance-gap/` | `src/gap.zig` (`gap`, `within`) | aarch64-macos, ReleaseSafe | `Proofs/ProvenanceGap/` |

Each holds schema-12 AIR from the patched 0.16.0 AIR-only compiler (`air/`), the generated
`Gen.lean` (with profile header, byte-identical to translator output: `scripts/gen-integrity.py`),
proofs, a schema-2 proof receipt (`receipt/`, without `after.json`), `manifest.json` and
`pins.json` (reviewer pins). The two differ in target, ABI, CPU features and theorem shapes, so
neither a profile nor a theorem set is special-cased.

```sh
python3 scripts/provenance-evidence.py [--fixture NAME|all] check [--strict] [--native-binary BIN]   # offline, CI
python3 scripts/provenance-evidence.py [--fixture NAME|all] replay [--strict]                        # offline, CI
python3 tests/roadmap/artifact-manifest/test_fixture.py                                              # edit-one-link and replay on copies
AIR2LEAN_BUILD_LOCK=... python3 scripts/provenance-evidence.py --fixture NAME regenerate WORKDIR \
  --zig-air PATCHED_ZIG --stock-zig STOCK_ZIG                                                        # heavy, guarded
```

`check` requires every example-local link to be current; drift of the repository-wide links
(compiler patch, translator, runtime, toolchain) is reported as `aged` and fails only with `--strict`.
`regenerate` builds the translator, re-exports with the fixture's target, translates, rebuilds the
native binary and a guarded receipt, requires byte-identical AIR, Gen.lean and (for the same stock
compiler) binary, then strictly checks a fresh manifest. To refresh a fixture after an intentional
change: commit the example/Gen/proofs (and new AIR), run `regenerate WORKDIR --refresh` on the
clean, committed tree (`--refresh` skips the comparison with the committed audit and manifest; a
new fixture needs it), then

```sh
python3 scripts/provenance-evidence.py --fixture NAME install WORKDIR                        # path-redacted receipt copy
# commit the receipt
python3 scripts/provenance-evidence.py --fixture NAME record WORKDIR --stock-zig STOCK_ZIG   # manifest + pins.json
# commit the manifest
```

`install` verifies the sealed receipt against the whole tracked tree, so commit everything before
it and change nothing tracked until it has run. It copies `receipt.json`, `plan.json` and
`audit.json` with every host-local absolute path replaced: the attempt directory by `<attempt>`,
the checkout by `<repo>`, the home directory by `~` and any other absolute path by
`<host>/<basename>`, and refuses a copy that still contains one. Its `receipt.json` artifact hashes
are those of the unredacted files of the run (the copy's own bytes are what the manifest chains).

### Receipt replay and staleness

`manifest.json` hashes the translator, the runtime and the toolchain pins, so it goes stale whenever
ZigLean, Air2Lean, the translation scripts or the pins change: record both manifests last on a branch
and again after merges that touch those paths (`check` reports this as `aged`, not as a failure).

A committed receipt is replayed by `replay` without its revision (a pushed integration commit that
history rewrites or squash merges can remove) and without its attempt directory:

1. `plan.json` records the sha256 of every tracked source at the run. `replay` finds the Lean import
   closure of the proved module in the current tree and compares each closure file (plus
   `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `assurance/policy.json` and
   `tools/Assurance.lean`) with those hashes. A changed file under the fixture's own `Proofs/<Name>/`
   is `stale`; a changed shared file (ZigLean, toolchain pins, policy) is `aged` and fails only with
   `--strict`. Files outside the closure (translator, scripts) do not matter to the audited theorems.
2. The audit must have `status: pass`, no violations, a checked build, the tree's Lean toolchain and,
   for the proved module, exactly the theorem declarations the manifest chained (all allowed).
3. Manifest, receipt, plan and audit are scanned for host-local absolute paths.
4. `replay --rerun WORKDIR` (heavy, guarded) additionally reruns the proof receipt on the current
   tree and requires the same compiled theorem audit; it refuses to run on a `stale` receipt.

`replay` does not verify the sealed receipt itself (the unredacted files and `after.json` are not
committed, and `receipt.json` hash-binds the unredacted bytes) and authenticates no one: it
establishes that the receipt's claim concerns the bytes in the tree now, or names the files that
differ. Binary-to-model correspondence stays out of scope (the `native` link is identity only).
