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
| `receipt` | only with `--receipt ATTEMPT`: its `receipt.json`, `plan.json`, `audit.json`, `after.json` | changed proof receipt |

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
reproducible from `HEAD`, so `check-manifest` rejects it unless `--allow-dirty` is given. For
the same reason it rejects a chained proof receipt sealed over a dirty tree
(`tree.dirty_allowed`, [proof-receipts.md](proof-receipts.md)) unless `--allow-dirty` is given.

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
