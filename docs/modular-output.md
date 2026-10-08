# Modular output and incremental checking

By default `air2lean` writes one Lean file. With `--split-modules <Module>` it writes
the same declarations as one Lean module per call group, so Lake rebuilds only the
modules an edit affects. The default single-file output does not change.

```sh
lake exe air2lean AIR -o Proofs/Ex/Gen.lean --namespace Ex --prefix ex. \
  --split-modules Proofs.Ex.Gen --source-map-json Gen.source-map.json
```

`<Module>` is the umbrella's module name. `-o` must end in its path
(`Proofs/Ex/Gen.lean`), because the parts import each other by module name. You cannot
combine the flag with `--model-registry-template`.

## Layout

| File | Module | Contents |
| --- | --- | --- |
| `Gen/Types.lean` | `<Module>.Types` | `import ZigLean` (and model imports), types, inline assembly, model adapters, globals (`mem0`, tag/error names), `Tgt` |
| `Gen/F_<decl>.lean` | `<Module>.F_<decl>` | One call group: a strongly connected component of the call graph (`callGroups`), with its locals, exits, loops and `--proof-api` facts |
| `Gen/Dispatch.lean` | `<Module>.Dispatch` | `dispatch`, only when the program spawns threads |
| `Gen.lean` | `<Module>` | The umbrella: the profile header, then an import of every part |
| `Gen.modules.json` | | The manifest (`air2lean-module-split-v1`) |

Each group module imports `<Module>.Types` and the modules of the groups it calls,
spawns or references as a function value. `Dispatch` imports the spawn targets' groups.
Every part uses the same `namespace`, and each part's text is the single-file text of
that piece. Concatenating the parts in manifest order gives the single-file output.
`import <Module>` therefore sees the same declarations, so existing proofs only need
their `import` to name the umbrella.

Module names come from the stable declaration names (`docs/stable-generation.md`).
`<decl>` is the smallest declaration name in the group, with characters other than
ASCII letters, digits and `_` replaced by `_`, truncated to 100 characters.
Names are unique ignoring case, for case-insensitive file systems: a collision gets
`_2`, `_3`, … in name order. A name changes only when the set of declarations changes.

The translator rewrites only parts whose text changed. It deletes stale `.lean` files
in `Gen/` that start with the generated marker `-- air2lean-split-part`, such as the
module of a removed function. Other files there are kept.

## Invalidation keys

```sh
python3 scripts/module-split.py keys Proofs/Ex/Gen.modules.json --source-map Gen.source-map.json
python3 scripts/module-split.py compare old/Gen.modules.json new/Gen.modules.json \
  --old-source-map old.source-map.json --new-source-map new.source-map.json
```

A module's key (`air2lean-module-keys-v1`) is SHA-256 over:

* its Lean text;
* the profile metadata;
* the semantic fingerprints of its functions (with a source map). These already cover
  the float semantics, spawn policy, model registry and callee fingerprints;
* the keys of the generated modules it imports.

`compare` reports `changed` modules (different text) and `invalidated` modules
(different key). `invalidated` is exactly the changed modules plus every module that
imports one of them, transitively: the set Lake rebuilds. With source maps, a semantic
change that leaves the text identical still invalidates.

An isolated edit to one function's body changes only its group's text. Its callers,
transitively, and the umbrella are invalidated, and nothing else is. Some edits change
shared content in `Types`: a new type, a global or a renumbered global block. These
invalidate every module, as in single-file output. A profile or option change
invalidates every key.

## Qualification

```sh
python3 -B tests/roadmap/modular-output/test_keys.py
python3 -B tests/roadmap/modular-output/test_cli.py .lake/build/bin/air2lean
lake env lean tests/roadmap/modular-output/Split.lean
python3 -B tests/roadmap/modular-output/lake_incremental.py .lake/build/bin/air2lean
```

* `test_keys.py` is offline. It checks key propagation, profile and fingerprint
  sensitivity, and rejection of malformed manifests, import cycles, escaping paths and
  mismatched source maps.
* `test_cli.py` runs the translator on golden AIR (`recursion`, `pointers`, `errors`,
  `basic`, `layout`, `threads`). It checks four things:
  * Without the flag, `Proofs/<Example>/Gen.lean` is byte-identical.
  * The split holds the single file's declarations in order.
  * Renumbered, hashed input gives byte-identical modules.
  * One semantic edit changes exactly the edited group's text. The invalidated set
    equals both its import closure and the modules of the functions whose fingerprints
    changed.
* `Split.lean` checks at the Lean API level that the parts reassemble the single file
  and that each group imports exactly its callees' groups.
* `lake_incremental.py` builds a scratch Lake package. The package holds the layout
  example split into 53 modules, a copy of `Proofs/Layout/Proofs.lean` importing the
  umbrella, and `Proofs/Layout/Mem.lean` importing only the groups it uses. The script
  then:
  1. builds the package cold;
  2. edits `layout.digit` (flips a comparison) and rebuilds warm;
  3. deletes the build and rebuilds cold.

  The warm build rebuilt only `F_digit`, its caller `F_bumpDigit`, the umbrella and
  the proofs importing the umbrella (4 of 55 modules). `Mem` was not rebuilt. Every
  warm `.olean` was byte-identical to the cold build's, and every proof built both
  times. Run it under `scripts/build-guard.py`.
