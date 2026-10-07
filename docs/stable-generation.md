# Source maps and semantic fingerprints

`--source-map-json <path>` writes a sidecar next to the generated Lean file, for
example `Gen.source-map.json` beside `Gen.lean`. The flag never changes the
generated Lean text, so existing goldens and proofs stay byte-identical. It applies
to every emitted function, including memory, control flow, calls and recursion,
not only the scalar `--proof-api` slice (`docs/generated-code.md`).

```sh
lake exe air2lean AIR -o Gen.lean --namespace My --prefix my. \
  --source-map-json Gen.source-map.json
python3 scripts/semantic-fingerprints.py index Gen.source-map.json --generated Gen.lean
python3 scripts/semantic-fingerprints.py compare old.source-map.json new.source-map.json \
  --old-generated old/Gen.lean --new-generated new/Gen.lean --fail-on-change
```

## Sidecar (`air2lean-source-map-v1`)

The top level records the namespace, the same profile/float metadata as the
generated `-- air2lean-profile:` header, and the semantic options (spawn policy and
the model registry report, if any). Each function, in emission order, has:

| Field | Meaning |
| --- | --- |
| `source` | Identity after generic-instance renumbering (`Air2Lean/Air/Anon.lean`); the comparison key |
| `air_name`, `air_file` | The exporter's original identity and storage file (provenance only) |
| `definition` | The emitted Lean declaration in `namespace` |
| `proof_api` | `model`/`unfold` names when `--proof-api` emits an interface, else `null` |
| `callees` | Every function the body references: calls, function values, spawn targets |
| `canonical` | Params, return, type table, globals and body, debug instructions removed, instruction IDs renumbered `0, 1, …` in pre-order |
| `lines` | `[canonical instruction, dbg_stmt line]` pairs: a source map, not hashed |

## Fingerprints (`air2lean-semantic-fingerprint-v1`)

`local_sha256` is SHA-256 over canonical JSON of the function's `canonical` body,
the profile metadata and the options. The call graph is split into strongly
connected components. A component digest covers its members' local digests and
internal edges, plus the fingerprints of callees outside it. Each member's
`fingerprint` hashes the component digest with its own name. Hence:

* exporter instruction renumbering, shifted source lines, debug variables, storage
  filenames and unrelated functions or generic instances do not change it;
* a semantic change to a function changes its fingerprint, every member of its
  recursion group and every transitive caller, and nothing else;
* a different target profile, float semantics, spawn policy or model registry
  changes every fingerprint.

Callees without AIR (models, panic handlers) are listed as `boundaries` by name;
their contracts are covered by the options digest, not by a body.

## Proof-interface comparison

`compare` classifies each function:

| Class | Meaning |
| --- | --- |
| `unaffected` | Same fingerprint, same namespace, `definition` and `proof_api` names: downstream proofs can be reused |
| `invalidated` | Fingerprint changed: re-check proofs about it |
| `renamed` | Same fingerprint, different Lean names: proofs need their references updated |
| `added`, `removed` | Present on one side only |

`--fail-on-change` exits 1 if any old interface is invalidated, renamed or removed.
Malformed input exits 2.

## Limits

A fingerprint is an invalidation key, not a semantic-equivalence proof: equal
fingerprints mean the translated inputs agree after this normalization. It is
conservative. A reordered per-function type table, an AIR shape change between Zig
versions, or a renamed callee changes it even when meaning is preserved.
Fingerprints hash translator inputs, not the emitted Lean text: compare sidecars
produced by the same translator revision, since an `Emit.lean` change can alter
generated bodies without changing any fingerprint. `--generated` binds a sidecar to
its Lean file by profile header, namespace and declaration names, which rejects a
sidecar left from another run; it is not a content hash.
Generic-instance numbers come from `Anon.lean`'s first-use scan. A new instance of
an existing generic that is reached before the existing one renumbers it. Its
callers then report `invalidated`, and the instance itself appears as
`removed`/`added`. That is a reported break, not a silent one.

## Qualification

```sh
python3 -B tests/roadmap/stable-generation/test_fingerprints.py
python3 -B tests/roadmap/stable-generation/test_cli.py .lake/build/bin/air2lean
```

The first is offline: call-graph folding, recursion groups, boundaries,
classification and malformed sidecars. The second runs the built translator on
committed golden AIR (`recursion`, `pointers`, `errors`, `basic`, `variants`). It
checks that the flag leaves `Proofs/<Example>/Gen.lean` byte-identical. Renumbered IDs,
shifted lines, hashed storage names and an unrelated generic instance must keep every
fingerprint and interface name. One semantic change per example must invalidate
exactly the function, its recursion group and its callers. A second instance of an
already-referenced generic must keep the existing instance's identity.
