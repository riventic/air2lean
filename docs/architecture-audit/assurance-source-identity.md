# Assurance extractor source snapshot

An offline control against main `0be4c97205f474ca2140cf256501a522818878ec` changes only
`tools/Helper.lean`, imported by the extractor fixture. Pin/configuration, extractor source,
compiled artifact and Lake trace bytes stay fixed; the helper keeps the
same size and restored mtime. Main still reports `cache_reused: true`. A configured-library
source fingerprint makes that trace stale. This is a cache identity finding, not a kernel
counterexample; the test uses an injectable stand-in for Lake's dependency validation.

The original controls covered added/removed helpers, aliases, missing bindings and phase
mutations. The post-batch-C implementation now feeds configured library inputs to #469's
existing `input_tree_records`; it removes the duplicate walker and source-hash function.
The same traversal covers file and directory link identities/target bytes, and rejects broken
links and cycles. Source selection includes root `.lean` files and overapproximates each glob
by its first module component. Nondefault package/library `srcDir` rejects even with a decoy
old source tree. Configuration, optional manifest absence, and the selected root are bound.
The causal controls also cover canonical selected-root handling, including relative caller paths.

Source snapshot validity is distinct from compiled-artifact validity: a changed unrelated
source snapshot refreshes the trace without forcibly deleting the extractor. Lake always
rechecks actual dependencies. This is the configured-library portion of parked PR
[#418](https://github.com/riventic/air2lean/pull/418), commit `e6a16c1ee`, independently based
on current main. It does not authenticate actual witness import headers or completed replay
reuse, and it enables no premise reduction. Those preserved boundaries require separate
integration and controls.

## Compiler-owned non-gated Units

A real control on main `b33c931b22a177de154003a63dca541bc5005521` compiles the existing
`IdleLoop.Total` Unit and its local closure through `compile_all`, then audits it through
`audit_modules`. The original report passes policy and kernel replay. Changing only the
original `Total.lean` source while keeping the report, compiled artifacts, runtime and HEAD
fixed still passes `verify_fresh(..., allow_dirty=True)`: its private artifact row has
`source: null`. Restoring the source gives another passing admission. This establishes a
missing source-correspondence check, not an invalid Lean theorem. The same report's actual
headers include local imports not selected by its declaration dependency graph.

The correction belongs in that same compiler-owned audit flow. Snapshot original and staged
compiler inputs before compilation; derive their paths from the existing Unit plan. Capture
each successful compiler output and loaded companions immediately, then keep their identities
and the effective ordered lookup roots stable through extraction and replay. Traverse actual
import headers, including unused imports, against the owned Unit closure, canonical
trace-checked Lake artifacts and the pinned standard installation. Missing, shadowed,
ambiguous or unowned private inputs refuse. Saved reports for known non-gated Units require
the matching source/output context; stripping a scope label cannot remove that obligation.
The existing registered-witness producer's canonical source/output binding remains distinct.

The existing per-run replay cache remains the mechanism. Eligibility requires a complete
canonical Lake/standard import closure; private, missing or cyclic closure inputs replay
freshly. Existing byte fingerprints cover compiled companions, and final input validation
precedes cache publication. Caller `--sources` remains declaration-classification metadata.
This slice supplies no generated-producer authority, witness/gate qualification, NN census
qualification or premise reduction. Synthetic controls exercise these admission paths;
actual corrected Unit execution must be recorded separately from the historical baseline.
