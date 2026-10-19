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
