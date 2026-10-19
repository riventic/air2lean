# Assurance extractor source snapshot

An offline control against main `0be4c97205f474ca2140cf256501a522818878ec` changes only
`tools/Helper.lean`, imported by the extractor fixture. Pin/configuration, extractor source,
compiled artifact and Lake trace bytes stay fixed; the helper keeps the
same size and restored mtime. Main still reports `cache_reused: true`. A configured-library
source fingerprint makes that trace stale. This is a cache identity finding, not a kernel
counterexample; the test uses an injectable stand-in for Lake's dependency validation.

Controls also cover added/removed unimported helpers, source-file alias target changes,
missing source fingerprints, and mutations during preparation or extraction. The inventory
includes root `.lean` files and the existing Lake `roots` configuration. Directory aliases
and nondefault package/library `srcDir` with a decoy old directory are rejected explicitly.

Source snapshot validity is distinct from compiled-artifact validity: a changed unrelated
source snapshot refreshes the trace without forcibly deleting the extractor. Lake always
rechecks actual dependencies. This is the configured-library portion of parked PR
[#418](https://github.com/riventic/air2lean/pull/418), commit `e6a16c1ee`, independently based
on current main. It does not authenticate actual witness import headers or completed replay
reuse, and it enables no premise reduction. Those preserved boundaries require separate
integration and controls.
