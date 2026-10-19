# Assurance extractor runtime identity

An offline mutation control against main `0be4c97205f474ca2140cf256501a522818878ec`
found that `prepare_tool` reported `cache_reused: true` after changing only the bytes of
`lib/libleanshared.so`. The executable stubs, source, pin text, Lake configuration,
compiled extractor and Lake trace remained unchanged. The library's size and mtime were
also restored. The source/trace key therefore did not identify the installed runtime.
This demonstrates stale cache admission; it is not a kernel counterexample.

The regression uses the existing injectable Lake runner and fails on that original
implementation at the changed-library reuse assertion. With runtime byte binding it
passes and requests a fresh extractor build. Separate controls change installed
`.olean`, `.olean.private`, `.olean.server`, `.ir` and `.ir.sig` inputs while keeping
the executable stubs fixed; they also exercise aliases, missing targets, cycles and a
runtime mutation during preparation. A trace missing only the runtime field is rejected.

The extractor-sidecar correction binds only extractor preparation. Replay-cache import closures,
project compiled search roots, configured library sources and witness inputs are
separate boundaries; this audit does not claim those are complete or enable any
premise reduction. The implementation derives from the runtime/IR work preserved in
parked PR [#418](https://github.com/riventic/air2lean/pull/418), commits `4300b30a2`
and `4a56a4c75`, adapted to current main's existing `prepare_tool` API.

Takeover review additionally identified caller path overlays and empty sysroot output.
`theorem_universe.audit_modules` and registered witness compilation intentionally pass
private libraries via `LEAN_PATH`, so rejecting that variable would break checked callers.
The binding instead includes their ordered loaded-input trees and brackets both preparation
and actual extraction. Fixed-artifact controls mutate only a private companion or its
presence/order; separate controls mutate during each phase and require rejection. An
unsupported caller sysroot replacement and an empty Lake sysroot are rejected explicitly.

## Installed-runtime replay and report admission

Source inspection of main `024dfaf4bad67aef99c39887aed35c39ef9e5136` identifies two remaining
failure scenarios. First, keep the checker and selected project `.olean` bytes fixed after a
successful cached replay, then change an installed standard `.olean`, `.ir.sig` or shared
library. The existing cache checks only checker/project digests, so it can still report reuse.
Second, keep the saved report and every recorded project artifact fixed while changing that
installed input. `verify_fresh` checks the project rows and revision, but not the extractor's
recorded installed-runtime identity, so that mutation can remain acceptable. These are
source-derived cache/input-binding findings, not kernel-checked counterexamples.

The separate correction reuses `toolchain_runtime_sha256` in the existing replay/cache and
freshness path. The extractor identity must match when replay starts, the installed digest
must still match after the batch, and existing cache records require that same identity.
Freshness carries the root/digest and report verification recomputes the actual installed
bytes, requiring agreement with the extractor binding. Missing old bindings cannot license
reuse or report admission. There is no new cache, collector or expanded reuse eligibility.

Prepared controls preserve executable/project artifact/report bytes and restore size/mtime
while mutating installed inputs; other cases remove only a binding or mutate during replay
and require the previous cache record to remain untouched. Wiring checks connect the existing
extractor identity to replay/freshness. These new controls have not yet executed. Complete
project/private import closure, source/compiler correspondence, registered witnesses and NN
qualification remain separate open boundaries. No premise reduction is enabled.
