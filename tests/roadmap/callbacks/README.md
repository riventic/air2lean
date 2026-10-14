# Callback and function-pointer contracts (E02)

`callbacks.zig` declares `extern fn ext_visit` and takes its address, in a vtable
(`ext_ops`) and as a callback; `async_cb.zig` calls a callback from a spawned thread.
`air/<version>` and `air-async/<version>` are their patched-compiler exports for Zig 0.17.0,
0.16.0, 0.15.2 and 0.14.1 (`provenance.json`). `registry-<version>.json` and
`registry-async-<version>.json` bind `extern:ext_visit` to `CallbackModel.lean`'s opaque
`visit` with the contract `contract` (assumed evidence, EXT-02/EXT-03; the async registry adds
the footprint that EXT-04 requires): given a writable `u32` context, a call fails only with a
stack overflow and its memory is a `u32` store to the context, up to the access log; given any
other context, it may throw `.illegal`. The proofs use the weaker callback contract
`visitCallback` that every target of the type meets (`contract_weaker`).

`check.sh` translates every version, keeps the 0.17.0 translations as `Callbacks/Gen.lean` and
`Callbacks/Async.lean`, checks `Callbacks/Proofs.lean` and `Callbacks/AsyncProofs.lean` against
them, requires the contract evidence to be the only assumption, and runs `test_cli.py`
(unbound address, template, signature and library mismatches, the footprint requirement in a
concurrent program). See docs/external-models.md §Binding call sites to contracts.

Re-export (from the repository root, per version):

```sh
ZIG_AIR_JSON_DIR=tests/roadmap/callbacks/air/0.17.0 ZIG_AIR_JSON_FILTER=callbacks. \
  "$(scripts/zig-air.sh 0.17.0)" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
  -target x86_64-linux -mcpu=baseline tests/roadmap/callbacks/callbacks.zig
```
