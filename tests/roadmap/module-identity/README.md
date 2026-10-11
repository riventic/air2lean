# Module identity (B1)

A fully qualified Zig name (`util.helper`) is a path inside one module
([AIR JSON §Identity](../../../docs/air-json.md#identity)). Before the fix, the exporter and
the translator identified functions and types by that name alone.

`check.sh` (CI step "Module identity regression (B1)", every Zig version) dumps these fixtures
with a patched compiler:

| Fixture | Checks |
|---|---|
| `mods/` | The root module and its dependency module `other` both have a `util.zig` with a `helper`; `entry(x) = util.helper(x) +% other.util.helper(x)`. Before the fix, the exporter wrote one `util.helper.json` and the generated `entry` computed `3x + 3x`. Now each function has its own file and module, and the generated `entry` computes Zig's `(x+1) + 3x`: checked in Lean (`#guard`) and natively (`native_test.zig`, with `AIR2LEAN_ZIG_NATIVE`). |
| `thread/` | A user `Thread.zig` (struct `Thread`, function `Thread.spawn`) is user code: without its AIR the call is rejected, with it the struct and function are translated (`root_Thread`, `root_Thread_spawn`) and computed like Zig. Never the std `Thread` model. |
| `collide/` | A root `ascii.isDigit` and std's `ascii.isDigit` would share the file `ascii.isDigit.json`: the exporter stops with exit status 1. |
| (copy of `mods/`) | Two input files that claim one identity: the translator rejects them. |

```sh
AIR2LEAN_ZIG_AIR=zig-air-0.16.0/bin/zig AIR2LEAN_ZIG_NATIVE=host-zig/zig \
  bash tests/roadmap/module-identity/check.sh
```

The trust-chain audit cases `std-name-spoof` and `std-type-spoof`
(`tests/roadmap/architecture-audit/trust-chain/check.py --require-fixed`) cover the same
binding from committed exports.
