# Module identity (B1)

A fully qualified Zig name (`util.helper`) is a path inside one module. The root module of
`mods/` and its dependency module `other` both have a `util.zig` with a `helper`:
`entry(x) = util.helper(x) +% other.util.helper(x)`, which Zig computes as `(x+1) + 3x`.
Before this fix, the exporter wrote one `util.helper.json` for both functions, and the
translator produced a Lean `entry` that computes `3x + 3x`.

`check.sh` (CI step "Module identity regression (B1)") dumps the fixture with a patched
compiler and checks that the exporter never writes two declarations under one identity and
that the translator rejects two input files with one identity
([AIR JSON §Identity](../../../docs/air-json.md#identity)).

```sh
AIR2LEAN_ZIG_AIR=zig-air-0.16.0/bin/zig bash tests/roadmap/module-identity/check.sh
```
