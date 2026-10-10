# Illegal-behaviour fixtures

Evidence for [docs/illegal-behavior.md](../../../docs/illegal-behavior.md): every op's model
checks its own illegal-behaviour precondition and throws `.illegal`, with or without a Sema
safety check before it.

| File | Content |
| --- | --- |
| `ib.zig`, `air/`, `Gen.lean` | functions that reach unchecked illegal behaviour, their 0.16.0 ReleaseSafe AIR (`-target x86_64-linux -mcpu=baseline`) and its retained translation |
| `Cases.lean` | the generated functions on each input class: `.illegal`, and a legal control row |
| `Runtime.lean` | the runtime ops (`Zig.Float.divExactTrunc`, `Zig.memcpy`, `Zig.checkIndex`, `Zig.checkAddr`, …) directly |
| `mutations.py` | emitter-output mutants that drop one op's check; `Cases.lean` must reject each |
| `probe.zig`, `probe-air/`, `expected.json`, `probes.py` | IB the translator rejects, and the documented gaps, each translated alone |
| `forlen.zig`, `for-air/<version>/` | `for` over a slice and a range or an array without safety, exported by every supported version: each translation has the patched Sema's length check (`.illegal`), and an export without `unchecked_ib` is rejected (`expected.json`) |
| `native.zig`, `native/` | what ReleaseSafe and ReleaseFast builds return for the same input classes |

```sh
tests/roadmap/illegal-behavior/check.sh
# optional: AIR2LEAN_ZIG_AIR=<patched 0.16.0 zig> re-exports the AIR; AIR2LEAN_ZIG=<stock 0.16.0 zig> reruns native.zig
```

The native rows are illegal behaviour, so the builds may disagree with each other (for
example a float `@divExact` of `2^-1074` by `1` is `0` in ReleaseSafe and `2^-1074` in
ReleaseFast). The model gives `.illegal` for every one, so the differential harness never
compares them: it counts them as `illegal` exclusions in every optimize mode.
