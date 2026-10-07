This directory covers roadmap L13 (volatile and device effects). The contract and the
exporter audit are in [`docs/volatile-effects.md`](../../../docs/volatile-effects.md).

`test_cli.py` runs the built translator on hand-written AIR. The fixtures use the exporter's
pointer schema: every `ptr` type entry carries `volatile`. Each case runs for Zig 0.14.1,
0.15.2 and 0.16.0.

* These are rejected with `VOLATILE_ACCESS` (phase `check`, category `unsupported_semantics`)
  and no generic `INSTRUCTION_FAILURE` for the same instruction:
  * volatile loads, stores, atomics, slice items, and a 0.16.0 `slice_elem_ptr`/`load` pair;
  * a read-only local copy read through `*const volatile`, which canonicalization must not
    forward;
  * `@volatileCast` away and `@intFromPtr`;
  * a volatile slice passed to a built-in std model.
* These non-volatile controls are accepted: the plain load, store and local copy, and
  `keep_volatile`, which only forms a volatile pointer value, like the committed
  `layout.asVolatile` golden.
* Ordinary translation fails closed and leaves its output file unchanged.
* The model registry hook is tested. A binding with a direct volatile pointer parameter is
  accepted only with that parameter in `footprint.writes`; a read footprint, `preserves`, and a
  nested volatile pointer are rejected.

`volatile_effects.zig` is the real-export fixture. `--export-dir` checks a fresh export of it:
every pointer type has a boolean `volatile`, each accessing function is rejected with
`VOLATILE_ACCESS`, and `keepVolatile` is checked. The export needs the patched compiler; see
`docs/volatile-effects.md` §Commands.

```sh
python3 tests/roadmap/volatile-effects/test_cli.py --self-test
python3 tests/roadmap/volatile-effects/test_cli.py "$PWD/.lake/build/bin/air2lean"
```
