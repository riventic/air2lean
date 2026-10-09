# Tagged unions with a `noreturn` variant (spike blocker B1)

A union field of type `noreturn` can never be active: the variant has no values, adds no payload
bytes, and Zig code that activates it is unreachable. `std.Io.Terminal.Mode` (0.16.0) has one off
Windows (`windows_api: noreturn`), and it reaches `Io.Threaded` through `stderr_mode`
(`docs/thread-io-translation.md` on the spike branch).

The translator (`uninhabitedTy` in `Air2Lean/Air/Op.lean`):

* gives the union an `inductive` without the variant: no constructor and no `get_f`/`modify_f`/
  `setTag_f` accessors. The tag enum keeps every value that the exporter reports;
* computes the memory layout from the tag and the inhabited fields only (`modelLayout`,
  `unionOffsets`), and compares it with the exporter's `abi_size`/`abi_align`, also for a
  tagged union inside another type in memory. The memory decoder throws `.illegal` for the
  variant's tag;
* rejects (fail closed) every instruction that activates, reads or points to the variant
  (`union_init`, `set_union_tag`, `struct_field_val`, `struct_field_ptr`), a union constant
  whose active variant it is, a union whose fields are all `noreturn` and an untagged union
  with one.

`noreturn_variants.zig` has a `union(enum) { a: u8, b: noreturn, c: u32 }`, a union with an
explicit, non-contiguous tag enum (`x = 3, gone = 7, y = 9`), a one-bit tag with the `noreturn`
variant first, and `std.Io.Terminal.Mode` (on 0.15.2, which has no `std.Io.Terminal`, a union of
the same shape), by value, as locals and in memory (pointers, a struct field). `air/0.16.0` and
`air/0.15.2` are its fresh exports with the patched compilers; `NoreturnVariants/Gen.lean` is the
retained 0.16.0 translation. `NoreturnVariants/Proofs.lean` proves (`decide +kernel`), for both
versions' translations, the values that `native.zig` checks on a native build of the same source,
and that the decoder rejects the `noreturn` tag.

`test_cli.py` checks that the CLI and `--diagnostics-json` reject, with the output untouched:
each instruction kind above and a union constant on the `noreturn` variant (edits of the 0.16.0
export), a union with only `noreturn` fields, an exporter size of `U` or `Io.Terminal.Mode` that
differs from the model's (also for `Mode` inside `Holder`, whose own size agrees), and
`reject.zig`'s exports (`air-reject/`). 0.16.0 stores a union with one possible active variant
without a tag (`One`: 2 bytes, the model's tagged layout 4), alone and inside a struct: both are
rejected. 0.15.2 stores the tag: `One` inside a struct translates, but its export of `memOne`
gives `One` no layout, which is rejected.

```sh
lake build ZigLean air2lean
bash tests/roadmap/noreturn-variants/check.sh
```

Refresh the fixture (patched compilers under `/opt/dev/air2lean-build`, stock compilers for
`native.zig`) and then `provenance.json`'s hashes:

```sh
cd tests/roadmap/noreturn-variants
for v in 0.16.0 0.15.2; do
  ZIG_AIR_JSON_DIR=air/$v ZIG_AIR_JSON_FILTER=noreturn_variants. zig-air-$v/bin/zig build-obj \
    -fno-emit-bin -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline noreturn_variants.zig
  ZIG_AIR_JSON_DIR=air-reject/$v ZIG_AIR_JSON_FILTER=reject. zig-air-$v/bin/zig build-obj \
    -fno-emit-bin -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline reject.zig
  zig-$v/zig test native.zig
done
```

Scope: `noreturn` is the only uninhabited type recognized (not, for example, an empty error set
or a struct with a `noreturn` field). A union with one possible active variant in memory on
0.16.0 is rejected (above), not modelled.
