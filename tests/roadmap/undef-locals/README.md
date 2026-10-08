# `undefined` stores to locals

A store of a wholly `undefined` value to a local is never replaced by a default (`0`, `false`)
that a later read could observe (`docs/generated-code.md` §`undefined` operands):

| Local | Translation |
|---|---|
| the next access to the local in the same body overwrites all of it with a defined value (a `store`, an output-only asm output), and nothing before it can leave the body (`br`, `repeat` or a dispatch to an enclosing block or loop) | the `undefined` store is dead: the local stays a typed `Locals` field |
| no pointer in its type; each place is the local or a field of a non-`packed` struct, used only by `load`, `store`, `struct_field_ptr`, `dbg` | a **byte local**: a `Locals` field of type `Zig.Bytes T`, starting all undefined |
| any other local | a stack block (`escapingAllocs`): `Zig.storeUndef` |

In a byte local, a store writes the value's bytes at the place's offset (`Zig.Bytes.set`,
`Zig.Bytes.setUndef`), a read of a place decodes only its bytes (`Zig.Bytes.get`, throws
`.unspecified` if one is undefined). A load of the whole local whose uses only copy it (a
`struct_field_val` of a field, a store to memory or to a byte local, a `ret`) keeps its bytes:
a field read decodes only the field, a store to memory is `Zig.storeBytes`, and a function that
returns it returns `Zig.Bytes T` (a caller's call is the same kind of copy, or decodes the whole
value if it reads it otherwise).

The fixture is hand-written AIR in the exporter's schema (`air/0.16.0`) for:

```zig
const Pair = struct { a: u32, b: u32 };
fn mk() Pair { var s: Pair = undefined; s.a = 1; return s; }
export fn fieldA() u32 { var s: Pair = undefined; s.a = 1; return s.a; }
export fn fieldB() u32 { var s: Pair = undefined; s.a = 1; return s.b; }
export fn copyA() u32 { const s = mk(); return s.a; }
export fn copyB() u32 { const s = mk(); return s.b; }
export fn wholeRead() u32 { var x: u32 = undefined; return x +% 1; }
export fn writtenRead() u32 { var x: u32 = undefined; x = 5; return x +% 1; }
export fn condWrite(c: bool) u32 { var x: u32 = undefined; if (c) x = 5; return x +% 1; }
export fn branchOut(c: bool) u32 {
    var x: u32 = 0;
    b: { x = undefined; if (c) break :b; x = 5; }
    return x +% 1;
}
```

`UndefLocals/Gen.lean` is its retained translation. `UndefLocals/Proofs.lean` proves that a read
of an undefined field or local throws `.unspecified` (`fieldB`, `copyB`, `wholeRead`,
`condWrite false`, `branchOut true`: a `break` past the write), and that a read of a written
part returns it (`fieldA`, `copyA`, `writtenRead`, `condWrite true`, `branchOut false`), also
after a copy of the whole value (`mk`).

```sh
lake build air2lean ZigLean
bash tests/roadmap/undef-locals/check.sh
```
