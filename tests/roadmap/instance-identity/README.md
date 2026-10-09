# Content-addressed instance identity (S1.1)

The compiler names a generic instance `<generic>__anon_<n>`, with a number that depends on the
compilation. The exporter writes a content-addressed `instance_key` next to it, and the
translator names the instance `<generic>__anon_<key[:12]>`
([AIR JSON §Instances](../../../docs/air-json.md#instances)).

`check.sh` (CI step "Instance identity (S1.1)", every Zig version) exports three programs with a
patched compiler and translates them:

| Program | Role |
|---|---|
| `a.zig` | One function per instantiation of the generics in `lib.zig` and of `mem.Allocator.dupe`: comptime types, integers, an enum, strings, functions, a struct value, a pointer to a declaration, and `anytype` parameters. |
| `a_reordered.zig` | The same functions, declared and referenced in the opposite order. |
| `b.zig` | Other instantiations first, then some of `a.zig`'s, under the same function names. |

`check_instances.py` then checks:

* every instance, and every reference to it, has a valid key, one per compiler name;
* one function name (one instantiation) has one key in every program and source order, and two
  instantiations never share a key, although the compiler names differ between the programs;
* one key is one instance body (the AIR without compiler names) in every program;
* the translation names each instance by its key, and a shared instance has the same Lean
  definition in every program.

`Instances.lean` checks the translator side without a compiler: keyed names do not depend on
compiler numbers or input order, a legacy export is numbered as before, and a name with another
instance's key, a malformed key and two keys with one name are rejected.

```sh
lake env lean tests/roadmap/instance-identity/Instances.lean
AIR2LEAN_ZIG_AIR=zig-air-0.16.0/bin/zig bash tests/roadmap/instance-identity/check.sh
```
