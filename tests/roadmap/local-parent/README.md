This is the bounded local-place part of roadmap L11. A local `@fieldParentPtr` removes
one proven terminal field of an `auto` or `extern` struct, preserving the allocation root
and preceding path. Same-pointee qualifier casts retain that path. Loads and stores through
the recovered parent use the original local, including nested container recovery. A
recovered pointer used as a value still causes normal stack-memory escape lowering.

Recovery requires the exact container type, field index and field child type. Packed
structs, union parents, bit-pointers, slice-field recovery, pointee reinterpretation and
unproven paths are rejected. Pointer operands/results must be single, nonnullable pointers;
recovery cannot discard const or volatile qualifiers. The existing memory-pointer lowering
still subtracts an exported field offset. A local whose place escapes, for example through
an array element inside a struct (`&bag.items[i].b`), is a stack block: nested fields and
parents of any depth use that memory lowering in the original block. `ZigLean/Mem/Parent.lean`
proves that memory recovery gives the container pointer (`Ptr.parent_field`, nested
`Ptr.parent_path`/`Ptr.parents_path`, `Ptr.parent_elem_field`) and that writes through the
recovered parent and through the field pointer are visible through each other
(`parent_store_visible`, `field_store_visible`). `Proofs.lean` proves that every accepted
local recovery, of any depth and types, removes exactly the terminal step of the place path
(`localParentPath_pop`, `localParentPath_push`): it keeps the root and the container path,
so it aliases the container. Constant indirect calls are in
[`../indirect-calls/README.md`](../indirect-calls/README.md). This slice does not qualify
packed local field access or pointer arithmetic on local places.

Run from the repository root, under the root's serialized compiler guard:

```sh
AIR2LEAN_LOCAL_PARENT_ZIG_VERSION=0.16.0 \
AIR2LEAN_LOCAL_PARENT_ZIG_AIR=/absolute/path/to/patched-0.16.0/zig \
AIR2LEAN_LOCAL_PARENT_ZIG_STOCK=/absolute/path/to/stock-0.16.0/zig \
LEAN_NUM_THREADS=1 bash tests/roadmap/local-parent/check.sh
```

`--synthetic-only` runs the parser/checker/emitter positives and negatives (including two
escaped array-element-in-struct recoveries, `arrayItem` and `arrayFirst`, decided against the
emitted memory code), kernel reduction proofs and the general recovery theorems, an executable first-occurrence cache lookup regression, elaborated generated behavior
assertions and semantic mutations. The cache lookup regression throws on a mismatch; it is
not a kernel theorem. Full qualification
also runs the stock source tests, exports fresh ReleaseSafe AIR with `source.` as its filter,
checks that all six source functions and their alloc/projection/parent/cast/call shapes
survive export, translates it and proves the same observed outputs. `direct`, `nested` and
`castAlias` must remain pure; `escaped` exercises a real call and stack-memory aliasing.
Missing or optimized-away AIR operations fail qualification rather than counting as coverage.

`arrayItem` (L11) recovers `bag.items[i % 2]` from its field `y` (an array element inside a
struct, runtime index) and then `bag` from `&bag.items`; its 12 decided observations check
that the writes through both recovered parents are visible through the original local.
The extended recipe (28 observations) passed on aarch64-macos with stock Zig 0.16.0 and a
patched AIR-only Zig 0.16.0 built from main's exporter; CI repeats it on Linux.

`AIR2LEAN_LOCAL_PARENT_KEEP_WORK=1` retains fresh AIR, generated Lean and mutation files.
There are no retained goldens to silently substitute for fresh source exports. The source
recipe is qualified only for Zig 0.16.0; other versions need separate export and native runs.
The two mutations redirect a recovered-parent field write and alter the recovered outer
write. Only a located false `decide` assertion counts as a kill; infrastructure, parse and
elaboration failures fail the gate. `python3 tests/roadmap/local-parent/test_harness.py`
checks the inventory/mutation gates offline without invoking a compiler.

The full recipe passed in ROOT's serialized Docker amd64 Linux environment,
emulated on an ARM engine, using stock and patched Zig 0.16.0. The run passed the two positive
and four negative kernel provenance claims, the runtime first-occurrence lookup regression,
four emitted synthetic behavior assertions, both strict semantic mutations, the stock source
test, a fresh AIR export and all sixteen emitted observations of that source. The script
uses ReleaseSafe with no explicit target or CPU flags; no more specific target/CPU claim is
inferred from this run. This is emulated Linux qualification. Native-machine ABI/backend
attestation, other Zig versions and a general translation-preservation theorem remain
unqualified. ROOT retained the successful attempt's artifacts for inspection. The same full
local-parent recipe subsequently passed against the composed P07 source, including the
current Names, cache hygiene and array-framing changes. Full CI for that composed source
remains pending.
