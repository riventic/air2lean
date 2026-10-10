# Union-member constant pointer bases (L06)

A pointer constant into a member of a global union is resolved like the nested bases of
`tests/roadmap/const-bases`: one existing global and an exact byte offset.

* Sema's `Value.ptrField` keeps a member pointer of an `extern` or `packed` union as its
  parent pointer, so every member is at the union's address. No projection is added.
* A member of an `auto` union (tagged, or bare with its ReleaseSafe safety tag) is a `field`
  base. The exporter (`zig-patch/air-json/json.zig`, `unionPayloadOffset`) gives it the
  payload offset. It requires the compiler's offset (`Type.structFieldOffset`, which
  `codegen.lowerPtr` and `codegen/llvm.zig` also use) to equal the model's. The model puts the
  more aligned of tag and payload first, the tag if they are equal, and uses the exported tag
  or safety tag and every non-`noreturn` member at its natural alignment. When the two
  offsets differ, for example for an explicitly aligned member or an untagged `auto` union,
  the exporter writes `{"unsupported": "union_field"}`.
* A union member of a `var` global is not a constant. Sema projects it at run time, with the
  ReleaseSafe tag check (`struct_field_ptr`, `get_union_tag`), which the translator already
  models.

`ZigLean/Mem/ConstPtr.lean` adds `Proj.unionPayload index ts ta pa` (offset
`unionPayloadOffset ts ta pa`, whatever `index` is) and proves:

| Property | Theorem |
|---|---|
| A tagged or bare member is the emitted `struct_field_ptr` at the payload offset; an `extern` member (`.field 0`) is the union's pointer | `unionPayload_step`, `externMember_step` |
| All members of one union alias | `unionMembers_alias` |
| A member of at most the largest member's size is disjoint from the tag | `unionPayload_tag_disjoint` |
| The LLVM backend agrees on every union step | `llvm_total_eq` (a union step is never `llvmMisplaced`) |

## Fixtures

`union_bases.zig` (source, `zig test` checks the offsets natively) has two globals:
`table : Holder` and `mixed : Mixed`.

| Function | Base | Offset |
|---|---|---|
| `extWordPtr`, `extHiPtr`, `extBytePtr` | `&table.ext.word`, `.pair.hi`, `.bytes[2]` (`extern union`, at 36) | 36, 38, 38 |
| `wideCellPtr`, `wideSlice` | `&table.wide.cells[2]`, `table.wide.cells[1..3]` (`union(enum(u32))`: tag first, payload at 4) | 48, slice 46 len 2 |
| `lowPairPtr` | `&table.low.pair[1]` (`union(enum)` with a `u64` member: payload first, tag at 8) | 1 |
| `barePairPtr` | `&table.bare.pair[1]` (bare union, safety tag first, payload at 1) | 78 |
| `outerPairPtr` | `&table.outer.inner.bare.pair[1]` (a bare union in a struct in a `union(enum(u64))` payload) | 16 + 8 + 1 + 1 + 1 = 27 |
| `maybeCellPtr` | `&table.maybe.?.cells[1]` (a union under an optional payload) | 52 + 4 + 2 = 58 |
| `resBytePtr` | `&(table.res catch unreachable).bytes[3]` (an `extern` member of an error-union payload) | 68 + 3 = 71 |
| `mixedLowPtr`, `mixedHighPtr` | `&mixed.raw[1]`, `&mixed.raw[3]` (a `union(enum(u32))` whose other member is `Failure![2]u8`) | 5, 7 (global 1) |
| `readWideCell`, `readExtByte` | reads at a run-time index through `&table.wide.cells` and `&table.ext.bytes` | 44, 36 |
| `projectWide`, `projectBare` | the same projections at run time from a `*const Holder`, with the tag checks | — |

`air/<version>` holds the unmodified exports from patched 0.16.0, 0.15.2 and 0.14.1
compilers. `zig-patch/build.sh` built them from this tree's exporter. `export.sh` runs
`ZIG_AIR_JSON_FILTER=union_bases. zig build-obj -fno-emit-bin -OReleaseSafe
-fno-error-tracing -fno-llvm -fno-lld -target x86_64-linux-musl -mcpu=baseline` (stage2_x86_64)
for each version. `provenance.json` pins the source, the exporter, every export and each
compiler binary (`test_cli.py --refresh-provenance <dir>` rewrites it). All three versions
export the same constants. Apart from the profile line, they translate to the same
`UnionBases/Gen.lean`, which is the retained 0.16.0 translation.

`UnionBases/Proofs.lean` connects the generated code to the model:

* Each generated constant equals its resolved `Path` (`*_resolve`, `*_run`), and the model's
  runtime chain agrees (`*_runtime`).
* The generated runtime projections, with their tag checks, give the generated constants
  (`projectWide_identity`, `projectBare_identity`).
* `extern` members alias (`extHi_alias`), as do tagged members (`wideMembers_alias`).
  Payloads are disjoint from their tags (`wide_payload_tag_disjoint`,
  `low_payload_tag_disjoint`).
* Reads through the constants give the active members' bytes (`*_read`, `readWideCell_mem0`,
  `readExtByte_mem0`).

## Rejections

`air-reject/<version>` holds the exports of `union_reject.zig`. `test_cli.py` checks each
version and an edited copy of the accepted program:

| Input | Diagnostic |
|---|---|
| `oddPtr`: `&odd.b` of `union(enum) { a: u8 align(4), b: u8 }`. The compiler puts the payload first (alignment 4), the model's natural layout would put the tag first | exporter `union_field`: `a pointer constant without a global (union_field) is outside the subset` (`CONSTANT_FAILURE`) |
| `resPtr`: `*const Failure!u32` to a member with error storage | `… outside the finite error-storage fragment` (`STRUCTURE_FAILURE`). A typed alias of symbolic error storage must name a matching subobject, which is not reconstructed through a union member |
| `{"unsupported": "union_field"}` injected into `wideCellPtr` | the `union_field` diagnostic |
| the accepted program on `stage2_llvm` | `mixedHighPtr` (offset 7, at or one past `Failure![2]u8`'s payload 6..8 through member `raw`) is rejected, because the scan cannot tell which member a folded offset came from. The other constants, `mixedLowPtr` (5) included, are accepted |

## Running

```sh
lake build ZigLean ZigLean.Mem.ConstPtr air2lean
bash tests/roadmap/union-bases/check.sh
# x86_64 Linux with a stock 0.16.0 compiler: the source's test on stage2_x86_64 and LLVM.
AIR2LEAN_ZIG_NATIVE=/path/to/zig bash tests/roadmap/union-bases/check.sh --native
```

`check.sh --native` passed with stock 0.16.0 x86_64-linux in a linux/amd64 container, on both
backends. The `zig test` also passes on aarch64-macos with LLVM.
