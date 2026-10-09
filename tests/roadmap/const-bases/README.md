# Nested constant pointer bases (L06)

A Zig pointer constant is an InternPool `{ base_addr, byte_offset }`. Its base is a root
(`nav`/`uav` global, `int` address, comptime-only object) or a projection of another pointer
constant (`field`, `opt_payload`, `eu_payload`). Sema folds an element of a runtime array into
the parent's `byte_offset`. The exporter (`zig-patch/air-json/json.zig`, `resolvePtr`) walks a
chain of any nesting, within a 64-projection budget, to one existing global identity and a
checked offset. Otherwise it writes an explicit `unsupported` reason. The translator emits
`⟨some block, off⟩`.

`ZigLean/Mem/ConstPtr.lean` (proof-only; not in `ZigLean.lean`) states this as an explicit
object/provenance model. Its `Path` is a root and its projections. `resolve` gives the
constant view; `runtime` applies the instruction emitted for each projection. It proves:

| Property | Theorem |
|---|---|
| A resolved constant equals the runtime projection chain from its global's root, on the root's block | `resolve_eq_runtime`, `resolve_block`, `resolve_off` |
| Nesting composes (elem of field of payload of a global, …) | `resolve_append`, `resolve_snoc`, `runtime_append` |
| `eu_payload`/`opt_payload` are the emitted payload-pointer instructions; a constant slice keeps its base | `errPayload_step`, `optPayload_step`, `slice_ptr_field` |
| Two constants into one global alias exactly when their total offsets agree | `resolve_eq_iff` |
| Distinct globals, sibling fields, distinct array elements, and a payload and its error code are disjoint | `distinct_globals_disjoint`, `sibling_disjoint`, `elem_disjoint`, `payload_code_disjoint` |
| `int` and comptime-only roots and unknown globals never resolve; a block-less access is `.illegal` | `resolve_int`, `resolve_comptimeOnly`, `resolve_unknown`, `access_unbacked` |
| The LLVM backend misplaces a constant payload exactly when its size is nonzero and its alignment is below 2. It then addresses the error code. | `llvmPayloadOffset_ne_iff`, `llvmPayloadOffset_is_code`, `llvm_total_eq` |

`air/0.16.0` is hand-written AIR in the exporter's schema 12. It uses the
stage2_x86_64, x86_64-linux-musl baseline ReleaseSafe profile, and its source is
`const_bases.zig`. Its comptime asserts check the recorded type-table layout:
`Holder { head: u64 @0, tail: u32 @8, maybe: ?Cell @12, res: Failure![3]u8 @20 }`, where
`Cell { tag: u16 @0, bytes: [4]u8 @2 }`.

| Function | Base | Offset |
|---|---|---|
| `resElemPtr` | `&(table.res catch unreachable)[2]`: elem of `eu_payload` of field | 20 + 2 + 2 = 24 |
| `maybeElemPtr` | `&table.maybe.?.bytes[1]`: elem of field of `opt_payload` of field | 12 + 0 + 2 + 1 = 15 |
| `maybeBytePtr` | another chain to the same byte | 15 |
| `maybeSlice` | `table.maybe.?.bytes[1..3]`: constant slice over the nested base | 15, len 2 |
| `resCodePtr` | `@ptrCast(&table.res)`: the error code's first byte, field only | 20 |
| `readResElem` | a load through `resElemPtr`'s constant | reads 22 |
| `projectRes`, `projectMaybe` | the same projections at run time from a `*const Holder` | — |

`ConstBases/Gen.lean` is the retained translation. `ConstBases/Proofs.lean` connects it to
the model. Each generated constant equals its resolved `Path` and the model's runtime chain.
The generated runtime projections from the global's address equal the generated constants.
The two chains to byte 15 alias, the payload is disjoint from its code, and `readResElem`
reads 22 from `mem0`. The LLVM offset would read element 0 (20) instead. An unbacked
address never resolves, and a read through one is `.illegal`.

`test_cli.py` checks the byte-identical translation and the explicit errors. Each error
carries a `--diagnostics-json` code:

| Input | Diagnostic |
|---|---|
| `{"unsupported": "int"}` directly, as a constant slice's pointer, or in a global initializer | `a pointer constant without a global (int) is outside the subset` (`CONSTANT_FAILURE`; `GLOBAL_FAILURE` for the initializer) |
| `comptime_alloc`, `comptime_field`, `arr_elem`, `payload_unbacked` | the same message with that reason |
| unknown global id | `pointer has unknown global id N` (`STRUCTURE_FAILURE`) |
| offset past the global's end | `a pointer constant at offset N is outside global G (S bytes)` (`STRUCTURE_FAILURE`) |
| `stage2_llvm` (also `stage2_wasm`, whose `lowerPtr` has the same `eu_payload` measure): a constant at or one past an alignment-1 error-union payload (offsets 22..25) | `… may address an alignment-1 error-union payload … outside the stage2_llvm profile` (`CONSTANT_FAILURE`) |

On `stage2_llvm`, the error code bytes (20, 21), the optional-payload element and slice (15),
and other fields (8, 26) stay accepted. With a `Failure!u16` payload, offsets 20 and 22 are
also accepted.

```sh
lake build ZigLean ZigLean.Mem.ConstPtr air2lean
bash tests/roadmap/const-bases/check.sh
# x86_64 Linux with a stock 0.16.0 compiler: the source fixture's native offsets.
AIR2LEAN_ZIG_NATIVE=/path/to/zig bash tests/roadmap/const-bases/check.sh --native
```

## Fresh exports

`air-fresh/<version>` (0.16.0, 0.15.2, 0.14.1) is the unmodified export of `const_bases.zig`
from a patched compiler of that version (stage2_x86_64, x86_64-linux-musl, baseline,
ReleaseSafe). `provenance.json` records the source, exporter (`json.zig`, `pointer-offset.zig`),
compiler and per-file hashes. The command was `ZIG_AIR_JSON_FILTER=const_bases. zig build-obj
-fno-emit-bin -OReleaseSafe -fno-error-tracing -fno-llvm -fno-lld -target x86_64-linux-musl
-mcpu=baseline`. The 0.15.2 and 0.14.1 compilers were built by `zig-patch/build.sh` from the
exporter of this tree. The 0.16.0 export is the earlier one, from an older exporter tree, so it
lacks the additive `src` and `column` fields. `test_cli.py` checks every version against the
hand-written fixtures:

* Every returned constant pointer has the same global (`const_bases.table`), offset
  (24, 15, 15, slice 15, 20) and `payload_base` marker in all three versions. The generated
  definitions of `resElemPtr`, `maybeElemPtr`, `maybeBytePtr`, `maybeSlice` and `resCodePtr`
  are identical to the retained `Gen.lean`, and the profile is identical but for the version
  and target triple. The three fresh translations are equal after the profile header line.
* Recorded differences: Sema's ReleaseSafe `projectRes`/`projectMaybe` include the
  `catch unreachable` error check and the `.?` null check that the hand-written fixtures
  omit. Sema also folds `readResElem` to `22`, so the hand-written fixture keeps the load
  through the constant that the proofs use.
* Every fresh program is rejected on `stage2_llvm` at offset 24, like the hand-written one,
  and also when downgraded to schema 11 (below).

This is export and translation evidence only. The native offsets are checked with a stock
0.16.0 compiler (`check.sh --native`); `zig test const_bases.zig -fno-llvm` was not run with
0.15.2 or 0.14.1 here.

## The LLVM constant `eu_payload` offset

`tests/roadmap/global-payload-pointers` recorded a small (`Failure!u8`) error-payload
constant. Its offset was 36 with LLVM and 38 at run time, where stage2_x86_64 gave 38 for
both. 38 is correct. Zig's semantics, Sema and the model put an alignment-1 payload after the
2-byte error code (`codegen.errUnionPayloadOffset(payload)`). The 36 comes from an LLVM-backend
bug, not from a model or exporter mismatch.

* `src/codegen/llvm.zig` `lowerPtr`, `.eu_payload` arm (0.14.1, 0.15.2, 0.16.0 and 0.17.0),
  calls `codegen.errUnionPayloadOffset(Value.fromInterned(eu_ptr).typeOf(zcu).childType(zcu))`.
  That argument is the error union type, not its payload. The error union's alignment is at
  least `anyerror`'s (2), so the function returns 0.
* The generic `src/codegen.zig` `lowerPtr` (self-hosted backends) passes
  `.childType(zcu).errorUnionPayload(zcu)`, which is correct. So does the exporter.
* The LLVM IR for x86_64-linux-musl (`-femit-llvm-ir`, stock 0.16.0) shows the bug. The
  constant is `getelementptr (i8, @storage.frozen, i64 36)`, while the runtime projection on
  the `var` is `@storage.mutable + 38`. The global's LLVM type is `{ i16, i8, [1 x i8] }`, so
  offset 36 is the `i16` error code.
* It is observable. `llvm_probe.zig` (`zig run llvm_probe.zig -fllvm -OReleaseSafe`, stock
  0.16.0 and 0.17.0, aarch64-macos) prints
  `constant=10 runtime=12 constant_read=20 runtime_read=22`. A read through
  `&(frozen.res catch unreachable)[2]` returns element 0. `const_bases.zig`'s test fails
  under `-fllvm` for the same reason.
* On x86_64-linux-musl (stock 0.16.0, baseline, ReleaseSafe, linux/amd64 container) the
  probe prints `constant=10 runtime=12 constant_read=20 runtime_read=22` with `-fllvm`, and
  `constant=12 runtime=12 constant_read=22 runtime_read=22` with stage2_x86_64.
  `check.sh --native` (stage2_x86_64) passes there; the same test under `-fllvm` fails at
  `resElemPtr` (2 bytes low). `UPSTREAM.md` drafts the Zig issue (not filed).
* Affected shape: any `eu_payload` constant base whose payload has runtime bits and
  alignment below 2, nested at any depth (`Zig.ConstPtr.llvmPayloadOffset_ne_iff`). Payloads
  of alignment at least 2 (`Failure!u16`, `Failure!u64`) start at 0 either way, which matches
  the controls that agreed across backends.

The translator fails closed. On a `stage2_llvm` profile it rejects every pointer constant
whose offset can lie at or one past such a payload of its global. The type scan is
structural and over-approximating: it visits every struct/tuple field, array item and
optional payload that contains the offset, and it rejects through unions and unknown layouts.
Other backends are unaffected, and the generated model keeps the correct, Sema-given offset.
The check reads the schema-12 `profile.backend`. Legacy schema 1–11 inputs carry no backend
(`unverified`, the named legacy reference model), so the backend that compiled them is unknown
and the LLVM backend cannot be excluded. The translator therefore treats `unverified` like
`stage2_llvm` here (`Air2Lean.mayMisplaceEuPayload`): the same constants are rejected with a
message that names the missing backend, and the same controls (the error code, the optional
payload, other fields, an aligned payload) are accepted. `test_cli.py` runs the hand-written
fixtures and all three fresh exports downgraded to schema 11 (no `profile`). A one-off sweep of
the 54 committed directories of legacy AIR (tests, examples, case studies) found no
newly rejected input. A legacy file whose constants touch such a payload now needs a re-export
with a schema-12 exporter that names a backend other than LLVM or wasm.
