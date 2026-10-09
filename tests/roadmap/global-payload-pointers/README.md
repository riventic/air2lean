# Global-backed payload pointers (L06)

The exporter resolves `opt_payload` and `eu_payload` constants through ordinary struct
fields and existing `nav`/`uav` global identities. Checked addition includes every parent
and leaf offset. A 64-projection budget rejects deep or cyclic paths without allocating a
global identity on failure. `arr_elem` remains unsupported because it denotes a
comptime-only array element in the supported compiler versions.

Payload constants require resolved, sized layouts, ordinary pointers in the generic address
space, and initialized, non-extern, non-threadlocal global backing. Packed/vector projections,
volatile accesses and zero-sized payloads are rejected. Optional payloads start at offset zero;
error payload offsets follow the compiler's alignment order and must agree with the memory
model. `payload_base: true` records that a constant reached this resolver, rather than an
already supported global-plus-offset path.

The source fixture includes nested optional and small, wide and equal-alignment error-union
payloads in frozen and writable globals. Generated clients check pointer identities, actual
heap reads, three writes, complete neighboring bytes and block metadata, and const-write
rejection. Compiler-folded read exports are checked separately from heap reads. Three
semantic mutations change the global root, parent offset or small payload offset; each
mutated generated module and its oracle definitions must compile before a named semantic
oracle failure counts. `Model.lean` and the shared pointer-offset kernel additionally check
framing, absent payload bytes, offset overflow and bounded traversal.

Run the checks from the repository root with the matching patched and stock compilers:

```sh
lake build ZigLean Air2Lean air2lean
export AIR2LEAN_LEAN=$(lake env which lean)
export LEAN_PATH=$(lake env printenv LEAN_PATH)
export AIR2LEAN_ZIG_NATIVE=/path/to/stock/zig
export AIR2LEAN_ZIG_AIR=/path/to/patched/zig
export AIR2LEAN_ZIG_VERSION=0.16.0
export AIR2LEAN_ZIG_BACKEND=stage2_x86_64
bash tests/roadmap/global-payload-pointers/check.sh --kernel
bash tests/roadmap/global-payload-pointers/check.sh --native
python3 -m unittest discover -s tests/roadmap/global-payload-pointers -v
work=$(mktemp -d)
bash tests/roadmap/global-payload-pointers/check.sh --export "$work/air"
bash tests/roadmap/global-payload-pointers/check.sh --export-reject "$work/reject-air"
.lake/build/bin/air2lean "$work/air" -o "$work/Gen.lean" --namespace GlobalPayload --prefix global_payloads.
python3 scripts/normalize-generated.py report "$work/Gen.lean" "$work/air" "$work/generated-report.json"
AIR2LEAN_GLOBAL_ACTUAL_GEN="$work/Gen.lean" AIR2LEAN_GLOBAL_CLIENT_OUT="$work/clients" \
  bash tests/roadmap/global-payload-pointers/check-generated.sh
```

The patched compiler must be built from the current seven-input exporter recipe, including
`pointer-offset.zig`. The same source/native and fresh generated-client procedure supports
0.14.1, 0.15.2 and 0.16.0 with matching compiler paths and version selection. The existing
Linux16 CI job runs these feature controls serially.

Source/native correspondence is bounded to `stage2_x86_64`, x86_64 Linux musl,
baseline CPU and ReleaseSafe. Native tests and exports explicitly select `-fno-llvm -fno-lld`.
Fresh AIR validation requires schema 12 and rejects LLVM, missing or mixed profiles, and GNU
ABI for this qualification. General translator acceptance is separate from this correspondence.

A native address probe on all three stock versions found the small error payload constant at
offset 36 with LLVM and its runtime projection at 38; stage2_x86_64 produced 38 for both.
Optional, wide and equal-alignment controls agreed across both backends. The original offset
oracle is unchanged. See `native-abi-boundary.json` for the diagnostic provenance.
`tests/roadmap/const-bases` (§The LLVM constant `eu_payload` offset) resolves the
discrepancy: 38 is correct. Zig 0.14.1–0.17.0's `codegen/llvm.zig` `lowerPtr` measures the
error union type instead of its payload, so it places an alignment-1 payload at the error
code. The translator rejects such constants on the `stage2_llvm` profile.
