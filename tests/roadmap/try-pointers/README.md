# Pointer-form try

This case exercises `try_ptr` and `try_ptr_cold` on addressed error unions. The exporter
writes their pointer operand and original error body. Translation reads the error tag
through `Zig.tryPayloadPtr`; on success it returns `Zig.errPayloadPtr` in the same
allocation. The pointer-try operation neither decodes the payload nor sets the tag. Compiler AIR
can include an earlier unused whole-union load: translation retains the full byte read,
bounds/alignment/race checks and access record through `loadDiscardBytes`, without
decoding an SSA value that has no runtime uses or allocating an extracted byte array.
The direct access uses the same validation and race-recording operations as `loadBytes`;
`loadDiscardBytes_eq` proves equality with a raw read whose result is discarded for every
memory state, including failures and clock/footprint changes. No performance gain is claimed
without measurement. Used loads retain their typed decoder.
Error propagation and cleanup
execute the compiler's original body, including `defer`, `errdefer` and the cold hint.

The accepted operand is a single pointer to a modeled error union. Its result must be a
single pointer to the same payload with matching constness and explicit pointer alignment.
Every reachable error-body path must exit the function and may not branch outside itself.
Analysis stops at the first terminator, and a branch to a local block resumes that block's
continuation; a dead return/trap after that branch cannot certify an exit. Falling-through
bodies, loops and switches with no explicit else are conservatively rejected.
For a function containing pointer try, error-flow summaries are computed bottom-up once
when its instruction IDs are unique. Flat siblings use an array reverse fold; recursion
visits nested bodies, including unreachable child bodies without treating them as reachable
outcomes. Functions without pointer try skip cache-only ID hashing and summary preparation. Direct
public checks with duplicate IDs fall back to uncached validation; diagnostics still come
from the original ordered checker traversal. Existing flattening and target-scope checks
are retained, so this is not a claim about whole-checker complexity.
Existing layout/encoding
checks still apply: the current memory model uses a two-byte error code, a 64-bit
little-endian pointer ABI, and payload offsets from `errUnionOffsets`. Unmodeled error
unions, volatile/allowzero pointers and unsupported layouts remain rejected. No claim
is made for representations that erase the error tag, or other target ABIs.

`ZigLean/Sep/Try.lean` provides a universal sequential-memory ownership rule for the
tag-only helper. Generated functions can additionally require whole-object raw ownership
for the preceding discarded read (`ZigLean/Sep/Discard.lean`). The tag rule owns
only aligned tag bytes, preserves heap/frame bytes and `Mem.Seq`, and returns the exact
payload address or original error name. Framing retains payload/cleanup ownership;
`Triple.bind` supplies the obligations for subsequent writes and cleanup. Access records
may change because the tag read participates in the existing race model.

The local Zig 0.14.1, 0.15.2 and 0.16.0 `Air.zig` and `Sema.zig` sources were inspected:
all use `ty_pl` plus `TryPtr { ptr, body_len }`; result pointer flags preserve constness,
volatility, allowzero and address space. Cold changes only the error-branch hint. This
inspection is distinct from compiler qualification. `provenance.json` records actual
export/native/kernel qualification separately; pending entries are not passing evidence.
Schema 11 does not encode the full target/CPU, so those facts are the recorded export
command's provenance, rather than facts independently recovered from its AIR.

Only the root's serialized compiler queue should run the following commands:

```sh
lake build Air2Lean.Check Air2Lean.Emit air2lean ZigLean.Sep.Try ZigLean.Sep.Discard
AIR2LEAN_ZIG_AIR=/qualified/patched/zig bash tests/roadmap/try-pointers/check.sh --export tests/roadmap/try-pointers/air/0.16.0
.lake/build/bin/air2lean tests/roadmap/try-pointers/air/0.16.0 -o tests/roadmap/try-pointers/TryPointers/Gen.lean --namespace TryPointers --prefix try_pointers.
python3 tests/roadmap/try-pointers/check-artifacts.py --record
AIR2LEAN_ZIG_NATIVE=/qualified/stock/zig bash tests/roadmap/try-pointers/check.sh --native
bash tests/roadmap/try-pointers/check.sh --check-artifacts
```

Use a fresh empty export directory. The patched compiler must contain this branch's
shared exporter. Export uses explicit `x86_64-linux`, baseline CPU, ReleaseSafe and
`-fno-error-tracing`. Checked AIR/generated Lean and hashes bind the retained artifacts;
hashes alone do not attest that export or proof checking occurred.

The artifact gate regenerates Lean, checks byte identity, kernel-checks memory rules,
runs source-generated alias/error/cleanup tests and synthetic parser/checker/emitter
cases. The undefined-payload case checks that taking its address does not decode it. Extra
regressions pin the full-object bounds/alignment/race checks and exact read footprints,
compare direct discarded access with the former raw read on successes and errors, and
exercise reachable nested block branches and scalar-signature pointer-try memory classification.
The native fixture checks the same concrete alias, error and cleanup observations.
`TryPointers/Proofs.lean` connects the actual generated `payload8` and `payload64`
definitions to a program that retains the whole-object read and the extra tag read on
error. Its sequential ownership precondition owns all 4 or 16 object bytes, requires
whole-object and tag alignment, and requires only the tag to decode. Payload/padding
bytes may remain undefined. The universal result preserves the exact payload address or
error name, whole owned heap, arbitrary frame and sequential memory.

After the baseline checks pass, the gate creates a temporary, typed `payload8` mutant
whose success return shifts the payload pointer by one byte. The mutant generated module
must compile successfully. Only exact exit 1 with located equality-proof errors inside
`payload8_program` counts as rejection; tool, import, syntax, type, signal and unrelated
proof failures fail the gate. Compiler-free tests exercise the mutation and classifier.

The finite runtime cases are differential evidence, not a universal compiler-preservation
proof. Temporary generated files/logs use `RUNNER_TEMP` when set, and are not uploaded.

The non-mutation Zig 0.16.0 CI job runs one sequential gate after the runtime and
translator build. It builds both ownership modules, runs the offline provenance/mutant
classifier tests, checks the retained artifacts and kernel/runtime/mutation gates, runs
the stock host compiler's native fixture, then exports fresh source AIR with the matrix's
patched compiler. `check-artifacts.py --fresh-air DIR` reuses the source/exporter hash,
profile, exact inventory and tag checks without recording or replacing checked hashes.
CI translates that fresh AIR and compares generated Lean byte-for-byte with retained
`Gen.lean`. Fresh AIR, generated Lean and diagnostics stay under `RUNNER_TEMP`; this gate
adds no artifact upload. Zig 0.14/0.15 exporter API source inspection and synthetic profile
checks are the current boundary, pending actual export/native qualification on those versions.

Compiler-free provenance regressions:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/roadmap/try-pointers -v
```
