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
outcomes. The checker skips cache-only ID hashing and error-flow summary preparation for functions without pointer try. Direct
public checks with duplicate IDs fall back to uncached validation; diagnostics still come
from the original ordered checker traversal. Existing flattening and target-scope checks
are retained, so this is not a claim about whole-checker complexity.
Block emission propagates an inner body directly only when no branch targets that block
and either its declared type is `noreturn` or its body is certified to exit outward.
Own-target branches retain the block's continuation. Target
membership is prepared once per emission context, including bare public contexts.
Void and nonvoid nested-branch runtime fixtures retain original error names and values.
Existing layout/encoding
checks still apply: these ownership and alias rules (`Sep/Try.lean`, `Sep/TryAlias.lean`)
cover the default two-byte error code only (the `…W` operations emitted for another
`--error-limit` width have no ownership rules), a 64-bit
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
inspection is distinct from compiler qualification. `provenance.json` is the historical receipt
(its `pending` entries are not passing evidence and stay unchanged because the integration
manifests pin its hash); the compiler export and native run are recorded in
`compiler-qualification.json` (see Compiler export below).
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
patched compiler. `check-artifacts.py --fresh-air DIR` requires explicit schema-12
Linux/baseline ReleaseSafe profiles, exact inventory and both pointer-try tags. The
separate `integration-qualification.json` binds the current combined exporter hash to
the unchanged historical provenance and origin exporter hash. It records inputs only;
it does not attest compiler or kernel qualification. Without that variant, the original
exporter hash remains mandatory. Changing the combined exporter requires a separate
reviewed variant update; this guard never rewrites historical receipts.
CI translates fresh AIR and binds its full generated hash, input hashes and profile
through `normalize-generated.py report`, then compares the complete generated body
with retained `Gen.lean`. In integration mode, the retained artifact gate also binds
the translator's full output and schema-11 AIR hashes/profile in a receipt before
comparing the complete body with historical `Gen.lean`; it compiles the full generated
file with its profile header. Without the integration variant it retains raw Gen
comparison. Historical provenance and raw retained AIR/Gen hashes remain unchanged.
Fresh AIR, generated Lean and diagnostics stay under
`RUNNER_TEMP`; this gate adds no artifact upload. Zig 0.14/0.15 exporter API source inspection and synthetic profile
checks are the current boundary, pending actual export/native qualification on those versions.

Compiler-free provenance regressions:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/roadmap/try-pointers -v
```

Current finite-error storage integration keeps every retained AIR file and
`provenance.json` unchanged. The historical generated file is retained at
`origin/TryPointers/Gen.lean`; `emitter-integration.json` binds that identity, the
current emitter, and the exact current generated file as inputs only. The gate
cannot rewrite the historical receipt in this mode. Both retained and fresh output
comparisons still compare the full body with current `TryPointers/Gen.lean`.
Current generated pointer operations enforce the AIR domain `Bad`/`Other`.
The generated-program ownership contracts therefore require any present error to
belong to that domain; payload addresses, full-object/tag reads, frame ownership,
and cleanup results retain the same guarantees. Generic tag-only helper rules
remain unrestricted. Runtime controls retain every previous oracle and separately
check that a foreign symbolic error fails with `unspecified`. Compilation and
runtime qualification of this caller update remain ROOT's responsibility.

## Aliasing and cleanup rules

The tag-only rule above does not say what a payload alias observes. `ZigLean/Sep/TryAlias.lean`
(not imported by the `ZigLean` runtime umbrella) owns the whole typed union `pts p a u`:
every pointer try on `p` returns `tryView α p u` (the same payload address, or the original
error); a load through any such address reads the payload in place; a store through it turns
`pts p a (.ok x)` into `pts p a (.ok y)` without writing the tag. `tryAliasWriteRead` is the
two-alias composition. Side conditions are explicit: `Nat.min a 2 ∣ a` and divides the tag
offset, and the payload access alignment divides `a` and the payload offset.

`TryPointers/AliasProofs.lean` applies these rules to the actual retained generated
definitions (compiler-exported AIR, unchanged Gen):

| Definition | Rule |
|---|---|
| `writeAlias p y` | Result `writeView y u`; the union afterwards holds `writeView y u`. An error writes nothing. |
| `cleanup p o e` | Distinct counters: success increments `o` only; error increments `e` then `o`, returns the original error and leaves the union unchanged. |
| `cleanup p c c` | One counter for both cleanup pointers: +1 on success, +2 on error. |
| `coldPayload p e` | Success returns the payload address with `e` unchanged; the cold error body increments `e`. |

The result is read before cleanup runs. Counter increments are `add_safe`, so the rules require
room for each increment; the runtime test checks that overflow fails with `.overflow`.

`aliases/` holds two further functions from `try_aliases.zig`. Their schema-11 AIR is
**hand-written** in the 0.16.0 exporter shape (`aliases/provenance.json`); the compiler export and
native run are in `compiler-qualification.json`, the proofs below still run on the retained
hand-written-AIR translation. `aliases/TryAliases/Proofs.lean` proves:

* `twoPaths p p y` (one union through both pointer-try operands): the same result as `writeAlias`.
* `twoPaths a b y` (separately owned unions): only `a` is written and only `b` is read. An error
  on either path returns that path's error and writes nothing.
* `resetOnError p f` (`errdefer cell.* = f`): the error name is read before the cleanup store,
  so the original error is returned while the union now holds `.ok f`. Success leaves it
  unchanged and returns the payload address. The store uses the finite-domain dictionary;
  for a success value it writes the generic encoding.

`aliases/TryAliases/Runtime.lean` checks these cases and the corresponding retained-AIR cases.
These are a caller-held payload pointer, a shared cleanup counter (the native call sequence
ends at 3), `writeAlias` errors, `coldPayload` success and cleanup overflow.
`try_aliases.zig` has the matching native tests. The cases are finite. Remaining exclusions:
concurrent aliases (the rules need `Mem.Seq`), overlapping
but unequal union objects, aliases through casts or different element types, cleanup that frees
the union, and payloads wider than one byte in the generated cleanup rules.

```sh
lake build ZigLean.Sep.TryAlias
python3 tests/roadmap/try-pointers/aliases/check-artifacts.py
bash tests/roadmap/try-pointers/aliases/check.sh --check-artifacts
AIR2LEAN_ZIG_NATIVE=/qualified/stock/zig bash tests/roadmap/try-pointers/aliases/check.sh --native
AIR2LEAN_ZIG_AIR=/qualified/patched/zig bash tests/roadmap/try-pointers/aliases/check.sh --export "$fresh/air"
python3 tests/roadmap/try-pointers/aliases/check-artifacts.py --fresh-air "$fresh/air"
```

A fresh export differs from the hand-written AIR in instruction IDs, debug lines and the schema-12
profile; its translation is the retained `Gen.lean` up to the profile header (see below).

## Compiler export

`air-fresh/0.16.0` (`try_pointers.zig`: `payload8`, `payload64`, `writeAlias`, `cleanup`,
`coldPayload`) and `aliases/air-fresh/0.16.0` (`try_aliases.zig`: `twoPaths`, `resetOnError`) are
unmodified schema-12 exports from a patched 0.16.0 compiler (Linux x86_64, baseline CPU,
ReleaseSafe, no error tracing; build tree and commands in `compiler-qualification.json`).
`compiler-qualification.py` checks their hashes, exact inventory, profile and pointer-try tags, and
with `--translator` that each translates to the retained `TryPointers/Gen.lean` and
`aliases/TryAliases/Gen.lean` up to the profile header (`normalize-generated.py report`/`compare`).
The translated bodies are identical, so the proofs about the retained modules, including the
hand-written `twoPaths`/`resetOnError`, are proofs about the compiler's AIR for these sources.
Native: stock 0.16.0 `zig test` of `try_pointers.zig` (4 of 4) and `try_aliases.zig` (8 of 8) on
an aarch64-macos host; no x86_64 Linux run.

```sh
bash tests/roadmap/try-pointers/check.sh --check-qualification
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest tests/roadmap/try-pointers/test_compiler_qualification.py
python3 tests/roadmap/try-pointers/compiler-qualification.py --fresh "$root"   # $root/try_pointers, $root/try_aliases from the --export commands
```
