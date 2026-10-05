# Flow timestamp addition: original production source

This case study translates Flow's `addDuration` from the production file
`optimizer/engine/src/des/time.zig` in `/opt/dev/boxhub`. The wrapper imports that
file as the Zig module `flow_time_original` and instantiates its generic function
at `u32` and `u64`. It contains no timestamp arithmetic. Zig inlines the original
function into both AIR entry points; `FlowTime/Gen.lean` is generated from that AIR.

The recorded production revision, source SHA-256, export profile and toolchain
are in `provenance.json`. The source is an external dependency, not a vendored
copy. The same file bytes may be supplied from a different checkout with
`FLOW_TIME_SOURCE`; a missing or changed file fails before compiler execution.
Changing the expected hash requires a new original-source export and proof check.

`FlowTime/Proofs.lean` proves the following for **every** pair of `u32` inputs and
for **every** pair of `u64` inputs:

- If the natural-number sum is below `2^width - 1`, the generated definition
  returns that exact sum. The addition does not wrap and the reserved maximum
  cannot be returned successfully.
- The definition returns `error.TimeOverflow` **if and only if** the natural sum
  overflows the machine width or equals the reserved maximum.
- Both generated definitions equal a total contract returning an ordinary Zig
  error union, so neither panics nor diverges for any input.

The body lemmas unfold `timestamp32` and `timestamp64` from the generated module.
The generic arithmetic lemmas then establish the shared representability rule;
they are connected to the production-derived definitions by those body lemmas.
No extra axioms, admitted proofs, or native decision procedure are used.

## Reproduce

Use an existing **patched** Zig 0.16.0 compiler for AIR export, a separate stock
Zig 0.16.0 compiler for native tests, and the built air2lean executable:

```sh
FLOW_TIME_SOURCE=/path/to/boxhub/optimizer/engine/src/des/time.zig \
AIR2LEAN_ZIG_AIR=/path/to/zig-air-0.16.0/bin/zig \
AIR2LEAN_ZIG_NATIVE=/path/to/stock-zig-0.16.0/zig \
AIR2LEAN_TRANSLATOR=/path/to/air2lean \
  bash scripts/flow-time.sh
```

Run this command from the air2lean repository with the pinned Lean toolchain
available. It checks the production hash, exports AIR with the explicit
`x86_64-linux-musl` / `baseline` / `ReleaseSafe` profile, compares both complete JSON
exports and the complete generated Lean body with committed artifacts, tests the wrapper's
native boundary cases, builds `ZigLean`, and kernel-checks the generated module
and proofs. The native compiler version is checked before export. Only the stock-compiler
native test uses the host target; it imports the same wrapper
and original source. The script creates temporary compiler and Lean outputs and
removes them on exit. It never updates the checked artifacts silently.

The retained AIR is the historical schema 11 export. Fresh reproduction requires
schema 12 with the exact Zig 0.16.0 LLVM, Linux x86_64 musl baseline, ReleaseSafe,
64-bit little-endian, 16-bit error-set, and disabled error-tracing profile checked
by `tests/roadmap/flow-time/compare-air.py`. Its resolved target triple and complete
CPU feature list are explicit in that guard. Both fresh entry points must have
identical profile facts before translation. Other profiles fail closed.

After translation, the shared `scripts/normalize-generated.py` helper writes a
receipt binding the raw AIR hashes, profile, full generated hash, and body hash.
The Flow guard checks its exact two-file inventory and hashes before permitting
only the top-level schema 12/profile-to-schema 11 protocol transition. Function
names, version/endian, instructions, types, layouts, parameters, results, globals,
and nested metadata remain observable. The complete generated body must equal
the retained module; the **full headered fresh module** is kernel-checked with the
universal proofs. A receipt is provenance evidence, not a compiler-preservation
proof. Historical AIR, generated Lean, source hash, and provenance remain intact.

The essential original-source binding is:

```sh
mkdir -p out FlowTime
ZIG_AIR_JSON_DIR="$PWD/out" ZIG_AIR_JSON_FILTER=flow_time. "$AIR2LEAN_ZIG_AIR" \
  build-obj -fno-emit-bin -fllvm -OReleaseSafe -fno-error-tracing \
  -target x86_64-linux-musl -mcpu=baseline \
  --dep flow_time_original -Mroot=case-studies/flow-time/flow_time.zig \
  -Mflow_time_original="$FLOW_TIME_SOURCE"
"$AIR2LEAN_TRANSLATOR" out -o FlowTime/Gen.lean \
  --namespace FlowTime --prefix flow_time.
```

Provenance guards can be checked without invoking any compiler:

```sh
bash scripts/flow-time.sh --check-source
python3 tests/roadmap/flow-time/test_provenance.py
python3 tests/roadmap/flow-time/test_compat.py
```

The boundary tests cover ordinary addition, the largest allowed result, equality
with the reserved timestamp, `max + 0`, and wrapped results including zero for
both widths. These samples supplement the universal Lean proofs.

## Trust and scope

The Lean kernel checks the generated Lean contracts. Applying them to the
production Zig function also trusts Zig semantic analysis and inlining, the AIR
export patch, air2lean translation, and `ZigLean` bit-vector/error semantics.
The pinned original-source hash and regenerated artifacts make that provenance
reviewable; they do not remove those compiler and translation assumptions.

This is a proof of the production timestamp addition rule at two unsigned widths.
It does not establish invariants of Flow's entire scheduler, event queues, or
other production callers. CI can kernel-check the committed generated definitions and proofs without an
external checkout or either Zig compiler:

```sh
bash scripts/flow-time.sh --check-artifacts
```

The CI workflow runs this artifact-only command, including its eight synthetic
compatibility regressions, and the five Python provenance guard regressions once
in the default full job. It deliberately supplies an unavailable
production source path: the artifact gate must succeed without the private checkout.
CI does not regenerate production AIR or run production native tests, and this gate
makes no compiler-preservation claim. It uses ordinary CI logs and temporary files.

This checks the committed artifacts only. The full original-source reproduction
requires the source dependency, reexports and compares AIR, and reruns native tests.

The compatibility guard's synthetic offline regressions reject profile changes,
semantic-body changes, missing/extra exports, malformed generated headers, and
receipt tampering. They do not execute a compiler or attest a new original-source
export. Fresh source/native/kernel qualification of this schema transition is a
separate required check; artifact-only CI checks the retained proof domain.
