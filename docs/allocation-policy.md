# Allocation failure and request-size policies (M03)

`Zig.AllocPolicy` is a model environment parameter in `Mem.allocPolicy`. A nonzero request
fails when any of these selects it:

- `Mem.failAt`, the additive legacy failure index;
- `maxBytes`, a per-request cap;
- `failures`, a finite list of zero-based attempt indices;
- `fails`, an arbitrary failure oracle over (attempt index, request bytes);
- `budget`, an optional bound on live heap bytes including the request
  (`Mem.liveHeapBytes`, summed only when a budget is set).

All failures leave the caller's existing heap intact. Each attempted nonzero request
increments `Mem.allocs`, including failed ones. Zero-byte requests do not allocate or consume
a policy decision. Duplicate indices have no extra effect.

The default policy has no failures and no fixed cap (`maxBytes = unboundedAllocBytes = 2^64`,
so every `usize` request passes the size check). The model therefore never rejects a valid
large request only because of a model constant. The differential harness keeps its legacy
1 MiB cap as an explicit choice: `AllocPolicy.harness` in `tests/diff/Diff.lean`, and
`TestAllocator.max_alloc_bytes` natively. It does not use the model default. To select a 2 MiB cap, failures at attempts 0
and 2, every odd attempt above 64 bytes and a 16 MiB live-heap budget:

```lean
let initial : Zig.Mem := { allocPolicy :=
  { maxBytes := 2097152, failures := [0, 2], fails := fun i n => i % 2 == 1 && 64 < n,
    budget := some 16777216 } }
```

The finite list is a special case of the oracle. `AllocPolicy.asOracle` moves the cap and
the list into `fails`. `allocDenied_asOracle` and `rawAlloc_asOracle` (`ZigLean/Sep/Alloc.lean`)
prove that every `usize` request gets the same decision, outcome and memory apart from
the policy field. `rawAlloc_eq` characterizes every `rawAlloc` run: it either fails after
only counting the attempt, or allocates a new heap block. Policies do not qualify native malloc, a
custom allocator's policy, successful resize, address reuse or multiple allocator
identities. Those remain separate M01/M02/M05 work.

`rawAlloc_run` and existing `create_run`/separation triples now quantify over the policy
as part of arbitrary initial memory. `releaseAttempt_run` and `releaseAttempts_run` state
that a finite allocate/free client has an actual returned outcome, one outcome per request,
and restores its original heap regardless of failure choices and cap. This is stronger
than a partial triple satisfied by a diverging computation. Premises remain positive size,
positive alignment and `Mem.Seq`; the theorem does not assume resources or success.
These definitions passed the coordinator's kernel build at revision
`853cef53211d08a62e368739160f56dea6a3408e`; the qualification record identifies the
selected local profile and remaining review/regression gates.

`Lists.appendEach` (`Proofs/Lists/Policy.lean`) calls the translated
`ArrayListUnmanaged(u32).append` once per value and continues after `OutOfMemory`.
`appendEach_run` and its explicit form `appendEach_anyPolicy` hold for every policy `P` and
legacy index `f`, with no success or resource premise. The client returns one actual
result per value, never a panic or `.illegal`. Each result is `ok` or `OutOfMemory`. The
final well-formed list `alist` is the original items followed by exactly the successfully
appended values, with the frame and `Mem.Seq` preserved. A failure leaves the list unchanged
(`append_run`), and any number of failures can occur in one run.

`tests/roadmap/allocation-policy/Oracle.lean` is a Lean-only runtime check. It covers
index and size oracles, list-to-oracle agreement, a budget that is freed and reused, the
uncapped default against the explicit harness cap, and a translated `Lists.dupe` of
1 MiB + 1 bytes. That request succeeds by default and fails under the harness cap. It also
runs `appendEach` with three failures before successful appends. These checks have no
native counterpart because `TestAllocator` has neither an oracle nor a budget. `check.sh`
runs this check after the ten native comparisons.

The native differential `TestAllocator` uses the same explicit policy, over page allocation,
and still reports actual harness allocation failure separately. Existing lists inputs retain
the null/index protocol. The first allocator argument can also be:

```json
{"fail_at": null, "failures": [0, 2], "max_bytes": 2097152}
```

Missing fields default to the legacy policy; malformed/negative policy values are rejected.
The shared JSON transport uses nonnegative signed-64-bit integers on native 64-bit fixtures,
while semantic indices/caps are Lean naturals. The complete input object is part of the
correspondence evidence. The cap is a per-request semantic policy, not an assurance that
the host can satisfy a request. Zero-length allocations bypass policy in both models.

The standalone fixture compares ten exact cases: legacy success/failure, several failures,
combined legacy/trace failure, duplicate indices, all failures, cap equality/overflow,
raised-cap success above 1 MiB, harness-cap rejection (case `default-cap`, the legacy 1 MiB cap), and zero-size allocation. Each
successful block is freed and each run checks attempt count and absence of live blocks.
Small existing `sumRange` fixtures separately exercise the JSON object transport.

Qualification commands (the coordinator runs compiler commands sequentially under its
sampled memory/time guard):

```sh
python3 tests/roadmap/allocation-policy/static.py
bash tests/roadmap/allocation-policy/check.sh
python3 tests/roadmap/allocation-policy/mutations.py
AIR2LEAN_EXAMPLES=lists scripts/diff.sh
```

The three semantic mutants ignore the failure trace, ignore the cap, or omit live-allocation
removal. Each must compile, then fail an explicit fixture outcome/ownership assertion.
Compiler errors, unexpected panics, missing tools and killed processes do not count as
mutation detection. Temporary copies preserve the original source. Existing mutation (h)
continues to remove only legacy `failAt`, retaining the configured policy.

[The qualification record](allocation-policy-report.json) preserves the earlier historical
results and appends the coordinator's complete post-cleanup recheck at revision
`6cf2011b33ee242be653b9fb2137661328307bd0`. The full committed proof package passed
(104 jobs); selected native policy fixtures passed ten exact comparisons under both
Zig 0.16.0 and 0.15.2 on aarch64-macos with baseline CPU/ReleaseSafe; all three semantic
mutants were detected. The lists-client gate passed 1,503 exact comparisons with zero
fail matches, unspecified outcomes, caps or mismatches, and its libm self-check matched
320/320 samples. The appended record binds each command, code hash and distinct log path
to that checked revision, including separate native-version logs even where their contents
have the same hash. The default-cap cleanup and guard-order optimization have now been
rechecked. After the fixture-only cleanup, revision `989983de97216a7d09632a3bcc91088f716714c5`
also passed ten exact native policy comparisons under each version. The coordinator
completed eight independent review angles and candidate verification per disjoint scope,
fixed the confirmed cleanups, and found no remaining findings in the final cleanup delta.
Reference Linux CI and universal acceptance review remain pending, so full M03
qualification remains false. These selected
model-policy checks do not establish general allocator or cross-target correspondence.

The gate explicitly builds `ZigLean.Sep.Alloc` before compiling its client fixture;
`lake build ZigLean` alone does not produce that imported separation module. CI runs the
policy gate and semantic mutants in the 0.16.0/0.15.2 full jobs, on the native 64-bit
reference host. `AIR2LEAN_ALLOCATION_REPORT_DIR` retains raw Lean/native JSON comparisons;
CI sets it under `RUNNER_TEMP` and retains run logs there, outside the cached `.lake`
directories. It does not introduce an artifact upload or publish a qualified claim from
an incomplete gate.
