# Allocation failure and request-size policies (M03)

`Zig.AllocPolicy` is a model environment parameter in `Mem.allocPolicy`. It has a
per-request `maxBytes` cap and a finite list of zero-based nonzero allocation attempt
indices that fail. `Mem.failAt` remains an additive legacy failure index. All failures
leave the caller's existing heap intact; each attempted nonzero request increments
`Mem.allocs`, including cap failures. Zero-byte requests do not allocate or consume a
policy decision. Duplicate indices have no extra effect.

The default policy (`maxBytes = 1048576`, `failures = []`) reproduces the original runtime.
To select a 2 MiB cap and failures at attempts 0 and 2:

```lean
let initial : Zig.Mem := { allocPolicy := { maxBytes := 2097152, failures := [0, 2] } }
```

For every finite execution prefix, a finite list can represent its permitted failure
decisions. The default beyond the list is success subject to the request cap and legacy
index. This does not model an arbitrary infinite failure function or a total live-byte
budget. It does not qualify native malloc, a custom allocator's policy, successful resize,
address reuse or multiple allocator identities. Those remain separate M01/M02/M05 work.

`rawAlloc_run` and existing `create_run`/separation triples now quantify over the policy
as part of arbitrary initial memory. `releaseAttempt_run` and `releaseAttempts_run` state
that a finite allocate/free client has an actual returned outcome, one outcome per request,
and restores its original heap regardless of failure choices and cap. This is stronger
than a partial triple satisfied by a diverging computation. Premises remain positive size,
positive alignment and `Mem.Seq`; the theorem does not assume resources or success.
These are source definitions pending a fresh kernel check in the qualification record.

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
raised-cap success above 1 MiB, default-cap rejection, and zero-size allocation. Each
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

[The qualification record](allocation-policy-report.json) separates completed static checks
from unavailable compiler/kernel/differential checks. M03 is not qualified until those checks
and the universal acceptance review pass against an exact revision/profile. This fixture
compares the selected model policy on native reference layouts; it is not general allocator
or cross-target correspondence.

The gate explicitly builds `ZigLean.Sep.Alloc` before compiling its client fixture;
`lake build ZigLean` alone does not produce that imported separation module. CI runs the
policy gate and semantic mutants in the 0.16.0/0.15.2 full jobs, on the native 64-bit
reference host. `AIR2LEAN_ALLOCATION_REPORT_DIR` retains raw Lean/native JSON comparisons;
CI sets it under `RUNNER_TEMP` and retains run logs there, outside the cached `.lake`
directories. It does not introduce an artifact upload or publish a qualified claim from
an incomplete gate.
