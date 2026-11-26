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
large request only because of a model constant. Lean represents every allocated byte, so a Lean runtime run of a very large request under
the default policy can exhaust host memory. Runners that accept untrusted sizes select an
explicit cap or budget. The differential harness keeps its legacy
1 MiB cap as an explicit choice: `AllocPolicy.harness` in `tests/diff/Diff.lean`, and
`TestAllocator.max_alloc_bytes` natively. It does not use the model default. To select a 2 MiB cap, failures at attempts 0
and 2, every odd attempt above 64 bytes and a 16 MiB live-heap budget:

```lean
let initial : Zig.Mem := { allocPolicy :=
  { maxBytes := 2097152, failures := [0, 2], fails := fun i n => i % 2 == 1 && 64 < n,
    budget := some 16777216 } }
```

The finite list is a special case of the oracle. `AllocPolicy.asOracle` moves the cap and
the list into `fails`. `allocDenied_asOracle` and `rawAlloc_asOracle`
(`ZigLean/Mem/AllocLemmas.lean`) prove that every `usize` request gets the same decision,
outcome and memory apart from the policy field. `rawAlloc_eq` characterizes every `rawAlloc`
run: it either fails after only counting the attempt, or allocates a new heap block. Policies
do not qualify native malloc, a custom allocator's policy, successful resize or address reuse.
Those remain separate M02/M05 work. Allocator identities, arenas and fixed buffers (M01) are
translated from their Zig code ([allocator-identity.md](allocator-identity.md)).

**Translated allocators.** With `--allocator-model translated` the same policy decides the OS
primitives: `mmap` and a growing `mremap` fail exactly when `rawAlloc` would
(`mapDenied_iff`), so the oracle embedding holds for them too (`mapDenied_asOracle`,
`ZigLean/Os/MmapRun.lean`). `tests/roadmap/alloc-translated/AllocTranslated/Eval.lean` runs the translated
`std.heap.page_allocator` under finite failure lists, index and size oracles, a cap and the
oracle form of a list policy, with several failures in one run; every failure takes the
allocator's `OutOfMemory` path. In the proofs a failure is the `null` that `FAllocSpec.alloc`
always allows: every client contract over `FAllocSpec` (the generated wrappers' `alloc_spec`,
`create_spec`; the generic list client `Lists.Alloc.push_spec`) covers both outcomes for every
allocator and every failure choice ([alloc-spec.md](alloc-spec.md)). They replace the `std`
heap's `releaseAttempt_run`/`releaseAttempts_run`, retired with the legacy logic (L5c,
[alloc-spec.md](alloc-spec.md#retired-claims)); the `releaseAttempts` client stays as a
test-local def of the executable checks below.

`Lists.Append.appendEach` (`Proofs/Lists/Policy.lean`) calls the translated
`ArrayListUnmanaged(u32).append` once per value and continues after `OutOfMemory`.
`appendEach_spec` holds for every allocator that meets the allocator contract `CAllocSpec`,
so for every failure decision of the allocator, with no success premise; its one size premise
is the contract's room (`fits`) for each capacity the list can grow to, as `append_spec` asks.
A concrete allocator enters only through its proved contract. The client returns
one result per value, never a panic or `.illegal`. Each result is `ok` or `OutOfMemory`. The
final list `alist` is the original items followed by exactly the successfully appended
values, and the fee of its buffer comes back. A failure leaves the list unchanged
(`append_spec`), and any number of failures can occur in one run. It is a `CTriple`, as the
allocator contract is ([alloc-spec.md](alloc-spec.md#retired-claims) records the `std` heap
form it replaces).

`tests/roadmap/allocation-policy/Oracle.lean` is a Lean-only runtime check. It covers
index and size oracles, list-to-oracle agreement, a budget that is freed and reused, the
uncapped default against the explicit harness cap, and a translated `Lists.dupe` of
1 MiB + 1 bytes. That request succeeds by default and fails under the harness cap. It also
runs the `append` loop of the `std` heap model's translation (a test-local `appendEach`) with
three failures before successful appends. The embedding, the uncapped default and the 1 MiB
fixture stay Lean-only (the native harness keeps its cap); the oracle and the budget have the
native counterpart below. `check.sh` runs this check before the twenty native comparisons.

### Native differential

The native differential `TestAllocator` (`tests/diff/common.zig`) uses the same explicit
policy, over page allocation, and still reports actual harness allocation failure separately.
Existing lists inputs retain the null/index protocol. The first allocator argument can also
be a policy object:

```json
{"fail_at": null, "failures": [0, 2], "max_bytes": 2097152, "budget": 96,
 "oracle": [{"attempt_min": 2, "attempt_max": 2}, {"attempt_mod": 3, "attempt_rem": 1, "bytes_min": 64}]}
```

`oracle` is `AllocPolicy.fails` and `budget` is `AllocPolicy.budget`. An oracle is a list of
rules, and attempt `i` of `n` bytes fails when one rule matches `(i, n)`. A rule matches when
all its bounds hold: `attempt_min ≤ i ≤ attempt_max`, `i % attempt_mod = attempt_rem`, and
`bytes_min ≤ n ≤ bytes_max`; a missing bound does not restrict, so `{}` matches every request.
A rule with `attempt_min = attempt_max` and `bytes_min = bytes_max` is one entry of a decision
table, so the rules express every oracle on the finitely many requests of a terminating run;
the model's `fails` stays an arbitrary function. The budget fails a request when the bytes of
the live allocations plus the request exceed it (`Mem.oracleDenies`; natively
`TestAllocator.overBudget` over its live list). The model side builds the policy from the
same object (`withFailAt`, `tests/diff/Diff.lean`).

Missing fields default to the legacy policy; `"max_bytes": null` selects the model's default,
no request cap (`unboundedAllocBytes`; natively `TestAllocator.request_cap = maxInt(usize)`, so
on both sides every `usize` request passes the size check). Malformed/negative policy values, an
`attempt_mod` of 0 and a field that is not part of the policy are rejected on both sides.
The shared JSON transport uses nonnegative signed-64-bit integers on native 64-bit fixtures,
while semantic indices/caps are Lean naturals. The complete input object is part of the
correspondence evidence. The cap is a per-request semantic policy, not an assurance that
the host can satisfy a request. Zero-length allocations bypass policy in both models.

**Translated clients under generated policies.** The lists differential (`scripts/diff.sh`,
`AIR2LEAN_EXAMPLES=lists`) runs each allocating function (`sumRange`, `dupe`, `dupeZLen`,
`evens`, `listSum`) natively and in the model under the same policy object. After each
function's 300 legacy lines, `tests/diff/gen_inputs.zig` writes 40 lines with a generated
policy: up to three oracle rules, a budget on half of the lines, and on some a failure list
and a request cap (`writePolicy`). They come from a generator stream of their own, so the
other inputs stay the same, and `scripts/fresh-inputs.sh` regenerates them with every seed.
`evens` (an `ArrayListUnmanaged` that grows: the old and the new buffer are live together)
and `listSum` (every node live) make the budget and the attempt rules decide later requests
too. Each case compares the result, the buffers and the live-allocation count, as every lists
case does; there are no exclusion pins for these lines. The functions return at their first
`OutOfMemory`, so a run with several failures is compared by the standalone fixture.

**Large requests under the default policy.** After its policy lines, `sumRange` gets six lines
under `{"max_bytes": null}` (`large_lines`, a generator stream of their own): a buffer of
1 MiB + 4 bytes (`n = 2^18 + 1`, one item past the harness cap), four of up to 4 MiB, each
written and read item by item, and `n = 2^62`, whose byte count `4 * n` overflows, so
`Allocator.alloc` returns `OutOfMemory` before any request. Natively and in the model the large
buffers are allocated and the sums agree: a valid large input does not fail because of a
model constant. The lines are only requests the host can hold, because the model represents
every allocated byte. They are practical because a store costs its own bytes, not its
block's ([kernel-eval-bytes.md](kernel-eval-bytes.md#compiled-execution-stores-in-place-m03));
before, a loop of stores into one block was quadratic in its size. Run of 2026-11-25 on native
x86_64-linux (ReleaseSafe), Zig 0.16.0, 0.17.1 and 0.15.2 each: 1,710 lists cases, 1,709 exact
matches (the six large lines among them), 0 mismatches, the pinned `allocatorWord` exclusion;
each whole run, the build of the Lean side included, took under two minutes.

**Large requests through the translated allocator.** The lines above run the `std` allocator
model. `tests/roadmap/alloc-translated`
([README](../tests/roadmap/alloc-translated/README.md#requests-above-1-mib-against-the-native-run-m03))
sends requests of 1 MiB + 1 byte and 4 MiB through the translated `PageAllocator`
(`page_sum`, down to `Zig.Os.mmap`; the failure decision there is `Mem.mapDenied`, the same policy)
under the default policy and compares the results with the native run, for the Zig 0.17.1 and
0.16.0 translations on x86_64-linux and aarch64-macos. The model's side is a compiled executable:
Lean's interpreter keeps a frame per iteration of a loop in the concurrent monad and does not run
loops of that length. Under the harness policy (the old cap) the same run is denied, which the
check requires.

**Standalone fixture.** `tests/roadmap/allocation-policy` compares twenty exact cases of
`rawAlloc` against `TestAllocator`. Ten cover the failure index, the list and the cap: legacy
success/failure, several failures, combined legacy/trace failure, duplicate indices, all
failures, cap equality/overflow, raised-cap success above 1 MiB, harness-cap rejection (case
`default-cap`, the legacy 1 MiB cap), and zero-size allocation. Ten cover the oracle and the
budget: every even attempt (three failures in one run), by size, by attempt and size, two
rules, every request, an oracle with a list and a cap; a budget with every block held (its
boundary and the held bytes are compared), a budget whose blocks are released, a budget of 0,
and a budget with an oracle. `Check.lean` states each oracle as a Lean function and
`fixture.zig` as rules, so the comparison also checks the rule semantics. Each run checks the
attempt count and the absence of live blocks. `compare.py` requires all twenty cases by name.

Qualification commands (the coordinator runs compiler commands sequentially under its
sampled memory/time guard):

```sh
python3 tests/roadmap/allocation-policy/static.py
bash tests/roadmap/allocation-policy/check.sh
python3 tests/roadmap/allocation-policy/mutations.py
AIR2LEAN_EXAMPLES=lists scripts/diff.sh
```

For a Zig version other than the one whose translation `Proofs/Lists/Gen.lean` holds, the
lists differential runs in a check tree (`scripts/check-tree.py create DEST --host-goldens
VERSION`, then `scripts/diff.sh` there), as `scripts/check.sh` does.

Run of 2026-11-24 on native x86_64-linux (ReleaseSafe, baseline CPU), Zig 0.17.1, 0.16.0 and
0.15.2 each: the lists differential compared 1,704 cases, of them 200 under generated
oracle/budget policies, with 1,703 exact matches, 0 mismatches and the one pinned
`allocatorWord` exclusion; the fixture gave 20 exact policy comparisons; all seven mutants
were detected. This is a local run, not a qualification record.

The seven semantic mutants ignore the failure trace, ignore the cap, omit live-allocation
removal, ignore the failure oracle, ignore the budget, count only the request against the
budget, or drop a rule's upper bound on the request. Each must compile, then fail an explicit fixture outcome/ownership assertion.
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

The gate builds the fixtures' imports first (`scripts/lean-deps.py --build`); the fixtures
import the memory model only, not the legacy separation logic. CI runs the
policy gate and semantic mutants in the 0.16.0/0.15.2 full jobs, on the native 64-bit
reference host. `AIR2LEAN_ALLOCATION_REPORT_DIR` retains raw Lean/native JSON comparisons;
CI sets it under `RUNNER_TEMP` and retains run logs there, outside the cached `.lake`
directories. It does not introduce an artifact upload or publish a qualified claim from
an incomplete gate.

## Sentinel bytes and raw allocator preconditions (M04)

Sentinel bytes count in every request. `allocSentinel(u8, n, s)` asks for `n + 1` bytes;
sentinel reallocation (`Zig.Allocator.reallocSentinel`, the `len + 1`-byte absorbed-buffer
pattern over the recognized 0.16.0 byte `realloc`) asks for `n + 1` bytes and stores the
sentinel at `n`; `freeSentinel` releases all `len + 1` bytes. The cap therefore applies to
the request including the sentinel, and every attempt consumes one policy decision.
`tests/roadmap/sentinel-realloc/Check.lean` runs these rules (every remap mode, failure traces,
overflow, a payload-only `realloc`). The sentinel invariant itself is proved over the translated
`std.mem.Allocator` wrappers for every allocator that meets `CAllocSpec`, not over this model:
`Interfaces.SentinelSpec` (`tests/roadmap/interfaces`; [alloc-spec.md](alloc-spec.md#retired-claims)).

The model's raw interface (`vtableAlloc`, `vtableResize`, `vtableRemap`, `vtableFree`,
`ZigLean/Mem/Alloc.lean`) requires an alignment `2 ^ k`, `k < 64`, a nonzero length, and for
resize/remap/free the whole live heap block allocated with that alignment; violations are
`.illegal` (executable checks in `tests/roadmap/sentinel-realloc/Check.lean`). The translator does
not reach it: the raw calls are `inline` vtable dispatch, and under `--allocator-model
translated` they are calls through the vtable whose contract is `FAllocSpec`. See
`tests/roadmap/sentinel-realloc/README.md`.
