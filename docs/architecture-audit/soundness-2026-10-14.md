# Soundness audit 2026-10-14: wrong or empty proofs since the trust-chain audit

Base: `origin/main` at `e1f163c8e` (2026-10-14), 2764 commits after the trust-chain audit
([trust-chain.md](trust-chain.md), `af9ddc30`, 2026-10-08). This audit changes no code. The
question it answers: how large is the risk that a proof is wrong because something is missed or
translated wrongly? A finding is either an accepted input whose Lean model differs from Zig, or a
claimed theorem that is vacuous or says less than it appears to.

Severities as in [trust-chain.md](trust-chain.md): **SOUNDNESS** (a false or empty claim reaches
the user), **FAIL-OPEN** (the guard that should reject is missing; a constructed case shows it),
**HARDENING** (defence in depth or a wrong label).

Counterexamples are in
[`tests/roadmap/architecture-audit/soundness-1014/`](../../tests/roadmap/architecture-audit/soundness-1014/).
`check.sh` there prints `vulnerable` or `fixed` for each case and exits non-zero with
`--require-fixed` while any case is open. Every Lean file uses the standard axioms only.

## Summary

The old suite is green: `trust-chain/check.py --require-fixed` reports every case `fixed`. Its
open gap, a `for` loop with safety off whose length is not in AIR, is closed (§0).

The model changes since 2026-10-08 hold up. Each was checked for a provably false native
statement, an unsatisfiable precondition, and an adequacy path (§Reviewed and sound). The risk
now lies at the two ends of the pipeline:

* **The claim layer** can report `no-panic: proved` from a vacuous theorem (S1). It also reads
  non-strict concurrent results as covering runs that the model drops (S4).
* **The translator** has a namespace that model selection still matches by name (S2). It also
  labels unchecked illegal behaviour as a safety panic (S3).

| # | Severity | Finding | Counterexample |
|---|---|---|---|
| S1 | SOUNDNESS (claims) | A theorem without a non-vacuity witness is capped at `safety`, and `project.py absence_claims` turns every `safety` goal into `no-panic: proved`. A vacuous theorem therefore proves "no panic" for a root that panics. | `vacuous-safety/probe.py`, `Vacuity.lean` (kernel) |
| S2 | SOUNDNESS (constructed, `--allocator-model translated`) | A user file `posix.zig` binds the trusted OS primitive `Zig.Os.mmap`, because `posix` is missing from `Identity.stdNamespaces`. This is trust-chain finding 1 again, for a namespace added later. | `translator/posix-spoof` (real export, `#guard`) |
| S3 | SOUNDNESS (outcomes) | Unchecked illegal behaviour gives a safety-panic constructor (`.panic`, `.overflow`, `.divByZero`), not `.illegal`. The affected ops are `@enumFromInt`, inactive union fields (tagged and bare), plain `+ - *`, `/`, and `@intCast` with safety off, on 0.16 and 0.17. A contract that admits `panic` then admits illegal behaviour that natively returns a value. | `translator/unsafe-panic` (real export, kernel `rfl`, native output) |
| S3b | SOUNDNESS (outcomes), **open** | The rest of S3 (§S3, status): `@shrExact` with safety off (`shr_exact` and no `shrOverflow` check) gives `.overflow`, a safety panic, not `.illegal`. Sema's check comes *after* the op, so neither the op nor its operands tell the checked from the unchecked form. The model needs the check's presence as an export fact (as `for_len`). | none committed yet; the follow-up PR adds it to `translator/` |
| S4 | SOUNDNESS (claim reading) | A non-strict protocol (`Proto.strict = false`) discharges every error leaf, including `.unspecified` and `.unsupportedTimer`. Natively the program goes on after those. `run_sound` results ("every result satisfies Q") then omit native runs. | `nonstrict-unspecified/NonStrict.lean` (kernel), `nan.zig` (native) |
| F1 | FAIL-OPEN | The export's `std` module is not bound to the reviewed std sources. A std lib modified via `--zig-lib-dir` still gets the reviewed std models. | `translator/libdir-spoof` (real export from a patched lib, `#guard`) |
| F2 | FAIL-OPEN | Allocator contracts (`FAllocSpec`, `CAllocSpec`) carry no non-vacuity obligation. An invariant whose fee never holds (allowed by `fee_add`, #302) lets an allocator that traps on every call satisfy the **total** contract. No allocator proof states that its `own ⋆ fee` holds after its `init`. | `contract-vacuity/FeeFalse.lean` (kernel) |
| F3 | FAIL-OPEN | Witnesses do not link claims to the program. Non-vacuity witnesses pick any `Mem.FSeq` memory, not `mem0`. No shipped `Proofs/` claim uses `FTriple.run_init*`/`FTotalTriple.run_init*`. The `CTriple` claims of `Proofs/Lists` (`Alloc`, `Append`, `Container`) have no witness, apart from two fixtures in `tests/roadmap/lists-fba`. | survey (§F3) |
| H1 | HARDENING | `@trap()` is emitted as `throw .panic`; natively it is SIGILL. | `translator/trap` |
| H2 | HARDENING | `PageAlloc.vt.alloc` is `Sched.soloRun 16`: the shipped `fallocSpec` is a partial triple at a fixed depth of 16, although `alloc_ct` holds at every depth. | code-read |
| H3 | HARDENING | `alloc` throws `.stackOverflow` for every block kind without room: thread-local instances, `.global` runtime cells, and `Future.slotAlloc`'s `.heap` cell. Partial claims allow `.stackOverflow` under STK-01, which speaks only of the native stack. | code-read (`ZigLean/Mem/Basic.lean:942`) |
| H4 | HARDENING | A pure-mode sentinel slice parameter loses its sentinel, so `s[len]` is `.illegal`. Natively it returns the sentinel. This is conservative but undocumented. | sub-audit fixture (not committed) |
| H5 | DOC/POLICY | `docs/illegal-behavior.md` row 23 is stale: the optional/C-pointer unwraps now give `.illegal`. Several std rows added after af9ddc30 select hand-written models for std functions: `Io.async`, `Io.Future.await`/`cancel`, `Io.checkCancel`, `Thread.detach`, `Io.Group.async`/`groupDeferC`. Under CLAUDE.md ("never hand-write a model of a std module") they need a maintainer decision or a deletion plan. | code-read |

**Answer to the maintainer's question.** Inside the kernel-checked part, no wrong proof was found.
Every model change reviewed here is fail-closed for the logics that forbid errors (`FTriple`,
`FTotalTriple`, `CTriple`, strict protocols).

The risk sits at two points:

* **The reporting layer.** S1 reports a vacuous theorem as `no-panic: proved`. S3 and S4 give
  model errors a meaning they do not have natively, so the outcome-level claims about them are
  wrong.
* **Identity checks of the translator.** S2 and F1 keep a std or OS model bound to code that is
  not std's.

All four SOUNDNESS findings have concrete counterexamples. S2 and F1 need deliberately crafted
input. S1, S3 and S4 apply to ordinary use.

## 0. Re-run of the trust-chain suite

`python3 tests/roadmap/architecture-audit/trust-chain/check.py --require-fixed` reports `fixed`
for all 13 cases on `e1f163c8e`.

The open gap of row 3 was a `for` loop with safety off whose second operand is a range or an
array. It is now closed, and fail-closed:

* The patched Sema of every supported version (`zig-patch/<version>/hook.patch`) emits the length
  comparison as `if (!ok) unreachable`. The bare `unreach` is `.illegal`.
* The export then lists `for_len` in `unchecked_ib`.
* `Check.checkForLenFact` (`Air2Lean/Check.lean:2966`) rejects every function that has a loop when
  the export lacks that fact.
* The sub-audit confirmed the 0.17.0 export carries `unchecked_ib: ["for_len"]`.

## S1. A vacuous theorem proves `no-panic` (SOUNDNESS, claim layer)

**Location.**

* `scripts/claims.py` `assess` (about l. 357): a functional strength without a verified
  non-vacuity witness becomes `safety` (`strength = 'safety'`).
* `scripts/outcomes.py:69` `STRENGTH_ABSENCE['safety'] = ('no-panic',)`.
* `scripts/project.py:1126` `absence_claims` counts every direct goal of a strength that carries
  an absence claim.

The cap was meant to mean "this theorem proves less". In fact the premise may be unsatisfiable,
in which case the theorem proves nothing, and `safety` still carries `no-panic`.

**Counterexample** (`vacuous-safety/probe.py`). It uses the claims-audit fixtures and the shipped
`claims`/`project` functions:

* `AuditClaims.unsat_pre` assumes `x.toNat > 300` for `x : BitVec 8`.
* `AuditClaims.total_false_pre` is `FTotalTriple (fun _ => False) spin Q`.

Each is declared as a `safety` goal with a scoped domain. Both are `accepted`, bound `direct`,
reach level `proved_scoped`, and give `absence_claims = {no-panic: proved}`.

`Vacuity.lean` proves, in the kernel, that both premises are unsatisfiable and that
`root 255 = throw .overflow`: the root panics. The claims-audit tests miss this because they
declare only `total_correctness`, and with "all inputs" the scoped domain rejects the goal.

**Structural fix.** No witness, no claim. A theorem without a verified non-vacuity witness gets
strength `none`, not `safety`. `absence_claims` also requires the witness, and refuses a goal
whose derived domain is scoped unless the manifest declares that scope. Keep `safety` for
theorems whose premises are witnessed but whose liveness is not.

**Status (2026-10-15): fixed (stop-gap).** `claims.py assess` gives a theorem without a
`verified`/`trivial` non-vacuity witness no strength, whatever its head. `project.py` binds such
a goal as `unwitnessed` (never `direct`). `absence_claims` also requires the witness and a
universal or declared-scoped domain. `vacuous-safety/probe.py` prints `fixed`. The witness is
still any `FSeq` memory; a manifest goal also needs the `mem0` companion of F3.

## S2. `posix.*` is matched by name (SOUNDNESS, constructed)

**Location.** `Air2Lean/Air/Identity.lean:66`:

```lean
stdNamespaces := #["mem","Thread","Io","atomic","time","debug"]
```

A callee in one of these namespaces gets the module-qualified key `root:…`. Every other name keeps
its bare FQN. So `posix.mmap` from module `root` stays `posix.mmap`. That key matches the OS rows
of `StdModels.lean:235-237` (`stdModel?`/`osFn?`), which were added after af9ddc30.

**Counterexample** (`translator/posix-spoof`, real 0.16.0 export, x86_64-linux):

* The user file `posix.zig` defines `mmap` with std's signature. It uses std's own `posix.PROT`
  and `posix.MAP` types, so `checkOsCall`'s check of the flag types passes.
* Its body always returns `error.OutOfMemory`.
* `spoof.mapped()` maps a page, writes 7 and reads it back. Natively it returns 0, because the
  map fails.
* `air2lean --allocator-model translated` emits `Zig.Os.mmap Zig.Os.Target.linux …`, and
  `PosixSpoof.lean` checks `word mapped (mem0 .fresh) = "ok 7"`.

In std mode the same input is rejected ("no AIR file and no model"), and with the user's AIR
included it is rejected as a conflict.

**Structural fix.** Std and OS model lookup takes the pair `(module, fqn)` and requires the std
module, as trust-chain finding 1 proposed. The key spelling then does not matter. At minimum,
derive `stdNamespaces` from the first component of every name in the model tables: StdModels,
the special types in Json, TimedCheck, the panic handlers in Op/Sem, and the name tests in
Check. Add the case to `trust-chain/check.py`.

**Status: fixed.** A root name gets the key `root:<name>` when it starts with any namespace of
`lib/std` (`Identity.stdNamespaces`, now the one complete list, 0.17.0's `lang` and `spirv`
included), so no name-matched lookup (std models, OS primitives, special types, panic handlers)
can match a root identity, whichever namespace a later model uses. The list fails closed: a
std identity outside it is rejected (`Identity.checkedKey`); `test_std_sources.py` compares it
with each present `lib/std`, and `tests/roadmap/models/StdModels.lean` checks that every model
row lies inside it. `posix-spoof` is rejected (`the callee 'root:posix.mmap' has no AIR file`);
CI runs `soundness-1014/check.sh --require-fixed posix-spoof`.

## S3. Unchecked illegal behaviour is reported as a safety panic (SOUNDNESS, outcomes)

**Location.**

* `ZigLean/Basic.lean:321` `Zig.enumOf` (`none => throw .panic`). It is reached through
  `Emit.lean` `enumIntCast` (l. 1166, 1169) and 0.17's logical `bit_cast` (l. 1210).
* The union accessor's wildcard `| _ => throw .panic` (`Emit.lean:569`, `U.get_f`), for tagged
  and bare unions.
* The plain `add`/`sub`/`mul`, `intcast` and `div_trunc` give `.overflow` and `.divByZero`.

[illegal-behavior.md](../illegal-behavior.md) says "every op's model checks its own
illegal-behaviour precondition. It throws `.illegal`". Its rows 6–9, 13, 18 and 21 then list
these exceptions. The doc defines a panic constructor as "a Sema check that fires", but no Sema
check is present here.

**Counterexample** (`translator/unsafe-panic`). `up.zig` holds `@setRuntimeSafety(false)`
versions of these ops; the AIR is the real 0.16.0 export.

* **Model:** `UnsafePanic.lean` proves by `rfl`:
  * `enumUnsafe 3#2 = throw .panic`
  * `unionUnsafe (.b 7#32) = throw .panic`
  * `bareUnsafe (.b 9#32) = throw .panic`
  * `unionLocal 11#32 = throw .panic`
* **Native** (stock 0.16.0 ReleaseSafe, `native.zig`): `enumUnsafe(3) = 3`,
  `unionUnsafe(.b=7) = 7`, `bareUnsafe(.b=9) = 9`, `unionLocal(11) = 11`,
  `addUnsafe(max, 7) = 6`. None of them panics.
* **0.17.0** behaves the same: `int_cast` and `bit_cast` reach `Zig.enumOf`, and Canon merges
  `bit_cast_safe` into `bit_cast`.

**Impact.**

* Error-forbidding triples stay sound: every `Zig.Error` refutes them.
* The outcome layer reads these constructors as a native safety panic: `outcomes.py` maps them
  to `panic`. A goal may declare `outcomes.admits: ["valid", "panic"]`, documented as "a function
  that panics on bad input", so such a contract admits illegal behaviour that natively returns a
  value.
* The differential harness reports a `mismatch` only on a sampled input.
* `--allow-unqualified-build-mode` (ReleaseFast) widens the gap to every function.

**Structural fix.** Keep checked and unchecked forms distinct through Canon and Normalize: a
`safe` flag on `Op`, as trust-chain finding 12 asked. The unchecked form throws `.illegal`. The
safe form keeps its constructor where the check is inside the op (0.17's `int_cast_safe` and
`bit_cast_safe`); elsewhere the Sema `cond_br` already fires first. `Zig.enumOf` and the union
wildcard throw `.illegal`. Then rewrite the affected rows of illegal-behavior.md.

**Status: fixed.**
- **Op.** `Mode.unchecked` (plain `add`/`sub`/`mul`) is now separate from `Mode.checked`
  (`*_safe`), and `Op.intCast` and `Op.bitcast` carry `safe`. Canon keeps 0.17.0's
  `bit_cast_safe` apart as the canonical tag `bitcast_safe`.
- **Runtime.** `Zig.add`/`sub`/`mul`/`intCast`/`enumOf` take `(safe : Bool := true)`. The plain
  form is emitted with `(safe := false)` and throws `.illegal` (`Zig.Error.ifSafe`).
- **Ops without a checked form.** Their Sema check is a `cond_br` before the op (verified on real
  0.16.0 and 0.17.0 exports). Integer division by zero, the division `minInt / -1` and the union
  accessor wildcard throw `.illegal`.
- **Unchanged safe outcomes.** For example `lightOf` (`intcast_safe` to an enum) is still
  `.panic`, and `Proofs/Variants` `lightOf_invalid` is unchanged.
- **Rules and witnesses.** The library rules over these ops (`add_step`, `add_ok`,
  `WP.liftMem_add`, `intCast_step`, the literal simprocs and the others) are generalized over
  `safe`; no new rule is added. `unsafe-panic` is fixed, and `Fixed.lean` proves `.illegal` for
  every unchecked op of `up.zig`. CI runs `soundness-1014/check.sh --require-fixed unsafe-panic`.
- **Not covered: S3b (open).** Row 13 (`shr_exact` without safety) still gives `.overflow`:
  Sema checks it *after* the op, so the op cannot tell the forms apart. That needs the check's
  presence as an export fact, as `for_len` has. Follow-up after F1.

## S4. Non-strict protocols discharge `.unspecified` (SOUNDNESS, claim reading)

**Location.** `ZigLean/Conc/Logic.lean:194`, `Proto.Safe`:

```lean
| .leaf (some (.error e)) => P.strict = false ∨ e = .stackOverflow
```

So `run_sound` states "every `ok` result satisfies `QM`" and discards every error. That is right
for an error that stops the native program (`.panic`, a trap) and for illegal behaviour
(`.illegal`). It is wrong for `.unspecified` and `.unsupportedTimer`: illegal-behavior.md defines
`.unspecified` as "Zig leaves the result open. This is not IB", so the native program goes on and
returns.

**Counterexample** (`nonstrict-unspecified/NonStrict.lean`, kernel). `main` is `@bitCast` of a NaN
to `u64`, through `Float.toBits?`. `main_never_returns` uses `run_sound` with a trivial non-strict
protocol and states, in the shape of the published results, that every result of every schedule
satisfies `False`. Natively (`nan.zig`, Zig 0.16.0 ReleaseSafe) the program prints
`7ff8000000000000` and returns.

The model throws `.unspecified` in several ordinary cases: a racing mixed-size atomic (§R1 below),
a pointer `cmpxchg` whose identity and address disagree, `@min(+0.0, -0.0)`, an `f80` conversion
of an invalid value, and undefined bytes. Every one of them is dropped from a non-strict claim.

**Affected shipped results.** These use `run_sound` with no `run_safe` companion:

* `Cancel.Group.cancelClient_spec`. "Sampled schedules give no error" is the only evidence that
  no `.unspecified` path exists.
* `Atomics.MPR.mpRelaxed_spec`. Its errors are intended races, which are `.illegal` and
  therefore fine.

Every other `run_sound` user in `Proofs/` also proves `run_safe` in strict mode. These results
are not registered claim heads, so `claims.py` does not accept them. They are, however, the
theorem-inventory statements of the concurrency case studies.

**Structural fix.** The non-strict error leaf admits only errors that stop the native program or
are illegal behaviour: `P.strict = false ∧ e.nativeStops ∨ e = .stackOverflow`, where
`nativeStops` holds exactly for `.panic`, `.overflow`, `.divByZero`, `.outOfBounds`,
`.unreachable`, `.illegal`, `.trap` and `.deadlock`. `.unspecified` and `.unsupportedTimer` then
need a proof of absence even in partial correctness, as `FTriple` already requires.

## F1. The `std` module is not bound to the reviewed sources (FAIL-OPEN)

**Location.** `zig-patch/air-json/identity.zig:129` writes `std` for whatever `zcu.std_mod` is.
`StdModel.qualifies` (`StdModels.lean:96`) checks the Zig version only. The `StdReview.sha256`
rows are checked only by a test (`tests/roadmap/models/test_std_sources.py`), never against the
input.

**Counterexample** (`translator/libdir-spoof`). The patched compiler's lib was copied with
`allocator-create.patch` applied, so `Allocator.create` always returns `error.OutOfMemory`. The
case was exported with `--zig-lib-dir`.

* The export still says `zig_version 0.16.0` and `module: std`.
* `h.made` translates to `Zig.Allocator.create p0 4 4`, and `LibSpoof.lean` shows the model
  result 5.
* Natively `made` returns 0.

`-Mstd=` overrides fall into the same case.

**Structural fix.** The exporter records, in the profile, the SHA-256 of each std file that
defines a model or a special type, or one digest of `lib/std`. The translator compares it with
the model's `StdReview` row and rejects a mismatch. If that is not wanted, add a premise
"unmodified std" with an ID and list it in every claim that uses a std model.

## F2. Allocator contracts have no non-vacuity obligation (FAIL-OPEN)

**Location.** `ZigLean/Sep/Full/AllocSpec.lean`: `FAllocInv` and `FAllocSpec`, and
`ZigLean/Sep/Full/Dispatch.lean`: `CAllocSpec`. The implementation picks the invariant `I`:
`own`, `tok`, `fee` and `fits`. `fee_add` holds for a fee that never holds, since
`False ⋆ False = False`. `AllocNeg.not_fallocSpec` refutes bad allocators only under the extra
premise `hsat` that the fee holds somewhere. That premise is not in the contract, and no
allocator proof states it: not `AllocFba.fallocSpec`, not `PageAlloc.fallocSpec`, not the arena.

**Counterexample** (`contract-vacuity/FeeFalse.lean`, kernel). `trap` throws `.illegal` at every
entry. With `own := emp`, a token that never holds and a fee that never holds,
`trap_spec : FAllocSpec FLogic.total trap ctx I` holds. That is the total contract, satisfied by
an allocator whose every call is illegal behaviour.

Client proofs stay sound: a client must supply `I.fee φ`, which it cannot do for this `I`. But
"allocator X satisfies the allocator contract", the per-implementation half of
"build generic, prove individual items against it", is not evidence of anything without a
witness.

**Structural fix.** Make the witness part of the contract. Each implementation proves
`FAllocSpec … I` together with `I.Reachable`, an `EUpd` from the state right after the
allocator's `init`, or from its globals at program start, to `I.own ⋆ I.fee φ` for some
`φ > 0`, plus `I.fits n k` for some `n > 0`. The interface lemmas (`not_fallocSpec`) then take
`I.Reachable` instead of `hsat`. This is the mechanism of §Vacuity mechanism applied to a
contract.

**Status (2026-10-15): assigned to P09.** Maintainer decision 2026-10-15: every allocator
instance must come with a creation triple from its hand-stated creation precondition to `I.own`
and an `FAdmit` companion for that precondition ([invariant-synthesis.md](../invariant-synthesis.md),
decision 2). That is P09's acceptance; until it lands the FBA, page allocator and arena are still
open, and `contract-vacuity/FeeFalse.lean` still type-checks.

## F3. Witnesses are not tied to the program's start (FAIL-OPEN)

The full-state witnesses (`ZigLean/Sep/Full/Witness.lean`: `FAdmit`, `FLive`, `CAdmit`, `CLive`)
ask for some `Mem.FSeq` memory that holds the precondition. They do not ask for `mem0 σ` or a
memory reachable from it. The adequacy theorems exist (`Full/Init`: `FTriple.run_init`,
`run_init_ok`, `FTotalTriple.run_init`, `*_plain`; `FAdmit.Start`), but no `Proofs/` claim uses
them. Only `tests/roadmap/{global-init,lists-fba,memory-hardening}` do.

The sub-audit's survey of the 76 classified theorems of the 11 claim-carrying `Proofs/` modules
found these without any witness:

* the `CTriple` claims of `Lists.Alloc`, `Lists.Append` and `Lists.Container`; `push_spec` and
  `append_spec` have fixture witnesses in `tests/roadmap/lists-fba` only, and `freeAll_spec`,
  `linkedAdd_spec`, `arrayAdd_spec` have none anywhere;
* every step and loop lemma (capped at `safety`, see S1);
* the `FTTriple` helpers of Cancel, Detach, Deadline, Handoff and Iogroup;
* the legacy `TTriple` `wp_*` lemmas.

`claims.py` reads the generated module but does not require that a functional claim's premise is
reachable from that module's `mem0`.

**Status (2026-10-15): fixed for entry-point roots** (maintainer decision 2026-10-15, option a).
`reachability_witness T := proof` (`ZigLean/Witness.lean`) adds `T.reachable`, `T`'s premise
telescope with the memory pinned to the root's `N.mem0 σ`, computed from `T`'s kernel type and
checked by the extractor like the other companions. `claims.py check_goal` rejects and
`project.py` binds `unwitnessed` a manifest goal whose companion is not `verified`/`trivial`
(`not_required` when the claim names no start memory or no memory).
`tests/roadmap/claims/Fixture.lean` (`ClaimStart`) has a reached and an unreached goal. Library
theorems keep the non-vacuity witness. Allocator implementations: see F2.

## H1–H5

* **H1.** `Emit.lean:3491` emits `| .trap => "throw .panic"`. `@trap()` is an illegal
  instruction, and the outcome should be `.trap` (`hardware_trap`). Fixture: `translator/trap`
  (`t.zig`, `air/`).
* **H2.** `tests/roadmap/alloc-translated/PageAlloc.lean`: `vt.alloc := Sched.soloRun 16 …`. A
  run deeper than 16 has no result and satisfies the partial triple. Use the depth-generic
  `alloc_ct` in the contract (`CAllocSpec`), or quantify the depth.
* **H3.** `Mem.alloc` throws `.stackOverflow` when there is no room, for every kind
  (memory-model.md MM-18, fail-closed point 4). Partial claims allow `.stackOverflow` under
  STK-01, which is about the native stack, not about a heap cell or a thread-local instance.
  Give non-stack kinds their own outcome, or extend STK-01 by name.
* **H4.** Sentinel slices in pure mode drop the sentinel: `s[len]` is `.illegal`, natively
  defined. This is conservative; document it or carry the sentinel.
* **H5.** illegal-behavior.md row 23 is stale (now `.illegal`). For the std rows that select
  hand-written models (`Io.async`, `Future.await`/`cancel`, `Io.checkCancel`, `Thread.detach`,
  `Io.Group.async`), record a maintainer decision or a `legacy-to-retire` deletion plan.

## Reviewed and sound

Each change was checked against three questions: is a false native statement provable, is a
precondition never satisfiable, and does an adequacy path to a real run exist.

| Change | False native statement? | Vacuous precondition? | Adequacy |
|---|---|---|---|
| Mixed-size atomics R1 (#323, `ALoc.overAt`) | No. Retirement needs every access to the shared bytes to have happened before the op. A racing mixed-size access throws `.unspecified`, and an access to the other bytes of a retired location starts a new location from the newest bytes. Older values are lost only on schedules the model makes `.unspecified`. That is fail-closed for error-forbidding logics, but S4 for non-strict ones. | No (`MixedSizeCX.arena_rule`, `HeaderMixCX`) | thread rules → `CTriple` → `WP.call_fowned` → `run_sound`/`run_safe` |
| MM-20 const reads record nothing | No. No write to a `const` global is ever recorded (`accessW`, `recordAccessIn`). The consumer table of memory-model.md §MM-20 checks out. External writers fall under EXT-06. | No (`ConstReadCX`) | as above |
| `CTriple` via `CTriple.Run` (#299) | No. A stop at a non-solo op is `False` (`SyncOp.Solo`), which closes structure audit #1. Resumption needs `MsgCov` or the solo answer; `MsgCov` is carried by `FOwned` and kept by `FStepIn.msgCov`. | witnesses: see F3 | `toSolo` (in-thread `FTriple`), `WP.call_fowned` (`Run.safe`: error leaf = `.stackOverflow` only) |
| `weakCasPtr` (#304) | No. Spurious failure is an option of every matching message (`weakCasOpts`, `weakCasPtrPrep`). The pointer compare gives `.unspecified` where identity and address disagree. | — | `WP.cmpxchgWeakC`, `CTriple.weakCasPtr` |
| Ticks and stack resources (#328) | No. `Mem.ticks` is observed only by `TickAuth`, and the translator emits no `tick` yet, so no claim uses credits for cost. `sp`/`plain` keep stack pushes sound (`push_without_sp_cx`); `noStack` needs `Mem.NoStack`, which the generated `mem0` has (no `withStack`). | `plain` only from adequacy (`initRes_holds_plain`) | `FTriple.run_init_plain`, `FTotalTriple.run_init_plain` |
| Allocator fee (#302) | No for clients, which must hold the fee. | **Yes for implementations: F2** | lists-fba only (F3) |
| ResetLedger | No: ghost state only, and `Holds`/`GOk` are unchanged. The `reset` precondition (the whole epoch token) is reachable from `init`. | — | arena tests only |

## The vacuity mechanism (proposal, not built)

**One companion per claim, computed from the claim's own type, pinned to the program's start.**
`ZigLean/Witness.lean` already computes `T.nonvacuous` and `T.returns` from a theorem's premise
telescope. Add a third, `T.reachable`. For a goal whose root's generated module defines
`mem0 σ = Mem.ofGlobals σ gs`, the companion is:

```
∃ σ xs, FAdmit.Start.reach gs (P xs)
FAdmit.Start.reach gs P := ∃ R, EUpd ((globals gs ⋆ plain) ⋆ gclaims gs) (P ⋆ R)
```

where `P` and `xs` are `T`'s precondition and binders.

* For an `Eq` head it reduces to today's argument telescope.
* For a `Sched.run` statement it is `∃ σ o fuel v m, (Sched.run … (mem0 σ)).run = some (.ok (v, m))`.
  The `*_completes` theorems already have this shape; the mechanism makes them mandatory.
* For an interface implementation (F2) it is `I.Reachable`, the same `EUpd` from the
  implementation's `init`.

`claims.py` then gives no strength (`none`, not `safety`) to a functional or absence claim whose
`reachable` companion is not verified, and `absence_claims` requires it too. The extractor checks
each companion as it checks today's: its kernel type must be exactly the computed statement. One
rule closes S1, F2 and F3 together.

## Re-running

```sh
scripts/full-build.sh
python3 tests/roadmap/architecture-audit/trust-chain/check.py --require-fixed
python3 scripts/build-guard.py --report r.json --log l.log -- \
  tests/roadmap/architecture-audit/soundness-1014/check.sh   # add --require-fixed for a fix branch
```

The translator cases re-translate their committed AIR with `.lake/build/bin/air2lean` and
elaborate the witnesses (`translator/check.sh`). To regenerate the AIR, use the patched
compilers: `scripts/zig-air.sh 0.16.0` (or `0.17.0`) with
`build-obj -fno-emit-bin -OReleaseSafe -target x86_64-linux -mcpu=baseline -fno-error-tracing`.
`libdir-spoof` adds `--zig-lib-dir <copy of lib with allocator-create.patch>`.

The native results come from stock 0.16.0 ReleaseSafe on aarch64-macos: `unsafe-panic/native.zig`
and `nonstrict-unspecified/nan.zig`.
