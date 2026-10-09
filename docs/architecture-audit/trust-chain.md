# Architecture audit 1/6: trust chain and fail-closed translation

Audit of `origin/main` at `af9ddc30` (2026-10-08). Scope: the patched AIR exporter
(`zig-patch/air-json/json.zig`), decode (`Air2Lean/Air/{StrictJson,Json,Profile}.lean`),
canonicalization (`Canon.lean`), normalization (`Normalize.lean`), the checker (`Check.lean`),
the emitter (`Emit.lean`), the std-model table (`StdModels.lean`), the `ZigLean` runtime
functions that generated code calls, the Lean trust escape hatches, and the receipt and claim
layer (`scripts/claims.py`, `scripts/project.py`, `scripts/proof-receipt.py`).

The question for every link: can the pipeline accept an input and emit Lean whose meaning
differs from what the Zig compiler does, with no check catching it? Severity:

* **SOUNDNESS**: an input is accepted and the generated model differs from Zig's semantics,
  so a provable claim about the model is false for the program. Unless marked *hand-edited*,
  the input is a real export from the patched 0.16.0 compiler.
* **FAIL-OPEN**: there is no counterexample from a real export yet, but the mechanism that
  should reject the input is absent. Correctness rests on an unenforced convention.
* **HARDENING**: defence in depth. A later stage or the exporter currently guards the link.

This audit applies no fixes. The counterexamples are in
[`tests/roadmap/architecture-audit/trust-chain/`](../../tests/roadmap/architecture-audit/trust-chain/).
`check.py` there runs a built translator on each case and prints `vulnerable` or `fixed`.
With `--require-fixed`, a fix agent's regression fails while its case is still vulnerable. Three
Lean files state wrong model facts as checked theorems, with the expected Zig result in their
comments. All seven cases were `vulnerable` with the translator built from `af9ddc30`.

## Fix status (soundness batch)

`tests/roadmap/architecture-audit/trust-chain/check.py --require-fixed` gates every fixed case in CI.

| # | Status | Fix |
|---|---|---|
| 1, 9 | fixed | module identity (B1): the exporter writes the module of every function, type and global; std models and special std types match only the `std` module (`std-name-spoof`, `std-type-spoof`) |
| 2 | fixed | the exporter writes `address_space`; a used non-generic pointer is rejected (`addrspace`) |
| 3 | fixed, one gap | every op checks its own illegal-behaviour precondition (`.illegal`): `memcpy` counts and overlap, slice ends and sentinels, float/int `@divExact`, `@ptrFromInt`, `@alignCast`, bare `unreach`, `for` lengths, memory `@fieldParentPtr` (`unchecked-memcpy`, `docs/illegal-behavior.md`). Remaining: a `for` loop with safety off whose second operand is a range or array has no length in AIR |
| 4 | fixed | reviewed asm allowlist; other asm is a declared device event or rejected (`volatile-asm`) |
| 5 | fixed | comptime fields are exported (`comptime: true`) and rejected when used (`comptime-field`) |
| 6 | open | emitter placeholders (`reduce-bool-handedit`): memory-model fix MM-6 |
| 7 | fixed | claim goals bind to the root's generated definition (`claims-unbound`) |
| 8, 10 | fixed | admission: only ReleaseSafe/stage2_llvm by default, legacy schemas only with `--profile legacy-abi64-le` (`build-mode`, `legacy-default`) |
| 11 | fixed | schema-12 deny-by-default schema table (`unknown-key`, `missing-flag`) |
| 12 | partly | the `call*` prefix rule is gone and `memcpy`/`memmove` are distinct ops; safe/unsafe arithmetic tags still share a model (each throws) |
| 13 | open | Gen.lean header revision/digest binding |
| 14 | fixed | panic handlers resolve only in the `std` module (B1) |
| 15 | fixed | integer, enum and packed constants are range-checked at decode |

## Ranked findings

| # | Severity | Finding | Counterexample |
|---|---|---|---|
| 1 | SOUNDNESS | Std models are selected by unqualified FQN. A user file `atomic.zig`, `mem.zig`, `Thread.zig` or `Io.zig` spoofs them | constructed (`std-name-spoof`) |
| 2 | SOUNDNESS | Pointer `addrspace` is not exported. `*addrspace(.gs) T` is translated as a generic pointer | constructed (`addrspace`) |
| 3 | SOUNDNESS | Some op models rely on Sema safety checks that `@setRuntimeSafety(false)` or ReleaseFast removes: `memcpy` with overlap or a length mismatch is modelled as `memmove`, memory-mode `slice_elem_val` has no length check, float `@divExact` has no exactness check | constructed (`unchecked-memcpy`) |
| 4 | SOUNDNESS | Volatile inline asm is a pure Lean `opaque` of its inputs, so `rdtsc() == rdtsc()` is provably true | constructed, Lean theorem (`volatile-asm/SameTick.lean`) |
| 5 | SOUNDNESS | `comptime` struct fields are exported as runtime fields that overlap `v` at offset 0. The model gives them value `0` | constructed, Lean theorem (`comptime-field/ComptimeField.lean`) |
| 6 | SOUNDNESS (hand-edited) | Emitter fallbacks (`panic!`, `pure default`, `-- air2lean: unexpected op`) are reachable from accepted input. `panic!` is `default` in the kernel, which in the Zig monads is a *successful* return of the default value | constructed (`reduce-bool-handedit`, `PanicDefault.lean`) |
| 7 | FAIL-OPEN | Claim goals are not bound to their root's generated function. Any audited `TotalTriple`, even about `pure v`, satisfies any root's `total_correctness` goal | constructed (`claims-unbound`, from the claims fixture report) |
| 8 | FAIL-OPEN | The profile accepts `build_mode` `ReleaseFast`, `ReleaseSmall` and `Debug` AIR. `docs/build-modes.md` says ReleaseFast AIR is never translated | constructed (`unchecked-memcpy/air-releasefast`) |
| 9 | FAIL-OPEN | Type identity is name-based. A struct named `mem.Allocator`, `Thread` or `Io` becomes a model handle type, whatever its fields or module | reasoned (same mechanism as 1) |
| 10 | FAIL-OPEN | Legacy schemas 1–11 are accepted by default (no `--profile`) under an unverified 64-bit little-endian assumption. The target is not checked | reasoned (hand edit: drop `profile`, set `schema` 11) |
| 11 | HARDENING | The decoder has no deny-by-default. It ignores unknown keys everywhere except `profile`. Absent flags take defaults even under schema 12. `layout`/`size` strings are not enumerated at parse time | reasoned; every real export carries the fields |
| 12 | HARDENING | Normalize merges tags that differ in safety or aliasing (`add`/`add_safe`, `memcpy`/`memmove`, `intcast`/`intcast_safe`, `store`/`store_safe`, `ret`/`ret_safe`). It also accepts any tag with the prefix `call` | reasoned; sound only because each shared model throws (except finding 3) |
| 13 | HARDENING | The `Gen.lean` header records only the profile and float semantics. It omits the translator revision, the AIR digests and the semantic flags `--spawn-policy` and `--proof-api` | reasoned; `project.py check` re-translates, receipts and manifests do not |
| 14 | HARDENING | Panic-handler callees are recognized by name (`debug.defaultPanic`, `debug.FullPanic((function 'defaultPanic')).*`) | reasoned; a spoof only makes the model more pessimistic |
| 15 | HARDENING | Integer and enum constants are range-checked in `Check.checkConstant`, not at parse time. `Emit`'s `"default"` arms for constants rely on the parser's shape invariants | reasoned; `checkConstant` guards this today |

**Status on the unmerged branches** `codex/roadmap-batch7` and `codex/roadmap-batch8`. Neither
branch addresses findings 1–12:

* Batch 8 exports `src.module` for each exported function's own declaration, which is the
  identity that the fix for finding 1 needs. The std-model lookup still uses only the callee
  FQN.
* Batches 7 and 8 add `Air2Lean/Revision.lean`, a digest of the translator sources. It covers
  part of finding 13.
* Batches 7 and 8 add an asm effect contract (`AsmContract.lean`) for read-write and memory
  operands. Volatile register-only asm (finding 4) still lowers to a pure opaque, because
  `asmIsEffect` does not consider `volatile`.

## 1. Std models are selected by unqualified FQN (SOUNDNESS)

**Location.** `Air2Lean/StdModels.lean`: `stdModel?` and `stdModelBase` look up the name
before `__anon_`. `Check.checkProgram` accepts a callee without AIR exactly when
`modelledStdFn callee` holds, and `Emit` lowers the call to the model. The exporter writes
callee identity as `ip.getNav(f.owner_nav).fqn` (`json.zig` `writeRef`, `.func`). That name is
relative to the owning module, so std's `lib/std/atomic.zig` and a user's `atomic.zig` both
produce `atomic.*`.

**Counterexample (`std-name-spoof`).** The user file `atomic.zig` defines
`pub fn spinLoopHint() void { @panic(...) }`. `spoof.zig` exports `answer()`, which calls it
and returns 42. With the default filter `spoof.`, the export contains the callee
`{"func": "atomic.spinLoopHint"}`. The translator accepts it and emits
`let _i0 ← Zig.spinLoopHintC; pure (.ret 42)`, so `answer` returns 42 in the model. Natively it
always panics.

The only guard (`checkProgram`: a *translated* function may not reuse a model name) does not
fire, because the filter leaves the spoofing body out of the input. That is the normal
configuration. The same works for every table entry:

* a user `mem.zig` with `pub const Allocator = struct { pub fn alloc(...) ... }`;
* a user module or file named `Thread` (`Thread.spawn`, `Thread.join`);
* one named `Io` (`Io.futexWait`, `Io.Group.async`).

**Structural fix.** Make callee identity semantic instead of textual. For every `func` ref and
every named type, the exporter writes the owning module (`file.mod.fully_qualified_name`, which
batch 8 already writes for a function's own `src`) and whether it is the compiler's std module.
`stdModel?` then matches only the pair (std module, fqn). A model name from any other module is
reported as a collision, not resolved as a model and not treated as an unknown callee.

## 2. Address spaces are not exported (SOUNDNESS)

**Location.** `json.zig` `writeTypeEntry`, `.pointer`. It writes `size`, `const`, `child`,
`ptr_align`, `volatile`, `allowzero`, `sentinel`, `host_size`, `bit_offset` and
`vector_index`, but never `info.flags.address_space`. The reader's `Ty.ptr` and `Layout` have
no field for it. The only address-space guards are the `addrspace_cast` tag (marked
`unsupported` by the exporter) and pointer *constants* into a non-generic address space
(`resolvePtr`).

**Counterexample (`addrspace`).** `readGs(p: *addrspace(.gs) const u64) u64 { return p.*; }`
and `readGen(p: *const u64)` are exported for `x86_64-linux`, an accepted profile. The `types`,
`params`, `ret` and `body` of the two files are byte-identical. The translator emits the same
`Zig.load (BitVec 64) 8 p0` for both. A proof about `readGs` therefore reasons about generic
memory at address `p`, while native code reads `%gs:p`, the thread-local segment.
Address-space pointers can be parameters, fields, globals and results without any cast.

**Structural fix.** Export `address_space` in every pointer type entry. The reader requires it
in the current schema, and `Check.checkTy` rejects any value other than `generic`. This is one
entry of the per-kind attribute whitelist in finding 11, so the next pointer attribute that
the exporter omits fails closed as well.

## 3. Op models depend on Sema checks that may be absent (SOUNDNESS)

**Location.**

* `ZigLean/Mem/Basic.lean` `memmove`, whose comment says "For `@memcpy`, the AIR checks before
  that the two ranges do not overlap".
* `Emit.lean` `.memcpy`, whose comment says "the AIR checks that both agree". The item count
  comes from the destination.
* `Normalize` maps `memcpy` and `memmove` to one `Op.memcpy`.
* Memory-mode `.sliceElemVal` lowers to `loadItem s s.ptr i`, with no `i < s.len` check. Pure
  mode uses `Zig.index`, which does check.
* Float `.div .divExact` lowers to `Zig.Float.div`, with no exactness check.

Sema emits these checks only when `block.wantSafety()` holds (`Sema.zig` `zirMemcpy`:
`memcpy_alias`, `copy_len_mismatch`; slice bounds; `@divExact`). `@setRuntimeSafety(false)`
removes them inside a fully qualified `ReleaseSafe` function. ReleaseFast removes them
everywhere (finding 8).

**Counterexample (`unchecked-memcpy`).** `shiftCopy(buf, n)` runs with
`@setRuntimeSafety(false)` and does `@memcpy(buf[1..n+1], buf[0..n])`, whose ranges overlap.
Its real `ReleaseSafe` export has no `cmp_gte`/`bool_or` alias check before `memcpy`;
`shiftCopySafe` in the same source has one. The translator accepts the export and emits
`Zig.memmove`. The model therefore gives a defined result where Zig specifies illegal
behaviour (LLVM `memcpy` on overlapping ranges). A theorem about the model is then a claim
about a program whose native behaviour is undefined, and the `illegal_behavior` outcome
accounting never sees it.

The other unchecked AIR ops already throw in their models (`Zig.intCast`, `Zig.optPayload`,
integer `Zig.divExact`, `Zig.shlExact`, `unreach`). Only the ops listed above depend on the
convention.

**Structural fix.** Enforce one rule per op: *every AIR op's model checks its own
illegal-behaviour precondition and throws `.illegal`*, whether or not a Sema check precedes it.

* `memcpy` checks for overlap and equal lengths.
* Memory-mode slice item reads check the length.
* Float `div_exact` checks exactness.
* `memcpy` and `memmove` stay distinct ops.

In `ReleaseSafe` the Sema check still fires first (`.panic`), so existing proofs do not change.
Add an inventory that lists, for each `Op`, its illegal-behaviour precondition and the model
line that enforces it.

## 4. Volatile asm is a pure function (SOUNDNESS)

**Location.** `Emit.lean` `.asm` emits one `opaque airAsm_<hash>` per (source, constraints,
widths) and applies it as a pure term. `Check.lean` `.asm` ignores `isVolatile`.
`docs/generated-code.md` §Inline asm states this as a residual.

**Counterexample (`volatile-asm`).** `rdtscLow()` is
`asm volatile ("rdtsc" : [ret] "={eax}" (-> u32) :: .{ .edx = true })`, and `sameTick()`
returns `rdtscLow() == rdtscLow()`. The translator emits a 0-ary
`opaque airAsm_1434560075 : BitVec 32`. `SameTick.lean`, the unchanged generated text plus a
theorem, proves `Audit.sameTick = pure true` with `simp`. Natively `sameTick` returns `false`.
Every volatile asm with an output (counters, `rdrand`, port reads) has the same problem.

**Structural fix.** Choose one:

* Reject `volatile` asm unless it has no outputs, like the compiler-barrier entry of batch 8's
  `asmPureRegistry`.
* Lower volatile asm to the effect form (`airAsmFx_<hash>`, batch 8) and thread an opaque
  oracle or state through it, so that two executions are not definitionally equal.

## 5. Comptime struct fields (SOUNDNESS)

**Location.** `json.zig` `.@"struct"` writes every field counted by `structFieldCount`, with
`structFieldOffset`. That includes `comptime` fields, and no flag marks them.

**Counterexample (`comptime-field`).** For `struct { v: u32, comptime k: u32 = 7 }`, the
export says `fields: [{v, offset 0}, {k, offset 0}]` and `abi_size: 4`: two runtime fields
that overlap. The model's `structure S` has a stored field `k`. `mk(v)` never writes it, so its
value is the `Inhabited` default. `ComptimeField.lean` proves
`Audit.mk x = pure { v := x, k := 0 }`. In Zig, `mk(x).k` is `7` for every `x`.

The layout comparison in `Check` would probably reject `S` once it reaches memory, because the
model encodes it in 8 bytes. A by-value or `Locals` use is accepted.

**Structural fix.** Export `comptime: true` and the comptime value for each such field. The
reader then drops comptime fields from the runtime type, or the checker rejects them.
`validateTypeGraph` rejects overlapping ranges in non-packed fields and fields outside
`abi_size`.

## 6. Reachable emitter fallbacks (SOUNDNESS, hand-edited)

**Location.** `Emit.lean` emits text, not `Except`. Each arm that it assumes unreachable emits
one of these:

* `(panic! "air2lean: ...")`, for an arithmetic `@reduce` of a bool vector, a bitwise
  `@reduce` of a float vector, `is_null_ptr` of a non-optional, an error-union pointer op on
  another type, and `try_ptr` of a non-error-union pointer;
* `pure default`, or a `"default"` constant;
* `-- air2lean: unexpected op in straight-line position`, which drops the instruction.

No stage scans the output for these markers. In the kernel `panic! msg` is `default`.
`PanicDefault.lean` proves by `rfl` that this is a successful return of `default` (`false`,
`0`, ...) with the state unchanged in `Zig.M` and `Zig.MM`. It is not a failure.

**Counterexample (`reduce-bool-handedit`).** Start from a real export of
`@reduce(.Or, v == zero)` on `@Vector(2, u32)` and edit its `op` to `Add`. `Check.lean` has no
`reduce` rule at all, so the function is accepted, and `Emit` writes
`let i10 ← (panic! "air2lean: arithmetic @reduce of a bool vector")`. The model of `anyLane`
then returns `false`. Sema rejects this source, so the input has to be hand-edited. The point
is that the checker does not enforce the emitter's precondition.

**Structural fix.** Make emission total over checked input by construction: `Emit` returns
`Except String`, and every "unreachable" arm throws. At minimum, the CLI rejects output that
contains `panic!`, `air2lean: unexpected` or `pure default` before writing it. Add a checker
rule for each emitter precondition, starting with the compatibility of the `reduce` operator
and the lane type.

## 7. Claim goals are not bound to their root (FAIL-OPEN)

**Location.** `scripts/claims.py` `check_goal(goal, theorems, outcome_counts)` looks up the
theorem by exact name, checks the policy flag, and compares the strength derived from the
conclusion *head* (`Zig.TotalTriple`, ...). `tools/Assurance.lean` records only that head.
Nothing relates the theorem's program term to `root.function` or `root.namespace`.

**Counterexample (`claims-unbound`).** The existing claims fixture report contains
`ClaimFixture.ret_total : TotalTriple P (pure v) ...`. Used as the goal theorem of a root
`basic.tardiness` with strength `total_correctness`, it makes `check_goal` return `accepted`.

**Structural fix.** Extend the extracted conclusion shape with the program constants: the
program argument of `Triple`, `TotalTriple` or `Returns`, or the left side of `Eq`. Require
that argument to be the generated definition `<namespace>.<mangled root function>` from the
root's generated module, as an exact kernel name applied only to bound variables. Reject a goal
whose theorem does not mention it.

## 8. Unqualified build modes are accepted (FAIL-OPEN)

**Location.** `Air2Lean/Air/Profile.lean` accepts `Debug`, `ReleaseSafe`, `ReleaseFast` and
`ReleaseSmall`. `docs/build-modes.md` says "ReleaseFast AIR is never translated", and only
ReleaseSafe with LLVM is qualified.

**Counterexample.** `unchecked-memcpy/air-releasefast/` is a real `-OReleaseFast` export of
`shiftCopySafe`, the source *with* runtime safety. No alias or length check remains. The
translator accepts it with `build_mode: ReleaseFast` in the header and emits `Zig.memmove`.

**Structural fix.** Profile admission follows `assurance/build-modes.json`: only qualified
(mode, backend) pairs are accepted, unless an explicit opt-in flag is given. The opt-in is
recorded in the generated header and in the claims.

## 9. Name-based model types (FAIL-OPEN)

**Location.** `Json.parseTy`, `"struct"`, maps `name == "mem.Allocator"` to `.allocator`,
`"Thread"` to `.thread` and `"Io"` to `.io` before it reads the fields. `checkTy` accepts these
types without recursion, and `usedTys` does not emit their fields.

**Scenario.** A user file `Thread.zig` (whose root struct is named `Thread`), or a user module
named `Io`, becomes an opaque model handle type. Field reads and writes of the user's struct are
then not typed against its real layout. Combined with finding 1, its methods become std
models.

**Fix.** The same as for finding 1: module-qualified identity (the std module) for model types,
and rejection of a model-named type from any other module.

## 10. Legacy schemas are accepted by default (FAIL-OPEN)

**Location.** For `schema < 12`, `Profile.parse` returns the `legacy-abi64-le` profile with
`unverified` facts and checks only `target_endian`, if present. `--profile` is optional.

**Scenario.** Take an export for a target that the schema-12 path rejects, such as a 32-bit
target or aarch64-linux, remove `profile` and set `schema: 11`. The translator then translates
it under the x86_64-linux 64-bit assumptions. The generated header records `legacy-abi64-le`,
and project manifests list `legacy-reference-abi` as an assumption, so `project.py` users see
the assumption. The bare CLI does not report it.

**Fix.** Require an explicit `--profile legacy-abi64-le` for schemas below 12 (deny by
default).

## 11. The decoder has no deny-by-default (HARDENING)

**Location.** `Json.lean` reads every object with `getObjVal?` or `optField`, so extra keys
are ignored. Only `profile` has a whitelist.

* `boolField` defaults absent flags to `false`: `volatile`, `allowzero`, `sentinel`, the
  `const`, `threadlocal` and `extern` of globals, `noreturn`, and asm `volatile`.
* `host_size` defaults to 0, and `ptr_align` and `abi_size` may be absent.
* `layout` and pointer `size` are free strings until `checkTy`. Every test of the form
  `layout == "packed"` or `layout == "extern"` treats an unknown `layout` string as `auto`.

`docs/volatile-effects.md` lists the missing-`volatile` default as a residual.

**Why it matters.** Findings 2 and 5 are exporter omissions. The next omission (a new pointer
flag, a new field kind, an attribute added in 0.17) will again be dropped silently, because
the reader never reports that a key or value is not understood.

**Fix (one mechanism).** Keep a schema table per kind (type kinds, ref forms, instruction tags).
For each schema version it lists the required keys, the optional keys and the allowed enum
values. Decoding rejects unknown keys and missing required keys. Semantic attributes have a
single whitelist per kind (`ptr: address_space ∈ {generic}`, `volatile`, `allowzero`, ...).
Legacy schema readers keep their current defaults behind the explicit legacy opt-in of
finding 10.

## 12. Merged tags and the `call*` prefix (HARDENING)

`Normalize.normalizeOp` maps these tags to shared ops:

* `add` and `add_safe` (likewise `sub` and `mul`) to `.checked`;
* `intcast` and `intcast_safe` to `.intCast`;
* `store` and `store_safe`, `ret` and `ret_safe`, `memcpy` and `memmove` to one op each;
* any tag with the prefix `call` to `.call`.

The merges are sound today because each shared model throws on the illegal input of the
unchecked op. The exception is `memcpy` (finding 3). A future Zig tag named `call_*` with
different semantics would be accepted silently.

**Fix.** List the four call tags explicitly. Keep the safe/unsafe distinction in `Op`, for
example as a `Safety` field, so that a model change cannot silently weaken an unchecked op.

## 13. Binding of the generated file (HARDENING)

`Main.lean` writes `-- air2lean-profile: {profile, float_semantics, correspondence}`, plus the
models. It does not record the translator revision, the AIR input digests, or the flags that
change semantics (`--spawn-policy`, `--proof-api`, `--prefix`). `scripts/project.py check`
re-translates and compares bodies, which is good. The artifact manifest and the proof receipt
only record identities, as documented.

**Fix.** The header records `{translator_revision, air_sha256 per file, flags}`.
`normalize-generated.py compare`, the manifest and the claims check then refuse a `Gen.lean`
whose header does not match a fresh translation of the recorded AIR by the recorded translator.

## 14–15. Panic-handler names; constant shapes (HARDENING)

`Op.panicErrorFor?` maps callee names to `Zig.Error`s. Suppose a user `debug.defaultPanic`
exits successfully at run time. The model still treats it as `.panic`, which only refuses
claims, so the error is conservative. Module-qualified identity (finding 1) covers this case
too.

`parseLeafVal` and `parseVal` accept integer and enum constants of any magnitude. The range
checks live in `Check.checkConstant`, and `Emit`'s constant arms (`"default"`) rely on the
parser's type-shape invariants. Moving the range check into the decoder would keep the
invariant in one place.

## Links reviewed without a finding

* **Exporter instruction writer.** Every decoded tag is listed explicitly, and any other tag
  is written as `"unsupported": true` (deny by default). `Normalize` rejects marked tags,
  `*_optimized` tags, and the runtime and legalization tags, each with a reason.
* **Decoding and profile.** `StrictJson` rejects duplicate keys and enforces depth, size and
  number bounds. The schema-12 `Profile` has a key whitelist and pins the pointer width,
  endianness, target scope, float mode and export stage.
* **Canonicalization.**
  * `validateRefs` (scoping, branch targets, no SSA refs inside constants) runs before and
    after the rewrites.
  * `forwardReadOnlyCopies` excludes volatile pointers and requires dominance.
  * `dropTrueChecks` drops only a duplicate of a dominating check in the same body, or
    `0 <= x` and `x <= x + y` for unsigned, non-wrapping adds.
  * `argRanks` checks every `arg` type against its parameter slot.
* **Volatile memory accesses.** `checkVolatile` rejects them for every access op.
* **Lean trust.**
  * `assurance/policy.json` allows only the axioms `propext`, `Classical.choice` and
    `Quot.sound`. `sorryAx`, `Lean.ofReduce*` and native-decide axioms cannot be allowlisted.
  * Project opaques (`Float.libm`, the asm opaques, the simp and label extension handles) are
    listed by exact name.
  * The audit walks every `ZigLean/` and `Proofs/` module and their transitive constants. No
    `axiom`, `native_decide` or `sorry` occurs in `ZigLean/` or `Proofs/`.
  * The only `implemented_by` is on `Float.libm`, which has no defining equation and so no
    logical content.

  The kernel meaning of `panic!` is a separate problem (finding 6). The audit does not inspect
  generated code for it.
* **Program-level consistency.** All files must share one profile. Duplicate function names
  are rejected, and shared named types and globals are compared structurally, including their
  layout.

## Re-running

```sh
python3 scripts/build-guard.py ... -- lake build air2lean
python3 tests/roadmap/architecture-audit/trust-chain/check.py
lake env lean tests/roadmap/architecture-audit/trust-chain/volatile-asm/SameTick.lean
lake env lean tests/roadmap/architecture-audit/trust-chain/comptime-field/ComptimeField.lean
lake env lean tests/roadmap/architecture-audit/trust-chain/reduce-bool-handedit/PanicDefault.lean
```

The `*.zig` sources next to each case regenerate its AIR with the patched compiler, for
example:

```sh
ZIG_AIR_JSON_DIR=out ZIG_AIR_JSON_FILTER=spoof. zig-air-0.16.0/bin/zig build-obj \
  -fno-emit-bin -OReleaseSafe -fno-error-tracing spoof.zig
```

* `addrspace` and `volatile-asm` add `-target x86_64-linux`.
* `air-releasefast` uses `-OReleaseFast` and the filter `mc.shiftCopySafe`.
* `reduce-bool-handedit` changes the exported `"op": "Or"` to `"Add"`.
