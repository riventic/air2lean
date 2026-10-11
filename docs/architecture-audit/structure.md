# Architecture audit 6/6: structure, extensibility and scaling

Date: 2026-10-08. Base: `origin/main` af9ddc30. Also inspected: `origin/codex/zig-0.17-integration`,
`codex/roadmap-air-semantics` (V01), `codex/alloc-translated-p1`, `codex/roadmap-big-endian`,
`codex/c-frontend-coverage`. This audit records findings only; it changes no code.

This audit asks whether the current structure supports five upcoming directions or gets in their way:

| # | Direction |
|---|---|
| D1 | std allocators, IO and sync translated from real code; only the posix primitives (`mmap`/`munmap`/`mremap`, futex, ...) are trusted |
| D2 | C programs through `zig translate-c` |
| D3 | Zig 0.14.1–0.17.0 (and 0.18+), x86_64, aarch64, wasm32 and big-endian targets, build modes and backends |
| D4 | large real programs: the whole std closure, performance, modular output, incremental checking |
| D5 | formal AIR semantics and translation certificates (V01/V02) |

Ranks: **BLOCKER** means the direction cannot be done soundly on the current structure.
**SCALING** means the direction works, but each step costs more over time. **CLEANUP** means
maintenance cost only. Costs are rough agent-days (d) or weeks (w).

## Measurements

| What | Value | How |
|---|---|---|
| Translator size | 11.4k lines; `Emit.lean` 3480, `Check.lean` 2711, `Memory.lean` 543 | `wc -l Air2Lean/**/*.lean` |
| `Op` constructors | 93; `match … op with` sites: Emit 46, Check 23, Memory 21, ProofApi 3 | `Air2Lean/Air/Op.lean`, grep |
| Wildcard arms `\| _ =>` | Emit 144, Check 99, Memory 39 | grep |
| Zig-version string literals / `zigVersion` branches in `Air2Lean/` | main: 81 in 12 files. 0.17 integration branch: 144 in 14 files (Canon 25, Check 23, StdModels 22, Emit 16, Normalize 11, BitCast 8) | grep `0\.1[4-7]\.\|zigVersion\|zigBefore` |
| Version literals in CI / scripts | `ci.yml` 95 on main, 125 on the 0.17 branch; 14 scripts | grep |
| Exporter | `json.zig` 1772 lines, one source for every version (comptime `Compat`); `hook.patch` is a one-line call per version; the 0.17 port changed about 157 lines | `zig-patch/` |
| Files touched to add one tag pair (`byte_swap`/`bit_reverse`, 624c5f00) | 24 files; 6 of them in the translator/exporter/runtime core | `git show --stat` |
| CI | 1 workflow, 1322 lines, 131 steps, 78 `if:` conditions, 9 jobs; about 34 min wall time and about 150 job-minutes per green run (run 37811576830); 19 of the last 30 runs were cancelled (11) or failed (8) | `gh run list/view` |
| Python | 57 scripts (14.7k lines) and 131 test `.py` files under `tests/roadmap` (25k lines); 11 scripts load sibling scripts with `spec_from_file_location` | `wc`, grep |
| Whole closure of the tiny `examples/lists` (0.16.0, unfiltered export) | **1742 functions, 62 MB of AIR, 154k instructions.** About 65% of the JSON bytes are per-function copies of the type table | `scratch/closure` (not committed) |
| The same closure in `--diagnostics-json` | Only the first 256 files are inspected (`Diagnose.maxFiles`). Of those, 146 pass and 110 are rejected or blocked; 624 diagnostics are "named dependency absent/blocked" | translator from main lineage |
| Generated output | Largest Gen.lean 1543 lines. Elaboration takes 0.6–2.2 s per example; the cold threadsync proof takes 30 s | `assurance/perf-budgets.json` |

## Fix status (soundness batch)

| Risk | Status | Fix |
|---|---|---|
| B1 | fixed | module identity: exporter `module` fields, `Air2Lean/Air/Identity.lean` keys, required in schema 12 |
| S2 | fixed | `Op.effects` is the exhaustive classifier (no wildcard arm); `air2lean --print-op-table` feeds `scripts/coverage.py`; unknown and unlisted `call*` tags are rejected |
| B2, B3, B4, S1, S3, S4, C1, C2 | open | content-addressed instances and later structure work |

## Ranked risks

### B1 — BLOCKER (D1, D2, D4; soundness today): a function's or type's identity is its module-less fqn

The exporter names a function by `ip.getNav(owner_nav).fqn`. That name is the path of the file
inside its module plus the declaration. It does not include the module. The JSON filename,
call operands, `StdModels` lookup and the `Ty.allocator`/`thread`/`io` recognition
(`Air/Json.lean:185-187`, which matches the bare struct names `"mem.Allocator"`, `"Thread"`
and `"Io"`) are all keyed on this string.

**Counterexample (reproduced; the files are under `scratch/mods`, not committed):** the root module has
`util.zig` with `helper(x) = x +% 1`. A dependency module `other` also has `util.zig`, with
`helper(x) = x *% 3`. `entry(x) = util.helper(x) +% other.util.helper(x)`.
`zig build-obj --dep other -Mroot=main.zig -Mother=b/root.zig` with the patched 0.16.0 compiler
writes **one** `util.helper.json`, holding the `mul_wrap` body. The exporter's identity check
compares only the fqn, so the second function silently replaced the first. The translator exits
0 and emits two `Zig.call (util_helper p0)` calls with the same body: Gen.lean computes `3x+3x`,
but Zig computes `(x+1)+3x`.

A similar case: a user `Thread.zig` with `pub fn spawn` exports `Thread.spawn`, the same string
as the std model symbol. Today only two checks reject it: the "translated function conflicts
with built-in std model" check, and an arity mismatch in `checkModelSignature`. A user file with
the right arity, and same-named struct types, is accepted by name.

Why this blocks the directions:

* D1 brings std and user code into one translation unit. Both have `mem.Allocator`, `Thread`
  and `Io` names, and custom allocators are often named `Allocator`.
* D2: `translate-c` output is a root module named after the C file. C identifiers are global,
  and libc shims are separate modules.
* D4: real programs have many modules (`build.zig` dependencies).

**Recommendation.**

* The exporter emits a structured identity:
  `{module: <Package.Module fully-qualified name or root-path hash>, fqn, instance_key}`.
  It fails closed when two different `func_index`/`owner_nav` values write the same storage key
  in one compilation.
* The translator keys calls, std models, type recognition and Lean names on `(module, fqn)`. A
  std model also requires `module == "std"`.

Stop-gap (about 0.5 d): make the exporter's `openOwnedOutput` reject a second, different
`owner_nav` with the same fqn.

**Cost:** exporter 1–2 d, translator 2–3 d, goldens regenerated once. **Do now**: this is a
soundness bug that needs a fix agent.

### B2 — BLOCKER (D1): std types and functions are special-cased in the IR, not bound at a model boundary

`Ty` has the constructors `.allocator`, `.thread` and `.io`. Their fields are "not translated",
and their layouts are hard-coded (`Check.lean:256-258`: 16/8/16 bytes). `StdModels.lean` routes
about 30 std symbols to hand-written ZigLean models by name. Translating `mem.Allocator` from
real code needs `Allocator` to be a plain `struct {ptr, vtable}` with indirect calls through the
vtable. As long as `Ty.allocator` exists, the same AIR type has two incompatible meanings. The
P1 branch (`alloc-translated-p1`) adds a third mode inside `Check`/`Emit`/`StdModels`: 650
changed lines, 222 in Check alone.

**Recommendation.** Make the model boundary one mechanism, used only at calls:

* The existing `ModelRegistry` path, keyed by the B1 identity, becomes the only way to replace
  a callee by a model.
* Types are always translated structurally. Delete `Ty.allocator`/`thread`/`io` once their
  clients migrate.
* A model binding names its abstraction theorem: an `AllocSpec` instance, or an explicit
  posix premise.
* `--allocator-model=std|translated` should select a registry, not branch through
  `Check`/`Emit`.
* Freeze `StdModels`: no new rows. The posix primitives go in as registry entries.

**Cost:** about 1 w, on the alloc P1 critical path. **Do now as a design decision** (tell the
P1 agent). The deletion happens with P6.

### B3 — BLOCKER (D3) and SCALING: version and target semantics are string compares spread across stages

`Normalize.lean`'s module doc says all version knowledge lives in the tag table. That is no
longer true:

* `Check`/`Emit` branch on `zigVersion == "0.16.0"` (for example `memoryBitCastVersion`,
  `FCtx.zigBefore016`, the `Rt016` suffix, the allocSentinel/realloc qualification lists, and
  `TimedCheck` requiring 0.16.0).
* The 0.17 branch roughly doubles this: Canon 25 references, a new `BitCast.lean`, splat rules,
  and a `when_defined` proof gate.

Target facts are also fixed in several places:

* `Profile.lean` admits only `pointer_bits == 64`, `endian == "little"` and
  x86_64-linux/aarch64-macos.
* `modelLayout` hard-codes pointer = 8 and slice = 16 bytes.
* `ZigLean/Mem/Enc.lean` is little-endian by construction.
* Emit writes `BitVec 64` for lengths.

So wasm32 (32-bit `usize`) and big-endian targets are blocked in Check, Emit and ZigLean at
once. Each new version adds more `if zigVersion ==` branches, and none of them is tied to the
profile record that the receipts attest.

**Recommendation.**

* Add one `Air2Lean/Dialect.lean` with
  `structure Dialect where bitCast : .memory | .logical; unionWriteOrder; floatRtSuffix; ptrBytes; endian; errorSetBits; …`.
  `Dialect.ofProfile : BuildProfile → Except String Dialect` is the only function that reads
  `zigVersion`, the target triple or the build mode, and it fails closed for unknown
  combinations. Check, Emit, Memory and Canon take a `Dialect`, never a version string.
* Add a CI lint that rejects Zig-version literals in `Air2Lean/` outside `Dialect.lean`,
  `Normalize.lean` and the Canon version table.
* Python and CI read the version list from `compatibility.json` (see C1).
* For T02/T03, ZigLean's memory model takes `ptrBytes`/`endian` as parameters (a `Target`
  structure) instead of literals.

**Cost:** the Dialect record and lint, 2–3 d. Do it now, before the 0.17 integration merges its
additional branches (or as the first commit of that merge). The ZigLean target parameters take
2–4 w and belong before any wasm32 or big-endian work. The `codex/roadmap-big-endian` branch
currently adds a parallel `ZigLean/Endian.lean` instead.

### B4 — BLOCKER (D5) and design check: shallow Gen.lean with translation-validation certificates

The question was whether V02 needs a deep embedding and whether to switch now. **No.** The V01
branch has the right shape:

* a deep-embedded interpreter over the translator's own `Func` (`Sem.lean`);
* a printed `Func` term;
* a kernel-checked theorem per function, `execFunc func = <generated def>` (`Certificate.lean`).

The shallow Gen.lean stays the proof-facing artifact. The certificate makes the emitter
untrusted per function, without proving Emit correct once and for all. Switching Gen.lean to a
deep embedding would wreck proof ergonomics (proofs could no longer unfold `def`s) and is not
needed.

Three structural risks remain:

1. **Two memory models.** `Sem` keeps locals as value cells. Gen.lean keeps them as `Locals`
   fields (non-escaping) or as `Zig.Mem` bytes (escaping). It also has two slice
   representations: `Array` in pure functions and `Zig.Slice` in memory functions. A
   certificate covers only the fragment where these coincide. **Rec:** state `Sem` over
   ZigLean's `Zig.M`/`Zig.Mem` from the start, and treat the `Locals`/`Array` fast paths as
   emitter optimisations that get their own lemma. Do not grow `Sem` a third memory model.
2. **Emission strategies multiply.** Today there are several: pure vs memory, Locals vs Mem,
   `TimedEmit`'s separate Program path, `--proof-api`, and `--spawn-policy`. Each needs its own
   simulation argument. **Rec:** freeze the number of emission strategies until V02 covers the
   existing ones, and put new features (D1 vtables, D2 `[*c]`) on the Mem path.
3. **Certificate cost scales with program size** (154k instructions for a tiny program's
   closure). Certificates have to be per function and per module (see S1), and checked
   incrementally.

**Cost:** design decisions only, now; the implementation is V01/V02 itself.

### S1 — SCALING (D4, D1): one monolithic Gen.lean per program, program-relative names, no std reuse

* All JSON files of a program become one Lean file (`Main.lean`), and every proof imports it.
  Any change invalidates every proof.
* `Anon.renumberAnon` numbers generic instances by first use in *this* program, so
  `mem.Allocator.alloc__anon_1` means different instances in different programs. A proof about
  translated `PageAllocator`/`ArenaAllocator` cannot be reused across programs, and it is
  re-elaborated per program.
* The exporter writes the full type table into every function file: 24 MB of the 37 MB JSON in
  the `lists` closure.
* The diagnostics mode stops at 256 files.

The D1 plan ("prove PageAllocator once for any vt ⊨ AllocSpec") needs translated std code
to be a **shared, versioned library**, not part of each program's Gen.lean.

**Recommendation.**

1. Content-addressed instance names, from the exporter's `instance_key`: the generic owner
   plus a hash of the comptime arguments. Do this with B1.
2. One Lean module per Zig file or module, with stable interfaces (signatures plus
   `@[irreducible]` or opaque bodies for callees from other modules).
3. A std translation cache keyed by (Zig version, Dialect, translator hash, identity). It
   produces a `ZigStd_<ver>_<profile>` Lake package that programs import.
4. The exporter writes `types.json` once per compilation, and function files reference it.
5. Remove the 256-file cap, or make it explicit per run.

**Cost:** 1 is about 2 d (with B1); 2–3 is 2–4 w (I02/I04); 4 is about 2 d. **Sequencing:** 1
now; 2–4 before the alloc P4/P5 proofs are written, or they get written against unstable names.

### S2 — SCALING (all directions; soundness hazard): adding an AIR tag needs about 7 core edits, and wildcard arms fail open

A new `Op` constructor needs changes in Normalize, Op, Check, Memory and Emit (and sometimes
TimedCheck and ProofApi), plus the runtime, coverage/<ver>.json for every version, tests and
docs: 24 files for byte permutation. Lean's exhaustiveness check does not help, because the
safety analyses end in `| _ =>`. For example, `CheckCtx.checkVolatile` lists the pointer
accesses and ends in `| _ => #[]`, its `derived?` ends in `| _ => none`, and
`summarizeTryErrors` ends in `| _ => (later, cache)`. A new memory-accessing or control-flow
op (D1 needs several: pointer atomics, `ret_addr`, vtable loads; 0.17 adds 16 tags) is
therefore silently treated as "no access, no exit" by these checks unless the author remembers
every site.

The L14 gate (`coverage.py l14`) finds Emit dispatch arms by **regex over Lean source**. It
checks that an arm exists, not that the analyses classify the op.

**Recommendation.**

* Add one exhaustive, wildcard-free
  `Op.effects : Op → {reads, writes : Array Val, derivesPtr : Option Val, control : …, bodies : Array (Array Inst)}`
  in `Op.lean`. Check, Memory, Emit and Sem consume it, so adding a constructor fails to
  compile until it is classified.
* Have the translator print its op table (`air2lean --op-table-json`) and let `coverage.py`
  read that instead of scraping source.

**Cost:** 3–5 d. **Do now** (before D1 P1 and the 0.17 tags land).

### S3 — SCALING: CI is one 1322-line workflow that reruns everything on every push

Nine jobs and about 150 job-minutes per push. The 0.16.0 full job (34 min) is the critical
path. 78 `if:` conditions select steps by matrix cell. Offline Python gates (minutes) are
serialised behind the Lean/Zig builds in the same jobs. Mutation shards (5 jobs) run on every
PR. Each version or target added to D3 multiplies the matrix, and the 0.17 branch adds 74 lines
of version-specific steps. Patched-compiler and Lake caches exist and are keyed correctly.

**Recommendation.** Split the workflow into reusable workflows:

* `offline.yml`: Python gates, under 5 min, as the required fast signal;
* `translate.yml`: per version, goldens and stale-Gen check;
* `proofs.yml`;
* `mutation.yml`: label- or merge-queue-triggered, plus nightly.

Generate the version matrix from `compatibility.json`, add path filters (docs-only PRs skip
Lean), and move the `if: matrix.zig == '0.16.0'` step groups into a job of their own.

**Cost:** 2–3 d. **Sequencing:** next, before 0.17 doubles the version-specific steps.

### S4 — SCALING (D3): exporter maintenance per Zig version

The structure is sound:

* one `json.zig` with a comptime `Compat` section;
* a `@compileError` for versions without a branch;
* a one-line hook in `Zcu/PerThread.zig`;
* tarball pins checked by sha256.

The 0.17 port was about 157 changed lines. Two risks remain:

* `json.zig` uses compiler internals (InternPool, Type, Value, Air), so 0.18 will break some
  `Compat` arms.
* Semantic drift (renamed tags, the changed `@bitCast`) lands in the translator (B3), and
  golden churn is large: the 0.17 branch has 478 files and +242k lines, mostly goldens.

**Recommendation:**

* Keep the design. Add a per-version export-schema contract test: a small Zig corpus whose
  JSON is validated by `validate-air.py`.
* Keep semantics out of the exporter except layout facts.
* Store goldens per version as content-addressed fixtures, so that only changed functions show
  up in diffs.

**Cost:** 1–2 d. **Later.**

### C1 — CLEANUP: Python tooling has no shared core

Several scripts each implement source hashing and closures with different file sets and
bounds: `diff-report.source_hashes` (a hand-listed file set), `coverage.project_source_hashes`,
`project.hash_bounded`, `theorem-inventory._sha256`, `perf-budgets.digest`,
`assumptions.file_sha256`, `build-guard.digest`, `qualify-upgrade`, `release-record`,
`semantic-fingerprints` and `counterexample.sources_digest`. Eleven scripts import siblings by
file path. Version lists are repeated in 14 scripts, `workflow-common.sh` and `ci.yml`.
`compatibility.json` duplicates `zig-patch/versions.toml`.

Different closures mean two receipts can disagree about "the source" while both say
"current". That is a trust-chain risk, not only a style issue.

**Recommendation:**

* Add a `scripts/a2l/` package with `hashing.py` (one bounded file digest plus one canonical
  JSON digest), `closure.py` (one definition per artifact kind), `versions.py` (reads
  `compatibility.json`, the single source; `versions.toml` is generated or checked) and
  `manifest.py`.
* Add a lint that rejects `hashlib.sha256` outside the package.
* Migrate scripts when they are next touched.

**Cost:** about 1 w, done incrementally. **Later**, except that `versions.py` comes with S3.

### C2 — CLEANUP: Check/Emit god files and bespoke per-roadmap harnesses

`Emit.lean` (3480 lines) and `Check.lean` (2711 lines) mix types and layout, memory, calls and
models, and control flow. `tests/roadmap` has 79 directories, 27 bespoke `check.sh` files and
64 Lean `main`s. **Recommendation:**

* Split Check and Emit by concern along the `Op.effects` lines from S2.
* Give roadmap harnesses one runner, a `harness.toml` per directory, that CI enumerates instead
  of 146 hand-written `tests/roadmap` references in `ci.yml`.

**Cost:** 1–2 w, done opportunistically. **Later.**

## Notes on D2 (C via translate-c)

There are no extra structural blockers beyond B1, S1 and S2:

* translate-c output has globally named C symbols and a root module named after the file (B1);
* it pulls in `std.zig.c_translation`/`c_builtins` (S1, closure size);
* `[*c]` pointers, `@ptrCast` chains and `c_va_*` tags need new `Op`s and effects (S2).

libc models go through the same registry as posix (B2). There are no C-specific modes in
Check or Emit.

## Recommended sequencing

**Do now, before more features (about 2–3 agent-weeks, can run in parallel):**

1. **B1** identity: exporter stop-gap now, then structured `(module, fqn, instance_key)`
   identity. This is a soundness fix and takes priority over new roadmap items.
2. **S2** `Op.effects`, exhaustive and consumed by every analysis, plus the op-table export for
   the L14 gate.
3. **B3** `Dialect` record and a lint against version literals. Land it with, or before, the
   0.17 integration.
4. **B2** and **B4** design decisions, written down and given to the P1 and V01 agents:
   * no new `Ty` special cases or `StdModels` rows; model binding goes only through the
     registry;
   * `Sem` over ZigLean `Mem`;
   * the emission-strategy freeze.
5. **S1.1** content-addressed generic-instance names (shares the exporter change with B1).

**Next (with alloc P1–P3 and the C front end):** S3 CI split; S1.4 shared type table; C1
`versions.py`.

**Later (before "large real programs" and wasm/BE):**

* S1.2–3: per-module output and a versioned std translation package;
* B3: target-parameterised ZigLean (ptrBytes, endian);
* B2: deletion of `Ty.allocator`/`thread`/`io` after migration;
* S4: export contract tests;
* C1/C2 consolidation.
