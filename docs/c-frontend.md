# C programs through translate-c (X01)

air2lean verifies C programs by first turning them into Zig with Zig's own C translator,
then running the ordinary Zig route. This page records the route, the trust statement, the
measured coverage of a 41-file C corpus, the named gates, the gaps in priority order, the
libc boundary, and a phased plan. The harness is `tests/roadmap/c-frontend/` (`check.sh`,
`run.py`, `cgen.py`, `test_run.py`). The register row (X01) is at the end.

## Architecture

```
f.c ──zig translate-c──▶ c_f.zig ──patched Zig 0.17.1 (AIR only)──▶ AIR JSON ──air2lean──▶ Gen.lean ──▶ proofs
        (stock 0.17.1,             (build-obj -fno-emit-bin -OReleaseSafe          (--allocator-model translated,
         -target x86_64-linux-      -target x86_64-linux-musl -mcpu=baseline -lc,    --assume-weak-exports,
         musl -lc)                  Zig's libc as the module `zigc`,                 --diagnostics-json, then
                                    ZIG_AIR_JSON_FILTER = the closure of `c_f.`)      emission, Lean elaboration)
```

* **translate-c** (Zig 0.17.1) is the Aro-based translator in `lib/compiler/translate-c/`,
  built from source on first use and cached. It is invoked as
  `zig translate-c -target x86_64-linux-musl -lc f.c`; `-lc` selects Zig's bundled musl
  headers. Zig 0.15.2 still ships the clang-based translator; the harness records its
  result for comparison only.
* The translated module is the root module `c_<file>` (not `<file>`: a root module named like
  a std file, for example `enums` or `linked_list`, shares its name prefix with std's own
  functions, and the translator then qualifies every name with the module).
* The translated module calls std code: `std.zig.c_translation.helpers` (`__helpers.*`, for
  example `signedRemainder`, which calls `debug.assert`) and `std.mem.zeroes` (C `= {0}` and
  missing initialisers, which calls `mem.asBytes`). Their AIR is exported and translated like
  user code; nothing C-specific is modelled. The exporter's filter is a list of name prefixes,
  so the harness closes the export (`run.py` `stage_air_export`, the fixed point of
  [project-workflow.md](project-workflow.md#dependency-closure)): each round adds the exact
  names of the referenced functions that have no AIR and exports again, and at the end every
  exported function the C module does not reach (another instance behind the same prefix) is
  removed. Panic handlers are the translator's own boundary and are never exported.
* The translator runs with `--allocator-model translated`
  ([allocator-model.md](allocator-model.md)), the mode the project is moving to. Translated C
  has no `std.mem.Allocator`; only this mode admits recovering a typed pointer from `void *`
  (`?*anyopaque` → `[*c]T`), which it checks to be free of error storage.
* Non-`static` C functions become `pub export fn`; `static` ones become `pub fn` with
  `callconv(.c)`. The harness exports every function reachable from `entry`.
* The AIR is exported from the compilation that `zig build-exe -target x86_64-linux-musl -lc`
  makes of the translated module. For a static musl target that compilation holds Zig's libc
  (`lib/c.zig`) as its module `zigc` (`src/Compilation.zig`, `zigc_strat == .zcu`), built with
  the program's own settings; the harness names the same module on the command line
  (`--dep zigc -Mroot=c_f.zig -fno-stack-check -fno-stack-protector -fno-builtin
  -Mzigc=<lib>/c.zig`), since the AIR-only compiler builds objects.
* libc functions are `pub extern fn` declarations. They are the libc boundary below: the
  translator binds an extern call by its linker symbol only ([EXT-03](premises.md#ext-03),
  [air-json.md](air-json.md#extern-calls)): to a trusted base model with a named premise, to
  the function of the AIR set that defines the symbol, or it rejects the program with
  `CALLEE_EXTERN_UNBOUND`, naming the symbol. The definitions of Zig's libc are weak
  `@export`s: the exporter's [export table](air-json.md#export-table) names them, the export
  closure follows a called symbol to its defining function, and the translator binds it under
  `--assume-weak-exports` ([EXT-07](premises.md#ext-07): the image links no other definition
  of the symbol), which the generated header records.

### Trust statement

> A theorem about `Gen.lean` produced from `f.c` is a theorem about the Zig program that
> stock `zig translate-c -target x86_64-linux-musl -lc f.c` (Zig 0.17.1) emits, as that
> Zig program is compiled by Zig 0.17.1 for x86_64-linux-musl with libc linked, in ReleaseSafe,
> and modelled by air2lean under its existing claims ([claim-strength.md](claim-strength.md)).
> A libc function that the program calls and Zig's libc defines in Zig is part of that
> program, under premise EXT-07 (the image links no other definition of its symbol). It is not a
> claim about `f.c` under ISO C or as compiled by gcc or clang. translate-c, the musl headers
> it reads, the Zig front end up to AIR and the patched AIR exporter are in the trusted base.
> Where translate-c's Zig is stricter than C (a ReleaseSafe panic on signed overflow, on a
> `@intCast` or on `@alignCast`) or differs from C (the findings below), the theorem follows
> the Zig meaning.

C undefined behaviour is therefore not modelled as such: signed overflow is a Zig
`integerOverflow` panic; an out-of-bounds `[*c]` access is a memory error of the Zig model;
uninitialised reads are Zig `undefined` reads. The harness compares every accepted program
with its C meaning on concrete inputs (below), so a divergence between the C and the Zig
meaning shows up as a `zig_native` failure (gate `NATIVE-DIVERGENCE`) rather than silently.

## Harness

Every corpus file defines `unsigned entry(unsigned a, unsigned b)`, deterministic and
resetting any state it uses. Inputs are Q01's `INPUTS` (`tests/roadmap/fuzz/zig_gen.py`):
`(0,0) (1,2) (4294967295,7) (305419896,2863311530)`.

| stage | what runs | outcome values |
|---|---|---|
| `c_native` | `zig cc -O0 -fsanitize=undefined -fsanitize-trap=undefined` on the host with a driver that calls `entry` twice per input | `ok` (expected values), `compile_error`, `runtime_error`, `nondeterministic` |
| `translate_c` | `zig translate-c` 0.17.1; warnings, and C functions (from `nm` of the C object) that became `extern fn` | `ok`, `demoted`, `failed` |
| `zig_native` | `zig test -OReleaseSafe -lc` on the host of the translated Zig (translated for x86_64-linux-musl) plus `expectEqual` against the C values; target-dependent header declarations such as `jmp_buf` are host-checked only | `ok`, `mismatch`, `compile_error`, `runtime_error` (a ReleaseSafe panic) |
| `air_export` | patched Zig 0.17.1 AIR export (as `scripts/translate.sh`), closed over the std callees | `ok`, `failed` |
| `air2lean` | `air2lean --diagnostics-json --allocator-model translated`; diagnostic codes | `checked`, `rejected` |
| `lean` | emission, Q01's `#guard` checks of `entry` on `mem0` (`zig_gen.lean_checks`), `lake env lean` | `ok`, `guard_failed`, `elab_failed`, `emit_failed`, `deferred` |

`lean` runs only when air2lean accepted the program and the translated Zig agreed with C.
The headline outcome is `lean_ok`, else `gated` when a named gate (below) rejects the file,
else the first failing stage in the order
`c_native, translate_c, air_export, air2lean, zig_native, lean`.

```sh
tests/roadmap/c-frontend/check.sh --light                 # CI: record check and unit tests, no tools
# heavy (local): wrap the whole call in one build-guard
AIR2LEAN_ZIG_NATIVE=~/.cache/air2lean/host-0.17.1/zig \
AIR2LEAN_ZIG_AIR=$(scripts/zig-air.sh 0.17.1) \
AIR2LEAN_ZIG_NATIVE_0152=~/.cache/air2lean/host-0.15.2/zig \
python3 scripts/build-guard.py --timeout 10800 \
  --report /tmp/cf.json --log /tmp/cf.log -- tests/roadmap/c-frontend/check.sh --heavy /tmp/cf-out
# generated UB-free programs (cgen.py), same environment and guard
tests/roadmap/c-frontend/check.sh --generated /tmp/cf-gen 0 30
```

`--heavy` builds the translator (`lake build ZigLean air2lean`), rewrites
`tests/roadmap/c-frontend/record.json`, and needs the tables below regenerated with
`python3 tests/roadmap/c-frontend/run.py tables`. `check.sh --light` (CI) verifies that the
record covers exactly the corpus with matching source hashes, that its summary and each
file's gates recompute from the per-file stages, that this page contains the generated tables
verbatim, the harness unit tests (`test_run.py`) and the generator's invariants. Committed
AIR: none; the per-file work directories stay local.

**Two hosts.** The compilers and the translator run where the patched compiler is; Lean
elaboration can run on a build host that has only Lean:

```sh
python3 tests/roadmap/c-frontend/run.py heavy --no-build --defer-lean --out WORK   # stages up to emission
# copy WORK/<file>/Check.lean to the build host (same relative paths), then there:
python3 tests/roadmap/c-frontend/run.py lean --out WORK                           # elaborates, rewrites the record
```

`--defer-lean` records the stage as `deferred` with the hash of `Check.lean`; `run.py lean`
elaborates exactly that file (a missing or changed one is `elab_failed`).

On macOS 27, Zig `translate-c` never finishes when its stdout is a pipe (it spins
in `fcopyfile`); the harness redirects stdout to a file.

## translate-c findings (Zig 0.17.1 and 0.16.0, Aro-based; 0.15.2 clang-based)

Shapes are quoted from the translated corpus (`.zig` files in the heavy work directory).

| C construct | translate-c Zig shape | notes |
|---|---|---|
| `[*c]` pointer arithmetic | `p + @as(usize, @bitCast(@as(isize, @intCast(n))))`; `p[@bitCast(@as(isize, @intCast(i)))]`; `q - p` is `@divExact(@as(c_long, @bitCast(@intFromPtr(q) -% @intFromPtr(p))), @sizeOf(T))`; `<` on `[*c]T`; array decay `@as([*c]T, @ptrCast(@alignCast(&buf)))` | a negative index becomes a huge `usize` (`p[-1]` is index 2⁶⁴−1) |
| `p++` in an expression | `blk: { const ref = &p; const tmp = ref.*; ref.* += 1; break :blk tmp; }` | |
| unsigned arithmetic | `+%`, `-%`, `*%`, `+%=` | wraps, as C |
| signed arithmetic | plain `+ - *`; `/` is `@divTrunc`; `%` is `__helpers.signedRemainder`; `>>`/`<<` take `@intCast` counts | C UB (overflow, shift ≥ width) is a ReleaseSafe panic |
| integer promotions | operands widened with `@as(c_int, c)`; narrowing stores `@truncate`; signed narrowing `@bitCast(@as(i8, @truncate(x)))` | |
| casts | integer: `@truncate`, `@bitCast`, `@intCast`, `@as`; pointer: always `@ptrCast(@alignCast(p))`, `void *` is `?*anyopaque`; `@intFromPtr`/`@ptrFromInt` | `@alignCast` adds a ReleaseSafe alignment check C does not have; for an alignment above 1 it is an `int_from_ptr` of the source pointer |
| comparison results in arithmetic | `@intFromBool(a > b) - @intFromBool(a < b)` | **bug**: `u1` arithmetic, panics where C yields −1 (G8) |
| `if`/loops, `break`/`continue` | `while (c) : (i += 1)` for `for`; `do … while` is `while (true) { …; if (!c) break; }` | |
| `switch` | `while (true) { switch (x) { v => { …; break; }, else => … } break; }`; fallthrough duplicates the following case bodies | case labels nested inside other statements (Duff's device): "TODO complex switch", function demoted to `extern` |
| `goto`, labels | refused: "TODO goto" (0.15.2: "TODO implement translation of stmt class GotoStmtClass/LabelStmtClass") | the function is demoted to `extern fn`; callers still translate |
| bitfields | the record becomes `opaque` ("struct demoted to opaque type - has bitfield"); every function that touches a member or a local of the type is demoted | 0.15.2 identical |
| unions | `extern union`; anonymous member unions are `union_unnamed_N` | |
| structs | `extern struct`; `= {0}`/missing initialisers are `std.mem.zeroes(T)`; the rest of a partly initialised array is `@as([N]T, @splat(std.mem.zeroes(T)))` (0.17.1: a runtime array `splat`); by-value copies | |
| variadic definitions | "TODO unable to translate variadic function, demoted to extern" | calls to variadic externs (`snprintf`) are emitted directly |
| `setjmp`/`longjmp` | plain `extern fn` calls on `[*c]struct___jmp_buf_tag` | Zig has no `returns_twice`: a `volatile` local is not preserved (native result 1000, C 1006) |
| string literals | `"…".*` arrays `[N:0]u8`; tables `[4][*c]const u8{ "zero", … }` | |
| `static` locals | `const static_local_x = struct { var x: T = init; };` | |
| object-like macros | `pub const SCALE = @as(c_uint, 3);` | |
| function-like macros | `pub inline fn SQUARE(x: anytype) @TypeOf(x * x)` | |
| macros with `#`, `##`, undefined names | `pub const STR = @compileError("unable to translate C expr: …")` | harmless unless Zig code refers to them: uses in C are preprocessed first |
| enums | `pub const RED: c_int = 0;`, `pub const enum_color = c_int;` | |
| function pointers | `?*const fn (…) callconv(.c) T`; calls `f.?(x)` | |
| libc calls | `pub extern fn strlen([*c]const u8) usize;` (0.15.2: `c_ulong` for `size_t`) | |
| struct layout | `extern struct`, so C layout; `sizeof`/`_Alignof`/`offsetof` are `@sizeOf`, `@alignOf`, `@offsetOf` | |

translate-c 0.17.1 keeps the refusals of 0.16.0 (`.goto_stmt, .computed_goto_stmt,
.labeled_stmt => fail "TODO goto"`, bitfield records demoted to `opaque`, variadic
definitions demoted, "TODO complex switch") and the `u1` comparator subtraction (G8).

**Zig 0.16.0 compiler bug (not translate-c), absent in 0.17.1.** Indexing an array that is
reached through a dereferenced C pointer, `p.*.data[i]` with `p: [*c]S` or `r.*[i]` with
`r: [*c][3]T`, has the *array* type instead of the element type in stock Zig 0.16.0 (a
compile error, or a silent miscompile for `&p->e[i]`). Zig 0.17.1 compiles the shape
correctly: `arrays_2d`, `ring_buffer`, `struct_layout` and `hash_table` translate and agree
with C. The route is on 0.17.1, so the bug (former gap G3) no longer applies; a 0.16.0 run of
the harness still reports it as `zig_native`/`air_export` failures.

## Gates

A gate is a named rejection: the program is not translated, and the record says why. The
harness derives each file's gates from its stage records (`run.py` `gates`); `check.sh
--light` recomputes them. A file with a gate has the headline outcome `gated`.

| gate | condition (evidence in the record) | why it is a rejection | lifted by |
|---|---|---|---|
| `TC-GOTO` | translate-c demoted a C function with the warning "TODO goto" | a function with `goto` or a label never reaches the translator: translate-c (0.15.2, 0.16.0, 0.17.1) emits it as `extern fn`, so the translator sees a call to a symbol without a definition (`CALLEE_EXTERN_UNBOUND`) | requirement L03 (C `goto` state machines) together with a translate-c that emits them (§goto) |
| `TC-BITFIELD` | demotion with "struct demoted to opaque type - has bitfield" | the record type is `opaque`; every function that touches it is demoted | translate-c support for C ABI bitfield storage units (L08) |
| `TC-VARIADIC-DEF` | demotion with "unable to translate variadic function" | the definition is demoted; its callers call a variadic extern | `@cVaStart`/`@cVaArg` in translate-c and the AIR va tags (L14) |
| `TC-COMPLEX-SWITCH` | demotion with "TODO complex switch" | case labels inside nested statements (Duff's device) | translate-c |
| `LIBC-SETJMP` | the translated Zig calls `setjmp`, `_setjmp`, `sigsetjmp`, `longjmp`, `_longjmp` or `siglongjmp` | Zig has no `returns_twice`: translate-c's plain calls do not preserve a `volatile` local (measured: 1000 where C gives 1006); `longjmp` is a `noreturn` extern, outside EXT-03 | not planned |
| `EXT-VARIADIC` | the translator rejected a call to a variadic extern (`snprintf`) that is not a demoted definition | a variadic extern is outside EXT-03: its contract depends on the format arguments | a contract for the symbol over a byte buffer (libc boundary) |
| `NATIVE-DIVERGENCE` | the translated Zig compiles but, run natively in ReleaseSafe, panics or returns other values than the C program (`zig_native` is `runtime_error` or `mismatch`) | translate-c's Zig does not have the C program's meaning on these inputs (G8: `(a > b) - (a < b)` as `u1` arithmetic; `setjmp`), so a theorem about it would not be about the C program; the Lean stage does not run | upstream translate-c fixes |

A demotion with none of these warnings, and a `zig_native` compile error, are not gates: the
file keeps its failing stage as outcome.

### goto

translate-c (0.15.2, 0.16.0 and 0.17.1) never produces a labeled-switch dispatch loop
from C `goto`: any function containing a `goto` or a label is demoted to `extern fn`,
so a goto state machine reaches air2lean only as a call to a missing symbol
(`CALLEE_EXTERN_UNBOUND`). air2lean's L03 loop-switch support would consume such a dispatch
loop if something produced it. Options:

| option | what | trust | size |
|---|---|---|---|
| reject (done) | the gate `TC-GOTO`: a translate-c "TODO goto" demotion of a corpus/project function is a named rejection of the file, not a silent `extern` | no change | S |
| patch translate-c (Aro backend) | forward `goto`s within one compound statement (cleanup ladders such as `goto_cleanup`) become nested labeled blocks left with `break :label`; general `goto` (backward jumps, `goto_state_machine`) becomes `state: switch (label_id) { … continue :state next … }` over the function's labels, with locals hoisted above the switch | the patched translator replaces stock translate-c in the trusted base, so it needs its own review and native differential (this harness) | M for forward-only, L for general; best done upstream |
| C-side rewrite before translate-c | a goto-elimination pass (for example on Aro's or clang's AST) that emits structured C (flags + loops + `switch`) and then runs stock translate-c | the rewriter joins the trusted base and is C-semantics-sensitive (scopes of declarations jumped over, VLAs, computed goto) | L |

Recommendation: the gate now, the forward-only Aro patch upstream next (it covers
the error-cleanup idiom), general goto only with upstream acceptance and L03.

## Results

Corpus: 41 files in `tests/roadmap/c-frontend/corpus/`, one construct family each plus
realistic programs (`strings_loops`, `memcpy_loops`, `linked_list`, `ring_buffer`,
`sort_callback`, `hash_table`, `malloc_vec`, the goto state machine, the bitfield packet
parser, `varargs_sum`). Recorded in `tests/roadmap/c-frontend/record.json` with stock Zig
0.17.1 and the patched AIR-only Zig 0.17.1 (`scripts/zig-air.sh 0.17.1`), every stage on the
x86_64-linux build host.

* **27 of 41 files translate end to end** and their `Gen.lean` `entry` agrees with the C
  program on all four inputs (`#guard`). `libc_ctype` is the first with libc calls: its
  `isdigit`, `isalpha`, `isspace`, `toupper`, `tolower`, `abs` and `labs` are the functions of
  Zig's libc (`lib/c/ctype.zig`, `lib/c/stdlib.zig`), translated from the program's own
  compilation and bound under EXT-07 (§libc boundary). The others cover integer promotions, unsigned
  wrapping, signed arithmetic (`signedRemainder`), 64-bit arithmetic, floats, `_Bool` and
  short-circuit logic, side-effecting expressions, `switch` (incl. fallthrough by
  duplication), loops with `break`/`continue`, enums, unions (type punning), structs and
  designated/compound initialisers, struct layout, multi-dimensional arrays, string literals,
  static locals, globals, function pointer tables, recursion, macros, pointer↔integer casts,
  `void *` byte loops (`memcpy`/`memmove`/`memset` written in C), and the realistic programs
  `strings_loops`, `linked_list`, `ring_buffer`, `hash_table` and `memcpy_loops`.
* **10 files are rejected by a named gate** (§Gates): six translate-c demotions (`goto` × 2,
  bitfields × 2, a variadic definition, Duff's device), `setjmp`/`longjmp`, a variadic libc
  call (`snprintf`), and two programs whose translated Zig panics natively where C does not
  (G8, the comparator idiom in `sort_callback` and `libc_stdlib`).
* **4 files are open:** `casts` (G2: an optional-pointer cast of Zig 0.17.1), `libc_string`
  and `malloc_vec` (G1b: their libc symbols have a definition in Zig, but none binds yet, for
  the three reasons of §libc boundary; `malloc_vec` also G2), and `ptr_arith` (G4: accepted,
  but the model's result is `.illegal` where native Zig and C are defined).
* Every C program ran cleanly under UBSan; translate-c's Zig agreed with C natively in 32
  files. The 9 others: 6 do not compile (the demotions), `libc_stdlib`/`sort_callback` panic
  in ReleaseSafe on the comparator idiom (G8), and `setjmp_longjmp` returns 1000 where C
  returns 1006.
* translate-c 0.15.2 (clang) and 0.17.1 (Aro) refuse the same six files.
* Against the 0.16.0 baseline (17 `lean_ok`): `arrays_2d`, `ring_buffer`, `struct_layout`
  (the 0.16.0 compiler bug is gone), `hash_table` (also the export closure and array
  `splat`), `initializers`, `signed_ops` (export closure), `linked_list`, `ptr_int_casts`
  (global initial values) and `memcpy_loops` (`void *` casts) are new.

`cgen.py` (seeds 0–29, `tests/roadmap/c-frontend/generated-record.json`, Zig 0.17.1): every
program passed every stage. These programs use unsigned arithmetic, signed comparisons,
`switch` with fallthrough, bounded loops with `break`/`continue`, local arrays, pointers to
array items, helper calls and reset globals, and no goto, libc or casts through `void *`.

generated headline: {"lean_ok": 30}

<!-- c-frontend tables: generated by tests/roadmap/c-frontend/run.py tables; do not edit -->

| file | C native | translate-c 0.17.1 | translate-c 0.15.2 | Zig native | AIR export | air2lean | Lean | codes | gates |
|---|---|---|---|---|---|---|---|---|---|
| arrays_2d | ok | ok | ok | ok | ok | checked | ok | – | – |
| bitfield_packet | ok | demoted (entry) | demoted | compile_error | failed | – | – | – | TC-BITFIELD |
| bitfields | ok | demoted (entry) | demoted | compile_error | failed | – | – | – | TC-BITFIELD |
| bool_logic | ok | ok | ok | ok | ok | checked | ok | – | – |
| casts | ok | ok | ok | ok | ok | checked | ok | – | – |
| enums | ok | ok | ok | ok | ok | checked | ok | – | – |
| expressions | ok | ok | ok | ok | ok | checked | ok | – | – |
| float_basic | ok | ok | ok | ok | ok | checked | ok | – | – |
| func_pointers | ok | ok | ok | ok | ok | checked | ok | – | – |
| globals | ok | ok | ok | ok | ok | checked | ok | – | – |
| goto_cleanup | ok | demoted (run) | demoted | compile_error | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×2 | TC-GOTO |
| goto_state_machine | ok | demoted (scan) | demoted | compile_error | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×1 | TC-GOTO |
| hash_table | ok | ok | ok | ok | ok | checked | ok | – | – |
| initializers | ok | ok | ok | ok | ok | checked | ok | – | – |
| inline_static | ok | ok | ok | ok | ok | checked | ok | – | – |
| int_promotion | ok | ok | ok | ok | ok | checked | ok | – | – |
| libc_ctype | ok | ok | ok | ok | ok | checked | ok | – | – |
| libc_stdio | ok | ok | ok | ok | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×1 | EXT-VARIADIC |
| libc_stdlib | ok | ok | ok | runtime_error | ok | rejected | – | CALLEE_BLOCKED×4, CALLEE_EXTERN_UNBOUND×7, CONSTANT_FAILURE×2, INSTRUCTION_FAILURE×1, PREREQUISITE_SKIPPED×1, PROGRAM_FAILURE×9, STRUCTURE_FAILURE×1 | NATIVE-DIVERGENCE |
| libc_string | ok | ok | ok | ok | ok | rejected | – | CALLEE_EXTERN_UNBOUND×4, PROGRAM_FAILURE×5 | – |
| linked_list | ok | ok | ok | ok | ok | checked | ok | – | – |
| loops | ok | ok | ok | ok | ok | checked | ok | – | – |
| macros | ok | ok | ok | ok | ok | checked | ok | – | – |
| malloc_vec | ok | ok | ok | ok | ok | rejected | – | CALLEE_BLOCKED×5, CALLEE_EXTERN_UNBOUND×8, CONSTANT_FAILURE×5, INSTRUCTION_FAILURE×1, PROGRAM_FAILURE×11 | – |
| memcpy_loops | ok | ok | ok | ok | ok | checked | ok | – | – |
| ptr_arith | ok | ok | ok | ok | ok | checked | guard_failed | – | – |
| ptr_int_casts | ok | ok | ok | ok | ok | checked | ok | – | – |
| recursion | ok | ok | ok | ok | ok | checked | ok | – | – |
| ring_buffer | ok | ok | ok | ok | ok | checked | ok | – | – |
| setjmp_longjmp | ok | ok | ok | mismatch | ok | rejected | – | CALLEE_BLOCKED×1, CALLEE_EXTERN_UNBOUND×2, INSTRUCTION_FAILURE×2, PROGRAM_FAILURE×1 | LIBC-SETJMP, NATIVE-DIVERGENCE |
| signed_ops | ok | ok | ok | ok | ok | checked | ok | – | – |
| sort_callback | ok | ok | ok | runtime_error | ok | rejected | – | INSTRUCTION_FAILURE×2 | NATIVE-DIVERGENCE |
| static_locals | ok | ok | ok | ok | ok | checked | ok | – | – |
| string_literals | ok | ok | ok | ok | ok | checked | ok | – | – |
| strings_loops | ok | ok | ok | ok | ok | checked | ok | – | – |
| struct_layout | ok | ok | ok | ok | ok | checked | ok | – | – |
| switch_fallthrough | ok | demoted (duff_sum) | demoted | compile_error | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×1 | TC-COMPLEX-SWITCH |
| switch_simple | ok | ok | ok | ok | ok | checked | ok | – | – |
| unions | ok | ok | ok | ok | ok | checked | ok | – | – |
| varargs_sum | ok | demoted (sum) | demoted | compile_error | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×3 | TC-VARIADIC-DEF |
| wide_ints | ok | ok | ok | ok | ok | checked | ok | – | – |

Headline outcome (`lean_ok` = translated and #guard-checked; `gated` = rejected by a named gate; else the first failing stage):

| outcome | files |
|---|---|
| air2lean | 2 |
| gated | 10 |
| lean | 1 |
| lean_ok | 28 |

Gates (files each named gate rejects):

| gate | files |
|---|---|
| EXT-VARIADIC | libc_stdio |
| LIBC-SETJMP | setjmp_longjmp |
| NATIVE-DIVERGENCE | libc_stdlib, setjmp_longjmp, sort_callback |
| TC-BITFIELD | bitfield_packet, bitfields |
| TC-COMPLEX-SWITCH | switch_fallthrough |
| TC-GOTO | goto_cleanup, goto_state_machine |
| TC-VARIADIC-DEF | varargs_sum |

Rejection histogram (files whose diagnostics contain the code):

| code | files |
|---|---|
| CALLEE_BLOCKED | 3 |
| CALLEE_EXTERN_UNBOUND | 9 |
| CONSTANT_FAILURE | 2 |
| INSTRUCTION_FAILURE | 4 |
| PREREQUISITE_SKIPPED | 1 |
| PROGRAM_FAILURE | 9 |
| STRUCTURE_FAILURE | 1 |

Outcome by C construct family:

| construct | outcomes |
|---|---|
| 64-bit arithmetic | lean_ok: 1 |
| bitfields | gated: 2 |
| designated/compound initializers | lean_ok: 1 |
| enums | lean_ok: 1 |
| floating point | lean_ok: 1 |
| function pointers | gated: 2, lean_ok: 1 |
| globals | lean_ok: 1 |
| goto | gated: 2 |
| integer casts | lean_ok: 1 |
| integer promotions | lean_ok: 1 |
| libc ctype | lean_ok: 1 |
| libc stdio | gated: 1 |
| libc stdlib | air2lean: 1, gated: 1, lean_ok: 1 |
| libc string | air2lean: 1, gated: 1 |
| loops/break/continue | lean_ok: 1 |
| macros | lean_ok: 1 |
| multi-dim arrays | lean_ok: 1 |
| object-representation casts | lean_ok: 1 |
| pointer arithmetic | lean: 1, lean_ok: 1 |
| pointer<->integer casts | lean_ok: 1 |
| realistic | air2lean: 1, gated: 1, lean_ok: 5 |
| recursion | lean_ok: 1 |
| setjmp/longjmp | gated: 1 |
| short-circuit/_Bool | lean_ok: 1 |
| side-effecting expressions | lean_ok: 1 |
| signed arithmetic | lean_ok: 1 |
| static inline | lean_ok: 1 |
| static locals | lean_ok: 1 |
| string literals | lean_ok: 1 |
| struct layout | lean_ok: 1 |
| structs+pointers | lean_ok: 3 |
| switch | lean_ok: 2 |
| switch fallthrough | gated: 1 |
| unions | lean_ok: 1 |
| variadic call | gated: 1 |
| variadic definition | gated: 1 |
| void* byte loops | gated: 1, lean_ok: 1 |

<!-- end c-frontend tables -->

## Gaps, in priority order

Sizes: S ≤ 1 week, M 1–3 weeks, L > 3 weeks of focused work. "Files" counts corpus files
blocked (alone or with other gaps). G1, G3, G5, G6 and G9 of the 0.16.0 baseline are closed
(below the table).

| # | gap | translate-c Zig shape | rejected by | files | size | depends on |
|---|---|---|---|---|---|---|
| G1b | **libc symbols whose Zig definition does not translate** | `strcmp`, `strchr`, `malloc`, `free`, … bind through the C-ABI conversion (closed below) | (b) `CALLEE_EXTERN_UNBOUND` for `memcpy`, `memset`, `memcmp`, `strlen`: `compiler_rt` is another compilation, in ReleaseFast ([build-modes.md](build-modes.md)); (c) `lib/c/malloc.zig` reaches code outside the subset (§libc boundary); (d) `qsort`'s definition fails normalization ("global initializer"); `strchr` (`std.mem.findScalarPos`, Zig 0.17.1 `array_to_vector`) translates | 3 (`libc_string`, `malloc_vec`, `libc_stdlib`) | (b) M: programs of two build profiles; (c) L; (d) S | libc boundary; Q07, M01–M03, L09 |
| G4 | **negative `[*c]` index** | `p[@bitCast(@as(isize, @intCast(-1)))]` = index 2⁶⁴−1 | accepted, but the model's `p.elem 4 (2^64-1)` is past the block, so `entry` is `.illegal` while native Zig and C are defined (conservative, not unsound) | 1 (`ptr_arith`) | M: a signed (two's-complement) item offset for `[*c]`/many-item `ptr_elem_*`/`ptr_add` in the memory model, not a plain wrap modulo 2⁶⁴ (that would make index 2⁶² of a 4-byte item the same place as item 0, which the compiler's in-bounds pointer arithmetic does not promise) | L05 |
| G7 | **translate-c refusals** | `goto`/labels; bitfields; variadic definitions; case labels inside nested statements | gates `TC-GOTO`, `TC-BITFIELD`, `TC-VARIADIC-DEF`, `TC-COMPLEX-SWITCH` | 6 | goto: forward-only Aro patch M, general L (§goto); bitfields M–L (C ABI storage units as packed host integers); variadic definitions L; Duff M | upstream Aro translate-c or a pinned patch (joins the trusted base); L03, L08, L14 |
| G8 | **translate-c semantic divergences** | `(a > b) - (a < b)` → `@intFromBool(a > b) - @intFromBool(a < b)` (`u1` arithmetic); `setjmp`/`longjmp` as plain calls | gates `NATIVE-DIVERGENCE`, `LIBC-SETJMP` | 3 | S: upstream promotion fix | upstream translate-c |

Closed since the 0.16.0 baseline:

* **G1 (calls to `extern` functions).** The exporter writes an `externs` table and the
  translator binds each extern call by its linker symbol (EXT-03); an unbound symbol is
  `CALLEE_EXTERN_UNBOUND`.
* **G1b, the binding mechanism.** The exporter writes the compilation's `@export` records
  (the export table), the export closure follows a called symbol to its defining function in
  Zig's libc, and the translator binds a weak definition under EXT-07 (`libc_ctype`).
* **G1b (a), declarations that agree with the definition only at the C ABI.** The C-ABI
  conversion at the binding (§libc boundary, maintainer decision 2026-11-25): `strcmp`,
  `strchr`, `malloc`, `calloc`, `free` and `realloc` bind (`tests/roadmap/extern-abi`). What
  still keeps `libc_string`, `malloc_vec` and `libc_stdlib` out is G1b above.
* **G2 (Zig 0.17.1 casts of an optional pointer).** `--allocator-model translated` admits
  `?*anyopaque` ↔ `[*c]T` for error-free pointees (`memcpy_loops`); the self-referential struct
  cast (`linked_list`) translates in both modes; Zig 0.17.1's `int_from_ptr`/`ptr_cast` of
  `?*T` get the cast rules of the ≤0.16 `bitcast` (`casts`).
* **G3 (Zig 0.16.0 `p.*.f[i]`).** Not in 0.17.1.
* **G5 (zero-initialised globals whose address escapes).** The exporter writes the initial
  value (`linked_list`, `ptr_int_casts`).
* **G6 (std callees other than `zig.c_translation`).** The export closure above
  (`initializers`, `signed_ops`, `hash_table`).
* **Array `splat`.** Zig 0.17.1 emits a runtime `@splat` to an array as the AIR tag `splat`
  with an array type (translate-c: the zero tail of a partly initialised array). The
  translator emits `Vector.replicate len a`; a sentinel-terminated array is rejected, since the
  export does not carry the sentinel value (`tests/roadmap/zig017`: `air/splatArray.json`,
  `reject/splatSentinelArray.json`).
* **G9 (patched compiler on invalid Zig).** Not observed on 0.17.1: no translated corpus file
  fails to compile for AIR export. The two bitfield files export no function (`entry` itself is
  demoted), which the harness records as `air_export: failed` under the gate `TC-BITFIELD`.

## libc boundary

Symbols the translated Zig calls (`extern_calls` in the record). The rule is EXT-03: a symbol
is bound to the function of the AIR set that defines it (the real implementation compiled
through this same route), or to a trusted base model registered with a premise
(`--model-registry`, [external-models.md](external-models.md#extern-functions)), never to a
C-specific runtime model; without either the program is rejected.

**The pinned real code is Zig, and it is part of the program's compilation.** For a musl
target, the Zig 0.17.1 distribution defines every corpus symbol except `snprintf`, `setjmp`
and `longjmp` in Zig, not in musl's C (its `lib/libc/musl/src/string/` no longer has
`strlen.c`, `memcpy.c`, …): `lib/c/string.zig`, `lib/c/ctype.zig`, `lib/c/stdlib.zig`,
`lib/c/malloc.zig` and `lib/compiler_rt/`. `zig build-exe -lc` puts `lib/c.zig` into the
program's own compilation as the module `zigc`, with the program's build mode and panic
handler, so these functions are ordinary Zig for the existing route. The mechanism
(maintainer decision 2026-11-24):

* **Export records.** `lib/c.zig` defines each symbol with
  `@export(func, .{ .name = …, .linkage = .weak, .visibility = .hidden })`. The exporter
  writes the compilation's exports as `export-table.air2lean`
  ([air-json.md](air-json.md#export-table)).
* **Closure.** The harness's export closure follows an extern symbol to the function that
  the table names for it, as it follows a std callee without AIR.
* **Binding.** The translator binds the call to that function when it is the symbol's one
  definition in the program. A weak definition binds only with `--assume-weak-exports`:
  premise [EXT-07](premises.md#ext-07), the image links no other definition of the symbol
  (a strong `strcmp` in another object, archive or interposing shared library would replace
  Zig's). The harness passes the flag, and each generated header records `weak-exports`.
* **The C-ABI conversion at the binding** (maintainer decision 2026-11-25). The bound call is
  a direct call. Where the declared and the defined type of a parameter or of the result are
  the same, the value passes unchanged (`isdigit`, `abs`: `c_int` in, `c_int` out). Where they
  differ as the C ABI allows, the value is converted once at the call: each argument from the
  declared to the definition's parameter type, the result from the definition's to the declared
  result type. This is one general rule, not a model of any symbol. See below.

### The C-ABI conversion

translate-c declares C pointers (`[*c]const u8`, `?*anyopaque`); Zig's libc defines the
functions with Zig pointer types (`[*:0]const c_char`, `*const anyopaque`, `?[*]align(16) u8`).
Natively the value crosses the call unchanged: a pointer is an address in a register. The
definition's type still asserts things about it, and nothing checks them at a linker boundary
(no safety check is emitted for a value the caller passes), so a value that does not meet them
is illegal behaviour of the callee. The model makes that explicit
(`Air2Lean/Check.lean` `externAbiCall` chooses the conversion, `Emit.lean` applies it,
`ZigLean/Mem/Abi.lean` defines it):

| the target type asserts | where | a value that does not meet it |
|---|---|---|
| non-null | a single or many pointer (`*T`, `[*]T`, not optional, not C/allowzero) from an optional or C/allowzero one | `.illegal` |
| its alignment | a stricter alignment than the source's (`?[*]align(16) u8` from `?*anyopaque`) | `.illegal` (a null value has none) |
| its sentinel | a sentinel byte the source does not assert (`[*:0]const c_char` from `[*c]const u8`) | `.illegal` unless the byte occurs at or after the pointer in its live object (a null value has none) |

The conversion of the form is the cast rules' (L07): `ptrOfOptional` from `?*T`, the pointer
itself from `*T`, `[*]T` and a C/allowzero pointer, `ptrToOptional` to `?*T`.
`abiPtr_nonNull_eq`, `abiPtr_align_eq` and `abiPtrOpt_eq` state that the conversion agrees with
`ptrRequireNonNull`, `checkAlign` and `ptrToOptional` where only that requirement applies. The
test reads no byte as an access: it changes no state (`abiPtrCheck_run`), and the full-state
rules `FTotalTriple.abiPtrCheck_*` (`ZigLean/Sep/Full/Abi.lean`) let `fsym` walk it.

The sentinel test is a conservative over-approximation. A `strcmp` of two unterminated buffers
that differ before their end does not fail natively, but the model says `.illegal`. A pointer
into an object that does not exist is `.illegal`, as its address is (`ptrAddr`).

Only pointers are converted, and only when the pointees are compatible (or both free of error
storage, as the translated allocator model admits for `?*anyopaque` ↔ `[*c]T`). Everything else
stays rejected with `CALLEE_EXTERN_UNBOUND`, naming the symbol, the definition, the position
and the reason:

* a type that is not a pointer, or a differing integer, struct or other value;
* a function pointer: a call through it would need a conversion of its own (`bsearch`'s
  comparator);
* a sentinel the export does not record as a value. The exporter writes `sentinel_byte` for an
  8-bit item only, so `wcschr`'s `[*:0]const wchar_t` is rejected;
* a volatile, bit-offset or vector-element pointer, and a vector pointee;
* a callee whose address is taken: a call through the pointer would pass the value
  unconverted. A call through a pointer to the definition is checked as an indirect call,
  which needs equal types;
* a function that also calls the definition directly (`CALLEE_AMBIGUOUS`).

A function with a converted call is outside the certificate fragment and the timed subset.
`tests/roadmap/extern-abi` evaluates the conversion on translate-c output against Zig 0.17.1's
libc (`strcmp`, `strrchr`, `memrchr`, `malloc_usable_size`). It covers each `.illegal` case and
the rejected pairs (`test_cli.py`).

The remaining corpus symbols stay rejected for three reasons. Each is a translator or model rule,
not harness work:

1. **Definitions outside the subset.** `qsort`'s definition fails normalization. (`strchr`
   translates: its `std.mem.findScalarPos` loads 16-byte blocks as arrays and coerces them to
   vectors, Zig 0.17.1's `array_to_vector`, which the translator models lane-wise for every lane
   type, `tests/roadmap/zig017/tovec`. `libc_string` is now rejected only for reason 2.)
2. **`compiler_rt` is another compilation.** For an executable, `memcpy`, `memset`, `memcmp`
   and `strlen` come from `compiler_rt`, which the compiler builds separately and always in
   ReleaseFast (`Compilation.compilerRtOptMode`; not a qualified mode,
   [build-modes.md](build-modes.md)) while the program is ReleaseSafe. Their AIR
   can be exported (`zig build-lib … lib/compiler_rt.zig`), but one program then has two build
   profiles, which the translator rejects (`PROFILE_FAILURE`: mixed `build_mode`). Needs
   per-compilation profiles in one program (Q07) and an export table per compilation.
3. **`lib/c/malloc.zig` leaves the subset.** With libc linked, `malloc` is
   `std.heap.SmpAllocator` behind a size header. The translator rejects, in order of
   distance: the `undefined` context pointer it passes to the allocator's functions
   (`no_context: *anyopaque = undefined`, "an `undefined` operand is outside the subset");
   the `unordered` atomic load of a non-integer in `atomic.Mutex.unlock`; `Thread.getCpuCount` through libc's `sched_getaffinity`; and the page mapping: the
   trusted boundary `posix.mmap`/`munmap`/`mremap` (OSM-01) is qualified for Zig 0.16.0 only
   ("no reviewed std source for Zig 0.17.1 signature"), and below it std, with libc linked,
   calls musl's C functions `mmap`, `munmap`, `mremap` (variadic) and `__errno_location`,
   which no premise covers. No model is written by hand for any of this: `malloc`, `calloc`,
   `realloc` and `free` stay rejected until that code translates and OSM-01 is qualified for
   0.17.1.

| symbol | corpus files | status | definition in Zig 0.17.1 (x86_64-linux-musl) | notes |
|---|---|---|---|---|
| `isdigit`, `isalpha`, `isspace`, `toupper`, `tolower` | `libc_ctype` (`isdigit`, `isalpha` also `libc_stdio`) | **bound** (EXT-07) | `lib/c/ctype.zig`, over `std.ascii` | `libc_stdio` is rejected with the file (`EXT-VARIADIC`) |
| `abs`, `labs` | `libc_ctype`, `libc_stdlib` | **bound** (EXT-07) | `lib/c/stdlib.zig` | `@intCast(@abs(a))`: `abs(INT_MIN)` is a ReleaseSafe panic of the model and of the native program |
| `strcmp` | `libc_string` | **bound** (EXT-07, C-ABI conversion) | `lib/c/string.zig` | the file is rejected for the other symbols; `strings_loops` passes with equivalent hand-written C loops |
| `strchr` | `libc_string` | bound (EXT-07, C-ABI conversion); its definition is rejected (1) | `lib/c/string.zig` | |
| `memcpy`, `memset`, `memcmp`, `strlen` | `libc_string` | rejected: `CALLEE_EXTERN_UNBOUND` (2) | `lib/compiler_rt.zig`, `lib/compiler_rt/memcpy.zig` | |
| `qsort` | `libc_stdlib` | rejected: its definition fails normalization (1) | `lib/c/stdlib.zig` | the comparator is a function pointer, which the C-ABI conversion does not convert; G8 in the caller |
| `malloc`, `calloc`, `realloc`, `free` | `libc_stdlib`, `malloc_vec` | bound (EXT-07, C-ABI conversion); their definitions are rejected (3) | `lib/c/malloc.zig` | |
| `snprintf` | `libc_stdio` | gate `EXT-VARIADIC` | musl C (`src/stdio/snprintf.c`, `vfprintf.c`) | variadic, large, locale-dependent: a trusted base contract over a byte buffer first; translating it waits for variadic definitions (G7) |
| `setjmp`, `longjmp` | `setjmp_longjmp` | gate `LIBC-SETJMP` | musl assembly (`src/setjmp/x86_64/`) | not supported: no `returns_twice` in Zig; measured divergence |

The C objects (`nm -u` at `-O0`, `libc_symbols` in the record) also reference `memset` in 8
files: clang lowers `= {0}` initialisers to it. translate-c uses `std.mem.zeroes` instead,
so it is not a boundary symbol of the translated Zig.

## Phased roadmap

| phase | scope | acceptance |
|---|---|---|
| 0 (done) | corpus, harness, generator, committed records, CI record check | `check.sh --light` exits 0 in CI; `--heavy` reproduces `record.json` on a host with the patched compiler |
| 1: libc-free C kernels (done except G4) | the export closure, `void *` casts, array `splat`, named gates for translate-c demotions and divergences; the route on Zig 0.17.1 | every corpus file whose translate-c output has no demotion and no `extern` call is `lean_ok` or gated, except `casts` (G2) and `ptr_arith` (G4); `cgen.py` seeds 0–29 all `lean_ok` |
| 2: libc boundary | musl string/ctype/`abs`/`qsort` translated with the musl revision recorded; malloc family as trusted base with contracts in `docs/premises.md` | `libc_string`, `libc_stdlib`, `malloc_vec` `lean_ok`; every `extern_calls` symbol in the record is either a registered trusted-base row or translated AIR; a proof of one libc-using function (e.g. a `memcpy`/`strlen` specification) is kernel-checked |
| 3: translate-c completeness | G7, G8 upstream or as a pinned, reviewed translate-c patch | `goto_*`, `bitfields`, `bitfield_packet`, `varargs_sum`, `switch_fallthrough`, `sort_callback` `lean_ok`; the comparator idiom agrees natively |
| 4: realistic programs and proofs | project manifests accept C sources (I01); csmith (Docker image) differential at ≥ 1000 seeds; tutorial | csmith seeds with no out-of-scope constructs are `lean_ok` or carry a typed rejection; two kernel-checked proofs over translated C (ring buffer invariant, linked-list reversal) using P01–P05 tactics |

## Register row

Register row X01 (`assurance/register/X01.md`; open) is generated into `ROADMAP.md` and
`remaining-acceptance.md`.
