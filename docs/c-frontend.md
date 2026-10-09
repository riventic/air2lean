# C programs through translate-c (X01)

air2lean verifies C programs by first turning them into Zig with Zig's own C translator,
then running the ordinary Zig route. This page records the route, the trust statement, the
measured coverage of a 40-file C corpus, the gaps in priority order, the libc boundary, and
a phased plan. The harness is `tests/roadmap/c-frontend/` (`check.sh`, `run.py`, `cgen.py`).
The register row (X01) is at the end.

## Architecture

```
f.c ──zig translate-c──▶ f.zig ──patched Zig 0.16.0 (AIR only)──▶ AIR JSON ──air2lean──▶ Gen.lean ──▶ proofs
        (stock 0.16.0,           (build-obj -fno-emit-bin -OReleaseSafe          (--diagnostics-json,
         -target x86_64-linux-    -target x86_64-linux -mcpu=baseline,             then emission,
         musl -lc)                ZIG_AIR_JSON_FILTER="f.,zig.c_translation.")      Lean elaboration)
```

* **translate-c** (Zig 0.16.0) is the Aro-based translator in `lib/compiler/translate-c/`,
  built from source on first use and cached. It is invoked as
  `zig translate-c -target x86_64-linux-musl -lc f.c`; `-lc` selects Zig's bundled musl
  headers. Zig 0.15.2 still ships the clang-based translator; the harness records its
  result for comparison only.
* The translated module calls `std.zig.c_translation.helpers` (`__helpers.*`, for example
  `signedRemainder`) and `builtins`. Their AIR is selected with the prefix
  `zig.c_translation.` and translated like user code; nothing C-specific is modelled.
* Non-`static` C functions become `pub export fn`; `static` ones become `pub fn` with
  `callconv(.c)`. The harness exports every function reachable from `entry`.
* libc functions are `pub extern fn` declarations. They are the libc boundary below: each
  symbol needs either a trusted base model or a translation of real libc code.

### Trust statement

> A theorem about `Gen.lean` produced from `f.c` is a theorem about the Zig program that
> stock `zig translate-c -target x86_64-linux-musl -lc f.c` (Zig 0.16.0) emits, as that
> Zig program is compiled by Zig 0.16.0 for x86_64-linux in ReleaseSafe and modelled by
> air2lean under its existing claims ([claim-strength.md](claim-strength.md)). It is not a
> claim about `f.c` under ISO C or as compiled by gcc or clang. translate-c, the musl headers
> it reads, the Zig front end up to AIR and the patched AIR exporter are in the trusted base.
> Where translate-c's Zig is stricter than C (a ReleaseSafe panic on signed overflow, on a
> `@intCast` or on `@alignCast`) or differs from C (the findings below), the theorem follows
> the Zig meaning.

C undefined behaviour is therefore not modelled as such: signed overflow is a Zig
`integerOverflow` panic; an out-of-bounds `[*c]` access is a memory error of the Zig model;
uninitialised reads are Zig `undefined` reads. The harness compares every accepted program
with its C meaning on concrete inputs (below), so a divergence between the C and the Zig
meaning shows up as a `zig_native` failure rather than silently.

## Harness

Every corpus file defines `unsigned entry(unsigned a, unsigned b)`, deterministic and
resetting any state it uses. Inputs are Q01's `INPUTS` (`tests/roadmap/fuzz/zig_gen.py`):
`(0,0) (1,2) (4294967295,7) (305419896,2863311530)`.

| stage | what runs | outcome values |
|---|---|---|
| `c_native` | `zig cc -O0 -fsanitize=undefined -fsanitize-trap=undefined` on the host with a driver that calls `entry` twice per input | `ok` (expected values), `compile_error`, `runtime_error`, `nondeterministic` |
| `translate_c` | `zig translate-c` 0.16.0; warnings, and C functions (from `nm` of the C object) that became `extern fn` | `ok`, `demoted`, `failed` |
| `zig_native` | `zig test -OReleaseSafe -lc` on the host of the translated Zig (translated for x86_64-linux-musl) plus `expectEqual` against the C values; target-dependent header declarations such as `jmp_buf` are host-checked only | `ok`, `mismatch`, `compile_error`, `runtime_error` (a ReleaseSafe panic) |
| `air_export` | patched Zig 0.16.0 AIR export (as `scripts/translate.sh`) | `ok`, `failed` |
| `air2lean` | `air2lean --diagnostics-json`; diagnostic codes | `checked`, `rejected` |
| `lean` | emission, Q01's `#guard` checks of `entry` on `mem0` (`zig_gen.lean_checks`), `lake env lean` | `ok`, `guard_failed`, `elab_failed`, `emit_failed` |

`lean` runs only when air2lean accepted the program and the translated Zig agreed with C.
The headline outcome is the first failing stage in the order
`c_native, translate_c, air_export, air2lean, zig_native, lean`.

```sh
tests/roadmap/c-frontend/check.sh --light                 # CI: record check, no tools
# heavy (local): wrap the whole call in one build-guard
AIR2LEAN_ZIG_NATIVE=~/.cache/air2lean/host-0.16.0/zig \
AIR2LEAN_ZIG_AIR=/path/to/zig-air-0.16.0/bin/zig \
AIR2LEAN_ZIG_NATIVE_0152=~/.cache/air2lean/host-0.15.2/zig \
python3 scripts/build-guard.py --lock ~/.cache/air2lean/build-c.lock --timeout 10800 \
  --report /tmp/cf.json --log /tmp/cf.log -- tests/roadmap/c-frontend/check.sh --heavy /tmp/cf-out
# generated UB-free programs (cgen.py), same environment and guard
tests/roadmap/c-frontend/check.sh --generated /tmp/cf-gen 0 30
```

`--heavy` builds the translator (`lake build ZigLean air2lean`), rewrites
`tests/roadmap/c-frontend/record.json`, and needs the tables below regenerated with
`python3 tests/roadmap/c-frontend/run.py tables`. `check.sh --light` (CI) verifies that the
record covers exactly the corpus with matching source hashes, that its summary recomputes
from the per-file stages, that this page contains the generated tables verbatim, and the
generator's invariants. Committed AIR: none; the per-file work directories stay local.

On macOS 27, Zig 0.16.0 `translate-c` never finishes when its stdout is a pipe (it spins
in `fcopyfile`); the harness redirects stdout to a file.

## translate-c findings (Zig 0.16.0, Aro-based; 0.15.2 clang-based)

Shapes are quoted from the translated corpus (`.zig` files in the heavy work directory).

| C construct | translate-c 0.16.0 Zig shape | notes |
|---|---|---|
| `[*c]` pointer arithmetic | `p + @as(usize, @bitCast(@as(isize, @intCast(n))))`; `p[@bitCast(@as(isize, @intCast(i)))]`; `q - p` is `@divExact(@as(c_long, @bitCast(@intFromPtr(q) -% @intFromPtr(p))), @sizeOf(T))`; `<` on `[*c]T`; array decay `@as([*c]T, @ptrCast(@alignCast(&buf)))` | a negative index becomes a huge `usize` (`p[-1]` is index 2⁶⁴−1) |
| `p++` in an expression | `blk: { const ref = &p; const tmp = ref.*; ref.* += 1; break :blk tmp; }` | |
| unsigned arithmetic | `+%`, `-%`, `*%`, `+%=` | wraps, as C |
| signed arithmetic | plain `+ - *`; `/` is `@divTrunc`; `%` is `__helpers.signedRemainder`; `>>`/`<<` take `@intCast` counts | C UB (overflow, shift ≥ width) is a ReleaseSafe panic |
| integer promotions | operands widened with `@as(c_int, c)`; narrowing stores `@truncate`; signed narrowing `@bitCast(@as(i8, @truncate(x)))` | |
| casts | integer: `@truncate`, `@bitCast`, `@intCast`, `@as`; pointer: always `@ptrCast(@alignCast(p))`, `void *` is `?*anyopaque`; `@intFromPtr`/`@ptrFromInt` | `@alignCast` adds a ReleaseSafe alignment check C does not have |
| comparison results in arithmetic | `@intFromBool(a > b) - @intFromBool(a < b)` | **bug**: `u1` arithmetic, panics where C yields −1 (G8) |
| `if`/loops, `break`/`continue` | `while (c) : (i += 1)` for `for`; `do … while` is `while (true) { …; if (!c) break; }` | |
| `switch` | `while (true) { switch (x) { v => { …; break; }, else => … } break; }`; fallthrough duplicates the following case bodies | case labels nested inside other statements (Duff's device): "TODO complex switch", function demoted to `extern` |
| `goto`, labels | refused: "TODO goto" (0.15.2: "TODO implement translation of stmt class GotoStmtClass/LabelStmtClass") | the function is demoted to `extern fn`; callers still translate |
| bitfields | the record becomes `opaque` ("struct demoted to opaque type - has bitfield"); every function that touches a member or a local of the type is demoted | 0.15.2 identical |
| unions | `extern union`; anonymous member unions are `union_unnamed_N` | |
| structs | `extern struct`; `= {0}`/missing initialisers are `std.mem.zeroes(T)`; by-value copies | |
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

**Zig 0.17.0 translate-c is no better.** Its `Translator.zig` keeps the same refusals
(`.goto_stmt, .computed_goto_stmt, .labeled_stmt => fail "TODO goto"`, bitfield records
demoted to `opaque`, variadic definitions demoted, "TODO complex switch"), and running the
0.17.0 translator on the eight affected corpus files gives the same warnings and demotions;
`sort_callback` still gets the `u1` comparator subtraction (G8).

### goto

translate-c (0.15.2, 0.16.0 and 0.17.0) never produces a labeled-switch dispatch loop
from C `goto`: any function containing a `goto` or a label is demoted to `extern fn`,
so a goto state machine reaches air2lean only as a call to a missing symbol (G1, then
`CALLEE_MISSING`). air2lean's L03 loop-switch support would consume such a dispatch loop if
something produced it. Options:

| option | what | trust | size |
|---|---|---|---|
| reject (now) | a named gate: a translate-c "TODO goto" demotion of a corpus/project function is a typed rejection of that function, not a silent `extern` | no change | S |
| patch translate-c (Aro backend) | forward `goto`s within one compound statement (cleanup ladders such as `goto_cleanup`) become nested labeled blocks left with `break :label`; general `goto` (backward jumps, `goto_state_machine`) becomes `state: switch (label_id) { … continue :state next … }` over the function's labels, with locals hoisted above the switch | the patched translator replaces stock translate-c in the trusted base, so it needs its own review and native differential (this harness) | M for forward-only, L for general; best done upstream |
| C-side rewrite before translate-c | a goto-elimination pass (for example on Aro's or clang's AST) that emits structured C (flags + loops + `switch`) and then runs stock translate-c | the rewriter joins the trusted base and is C-semantics-sensitive (scopes of declarations jumped over, VLAs, computed goto) | L |

Recommendation: the gate now (Phase 1), the forward-only Aro patch upstream next (it covers
the error-cleanup idiom), general goto only with upstream acceptance (Phase 3).

**Zig 0.16.0 compiler bug (not translate-c).** Indexing an array that is reached through a
dereferenced C pointer, `p.*.data[i]` with `p: [*c]S` or `r.*[i]` with `r: [*c][3]T`,
has the *array* type instead of the element type in stock Zig 0.16.0 (a four-line repro
fails to compile; the same code through `*S` compiles; Zig 0.15.2 and 0.17.0 compile it).
translate-c emits exactly this shape for `p->data[i]`. Mostly it is a compile error
(`arrays_2d`, `ring_buffer`, `struct_layout`), but `&p->e[i]` coerces the wrong
`*[N]T` to `[*c]T` and **silently miscompiles**: `hash_table` returns a different value
from C in a Debug build (and panics in ReleaseSafe). The Debug-built patched compiler reaches `unreachable` on all four.

## Results

Corpus: 40 files in `tests/roadmap/c-frontend/corpus/`, one construct family each plus
realistic programs (`strings_loops`, `memcpy_loops`, `linked_list`, `ring_buffer`,
`sort_callback`, `hash_table`, `malloc_vec`, the goto state machine, the bitfield packet
parser, `varargs_sum`). Recorded in `tests/roadmap/c-frontend/record.json` with stock Zig
0.16.0/0.15.2 and the patched AIR-only Zig 0.16.0 (exporter `zig-patch/air-json/json.zig` sha256 066fab37…, with the G5 fix), on
aarch64-macos.

* **23 of 40 files translate end to end** and their `Gen.lean` `entry` agrees with the C
  program on all four inputs (`#guard`). These cover integer promotions, unsigned
  wrapping, signed arithmetic, 64-bit arithmetic, floats, `_Bool` and short-circuit logic,
  side-effecting expressions, designated initializers and compound literals, `switch` (incl.
  fallthrough by duplication), loops with `break`/`continue`, enums, unions (type punning),
  string literals, static locals, globals, function pointer tables, recursion, macros, a
  pointer-walking `strlen`/`strcpy`/`strcmp`/`strrev`, `char *` and `void *` views of objects
  (`casts`), `void *` byte loops (`memcpy_loops`), a linked list over a static node pool with
  removal through a pointer to a link (`linked_list`) and pointer/integer round trips
  (`ptr_int_casts`).
* Of the 29 files with no libc call and no translate-c demotion, 23 pass, 1 is accepted
  but evaluates to `.illegal` (G4), 4 hit the Zig 0.16.0 bug (G3) and 1 (`sort_callback`,
  accepted by air2lean) diverges natively (G8).
* The other 11 are rejected by name: the 6 translate-c demotions (G7), the 4 libc users at
  `CALLEE_EXTERN_UNBOUND` (no libc symbol is bound yet, §libc boundary; `snprintf` as a
  variadic callee) and `setjmp_longjmp` (the `noreturn` extern `longjmp`, and unbound `setjmp`).
* Every C program ran cleanly under UBSan; translate-c's Zig agreed with C natively in 27
  files. The 13 others: 9 do not compile (6 demotions, 3 × G3), `hash_table` diverges
  silently (G3: a wrong value in Debug, a panic in ReleaseSafe), `libc_stdlib`/`sort_callback` panic in ReleaseSafe on the
  comparator idiom (G8), and `setjmp_longjmp` returns 1000 where C returns 1006.
* translate-c 0.15.2 (clang) and 0.16.0 (Aro) refuse the same six files.

`cgen.py` (seeds 0–29, `tests/roadmap/c-frontend/generated-record.json`): every program
passed every stage. These programs use unsigned arithmetic, signed comparisons, `switch`
with fallthrough, bounded loops with `break`/`continue`, local arrays, pointers to array
items, helper calls and reset globals, and no goto, libc or casts through `void *`.

generated headline: {"lean_ok": 30}

<!-- c-frontend tables: generated by tests/roadmap/c-frontend/run.py tables; do not edit -->

| file | C native | translate-c 0.16 | translate-c 0.15.2 | Zig native | AIR export | air2lean | Lean | codes |
|---|---|---|---|---|---|---|---|---|
| arrays_2d | ok | ok | ok | compile_error | failed | – | – | – |
| bitfield_packet | ok | demoted (entry) | demoted | compile_error | failed | – | – | – |
| bitfields | ok | demoted (entry) | demoted | compile_error | failed | – | – | – |
| bool_logic | ok | ok | ok | ok | ok | checked | ok | – |
| casts | ok | ok | ok | ok | ok | checked | ok | – |
| enums | ok | ok | ok | ok | ok | checked | ok | – |
| expressions | ok | ok | ok | ok | ok | checked | ok | – |
| float_basic | ok | ok | ok | ok | ok | checked | ok | – |
| func_pointers | ok | ok | ok | ok | ok | checked | ok | – |
| globals | ok | ok | ok | ok | ok | checked | ok | – |
| goto_cleanup | ok | demoted (run) | demoted | compile_error | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×2 |
| goto_state_machine | ok | demoted (scan) | demoted | compile_error | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×1 |
| hash_table | ok | ok | ok | runtime_error | failed | – | – | – |
| initializers | ok | ok | ok | ok | ok | checked | ok | – |
| inline_static | ok | ok | ok | ok | ok | checked | ok | – |
| int_promotion | ok | ok | ok | ok | ok | checked | ok | – |
| libc_stdio | ok | ok | ok | ok | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×1 |
| libc_stdlib | ok | ok | ok | runtime_error | ok | rejected | – | CALLEE_EXTERN_UNBOUND×5, PROGRAM_FAILURE×6 |
| libc_string | ok | ok | ok | ok | ok | rejected | – | CALLEE_EXTERN_UNBOUND×6, PROGRAM_FAILURE×7 |
| linked_list | ok | ok | ok | ok | ok | checked | ok | – |
| loops | ok | ok | ok | ok | ok | checked | ok | – |
| macros | ok | ok | ok | ok | ok | checked | ok | – |
| malloc_vec | ok | ok | ok | ok | ok | rejected | – | CALLEE_EXTERN_UNBOUND×2, PROGRAM_FAILURE×2 |
| memcpy_loops | ok | ok | ok | ok | ok | checked | ok | – |
| ptr_arith | ok | ok | ok | ok | ok | checked | guard_failed | – |
| ptr_int_casts | ok | ok | ok | ok | ok | checked | ok | – |
| recursion | ok | ok | ok | ok | ok | checked | ok | – |
| ring_buffer | ok | ok | ok | compile_error | failed | – | – | – |
| setjmp_longjmp | ok | ok | ok | mismatch | ok | rejected | – | CALLEE_BLOCKED×1, CALLEE_EXTERN_UNBOUND×2, INSTRUCTION_FAILURE×2, PROGRAM_FAILURE×1 |
| signed_ops | ok | ok | ok | ok | ok | checked | ok | – |
| sort_callback | ok | ok | ok | runtime_error | ok | checked | – | – |
| static_locals | ok | ok | ok | ok | ok | checked | ok | – |
| string_literals | ok | ok | ok | ok | ok | checked | ok | – |
| strings_loops | ok | ok | ok | ok | ok | checked | ok | – |
| struct_layout | ok | ok | ok | compile_error | failed | – | – | – |
| switch_fallthrough | ok | demoted (duff_sum) | demoted | compile_error | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×1 |
| switch_simple | ok | ok | ok | ok | ok | checked | ok | – |
| unions | ok | ok | ok | ok | ok | checked | ok | – |
| varargs_sum | ok | demoted (sum) | demoted | compile_error | ok | rejected | – | CALLEE_EXTERN_UNBOUND×1, PROGRAM_FAILURE×3 |
| wide_ints | ok | ok | ok | ok | ok | checked | ok | – |

Headline outcome (first failing stage; `lean_ok` = translated and #guard-checked):

| outcome | files |
|---|---|
| air2lean | 5 |
| air_export | 4 |
| lean | 1 |
| lean_ok | 23 |
| translate_c | 6 |
| zig_native | 1 |

Rejection histogram (files whose diagnostics contain the code):

| code | files |
|---|---|
| CALLEE_BLOCKED | 1 |
| CALLEE_EXTERN_UNBOUND | 9 |
| INSTRUCTION_FAILURE | 1 |
| PROGRAM_FAILURE | 9 |

Outcome by C construct family:

| construct | outcomes |
|---|---|
| 64-bit arithmetic | lean_ok: 1 |
| bitfields | translate_c: 2 |
| designated/compound initializers | lean_ok: 1 |
| enums | lean_ok: 1 |
| floating point | lean_ok: 1 |
| function pointers | air2lean: 1, lean_ok: 1, zig_native: 1 |
| globals | lean_ok: 1 |
| goto | translate_c: 2 |
| integer casts | lean_ok: 1 |
| integer promotions | lean_ok: 1 |
| libc stdio | air2lean: 1 |
| libc stdlib | air2lean: 2 |
| libc string | air2lean: 1, translate_c: 1 |
| loops/break/continue | lean_ok: 1 |
| macros | lean_ok: 1 |
| multi-dim arrays | air_export: 1 |
| object-representation casts | lean_ok: 1 |
| pointer arithmetic | lean: 1, lean_ok: 1 |
| pointer<->integer casts | lean_ok: 1 |
| realistic | air2lean: 1, air_export: 2, lean_ok: 3, zig_native: 1 |
| recursion | lean_ok: 1 |
| setjmp/longjmp | air2lean: 1 |
| short-circuit/_Bool | lean_ok: 1 |
| side-effecting expressions | lean_ok: 1 |
| signed arithmetic | lean_ok: 1 |
| static inline | lean_ok: 1 |
| static locals | lean_ok: 1 |
| string literals | lean_ok: 1 |
| struct layout | air_export: 1 |
| structs+pointers | air_export: 2, lean_ok: 1 |
| switch | lean_ok: 2 |
| switch fallthrough | translate_c: 1 |
| unions | lean_ok: 1 |
| variadic call | air2lean: 1 |
| variadic definition | translate_c: 1 |
| void* byte loops | lean_ok: 1, zig_native: 1 |

<!-- end c-frontend tables -->

## Gaps, in priority order

Sizes: S ≤ 1 week, M 1–3 weeks, L > 3 weeks of focused work. "Files" counts corpus files
blocked (alone or with other gaps).

| # | gap | translate-c Zig shape | rejected by | files | size | depends on |
|---|---|---|---|---|---|---|
| G1 | **calls to `extern` C functions** (libc, and every function translate-c demoted) | `pub extern fn strlen([*c]const u8) usize;`, called directly; variadic `snprintf(…, ...)` | the exporter writes the callee as a constant `{"ty": <fn type>, "val": "(extern 'memset')"}` whose type is `k: other` (`"fn (…) callconv(.c) …"`); `Air2Lean/Air/Json.lean` `parseLeafVal` → `AIR_DECODE` "constant of unsupported type" | 9 (`AIR_DECODE`) | M (exporter callee/fn-type schema, decoder, checker binding to the E01 registry by exact symbol) + per-symbol models below | E01, E03, E04, L01, Q07 (schema bump), zig-patch |
| G2 | **closed** (codex/c-frontend-ptrcasts): pointer casts through `void *`/`char *` views and self-referential structs | `@ptrCast(@alignCast(p))` to/from `?*anyopaque`, `[*c]u8`; `struct node **link = &head` | was `Air2Lean/Check.lean` `errorCapabilityScan`: an opaque child (`.other`) or a type cycle gave "unresolved or cyclic symbolic storage provenance". Now the error capability is a least fixpoint over the type graph (`typeReach`, §Pointer casts below) | 0 (was 5) | done | L10, L07, L05 |
| G3 | **Zig 0.16.0 `p.*.f[i]` through `[*c]` pointers** (compiler bug, trusted base) | `r.*.data[i]`, `o.*.in[0].a`, `row.*[2]` | stock Zig: compile error or **silent miscompile** (`&p.*.e[i]` points at item 0); patched Debug compiler: `reached unreachable` | 4 | S for a fail-closed gate (reject translated sources with the shape, or rewrite it and re-verify natively); upstream fix; 0.15.2 and 0.17.0 compile the repro correctly | Q07, T06, V03 |
| G4 | **negative `[*c]` index** | `p[@bitCast(@as(isize, @intCast(-1)))]` = index 2⁶⁴−1 | accepted, but the model's `p.elem 4 (2^64-1)` is past the block, so `entry` is `.illegal` while native Zig and C are defined (conservative, not unsound) | 1 (`ptr_arith`) | S: wrap the C-pointer offset modulo 2⁶⁴ (two's-complement index) in the `[*c]` `ptr_elem_*`/`ptr_add` emission | L05 |
| G5 | **closed** (codex/c-frontend-g3): globals whose initial value is a comptime call and whose address escapes | `pub var pool: [8]struct_node = std.mem.zeroes([8]struct_node);` with `&pool[i]` / `@intFromPtr(&data[1])` | was: AIR global without `init` → `STRUCTURE_FAILURE` "global has no initial value". Zig 0.16.0 Sema resolves only the *type* of a global whose address a function takes and queues its value; the exporter now resolves the value first (§Escaped globals below). A pure-Zig gap, not C-specific | 0 (was 2) | done | L12, L06 |
| G6 | **closed** (codex/c-frontend-g3): std callees other than `zig.c_translation` | `std.mem.zeroes(T)` in function bodies (compound literals), `debug.assert` inside `signedRemainder` | was `CALLEE_MISSING`. The harness now exports the std callee closure of the C module (§Std callees below) | 0 (was 2) | done | I02, E04 |
| G7 | **translate-c refusals** | `goto`/labels: function demoted ("TODO goto"); bitfields: record `opaque`, users demoted; variadic definitions: demoted; case labels inside nested statements (Duff): "TODO complex switch" | translate-c 0.15.2/0.16.0/0.17.0 alike (the demoted functions then reach G1) | 6 | goto: gate S now, forward-only Aro patch M, general L (§goto); bitfields M–L (C ABI storage units as packed host integers); variadic definitions L (`@cVaStart`/`@cVaArg` and AIR va tags); Duff M | upstream Aro translate-c or a pinned patch (joins the trusted base); L03, L08, L14 |
| G8 | **translate-c semantic divergences** | `(a > b) - (a < b)` → `@intFromBool(a > b) - @intFromBool(a < b)` (`u1` arithmetic); `setjmp`/`longjmp` as plain calls | ReleaseSafe `integerOverflow` panic natively where C yields −1 (the standard `qsort` comparator idiom); `setjmp` loses a `volatile` local (Zig has no `returns_twice`) | 3 | S: upstream promotion fix; reject `setjmp`/`longjmp`/`sigsetjmp` at the libc boundary | upstream translate-c; G1 |
| G9 | **patched compiler on invalid Zig** | any compile error (G3, demotions) | the Debug-built AIR exporter reaches `unreachable` instead of exiting with the compile error | 4 | S | V03, I08 |

Order of attack: G4 and a G3 gate unblock the last libc-free kernels (Phase 1); G1 opens
the libc boundary (Phase 2); G7/G8 are translate-c work (Phase 3).

G1's exporter and binding are done (EXT-03, `docs/air-json.md` §Extern calls): each libc call
and each call of a demoted function now reaches program binding and fails closed with
`CALLEE_EXTERN_UNBOUND`, either "has no definition in the program … and no registry model"
or, for a variadic callee (`snprintf`, the demoted `sum` of `varargs_sum`), "is variadic,
which is outside the subset". Variadic calls therefore stay rejected until a variadic callee
can be translated (G7); there is no variadic model. A `noreturn` extern (`longjmp`) is rejected
by name at the call. What remains of G1 is the libc side (§libc boundary).

G4 stays open on purpose: `Ptr.elem` (`ZigLean/Mem/Basic.lean`) reads the `usize` index as a
natural number, so index 2⁶⁴−1 is past the block and the model is `.illegal` (conservative).
Native Zig computes the address modulo 2⁶⁴ (LLVM's GEP takes the index as signed), so the fix
is a model change for every many-item pointer, not a C one: `Ptr.elem` over `i.toInt`, with
the 28 proof files that unfold `Ptr.elem` over `toNat` re-proved under an `i < 2⁶³` side
condition. That is a separate model change with its own proof sweep.

### Escaped globals (G5)

Zig 0.16.0 resolves a container-level `var` lazily: when a function body takes the global's
address, Sema resolves only its type and queues the value analysis
(`ensureNavValAnalysisQueued`) for later in the same update. If the initial value is a comptime
call (`std.mem.zeroes`, which translate-c emits for every `static T x[N];`, or a labelled
comptime block), the function's AIR is dumped before the value exists, and the exporter wrote
the global without `init`. The exporter (`Compat.navInfo`, `zig-patch/air-json/json.zig`) now
runs the same analysis `Sema.ensureNavResolved(.fully)` would run (`ensureNavValUpToDate`)
when the value is still pending, unless that unit is already in progress; a failure is a
registered compile error and the global keeps no `init`, which air2lean rejects as before.
Earlier versions keep the value in `Nav.status` and are unchanged. Re-exporting every example
with the new compiler is byte-identical to the committed goldens. Fixture:
`tests/roadmap/c-frontend/escaped-globals/` (a list threaded through a global pool, an
address round trip into a global array, a global initialised by a comptime block), exported
AIR, retained `Gen.lean` and `#guard`s against native Zig; the previous exporter writes
`escaped.pool` and `escaped.data` without `init`.

### Std callees (G6)

translate-c's Zig calls std functions at run time (`std.mem.zeroes(T)` for compound
literals and default field values, `debug.assert` inside `__helpers.signedRemainder`). They
are translated from their AIR like user code. `run.py`'s AIR stage exports with the filter
`<stem>.,zig.c_translation.`, then adds the base name (without `__anon_N`) of every callee
that still has no AIR file, panic handlers excepted (air2lean classifies those by exact name),
and exports again, at most four rounds (`mem.zeroes`, then `mem.asBytes`). A prefix also
selects std's own instances that the program never calls, so the stage then keeps only the
functions reachable from the C module (calls and function addresses) and deletes the rest.
The record lists the added prefixes (`std_prefixes`) and the kept std functions.

### Pointer casts (G2)

translate-c writes every C pointer conversion as `@ptrCast(@alignCast(p))`, through
`?*anyopaque` for `void *` and `[*c]u8` for `char *`. The model already handles such casts at
the byte level: a pointer is a block and an offset, a cast keeps both (`pure p`), an access
decodes the bytes at the access type and checks the address against the pointer type's
alignment (`Mem.access`: misaligned is `.illegal`), and ReleaseSafe's `@alignCast` check is a
panic in the AIR. A type-confused access therefore never yields a silently wrong value: pointer
bytes read as an integer and undefined bytes are `.unspecified`, a byte other than 0 or 1 read
as `bool` is `.illegal`.

What rejected these programs was the checker's guard of the finite error-storage fragment
(L10): a pointer cast may not expose symbolic error bytes as numeric or opaque storage, so
both pointees' *error capability* (an error set or error union is reachable, following pointer
edges) must be known. It was computed by a tree walk that gave up on `anyopaque` and on any
cycle. It is now a least fixpoint, `cap t = isError t ∨ ∃ child c, cap c`, computed as
reachability with a visited set (`typeReach` in `Air2Lean/Check.lean`), so an error-free
self-referential struct has capability `false`. `anyopaque` is an error-free leaf, so error
storage can neither enter nor leave a `*anyopaque`. Unchanged for every graph that reaches an
error: it keeps the strict acyclic walk, so a cyclic error-bearing graph is still rejected,
and unknown types, `anyerror` and more than 1024 units of work stay rejected. One rule is new:
a cast between different pointee types (array decay excepted) whose graph reaches
`std.mem.Allocator`, `std.Thread` or `std.Io` is rejected, because the model keeps their storage
symbolically and a byte view of it would read the model's encoding, not the program's bytes.

`tests/roadmap/c-frontend/ptrcasts/` is the hand-written Zig fixture: a list with removal
through a pointer to a link, a binary tree of C pointers to its own type, `void *` round trips,
a `char *` view written through, and an opaque callback context, translated from patched
0.16.0 AIR and checked against native Zig (`native.txt`); four negatives (`pointerAsInt` is
`.unspecified`, `byteAsBool` `.illegal`, `misalignedChecked` `.panic`, `misalignedUnchecked`
`.illegal`); and `reject.zig` (error storage through `*anyopaque`, a cyclic error-bearing
view), which air2lean rejects. Run `tests/roadmap/c-frontend/ptrcasts/check.sh [--native]`.

## libc boundary

Symbols the translated Zig calls (`extern_calls` in the record), with the proposal per
symbol. "Translated" means compiling the real implementation (musl, pinned revision)
through this same route; "trusted base" means a Lean model with a stated contract,
registered like the existing allocator/posix models (E04), never a C-specific runtime model.

| symbol | corpus files | proposal | why |
|---|---|---|---|
| `memcpy`, `memset`, `memcmp` | `libc_string` | translated (musl `src/string/*.c`, generic C path) | small byte loops; musl's word-at-a-time paths need G2 casts, else use its byte loop |
| `strlen`, `strcmp`, `strchr` | `libc_string` | translated (musl) | `strings_loops` already passes with equivalent hand-written loops |
| `abs` | `libc_stdlib` | translated (musl `src/stdlib/abs.c`) | one line; `abs(INT_MIN)` is a ReleaseSafe panic in the Zig meaning |
| `isdigit`, `isalpha` | `libc_stdio` | translated (musl `src/ctype/`) | unsigned range tests |
| `qsort` | `libc_stdlib` | translated (musl `src/stdlib/qsort.c`) | needs function pointers (E02, L11), G2 and G8 |
| `malloc`, `calloc`, `realloc`, `free` | `libc_stdlib`, `malloc_vec` | trusted base over the existing allocator model (`Zig.Allocator`, M01–M03), as the posix.mmap base | allocation is a resource boundary; `calloc` = allocation + zero bytes; `realloc` per M02 |
| `snprintf` | `libc_stdio` | trusted base first (format contract over a byte buffer); translating musl `vfprintf` waits for variadic definitions (G7) | large, variadic, locale-dependent |
| `setjmp`, `longjmp` | `setjmp_longjmp` | not supported: rejected at the boundary | no `returns_twice` in Zig; measured divergence |

**Zig 0.16.0's libc is largely Zig.** For `x86_64-linux-musl`, Zig 0.16.0 links its own Zig
implementations ahead of musl's C: `memcpy`, `memset`, `memcmp` and `strlen` are compiler_rt
(`lib/compiler_rt.zig`, `lib/compiler_rt/memcpy.zig`), `strcmp`/`strchr` are
`lib/c/string.zig`, `isdigit`/`isalpha` `lib/c/ctype.zig`, `abs`/`qsort` `lib/c/stdlib.zig`,
and `malloc`/`calloc`/`realloc`/`free` `lib/c/malloc.zig` (a Zig allocator over pages). So
"translated from pinned real code" for these symbols means translating that Zig through the
ordinary route, pinned by the Zig tarball hash, with no translate-c and no musl C; only the
page source under `malloc` is an OS boundary (the existing `posix.mmap` base). Two exporter
gaps block it: those functions are exported with `@export` (`symbol(&f, "name")`, weak and
hidden), which the exporter does not report as an `export` (only the `export fn` keyword, so
an extern call to them stays unbound), and the libc is a separate compilation (its own root
`lib/c.zig`, build mode and module), so its AIR set must be exported with the program's
profile and joined under one module identity. `snprintf` and `setjmp`/`longjmp` remain musl C.

The C objects (`nm -u` at `-O0`, `libc_symbols` in the record) also reference `memset` in 8
files: clang lowers `= {0}` initialisers to it. translate-c uses `std.mem.zeroes` instead,
so it is not a boundary symbol of the translated Zig.

## Phased roadmap

| phase | scope | acceptance |
|---|---|---|
| 0 (this change) | corpus, harness, generator, committed records, CI record check | `check.sh --light` exits 0 in CI; `--heavy` reproduces `record.json` on a host with the patched 0.16.0 compiler |
| 1: libc-free C kernels | G2, G5, G6 (done), G4, G9, a fail-closed G3 gate and a named gate for translate-c demotions (goto, bitfields, variadic definitions); generator gains `void *` casts and struct pointers | every corpus file whose translate-c output has no demotion and no `extern` call is `lean_ok` or rejected by a named G3 gate (today 23 of 29); `cgen.py` seeds 0–299 all `lean_ok` |
| 2: libc boundary | G1; musl string/ctype/`abs`/`qsort` translated with the musl revision recorded; malloc family as trusted base with contracts in `docs/premises.md`; `setjmp` rejected by name | `libc_string`, `libc_stdlib`, `malloc_vec` `lean_ok`; every `extern_calls` symbol in the record is either a registered trusted-base row or translated AIR; a proof of one libc-using function (e.g. a `memcpy`/`strlen` specification) is kernel-checked |
| 3: translate-c completeness | G7, G8 upstream or as a pinned, reviewed translate-c patch; move the route to the first Zig version without G3 (Q07 qualification) | `goto_*`, `bitfields`, `bitfield_packet`, `varargs_sum`, `switch_fallthrough`, `arrays_2d`, `ring_buffer`, `struct_layout`, `hash_table`, `sort_callback` `lean_ok`; the comparator idiom agrees natively |
| 4: realistic programs and proofs | project manifests accept C sources (I01); csmith (Docker image) differential at ≥ 1000 seeds; tutorial | csmith seeds with no out-of-scope constructs are `lean_ok` or carry a typed rejection; two kernel-checked proofs over translated C (ring buffer invariant, linked-list reversal) using P01–P05 tactics |

## Register row

Register row X01 in `ROADMAP.md` and `remaining-acceptance.md` (open):

| ID | Title | Classification | Evidence / acceptance |
|---|---|---|---|
| X01 | C programs via translate-c | open | Route: C → stock `zig translate-c` (x86_64-linux-musl) → patched AIR export → air2lean; claims are about translate-c's Zig as compiled by Zig (translate-c and the musl headers join the trusted base), not ISO C semantics (`docs/c-frontend.md`). Baseline: 17/40 corpus files and 30/30 generated programs translate and agree with C under `#guard`. Close when phases 1–3 above are met: every corpus file is `lean_ok` or rejected by a named, documented gate (`setjmp`); every libc symbol the corpus calls is translated from pinned real code or a trusted-base model with a stated contract; the G3 compiler bug is gated or fixed by a qualified Zig version; `check.sh --heavy` is reproducible and CI checks the record. |
