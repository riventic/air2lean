# Architecture audit 2/6: memory model vs Zig semantics

Scope: `ZigLean/Mem/*` (blocks, bytes, `Enc`, allocators), the memory parts of
`Air2Lean/Emit.lean`/`Check.lean`, and `ZigLean/Sep/*`, measured against Zig 0.16.0 as the
Zig compiler builds it (ReleaseSafe, LLVM backend, aarch64-macos host). Base: `origin/main`
af9ddc30. The module-identity finding (B1) of the structure audit is not repeated.

Question asked of every mechanism: can it make a theorem about the generated Lean true
while the compiled program does something else, or make the model accept more than Zig?

Fixtures: [`tests/roadmap/architecture-audit/memory-model/`](../../tests/roadmap/architecture-audit/memory-model/).
`check.sh` exports each fixture with the patched 0.16.0 compiler (`-OReleaseSafe
-fno-error-tracing`), translates it, runs it in Lean from the generated `mem0`, builds it
natively with stock 0.16.0 ReleaseSafe, and asserts the recorded divergence. It fails once a
fix lands; the fixture then becomes an agreement test.

## Summary

| # | Finding | Class | Counterexample |
|---|---|---|---|
| MM-1 | Block addresses are a fixed, deterministic layout, and the model exposes them | SOUNDNESS | reproduced (`addrOfLocal`, `crossDistance`) |
| MM-2 | Address-dependent safety checks (`@alignCast`, `@ptrFromInt` alignment) are decided by the model layout | SOUNDNESS | reproduced (`overAlign`) |
| MM-3 | Pointer arithmetic outside the allocation is accepted, but LLVM sees `getelementptr inbounds` poison | SOUNDNESS | reproduced (`oobCompare`); fixed |
| MM-4 | `==` on ordinary pointers is structural; `@intFromPtr`, order and C-pointer `==` use addresses | SOUNDNESS | reproduced (`eqVsAddr`) |
| MM-5 | The stack has no bound | SOUNDNESS | native crash reproduced (`depth`) |
| MM-6 | Emitter placeholders (`panic!`, `pure default`) are successful no-ops in the logic | FAIL-OPEN | kernel theorems (`PanicDefault.lean`); fixed |
| MM-7 | The ReleaseFast premise ("no model throw ⇒ no illegal behaviour") is false | FAIL-OPEN | follows from MM-2, MM-3, MM-5; qualified |
| MM-8 | The Sep layer exports allocation-order address facts | FAIL-OPEN | code-read (`alloc_run`) |
| MM-9 | Stale-pointer and address-reuse semantics | FAIL-OPEN (known, M05) | partly on `codex/roadmap-address-reuse` |
| MM-10 | Fixed-buffer allocations do not alias their buffer | HARDENING | code-read |
| MM-11 | Pointer bytes read as integers and integer bytes read as pointers are `.unspecified` | HARDENING | code-read |
| MM-12 | Zero-length accesses and (before MM-3) address-zero projections need a live block | HARDENING (known, L05) | code-read, on `codex/roadmap-null-projection` |
| MM-13 | Value-level tagged-union retagging fills the new payload with `default` | HARDENING | code-read |
| MM-14 | Race footprint and dead blocks grow without bound in single-threaded runs | HARDENING | measured |
| MM-15 | Model `@memcpy` copies like `@memmove`; it relies on the ReleaseSafe alias check in AIR | control (agrees) | reproduced (`memcpyOverlap`) |
| MM-16 | `noalias` parameters are not modelled: an overlapping call gives a value | SOUNDNESS | reproduced (`na.shiftCopy`, `na.swapSelf`); fixed |

Mechanisms checked and found sound: block-id provenance for liveness (use after free, double
free, foreign free are `.illegal` by block id, not address); one-past-the-end accesses;
`undefined` propagation (`Byte.undef`, `.part`, `.mask`; `checkUndefOperands` rejects every
`undefined` operand that is not a store or `memset`, so no observable `undefined`→0); padding
bytes (undefined on encode, ignored on decode); `bool`, enum, optional-flag and error-code
decoding (invalid values are `.illegal`/`.unspecified`, never a value); `Enc` sizes (checked
against the exporter's `abi_size`/`abi_align` in `Check.lean`); 64-bit little-endian
(`Air/Profile.lean` rejects anything else); volatile (rejected, `docs/volatile-effects.md`);
`Triple` and the frame rule (proved for every memory satisfying `Mem.Seq`, no axioms,
`sorry` or `implemented_by` in `ZigLean/Sep`).

## Fix status (soundness batch)

`tests/roadmap/architecture-audit/memory-model/check.sh` asserts agreement with the native
build for each fixed finding below.

| Finding | Status | Fix |
|---|---|---|
| MM-1 | fixed | placement oracle `Mem.place` for every block kind; generated `mem0 σ`; theorems hold for every `σ` (premise SEM-07, `docs/address-placement.md`) |
| MM-2 | fixed | alignment checks follow the placement; a placement without the extra alignment panics as natively |
| MM-3 | fixed | checked pointer formation `Zig.ptrProject` (`getelementptr inbounds`): a derived pointer outside `[0, size]` of its block is `.illegal` |
| MM-4 | fixed | pointer `==` compares addresses for every pointer kind (`Zig.ptrEqAddr`, `Zig.optPtrEqAddr`) |
| MM-5 | fixed | stack budget `Mem.stackLimit`/`Zig.enterFrame`, `Zig.Error.stackOverflow`; premise STK-01 without a budget |
| MM-6 | fixed | emitter arms write an unbound `placeholder`; output with one is rejected (`EMITTER_PLACEHOLDER`), every formerly reachable arm is a checker rule |
| MM-7 | qualified | `docs/build-modes.md` lists the remaining exceptions of the ReleaseFast premise |
| MM-8 | fixed | no allocation-order address facts in Sep (every placement) |
| MM-9 | fixed | address reuse is one case of the placement (ALC-08) |
| MM-10, MM-12 | open | hardening (fixed-buffer aliasing; zero-length/address-zero projections) |
| MM-11 | fixed | `decodeLoad`: pointer bytes read as integers give the address; integer bytes read as a pointer give a blockless pointer |
| MM-13 | fixed | a retag from another field leaves the payload undefined (`undef_f`) |
| MM-14 | fixed | the race scan is skipped while only the main thread can run (`Mem.solo`) |
| MM-16 | fixed | per-call `noalias` scopes over the footprint (`Zig.naEnter`/`naMark`/`naExit`), roots from `Air2Lean/Noalias.lean`; untrackable functions rejected (`tests/roadmap/noalias/check.sh`) |

## Measurements

| Fixture | Model (Lean, from `mem0`) | Native ReleaseSafe 0.16.0 |
|---|---|---|
| `addrOfLocal` | `4096` | `6094021991` (a stack address) |
| `eqVsAddr` | `1` (`p1 == p2` false, addresses equal) | `3` (both true) |
| `crossDistance` | `9` | `8` |
| `crossOrder` | `1` | `1` (agrees here; layout-dependent) |
| `overAlign` | `2` | `panic: incorrect alignment` |
| `oobCompare(1)` | `1` | `1` |
| `oobCompare(2^63)` | `1` (now `.illegal`, MM-3 fixed) | `0` |
| `oobPtrCompare(2^63)` | `1` (now `.illegal`, MM-3 fixed) | `0` |
| `depth(1000)` / `depth(10^7)` | `1000` / no bound in the model | `1000` / `Segmentation fault` (stack overflow) |
| `memcpyOverlap(4)` / `(1)` | `1` / `.panic` (AIR alias check) | `1` / `panic: @memcpy arguments alias` |

`Theorems.lean` states the first four model results as theorems (`native_decide` on the
closed term; the model is deterministic, so any proof method gives the same value), for
example `overAlign_never_panics`. The native build violates each.

`check.sh` reproduced both columns from a fresh `lake build` of the audit branch (second native
run: `addrOfLocal` 6102688727; the other native values are stable). The model values of the two
`2^63` rows are the audit's; with MM-3 fixed, check.sh asserts `error Zig.Error.illegal` for them.

---

## SOUNDNESS

### MM-1. A fixed address layout is observable

`alloc` (`ZigLean/Mem/Basic.lean`) places block `k` at `alignUp nextAddr align`, starting at
4096, with a 1-byte gap, in allocation order. Globals are placed the same way by
`Mem.ofGlobals`, stack blocks at function entry. `ptrAddr` returns these numbers to
`@intFromPtr`; `ptrLt`/`ptrLe` compare them; `ptrFromAddr` resolves integers through them.
None of this is stated as a premise (`docs/premises.md` only says native allocator addresses
are not modelled).

Generated theorem statements are about `mem0`, a concrete memory (e.g.
`Proofs/Layout/Mem.lean` `writeTable_illegal` pins block 3 at address 4104). So Lean proves
`addrOfLocal = 4096` and `crossDistance = 9` (`Theorems.lean`), both false natively. Any
program that hashes, sorts, aligns, or computes distances from addresses gets a single,
model-chosen answer that is a theorem.

`codex/roadmap-address-reuse` (M05) adds `AllocPolicy.reuseAddr`, an opt-in oracle for heap
and owned blocks only. It keeps the default layout, fixed stack and global addresses, the
1-byte gap, and `mem0`-based statements, so this finding stays open there.

**Fix (one mechanism): an address-placement oracle in `Mem`, quantified in every statement.**
Make placement an environment parameter like `AllocPolicy`: `place : BlockId → (size align :
Nat) → Nat`. It is used for every block kind (global, stack, heap, owned), and its
well-formedness predicate contains only what Zig guarantees: nonzero; a multiple of the
declared alignment; disjoint from live blocks; end ≤ 2^64. No gap, no order. Generate
`mem0 (σ : Placement) (hσ : σ.WF)`, and state generated theorems for all `σ`. The fixed 4096
layout becomes one instance that only the differential harness picks. Proofs that need an
address fact must derive it from `WF`. The M05 branch's `reuseAddr` is a special case to fold
in.

### MM-2. Address-dependent safety checks follow the model layout

ReleaseSafe AIR implements `@alignCast` and `@ptrFromInt`'s alignment check as `@intFromPtr`
& mask, compared with 0, then panic (see `overAlign` in the generated code: `i5 &&& 4095 ==
0`). In the model, the address is MM-1's layout, which is often more aligned than the declared
alignment: the first block is 4096-aligned. So `overAlign` (`*align(4096)` cast of a `[2]u8`
local) returns 2 in the model and panics natively. `overAlign_never_panics` is a theorem that the
native program refutes. The reverse also happens: a byte buffer at an odd model address fails an
`@alignCast(…)` to `align(8)` that a 16-aligned native allocation passes.

This is the same root cause as MM-1. It is listed separately because it breaks "never panics"
and "never `.illegal`" claims, the claims that most proofs make.

**Fix:** MM-1's oracle. With `WF` guaranteeing only the declared alignment, any alignment
beyond it cannot be proved, and the check's outcome depends on `σ`.

### MM-3. Out-of-allocation pointer arithmetic is LLVM poison

Zig 0.16 lowers `ptr_add`, `ptr_sub`, `ptr_elem_ptr` and field pointers to `getelementptr
inbounds` (`src/codegen/llvm/FuncGen.zig`: `ptraddScaled`, `ptraddConst`). A result outside
`[base, base+size]` of the allocation is poison, and LLVM folds comparisons accordingly.
`Ptr.add`/`Ptr.elem` in the model accept any offset, and `@intFromPtr`/`<` see a plain address.
`oobCompare(2^63)` (`q = p + 2^63`, `@intFromPtr(q) > @intFromPtr(p)`) is `true` in the model
and `false` natively in ReleaseSafe. Neither Zig's safety checks nor the model's `.illegal`
catch it.

**Fix (one mechanism): checked pointer formation.** Replace the pure `Ptr.add` in generated
code with a `MemM` operation (`ptrOffset` here, `Zig.ptrProject` as implemented). It throws `.illegal` unless the result stays in `[0,
size]` of the pointer's block. For a provenance-free pointer (`block = none`), only offset 0 is
allowed. This is CompCert's "weakly valid pointer" rule. It also gives L05's address-zero
projection a principled rule: offset 0 is defined and any other offset is illegal, matching
`inbounds`.

**Status: fixed** (`codex/fix-mm-failclosed`). The operation is `Zig.ptrProject p project`
(`ZigLean/Mem/Basic.lean`): the same pointer is always allowed; any other result throws
`.illegal` unless base and result lie in `[0, size]` of the base's block (`Mem.inBounds`, one
past the end included). Liveness is not required, as in LLVM's LangRef. 0.14.1, 0.15.2 and
0.16.0 lower `ptr_add`/`ptr_sub`, `ptr_elem_ptr`/`slice_elem_ptr`, `struct_field_ptr`, the
slice field pointers and `unwrap_errunion_payload_ptr` to `getelementptr inbounds` (`gepStruct`
inbounds); `@fieldParentPtr` lowers to `ptrtoint`/`sub nuw`/`inttoptr` and is modelled with the
same rule, since the langref makes it illegal behaviour when the argument is not that field. The
emitter (`FCtx.projectExpr`) writes `pure p` for a constant offset 0. L05's
`ptrProjectNullable` is gone: projections from a C/allowzero base use `ptrProject`
(`ptrProjectNonnull` when the result type is nonnullable), so a nonzero offset from a
provenance-free address, including address zero, is now `.illegal`. Slicing forms `ptr + start`
before Sema's `start <= end` check, so an out-of-allocation start is `.illegal` in the model
where native ReleaseSafe panics (conservative). The audit fixture is an agreement test:
`oobCompare(1)` is `1` in both, and `oobCompare(2^63)`, `oobPtrCompare(2^63)` are `.illegal`.
Residual: `Zig.tryPayloadPtr` and `Zig.errSetOk` form the payload pointer after a checked access
to the error code, without a bounds check of their own (`docs/build-modes.md`).

Deliberate over-approximations (each `.illegal` where native Zig may be defined; conservative
for no-illegal proofs, wrong for outcome reports and native diffs): an out-of-allocation result is
`.illegal` when formed, while LLVM's poison is only illegal behaviour when used (the slicing
case above); a nonzero offset from a provenance-free address that an object outside the model
owns (MMIO, a `@ptrFromInt` register window) is `.illegal`, since the model has no such object;
`Ptr.elem` reads a `usize` index as unsigned, so `p + n` with `n ≥ 2^63` (a wrapped negative
offset that LLVM's signed GEP index would keep in bounds) is `.illegal`; and an offset-0
projection from address zero into a nonnullable result type (0.14.1/0.15.2 `&p.*.f` of a
`[*c]T`) is `.illegal` although no `getelementptr` is emitted.

### MM-4. Two pointer equalities

The translator emits `{a} == {b}` (structural `Ptr` equality: block id and offset) for
ordinary pointers. It emits `ptrEqAddr` (address equality) for C/allowzero pointers, and
addresses for `@intFromPtr`, `<` and `<=`. `eqVsAddr` makes `p1 = @ptrFromInt(n)` before a
callee's block covers `n` (so `p1 = ⟨none, n⟩`), then `p2 = @ptrFromInt(n)` afterwards (so `p2 =
⟨some b, k⟩`). In the model, `p1 == p2` is false and `@intFromPtr(p1) == @intFromPtr(p2)` is
true. No execution of the compiled program gives that combination, and natively the result is
`3` deterministically, whatever the layout. The same split shows for a pointer computed past one
block that numerically reaches another (with MM-3 fixed, forming that pointer is `.illegal`).

**Fix:** one pointer equality, by address (`ptrEqAddr`) for every pointer kind. Together with
MM-1, cross-block equality then depends on `σ` and is provable only from `WF`, as in Zig.
Alternatively, canonicalise provenance in every `@ptrFromInt` result whenever it is read. The
address rule is simpler and matches LLVM's `icmp`.

### MM-5. No stack bound

Calls and escaping locals never fail for lack of stack space. `depth(n)` recurses with a
64-byte escaping local. In the model it returns `n` for every `n` (evaluated up to 600; the
`partial_fixpoint` definition admits an induction proof for all `n`), while the native ReleaseSafe build dies with SIGSEGV for `n = 10^7`. No
premise mentions stack exhaustion (`grep -i stack docs/premises.md docs/claim-strength.md`).
Heap exhaustion, by contrast, is an explicit policy (`AllocPolicy`).

**Fix:** a stack budget in `Mem`, chosen by the environment like `spawnLimit`. Each frame
charges its escaping-local bytes plus a per-call constant. Exhaustion is its own outcome
(`.resource`, not `.illegal`). Theorems are stated for every budget or under an explicit
depth premise. Short of that, add a premise and a claim-strength row now: "results assume the
native stack does not overflow".

**Status: fixed on `codex/fix-mm-hardening`.** `Mem.stackLimit`/`stackUsed` and
`Zig.enterFrame`/`leaveFrame` (emitted for recursive functions that use memory),
`Zig.Error.stackOverflow` (outcome `stack_overflow`), premise STK-01 for every theorem that
recursion reaches, and a claim-strength note. `check.sh` now asserts agreement for
`stack_depth.zig` under an 8 MiB budget.

---

## FAIL-OPEN RISK

### MM-6. Emitter placeholders succeed in the logic

`Air2Lean/Emit.lean` has 17 `(panic! "air2lean: …")` sites and 2 `pure default` sites. It also
has a `.undef` → `0#b`/`false`/`default` value fallback (`resolveVal`). All of them assume
`Check.lean` rejected the input already. In the kernel, `panic! msg` is `default`, and
`default : Zig.MemM α` is `fun m => some (.ok (default, m))`: a **successful no-op**.
`PanicDefault.lean` proves `panic_memM_succeeds` by `rfl`. For `Zig.Result`, `default` is
`.error .overflow`, an arbitrary wrong error. A placeholder in a pointer position is `⟨none, 0⟩`.
So every gap between `Check` and `Emit` turns into a translation in which the unsupported
operation is proved to do nothing and succeed. Only the fuzz harness greps for the placeholder
text (`tests/roadmap/fuzz/air_fuzz.py`). The translator itself does not.

**Fix (one mechanism):** make the emitter total in `Except`. Every placeholder becomes a
translation error, so an unsupported case fails translation. As a stop-gap, a post-emission
gate in `Main.lean` can reject output containing `panic! "air2lean:` or a `default`
placeholder. Never emit a term whose logical value is a success.

**Status: fixed** (`codex/fix-mm-failclosed`). Every arm writes `Emit.lean`'s `placeholder`, an
unbound identifier, instead of `panic!`/`default`/a dropped instruction (the `.undef` value
fallback included; `undefined` is filler only where its bytes are overwritten or never read).
`emitWithNamesChecked` rejects output containing one (`EMITTER_PLACEHOLDER`, in the CLI and in
`--diagnostics-json`). Fourteen arms were reachable from hand-made AIR (`@reduce`/`@shuffle`
operand shapes, optional/error-union/union pointer ops, `union_init`, `memset` without a count,
bodies without a terminator); each now has a checker rule (`tests/roadmap/emitter-placeholders`).
No committed translation contained a placeholder.

### MM-7. The ReleaseFast premise does not hold

`docs/build-modes.md` says: "If the ReleaseSafe model does not throw on an input, the source has
no illegal behaviour on that input." That needs the model to throw on every illegal behaviour
that ReleaseSafe does not check. It does not. MM-3 (inbounds poison) and MM-5 (stack overflow)
are illegal behaviour with no model throw. MM-2 is a ReleaseSafe panic that the model reports as
success, so even the safe build disagrees.

**Fix:** qualify the premise in `build-modes.md` (and the README): it holds only for programs
with no address observation, no out-of-allocation pointer arithmetic, and bounded stack.
Restore it after MM-1, MM-3 and MM-5. This is a documentation change and a claim downgrade, not
a model change.

**Status: qualified** (`codex/fix-mm-failclosed`). `docs/build-modes.md` lists the open
exceptions (MM-1/MM-2, MM-5, float `@divExact`) under the premise, and the README sentence
names them. MM-3 is fixed on the same branch and listed there as fixed, with its residual.

### MM-8. Sep exports allocation-order address facts

`alloc_run` (`ZigLean/Sep/Block.lean`) concludes `∀ l c, m.heap l = some c → c.addr + c.size <
A`: every new block lies above every live block. `Mem.Seq.addr` (`AddrBelow`) is part of the
`Triple` invariant. `Triple.alloc` hides the fact, but the public `*_run` lemmas let a client
prove cross-block order and distance (`> 0`, `≥ 1` gap) for any memory. That is the MM-1
layout lifted into a "for all memories" statement. Natively, stack slots and allocator
addresses have no such order. The M05 branch replaces it with "clear of every live block"
(`Mem.newAddr_clear`), which is the right statement. That fix should land with MM-1.

### MM-9. Stale pointers and address reuse (known: M05)

On main, freed blocks keep their addresses forever. `ptrFromAddr` resolves a stale integer to
the dead block, which is `.illegal` on access, while natively the address can belong to a new
live object. `@intFromPtr(old) == @intFromPtr(new)` is provably false in the model and can be
true natively. `codex/roadmap-address-reuse` (a675f2c5) adds an opt-in reuse oracle with
`.strict`/`.liveBlock` provenance. It covers heap and owned blocks and leaves stack frames and
`mem0` statements fixed. Not re-reported in detail. MM-1's placement oracle would subsume it.

---

## HARDENING

### MM-10. Fixed-buffer blocks do not alias their buffer

`FixedBuffer.init base cap` (`ZigLean/Mem/Owned.lean`) records only `base`. Allocations are
fresh `.owned a` blocks at fresh addresses, and the backing buffer stays an independent live
block. A hand-written spec can prove "writing `buf[0]` leaves the allocated object unchanged",
which is false natively. The translator does not route these allocators yet
(`docs/allocator-identity.md` §Limits), so this affects only hand-written clients.
**Fix:** `init` takes ownership of the buffer's block (marks it lent: no direct access until
`deinit`/`reset`), and allocations are sub-ranges of that block (`Ptr` = buffer block +
offset).

### MM-11. Pointer bytes vs integer bytes

`Enc Ptr` decodes only `ptrFrag` bytes. `intOfBytes` rejects `ptrFrag`. So
`std.mem.asBytes(&ptr)`, hashing a pointer's bytes, or a byte-wise round trip through `[8]u8`
read as integers is `.unspecified`, though Zig defines it. This is conservative for no-error
proofs, but it makes outcome reports and native diffs wrong. **Fix:** PNVI-ae-style
exposure: a `ptrFrag` read as an integer yields its address under the MM-1 oracle. Integer
bytes read as a pointer go through `ptrFromAddr`.

**Status: fixed on `codex/fix-mm-hardening`.** `load` decodes with `decodeLoad`: a decode that
is `.unspecified` and meets pointer bytes is retried with each pointer byte read as the byte of
its pointer's address (`exposeBytes`, the block's `addr` plus the offset). `Enc Ptr` reads eight
integer bytes as the pointer to that address without a block (an access through it is
`.illegal`); resolving it to a live block like `ptrFromAddr` is left to the placement model
(TODO in `ZigLean/Mem/Enc.lean`). Atomic loads, `readSlice` and byte locals keep the strict
decode. Regression: `tests/roadmap/memory-hardening/Bytes.lean`.

### MM-12. Zero-length accesses, address-zero projections (known: L05)

`Mem.access p 0 _` still needs a live block and in-bounds offset. `memset`/`memmove`/`readSlice`
exempt `n = 0`; any other zero-sized access that reaches `Mem.access` does not. Before MM-3,
projections from address zero were `.illegal` even for offset 0 (`ROADMAP.md` L05;
`codex/roadmap-null-projection`). Both are conservative. MM-3's `ptrOffset` rule (offset 0 always
allowed) gives the consistent answer: with MM-3 fixed (`Zig.ptrProject`), an offset-0 projection
from address zero is defined, except into a nonnullable result type (`ptrProjectNonnull`); the
zero-length access rule is unchanged.

### MM-13. Value-level union retagging

For a tagged union held as a Lean value, `setTag_f` from another active field yields `.f
default`: the payload becomes 0, not undefined (`Air2Lean/Emit.lean` named-type emission,
"Zig: undefined"). Zig keeps the old bytes, which are undefined as an `f` payload. Today every
path found writes the whole payload after `set_union_tag` (result-location initialisation), and
partly `undefined` payload stores move the local to a byte block. No counterexample was
found, but this is the one remaining `undefined → 0` default in the value representation.
**Fix:** the value union constructor takes `Bytes` for a fresh payload (undefined), as byte
locals do.

**Status: fixed on `codex/fix-mm-hardening`.** A retag from another field gives `undef_f`, a
payload that is not defined: a read is `.unspecified`, its memory encoding is undefined bytes,
and it becomes defined by a whole-payload write (`set_f`) or a write of every field of a struct
payload (`setField_f`). A partial write deeper than one struct field leaves it undefined
(conservative). Regression: `tests/roadmap/memory-hardening/Union.lean`.

### MM-14. Unbounded footprint and block arrays

`recordAccess` appends every access to `Mem.footprint`, also with one thread, and `raceAt`
scans it linearly. Dead blocks are never removed. `depth(n)` evaluates in under a second for `n
≤ 600`, but `n = 20000` did not finish within minutes. This limits differential testing and
`decide`-style proofs on loops. **Fix:** with a single live thread, `recordAccess` keeps only
the entries a later spawn can race with: none, because a spawn copies the parent's clock.
Clear the footprint whenever `threads` has one live entry.

**Status: fixed on `codex/fix-mm-hardening`** by skipping the scan instead of clearing the
footprint (`Mem.solo`, `raceCheck`): clearing would change `Mem.recordAt`, on which the
concurrency proofs rely. The footprint and dead blocks still grow linearly.

### MM-15. `@memcpy` overlap (control)

`memmove` reads before it writes, so overlapping `@memcpy` is defined in the model. ReleaseSafe
AIR carries Sema's alias check, and the model panics like native (`memcpyOverlap(1)`). The
model is right only because export is pinned to ReleaseSafe (`docs/build-modes.md`). If any
other export mode is ever admitted, `@memcpy` needs its own overlap → `.illegal` rule.

### MM-16. `noalias` parameters

Zig lowers a `noalias` parameter to LLVM's `noalias` argument attribute (the language
reference documents nothing): during the call, memory accessed through a pointer based on the
parameter must not be accessed through any other pointer if either access writes. LLVM optimizes
on it (reordering, forwarding stores), so a violating call has no defined result. The exporter
did not write the attribute, and the model executed the call as if it were absent: a
`memcpy`-like `copy(noalias dest, noalias src, n)` with `dest = src + 1` (compiler_rt's
`memcpySmall`, which the C front end binds for `memcpy`) returned the `@memmove`-like bytes, and
`swap(&x, &x)` returned a value. A theorem could fix such a value; native code is undefined.

**Fix.** The exporter writes each function's `noalias` parameter indices (`noalias`, required
in schema 12). For a function with some, `Air2Lean/Noalias.lean` gives every access the
parameter its pointer is based on (LLVM's "based on": derived pointers, `@ptrFromInt` of a
derived integer, locals that hold one), and the checker rejects the function when that is
ambiguous or a based-on value escapes to memory or another function. The generated function
logs the accesses of each call from the footprint in a scope (`ZigLean/Mem/Noalias.lean`); two
overlapping accesses with different roots, one a write, are `.illegal`. Pointer tags in
`Zig.Ptr` (a precise provenance per pointer) were not chosen: they would change every pointer
construction, pointer equality and the keys of the futex and group tables. The static roots give
the same answer for every function the translator accepts, and fail closed on the rest.

---

## Recommended order

1. MM-6 (small, closes a fail-open translation path).
2. MM-7 (documentation and claim downgrade, immediate).
3. MM-3 `ptrOffset` (local to `Ptr.add` emission and `Mem`; done as `Zig.ptrProject`).
4. MM-1 placement oracle, with MM-4 (address equality) and MM-8 (Sep lemma), folding in M05.
   This is the largest change: `mem0` and every generated statement become parametric.
5. MM-5 stack budget, or at minimum the premise.
6. Hardening items as their features are touched.
