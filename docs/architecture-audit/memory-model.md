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
| MM-17 | A NaN stored to memory and read as an integer gives the model's canonical NaN bits | SOUNDNESS | reproduced on x86_64 and aarch64 ([nan-bits.md](nan-bits.md)); fixed |
| MM-18 | A stack-room resource is unsound over `Mem.top`/`Mem.roomFor`: freed stack space is never reused, other kinds and the placement consume it | SOUNDNESS (for total `alloc`) | code-read, three scenarios (§MM-18); design: per-thread stack regions |
| MM-19 | A translated Linux thread's locals can never lie in the stack part of its `mmap`ed thread mapping | SOUNDNESS (address claims) | native (`E3`, §MM-18); model: the mapping is a live block |

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
| MM-5 | fixed | per-thread stack budget (`Mem.withStack`, MM-18), `Zig.enterFrame`, `Zig.Error.stackOverflow`; premise STK-01 without a budget |
| MM-6 | fixed | emitter arms write an unbound `placeholder`; output with one is rejected (`EMITTER_PLACEHOLDER`), every formerly reachable arm is a checker rule |
| MM-7 | qualified | `docs/build-modes.md` lists the remaining exceptions of the ReleaseFast premise |
| MM-8 | fixed | no allocation-order address facts in Sep (every placement) |
| MM-9 | fixed | address reuse is one case of the placement (ALC-08) |
| MM-10, MM-12 | open | hardening (fixed-buffer aliasing; zero-length/address-zero projections) |
| MM-11 | fixed | `decodeLoad`: pointer bytes read as integers give the address; integer bytes read as a pointer give a blockless pointer |
| MM-13 | fixed | a retag from another field leaves the payload undefined (`undef_f`) |
| MM-14 | fixed | the race scan is skipped while only the main thread can run (`Mem.solo`) |
| MM-16 | fixed | per-call `noalias` scopes over the footprint (`Zig.naEnter`/`naMark`/`naExit`), roots from `Air2Lean/Noalias.lean`; untrackable functions rejected (`tests/roadmap/noalias/check.sh`) |
| MM-17 | fixed | a float's memory encoding leaves a NaN's bits undefined (`Float.detMask`, the defined-bit masks of `Zig.Packed`); NaN constants keep their bits (`nanConstParts`); `tests/roadmap/nan-bits/check.sh` |
| MM-18 | model fixed (step 1); resource open (steps 3-5) | per-thread stack regions with a LIFO budget and a reserve (§MM-18, `tests/roadmap/stack-region`) |
| MM-19 | fixed | `clone` hands the child the stack part of the mapping; blocks occupy their live bytes (§MM-19, `tests/roadmap/stack-region/ThreadStack.lean`) |

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
`Zig.tryPayloadPtr` and `Zig.errSetOk` form the payload pointer with `ptrProject` too
(`codex/fix-try-payload-bounds`). For the compiler's layouts the error code access already
puts it in bounds: the payload is at offset 0 or right after the 2-byte code at offset 0
(`errPayloadPtr_formed`, `ZigLean/Mem/Lemmas.lean`), so a truncated object reached through a
pointer cast fails at the code or payload access. The check matters for any other layout, such as
`errUnionOffsetsW` with a payload alignment that does not divide the code size
(`tests/roadmap/try-pointers/TryPointers/Runtime.lean`).

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
names them. MM-3 is fixed on the same branch and listed there as fixed.

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
checks the accesses of each call in a scope (`ZigLean/Mem/Noalias.lean`), right after each
instruction and in every function it may call; two overlapping accesses with different roots,
one a write, are `.illegal` before any later failure. Pointer tags in
`Zig.Ptr` (a precise provenance per pointer) were not chosen: they would change every pointer
construction, pointer equality and the keys of the futex and group tables. The static roots give
the same answer for every function the translator accepts, and fail closed on the rest.

### MM-18. Stack room and per-thread stack regions (`codex/stack-region`)

**Status: design approved (decision A, 2026-10-12); step 1 (model, emitters, regressions)
implemented, see §Implementation (step 1).** The logic side is in `docs/sep-full-state.md`
§Stack depth.

#### The finding

A total `alloc`/`allocStack` rule needs a resource `room` that guarantees that the next
stack block can be made. Today `alloc` throws `.stackOverflow` unless `Mem.roomFor` holds: the
placement's proposal is valid, or the fallback `alignUp Mem.top align` ends below
`Placement.addrLimit`. No resource can stand for that condition:

1. **Freed space is never reused.** `Mem.top` counts dead blocks. Under `Placement.fresh` and a
   small `addrLimit`, `while (…) { var x: u64 = 0; use(&x); }` (one `allocStack 8 8`/`free` per
   call) moves `top` up by 16 per iteration and throws `.stackOverflow` after
   `(addrLimit - 4096) / 16` iterations, with no live stack block. A rule in which `free` gives
   the room back proves the loop total; the model overflows.
2. **Other kinds consume it.** `rawAlloc`, `ownedRawAlloc`, the moving remap, `mmap`/`mremap`
   and in-place growth (`Mem.growFree`) place blocks without any stack token and raise `top`.
   A thread's stack room depends on every other thread's heap traffic.
3. **One placement kills it.** `Mem.placeOk` accepts a proposal that ends at `addrLimit`. A
   placement that puts one 1-byte heap block at `addrLimit - 1` makes `top = addrLimit + 1`;
   from then on every fallback fails. Since theorems hold for every placement, no total
   statement about a later stack block is provable.

#### What native code does (evidence)

Fixture: a ReleaseSafe program that records the addresses of escaping locals in a caller and
an inlinable callee, in a `noinline` caller/callee pair, in two sibling calls and in a spawned
thread, and prints the mapping that holds them (`/proc/self/maps`) and the stack rlimit.
Ran on x86_64-linux (Docker `--platform linux/amd64`, Rosetta) with 0.14.1, 0.15.2, 0.16.0 and
0.17.0, on aarch64-linux (native arm64 container) with 0.14.1, 0.15.2, 0.16.0 and 0.17.0, and
on aarch64-macos with 0.16.0 and 0.17.0 (0.14.1 and 0.15.2 do not link against the current macOS
SDK). The fixture is `tests/roadmap/stack-region/evidence.zig` (`check.sh --docker-linux`). The
results are the same on every row except E1 on aarch64-linux 0.14.1/0.15.2, where the inlined
callee's local lies below the caller's:

| | observation | consequence for the model |
|---|---|---|
| E1 | an inlined callee's local lies **above** the caller's earlier local (below on aarch64-linux 0.14.1/0.15.2); a `noinline` callee's lies below | the address order of locals across model frames is not fixed |
| E1' | the inlined callee's local and a later local of the caller **share one address** (LLVM stack colouring) | a dead stack block's address is reused inside one native frame |
| E2 | two sibling calls put their locals at the same address | reuse across frames |
| E3 | a spawned thread's locals lie inside the anonymous mapping that `std.Thread.spawn` `mmap`s (Linux: guard, stack, TLS, `Instance`; 16 MiB stack by default in all four versions) | MM-19 |
| E4 | main stack: 8 MiB on macOS, the container's rlimit (16 MiB) on Linux; threads: `SpawnConfig.default_stack_size` = 16 MiB (0.14.1–0.17.0) | stack sizes are environment facts, not program facts |

E1 and E1' rule out the obvious design: deterministic LIFO addresses (each new stack block just
below the previous one) would prove `&callee_local < &caller_local` and `&y != &z`, both false
natively. **The addresses must stay the placement's; only the accounting can be LIFO.**

#### The design

Each thread `t` gets a stack state. Its accounting is LIFO and does not depend on the placement;
the placement still chooses the addresses.

```
structure StackEntry where
  block  : Option BlockId     -- none: the frame charge of a recursive call (enterFrame)
  charge : Nat
structure StackState where
  budget  : Option Nat := none   -- S_t, bytes of model charge; none: no budget (today)
  base    : Nat := 0             -- the reserve [base, base + S_t)
  entries : Array StackEntry := #[]   -- push order
  cells   : Nat := 0             -- charge of the thread's lifetime cells (TLS instances, errno)
Mem.stacks : Array StackState    -- indexed by ThreadId, like Mem.clocks
```

* **Charge.** A stack block of `size` bytes and alignment `align` charges `size + align` (at least
  1, and at least the `size + align - 1` the fallback may take). A recursive call charges
  `frameBase` (its escaping locals are charged by their own blocks, so `enterFrame` drops its
  `bytes` argument).
* **Depth** `Mem.depth t`: the charges of the entries up to the topmost entry that is still
  live (a frame entry until `leaveFrame` pops it, a block entry while its block is live).
  Entries above it are popped logically and truncated at the next push. **`used t = cells +
  depth`, `slack t = S_t - used t`.** `free` does not change: a block's death pops its entry when
  every entry above it is dead too.
* **`allocStack size align`** of the current thread `t` with `budget = some S`: if
  `used t + charge > S`, `.stackOverflow`. Otherwise the block gets the placement's proposal if it
  is valid (`Mem.placeOk`, which now also excludes every live reserve), else the **LIFO
  fallback** `alignDown (base + S - depth - size) align`, inside the reserve and below every
  fallback block of a live entry. It pushes its entry. With `budget = none` it is today's
  `alloc .stack` (no room resource exists for such a thread).
* **Thread-lifetime cells** (`tlsAlloc` at `tlsEnter`, the macOS `errno` cell of `__error`) are
  reserved up front: when a thread gets its budget, `cells` is set to the charge of its TLS
  instances plus one `errno` slot, so `errno`, which `__error` makes at its first use deep in
  some call chain, never interleaves with the LIFO entries (natively it lives in the thread
  structure from the start). Their fallback is the bump from the bottom of the reserve, the
  LIFO fallback grows down from the top, and `cells + depth + charge ≤ S` keeps them apart. They
  die at thread end (`tlsExit`; `errno` joins it).
* **Reserve.** `[base, base + S)` is placed when the thread gets its budget: by a new proposal
  `Placement.reserve : ThreadId → Option Nat` if it is valid (aligned to 16, below `addrLimit`,
  clear of live blocks and reserves), else by the first fit. The main thread's budget is set on
  the start memory (`Mem.withStack S`, after the globals: `Mem.firstFit` succeeds under
  `Mem.GlobalsFit` and `S ≤ 2^40`). A child's budget is set at `fork` (environment parameter
  first, `SpawnConfig.stack_size` later, step 5); without a fit the spawn fails as
  `SystemResources` where the spawn policy allows a failure, else `.stackOverflow`. A reserve
  stays reserved until its thread has ended and its cells are dead.
* **Everything else avoids the reserves:** `Mem.addrFree` (so `placeOk`), `Mem.growFree`,
  `Mem.mappingRoom` and `Mem.top` (past every live reserve). Heap, `mmap` and allocator blocks
  keep failing as out of memory when the address space is full; that outcome is legitimate and
  every allocator spec already covers it.
* **`Mem.stackLimit`/`stackUsed` are removed**: the budget is per thread, and the main thread's
  budget is what `stackLimit` was (MM-5). The global counter was also wrong with threads (all
  threads charged one counter).

**Why the room is sound now.** `slack t` depends only on `t`'s own entries, cells and budget.
No other thread and no other block kind changes it, and the placement cannot reduce it (a
proposal inside a reserve is rejected; a proposal elsewhere consumes no reserve space). When
`used t + charge ≤ S`, the fallback always fits: it lies in `t`'s reserve, which no other block
meets, below the fallback blocks of the live entries and above the cells. The three scenarios
above: (1) a freed block's entry pops, so its charge comes back; (2) heap traffic never touches
`slack`; (3) a block near `addrLimit` does not meet a reserve placed before it, and a reserve
placed later avoids it.

**Why it stays native-faithful.** For a native run, take the placement that proposes every
block's native address and puts each reserve in address space the run never maps (premise
STK-02). Every native stack address is then a valid proposal: aligned, below `addrLimit`,
disjoint from the live blocks (native objects are disjoint) and from the reserves. So the model
reproduces the native layout, including E1, E1' and E2; the LIFO fallback is used only by
placements that no native run produces. The budget is an environment premise (STK-01, budgeted
form): the native stack of `t` holds every call chain whose model charge stays within `S_t`.

#### LIFO discipline of generated code

* `Emit.emitFunctionBody`: `enterFrame` (recursive functions that use memory), then the escaping
  locals' `allocStack` in `FCtx.stackBlocks` order, the body, the `free`s **in the same order**,
  then `leaveFrame`. `TimedEmit.functionDef` and the reference semantics (`Sem.lean`,
  `frame.forM Zig.free`) do the same. A body error ends the run, so nothing runs between a
  frame's allocations and its frees except the body's balanced calls. Across frames the frees are
  LIFO; within a frame they are FIFO.
* Nothing else frees a `.stack` block: `rawFree`/`poisonFree` need `.heap`, `Os.free` rejects
  every other kind, `munmap` needs `.mapped`, the owned allocators check their kind, and
  `tlsExit` frees cells. Generated code cannot call `Zig.free` on a pointer it chose.
* **Change:** the three emitters free in reverse allocation order, so every generated free is
  of the top entry (the logic's free rule needs that; `docs/sep-full-state.md` §Stack depth).
  Natively there is no free at all, so nothing observable changes. The goldens of all four
  versions are regenerated.
* **If a free is not LIFO** (no generated code does this): the entry stays, dead and unpopped,
  until every entry above it is dead. The slack comes back late, never early: conservative. A
  model in which an out-of-order free returned its charge at once would be unsound: `alloc b`,
  `alloc b'`, `free b`, then `alloc b''` with the returned room overflows a budget of
  `charge b + charge b'`.

#### Premises

* **STK-01 (amended):** with a budget, the native stack of thread `t` holds every call chain
  whose model charge (escaping locals `size + align`, `frameBase` per recursive frame, its
  lifetime cells) stays within `S_t`. Without a budget, unchanged. The charge is not a bound on
  the native frame; the premise relates the two.
* **STK-02 (new):** every thread's reserve can be placed in address space that the native run
  never maps while the thread lives (the reserve is never touched natively). It needs
  `S_t ≤ 2^40`, and the budgets of the live threads must sum to well below the address space
  the native run leaves unmapped (e.g. 64 threads of 1 GiB in a 2^47 space).
* Both are claimed by the tokens `allocStack`, `enterFrame`, `stackOverflow`, `withStack`.

#### Fail-closed points

1. A thread without a budget has no `sp` resource (`docs/sep-full-state.md`): a total stack
   allocation is not provable there; the partial rules are unchanged.
2. A budget whose reserve does not fit: the start memory with `S > 2^40` or globals that do
   not fit is excluded by the adequacy premise (Full/Init); a child spawn fails as above.
3. Out-of-order frees: conservative, as above.
4. Heap-kind runtime cells without an out-of-memory path (`Future.slotAlloc`: `alloc .heap`)
   keep today's `.stackOverflow` without address room: partial only, listed as follow-up (not a
   stack object; native `Io` implementations have their own fallback).
5. MM-19 below was open until step 2 (fixed).

#### MM-19. A child's locals cannot lie in its thread mapping

The translated `LinuxThreadImpl.spawn` (all four versions) `mmap`s one mapping (guard page,
`stack_size` bytes of stack, TLS area, `Instance`) and passes the stack's top to `clone`.
`Os.clone` ignores the `stack` argument. Natively the child's locals lie inside that mapping
(E3: `7ffffe77d000-7fffff7ff000`, 16904 KiB, holds the child's local at `7fffff77cfc0`). In the
model the mapping is a live `.mapped` block, so `Mem.placeOk` rejects every address inside it for
the child's stack blocks: `@intFromPtr(&local)` inside `thread.impl.thread.mapped` is provably
false in the model and true natively. Not caused by the stack region; the region makes the fix
natural (step 2): `clone` makes `[stack - S_c, stack)` of the mapping the child's reserve and
lets proposals for the child's stack blocks fall inside it; the parent's accesses to those bytes
are `.illegal` while the child runs (a conservative over-approximation); `munmap` after the join
releases it. Approved (coordinator, 2026-10-12): a soundness bug, fixed as step 2, with the
minimal general `Mem.LiveDisjoint` exception for a reserve nested in its mapping and the
`@intFromPtr` counterexample as a regression; Linux and macOS thread stacks are instances of one
per-thread reserve contract.

**Fixed (step 2, `codex/stack-region-mm19`).** The implementation needs no `LiveDisjoint`
exception; it changes what a block occupies instead:

* **A block occupies its live bytes** `[addr + lo, addr + size)`, `lo` its first live offset
  (`BlockKind.mappedLo`: 0 but for an OS mapping). `Block.clearOf` (so `Mem.addrFree`,
  `Mem.LiveDisjoint`) uses it. A prefix that `munmap` released is free address space again, as it
  is natively (`Os.unmapCase_prefix_ge`).
* **`clone` cuts the child's stack off the mapping.** `Os.Linux.clone` reads the stack top `top`:
  it must lie in a live mapping with `addr + lo < top ≤ addr + size`, else the spawn is
  `.unspecified`. Before the spawn the parent's write of the stack part is recorded (the
  hand-over edge); after it, `giveStack` re-checks the mapping (`.illegal` if it changed), moves
  the mapping's `lo` up to the stack top and records the range as the child's
  `StackState.native` (`NativeStack {host, lo, hi, start}`). Nobody reaches those bytes through
  the mapping while the child runs: a parent access is `.illegal` (conservative; natively it is a
  race on the child's stack at best).
* **The child's stack blocks may lie there, nothing else may.** `Mem.homeOk` accepts a `.stack`
  proposal of the current thread inside its own native stack (clear of every live block and of
  every other reserve); `Mem.placedFor?` is `homeOk || placeOk` and `allocAddr`/`allocOk` use it
  (for every other kind it is `placed?`, by `rfl`). `StackState.reserveClear` includes the native
  stack, so every other placement (`placeOk`, `growFree`, `mappingRoom`, `top`) avoids it.
* **Thread end gives it back.** `cloneExit` first runs `releaseStack`: it frees the child's live
  stack blocks in the native stack (as `free`), restores the mapping's `lo` with undefined bytes
  (a write by the child, so a later access by the joiner is ordered after it) and clears
  `native`. `munmap` after the join then succeeds as natively.
* **The native stack and the budget reserve are two ranges.** The child's own proposals must be
  valid anywhere in its native stack (E1); the LIFO fallback of a budget (MM-18) lives in a
  reserve that is never mapped natively (STK-02). Step 5 gives a child a budget reserve like the
  main thread's.

Statements that were false natively and changed with the model (each listed in the PR):
`Holds.apart`/`FTriple.apart` (byte `x` of `b` before an owned byte `y'` of `b'` or the
converse; the old "before the other block's start" is refuted by `ThreadStack.old_apart_false`,
two live bytes of two live blocks of a reachable memory); `Mem.addrFree_cell`,
`Mem.newAddr_clear`, `alloc_run`, `rawAlloc_run`, `alloc_slice_run` (`A + n ≤ c.addr +
c.kind.mappedLo`); `LiveDisjoint.addr_ne` takes the two bytes' `lo` bounds (default `by simp`);
`Owns.block` exports the owned byte's `lo` bound. Regressions:
`tests/roadmap/stack-region/ThreadStack.lean` (kernel: `child_local_in_mapping`,
`heap_not_in_stack`, `parent_stack_not_in_child_stack`, `parent_access_illegal`,
`old_apart_false`) and `tests/roadmap/os-threads/Check.lean` (clone with a real mapping, a stack
outside a mapping, munmap after join, restored bytes undefined).

#### Impact

* **Model and emitters** (step 1): `Mem/Basic` (state, `allocStack`, `enterFrame`/`leaveFrame`,
  reserves in `addrFree`/`top`), `Mem/Alloc` (`growFree`), `Os/Mmap` (`mappingRoom`), `Mem/Tls`,
  `Os/Clock` (cells), `Mem/Thread` (`fork`), `Emit`, `TimedEmit`, `Sem` (reverse frees,
  `enterFrame` without `bytes`); goldens and checked-in `Gen.lean` of four versions regenerated.
* **Lemmas** (step 1): `alloc_run_eq`/`alloc_run_noRoom`/`Mem.newAddr_*` stay for the heap kinds;
  `allocStack` gets its own run lemmas (`budget = none`: today's; `some`: the region). Re-proved
  where they unfold `allocStack` to `alloc .stack`: `Mem/Lemmas`, `Sep/Block` (legacy, existing
  statements only), `Sep/Full/{Triple,Tame,Disjoint,Block,Toy}`, `Conc/{Lemmas,Own,TlsLemmas}`.
  `LiveLayout` gains "the reserves are disjoint from each other and from every live block not in
  them". The partial rules' statements do not change (they export only "aligned and clear of
  every live block", MM-8).
* **Proofs and tests** that name `roomFor`/`stackLimit`: `memory-hardening/{NoRoom,Stack}`,
  `architecture-audit/memory-model/StackRunner`, `loop-tactics/Recursion`, `address-reuse/Kernel`,
  `alloc-fba/Client`, `one-logic/Block`, `tutorials/memory-safety/Controls`, `diff/Outcome`; the
  `*_safe` statements in `Proofs/` mention only `.stackOverflow` and do not change.
* About 15 library files and 10 test files; the generated programs change only in the order of
  their `free`s and the `enterFrame` argument.

#### Implementation (step 1)

* **The region is the `.stack` kind of `alloc`.** `allocStack` stays `alloc .stack`, so every
  `.stack` block (generated locals and the hand-written runtime clients' `alloc .stack`) is
  accounted, and the existing rules about `alloc` cover it: they were re-proved, not duplicated.
  `alloc` checks `Mem.allocOk kind` and places at `Mem.allocAddr kind`; for every kind but a
  `.stack` block of a thread with a budget these are `Mem.roomFor` and `Mem.newAddr` (by `rfl`).
  The lemmas that named `roomFor`/`newAddr` for any kind now name `allocOk`/`allocAddr`
  (`alloc_run_eq`, `alloc_run_noRoom`, `alloc_run_core`, `alloc_run`, `alloc_noErr`,
  `alloc_new_id`, `LDMono.alloc`); `Mem.allocOk_fit`, `Mem.allocOk_le` and `Mem.allocAddr_mod`
  give what the partial rules export (aligned, clear of every live block,
  inside the address space), so no rule statement changed.
* **State.** `Mem.stacks : Array StackState` (budget, reserve base, entries); an entry records
  its block (or a frame), the depth at its push and its charge, so the depth is O(1) (the top
  held entry's end). `StackState.held` pops dead entries lazily (`Array.popWhile`); a push stores
  the popped array. `leaveFrame` closes the topmost open frame entry.
* **The fallback is checked at run time** (`Mem.fitOk`): a fallback that met a live block or left
  the address space would throw `.stackOverflow`. In every memory that a run reaches it never
  does (the reserve holds only the thread's own fallback blocks, below the held entries); step 3
  proves that from the `sp` invariant. The check keeps the partial rules free of any new
  invariant.
* **Reserves.** `Mem.withStack S` gives the main thread its budget: the placement's
  `Placement.reserve 0` if valid (`Mem.placeOk`, 16-aligned), else the first fit, else no budget
  (fail closed). `Mem.placeOk` is `Mem.fitOk` plus `Mem.reservesFree`; `Mem.top` is past every
  reserve; `Mem.growFree` and `Mem.mappingRoom` avoid reserves.
* **Cells are deferred to step 5.** The TLS instances of spawned threads and the macOS `errno`
  cell are still made by `alloc .global` outside every reserve. That is sound (they consume no
  slack); what is missing is only a total `__error` under an exhausted address space (fail-closed
  point 4). `used = depth` until the threads step adds the cells' reservation.
* **Regressions** (`tests/roadmap/stack-region/Regressions.lean`, kernel): the three scenarios
  in their fixed form and their old behaviour without a budget, overflow exactly at the budget
  (blocks and frames), the splittable-room counterexample (`splitRoom_cx`) and its LIFO control,
  and E1/E1' as one placement under a budget (`e1_native_layout`).

#### Steps (phase 2, one small PR each, on `codex/stack-region`)

1. Model + emitters + lemmas + regressions (done, above).
2. MM-19: `Os.clone` hands the child the stack part of its mapping (done, §MM-19).
3. Logic: the `sp` resource, Holds conjunct, total rules (`docs/sep-full-state.md`), as one
   instance of the generic authoritative-counter pattern shared with the credits.
4. Full/Init gives the main thread `sp 0 S k₀` under `Mem.withStack S`; replaces interim (C) and
   `TotalTripleIn` (Full/Strength, memory-hardening/NoRoom, one-logic/Strength).
5. Threads: child budgets from the spawn, reserve release at thread end, the cells, thread rules.

---

## Recommended order

1. MM-6 (small, closes a fail-open translation path).
2. MM-7 (documentation and claim downgrade, immediate).
3. MM-3 `ptrOffset` (local to `Ptr.add` emission and `Mem`; done as `Zig.ptrProject`).
4. MM-1 placement oracle, with MM-4 (address equality) and MM-8 (Sep lemma), folding in M05.
   This is the largest change: `mem0` and every generated statement become parametric.
5. MM-5 stack budget, or at minimum the premise.
6. Hardening items as their features are touched.
