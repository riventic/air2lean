# Volatile and device effects (L13)

The memory model (`ZigLean/Mem`) has ordinary, repeatable memory only: a read of an
unchanged block returns the same bytes, and nothing outside the program observes a
store. A `volatile` access is the opposite: each read or write is an observable effect
that may read or change device state, and it may not be merged, repeated, reordered
with other volatile accesses or removed. By default the translator therefore **rejects** every
volatile memory access. There are two ways to give one meaning, both explicit and declared by the
project: a model registry binding (below), or a device contract (`--device-contract`, §Device
contract) that makes each volatile integer access an event of an observable trace.

## Exporter audit

Volatility is a property of the pointer type in Zig AIR; `load`, `store`, the atomics,
`memcpy`/`memset` and the item/projection tags have no separate volatile flag. The shared
exporter (`zig-patch/air-json/json.zig`, used unchanged by 0.14.1, 0.15.2 and 0.16.0)
writes `volatile: bool` in every `ptr` type entry (`writeTypeEntry`, from
`ptrInfo().flags.is_volatile`). Every operand's type is in the file, so a volatile access
is distinguishable in exported AIR for all three versions; the exporter does not drop the flag.

| Evidence | Result |
| --- | --- |
| `ptr` type entries in committed AIR (goldens, roadmap exports; 474 files, schemas 11–12, all three versions) | 5507 entries, every one with an explicit boolean `volatile` |
| real export with `volatile: true` | `tests/golden/layout/air/layout.asVolatile.json` (0.16.0, `@volatileCast` to `*volatile u32`, no access): still accepted, translation unchanged |
| pointer constants (`resolvePtr`) | a volatile *leaf* is already exported `unsupported: "payload_volatile"`; a parent's volatile bit is address metadata |
| inline asm | `assembly` carries `volatile: bool` (schema 8) |
| `@prefetch` | the `prefetch` tag is exported only as the unsupported marker (`coverage/*.json`: `rejected-exporter-unsupported`) |

The decoder (`Json.parseLayout`) still reads a missing `volatile` as `false`, so that older
synthetic fixtures keep decoding. No real export lacks the field. A producer that omitted it
would bypass this check (see Residuals).

## Checker contract

`CheckCtx.checkVolatile` (`Air2Lean/Check.lean`) runs before every instruction check, in
both ordinary translation and `--diagnostics-json`. It rejects:

* a load, store, atomic load/store/RMW/`cmpxchg`, `ptr_elem_val`, `slice_elem_val`,
  `@memset`, either side of `@memcpy`, `ret_load`, a pointer-state test or set
  (`is_null_ptr`, `is_err_ptr`, payload-pointer `_set`, `unwrap_errunion_err_ptr`,
  `try_ptr`, `set_union_tag`) and an asm lvalue output, through a volatile pointer;
* a derivation that drops the qualifier (`@volatileCast` away, `@intFromPtr`, or a
  projection to a non-volatile pointer), so later accesses cannot look ordinary;
* a built-in std model call with an argument that contains a volatile pointer: no std
  model has a volatile contract.

Forming a volatile pointer, casting to one, comparing, storing, passing to translated
functions and returning one stays accepted. These are address metadata, not accesses. A callee
that accesses the pointer is checked itself.

Canonicalization runs first. `forwardReadOnlyCopies` already kept volatile slice-item reads in
place. It now also never forwards a local copy read through a volatile pointer, so
`var x = 5; (&x as *const volatile u32).*` stays a load and reaches the checker.
The item-read rewrites keep the volatile pointer operand, and the checker rejects the result.

Diagnostics use the stable code `VOLATILE_ACCESS`, phase `check`, category
`unsupported_semantics`, with a canonical instruction anchor and guidance. That
instruction's generic `INSTRUCTION_FAILURE` check is skipped. Ordinary translation fails with the
same message and leaves its output unchanged.

## Declared contract: model registry

A device access becomes translatable only via a project model registry binding
([external-models.md](external-models.md)). `ModelRegistry.check` requires:

* each direct volatile pointer parameter to be listed in `footprint.writes`. A device read
  can change device state, so a read-only footprint or a `preserves` binding is rejected.
  The binding is then `tracked`, and its `contract` states the observable effect;
* no nested volatile pointer in any parameter, so a model cannot receive a device
  capability that its footprint does not name.

Return values may contain volatile pointers: the caller's accesses are checked. As for
every binding, an `assumed` contract is reported as an assumption, not as evidence.

## Device contract

`--device-contract <json>` (translation and `--diagnostics-json`) declares one device for the
program: its register map. Without the flag nothing changes: every check above applies and the
output is byte-identical (§Inline asm adds the asm rules that apply with and without it).

```json
{"schema": 1, "device": "uart", "registers": [
  {"name": "status", "address": 268435456, "bits": 32, "access": "read"},
  {"name": "data", "address": 268435460, "bits": 32, "access": "write"}]}
```

`asm` (optional, §Inline asm) lists the `asm volatile` that are device events; `registers` may
then be empty. Every other field is required and no other field is accepted. Names are identifiers; `bits` is 8, 16,
32 or 64; `access` is `read`, `write` or `read-write`; an address is nonzero, naturally aligned
and inside the 64-bit space; registers do not overlap and have distinct names
(`Air2Lean/Device.lean`).

**Checker.** With a contract, `CheckCtx.checkDeviceAccess` admits exactly these volatile accesses:
a `load`, `ptr_elem_val`/`slice_elem_val` (an item of a volatile slice or many-pointer; 0.14.1
and 0.15.2 canonicalize a volatile item read to it) and `store` of an 8/16/32/64-bit integer,
through a byte (not bit) pointer that is not a local place, and not a store of `undefined`. Every
other volatile access keeps its `VOLATILE_ACCESS` rejection: atomics, `@memcpy`/`@memset`,
pointer-state tests, asm lvalue outputs, a non-integer or odd-width pointee, a local
(`*const volatile` of a `var`), a qualifier-dropping derivation and a std model argument.

**Emission.** The output's header records the contract (`-- air2lean-device: {...}`), and the
namespace gets `def air2lean_device : Zig.Device` with the register map. A volatile load becomes
`Zig.vload air2lean_device bits align p` (an unused load is still emitted, bound to `_iN`), a
store `Zig.vstore air2lean_device bits align p v`. The source map records the contract under
`options.device`.

**Semantics** (`ZigLean/Mem/Device.lean`, premise [DEV-01](premises.md#dev-01)). `Mem.dev` holds
the environment's oracle and the trace:

* `Mem.dev.oracle : List DevEvent → Nat → (bits : Nat) → Option (BitVec bits)` answers a read of
  `bits` bits at an address, given every event so far. It is arbitrary; a theorem quantifies
  over it or states which answers it needs. The default oracle answers nothing.
* `Mem.dev.trace : List DevEvent` lists the events, oldest first: `.read addr bits value` and
  `.write addr bits value`.
* A device register is reached through a pointer without a block: `@ptrFromInt` of an address
  that no model block covers, or a pointer parameter whose value is `⟨none, addr⟩`. `vload`
  appends `.read addr bits v` with the oracle's answer `v`; `vstore` appends `.write addr bits v`.
  Neither touches a block, the footprint or the race state.
* A volatile access through a pointer into a model block, or to an address, width or direction
  that the register map does not declare, or a read the oracle does not answer, throws
  `.unspecified` (no modelled meaning; a proof of "never throws" shows it unreachable). A
  misaligned address throws `.illegal`.

So a device read is never a repeatable memory read: two reads are two events, and the second
answer may depend on the first read (`statusTwice_not_merged` below).

**Ordering guarantee.** The trace contains every executed volatile access of the program exactly
once, in program order (the order in which the model executes the AIR instructions, across calls
and loop iterations). Volatile accesses are therefore totally ordered among themselves, and none
is merged, duplicated, removed or reordered. Ordinary (non-volatile) memory accesses are not
events, and the model claims nothing about their order relative to device events. This matches
Zig's/LLVM's rule (volatile operations keep their number and order relative to each other; the
optimizer may move ordinary accesses across them), and it is sound only because DEV-01 assumes
that the device neither reads nor writes model memory (no DMA, no aliasing of model blocks).
Interrupts, other bus masters, timing and multi-threaded device access are not modelled; the
qualified claim is single-threaded. The compiled program is trusted to keep the AIR's volatile
order (TRU-03).

**Real-export evidence** (`tests/roadmap/volatile-effects`). `device_effects.zig` is a UART-style
driver over `*volatile Uart` (`extern struct { status: u32, data: u32 }`): `putc` polls the status
register until bit 0 is set, then writes the byte to the data register; `writeAll` calls it per
byte; `statusTwice` reads status twice; `clearStatus` discards a status read; `sendThenStatus`
writes then reads. The patched 0.16.0, 0.15.2 and 0.14.1 compilers export it; the three
translations are identical except for the profile header, and the 0.16.0 one is committed
(`DeviceEffects/Gen.lean`). `DeviceEffects/Proofs.lean` proves on that unchanged generated code:

* `putc_trace`: for every memory and every oracle satisfying the polling contract `Answers`
  (busy answers `vs`, then a ready answer `r`), `putc uart c` returns and the final memory is the
  initial one with exactly the trace `putcSpec vs r c` appended: one status read per poll, in
  order, then one data write of `c`. `putc_eventually`: every oracle that reports ready within
  finitely many polls satisfies such a contract.
* `statusTwice_trace`, `statusTwice_not_merged`: two read events; under a counting device the
  result is `0 ^^^ 1 = 1`, which a merged read (`a ^^^ a = 0`) can never give.
* `clearStatus_trace`: an unused read is still one event.
* `sendThenStatus_trace`: the write precedes the read, and the oracle answers the read after
  seeing the write.

`check-device.sh` requires the committed translation, the default rejection of the same AIR, the
proofs (no `sorry`/`axiom`/`native_decide`) and four semantic mutants of the generated code, each
of which Lean must reject in the targeted theorems: merging the two reads, moving the read before
the write, dropping the unused read, and an ordinary repeatable `Zig.load` for the status poll.
`check-device.sh --export DIR` re-exports with `$AIR2LEAN_ZIG_AIR` and requires the same
translation. `writeAll` is translated and pinned, but has no theorem.

## Inline asm

An M21 asm op is an `opaque` function of its register inputs, so two executions with equal inputs
are equal in Lean. That is sound only for an instruction whose outputs depend only on its inputs.
It was unsound for `rdtsc`, `rdrand`, port I/O or an output-less effect: a proof could show that
two counter reads are equal. The checker now accepts inline asm only in these two forms
(`CheckCtx.checkAsmEffect`):

1. **Reviewed allowlist.** The asm matches exactly one entry of `Air2Lean/AsmAllowlist.lean`,
   the single reviewed data file: template, ordered constraints (outputs, then inputs), clobbers
   and target architecture. A legacy profile without a target is the x86_64 reference model
   (PRF-01). Each entry records its reason and a reviewer note naming the fixture that needs it.

   | Template | Constraints | Clobbers | Target | Semantics | Fixture |
   | --- | --- | --- | --- | --- | --- |
   | `bswap %[ret]` | `=r`, `0` | none | x86_64 | opaque | `asm.bswap32` |
   | `xorl %%edx, %%edx` / `divl %[b]` | `={eax}`, `=&{edx}`, `{eax}`, `r` | none | x86_64 | opaque | `asm.divmod` |
   | `lzcnt %[x], %[ret]` | `=r`, `r` | `cc` | x86_64 | opaque | `asm.lzcnt64` (volatile) |
   | `popcnt %[x], %[ret]` | `=r`, `r` | none | x86_64 | opaque | `asm.popcnt64` |
   | `pause` | none | none | x86_64 | C03 spin hint | `progress.idle` |
   | `isb` | none | none | aarch64 | C03 spin hint | `docs/progress-hints.md` |

2. **Declared device event.** With `--device-contract`, an `asm` entry
   (`{"template", "constraints", "clobbers"}`, matched exactly) makes a `volatile` asm with at most
   one output, the expression's result, one event of the device trace:
   `Zig.vasm air2lean_device template inputs bits` appends `.asm template inputs bits value` with
   the value from `Mem.dev.asmOracle` (the trace so far, the template, the inputs). An output-less
   asm is `Zig.vasmEffect`. These events share the program order with `vload`/`vstore`. A
   `memory` clobber stays rejected even in a contract (the parser and the checker reject it),
   because DEV-01 says the device does not touch model memory. A non-volatile asm cannot be an
   event, because the compiler may merge or delete it.

Every other asm is `ASM_VOLATILE_EFFECT` (phase `check`, category `unsupported_semantics`, with
guidance). This covers `rdtsc`, `rdrand`, `cpuid`, port I/O, barriers, output-less asm, every
`memory` clobber, an allowlisted template with other constraints or clobbers, and non-volatile
asm off the list.

**Non-volatile asm.** Before L13, non-volatile asm with outputs was also a repeatable opaque. Zig
lowers it to an LLVM `call asm` without `sideeffect` and without memory attributes
(`codegen/llvm/FuncGen.zig`, `airAssembly`). Zig and LLVM then *may* merge two such calls or delete
an unused one. They are not *required* to, so a native run can still execute both and observe two
different `rdtsc` values. A model that makes them equal would therefore under-approximate the
legal executions, and that is unsound for a proof about the program. Being legal to CSE is not
enough. So the allowlist applies to non-volatile asm too (`ticksPlain`). The committed goldens
`bswap32`, `divmod` and `popcnt64` are non-volatile but input-determined, so they are on the list.

**Goldens.** Every committed asm fixture is on the list and translates byte-identically: the four
`examples/asm` goldens (also re-exported with the patched 0.16.0 and 0.15.2 compilers) and the C03
`progress.idle` spin hint. A default translation of all 72 committed AIR directories with the
previous and the new translator is identical. The only exception is the new device fixture,
whose rejection message now names `--device-contract`.

**Real-export evidence.** `device_asm.zig` (0.15.2/0.16.0 syntax; the committed export is 0.16.0
in `air-asm/`) has `elapsed` (two `rdtsc`), `random` (`rdrand`), `fence` (output-less `mfence`),
`barrier` (a `memory` clobber) and `ticksPlain` (non-volatile `rdtsc`). The default rejects every
one of them with `ASM_VOLATILE_EFFECT`. Under `tsc.json`, which declares only the `rdtsc` template,
`elapsed` translates to two `Zig.vasm` (`DeviceAsm/Gen.lean`) and the others stay rejected.
`DeviceAsm/Proofs.lean` proves `elapsed_trace` (two `asm` events in order, the second answered
after the first; the result is their difference) and `elapsed_not_merged` (under a counter oracle
the result is 1, and a merged value gives `a - a = 0`). The `merge_asm` and `repeatable_asm`
mutants (an M21 opaque constant for both reads) are rejected by `elapsed_trace`.
`test_cli.py` repeats these rejections on exporter-schema fixtures for 0.14.1, 0.15.2 and 0.16.0.

## Residuals

* **Inline asm.** Only the reviewed allowlist and declared device events are accepted (§Inline
  asm). Device asm supports at most one output, the result, and no memory operands; `cpuid` or a
  two-output `rdtsc` must be written with one result register. Lvalue outputs of device asm are
  rejected.
* **Missing flag.** A producer that omits `volatile` is read as non-volatile. The patched
  exporter always writes it; a third-party producer must too.
* **Device contract scope.** Only integer loads, item reads and stores are events. Fixed MMIO
  addresses written as pointer *constants* (`const r: *volatile u32 = @ptrFromInt(0x4000_0000)`)
  stay outside the subset: the exporter writes an integer pointer constant as unsupported
  (`mmioFixed`), so a driver takes its register block as a parameter or converts a runtime
  integer. Volatile atomics, bulk memory, `packed struct` registers, interrupts and
  multi-threaded device access are not modelled. The default stays rejection.
* **Real-export qualification.** The fresh exports of `volatile_effects.zig` and
  `device_effects.zig` were run with the patched 0.16.0, 0.15.2 and 0.14.1 compilers (commands
  below); CI repeats them for 0.16.0.

## Commands

```sh
lake build air2lean
python3 tests/roadmap/volatile-effects/test_cli.py --self-test
python3 tests/roadmap/volatile-effects/test_cli.py "$PWD/.lake/build/bin/air2lean"
# Real-export qualification (needs zig-patch/build.sh <version>; repeat per version):
air=$(mktemp -d)
ZIG_AIR_JSON_DIR="$air" ZIG_AIR_JSON_FILTER=volatile_effects. zig-air-0.16.0/bin/zig \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
  tests/roadmap/volatile-effects/volatile_effects.zig
python3 tests/roadmap/volatile-effects/test_cli.py --export-dir "$air" "$PWD/.lake/build/bin/air2lean"
# Device contract: translation pin, default rejection, proofs and mutants; then a fresh export.
bash tests/roadmap/volatile-effects/check-device.sh
AIR2LEAN_ZIG_AIR=zig-air-0.16.0/bin/zig bash tests/roadmap/volatile-effects/check-device.sh --export "$(mktemp -d)"
```
