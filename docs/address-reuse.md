# Address reuse and provenance contracts (M05)

By default, the model gives every block a fresh address (`ZigLean/Mem/Basic.lean`). A real
allocator reuses the address of a freed block. This page states which proofs depend on fresh
addresses and which do not. It also describes the opt-in reuse policy and the separate contract
for programs whose behavior depends on addresses.

The short answer: lifetime safety does not depend on fresh addresses. A pointer is a block id and
an offset. Block ids are never reused. Every liveness check (`Mem.access`, `free`, `rawFree`,
`poisonFree`, the ownership checks of `ZigLean/Mem/Owned.lean`) looks up the block id, never an
address. Addresses matter only for the operations that observe them: `@intFromPtr`,
`@ptrFromInt`, pointer order and address equality, the alignment check and the `@memcpy`
overlap check.

## The reuse policy

`AllocPolicy.reuseAddr : BlockId → Option Nat` (default: `fun _ => none`) proposes an address
for each new block. `alloc` takes the proposal for a heap block (`std.mem.Allocator`) or an
owned block (arena, fixed buffer) when it is valid (`Mem.reuseOk`):

* it is not 0;
* it is a multiple of the block's alignment;
* the block ends below `nextAddr`, so it stays below every later fresh block;
* the range `[A, A + size]` (one past the end included) does not meet the range of any live
  block (`Mem.addrFree`). Dead blocks do not count, so the address of a freed block is valid.

Otherwise the block gets the fresh address, as before. Stack blocks and globals always get fresh
addresses. Because the oracle is an arbitrary function of the new block id, quantifying over it
covers every sequence of address choices that keeps live blocks apart. That includes "reuse the
most recently freed block" and "never reuse".

The default policy proposes nothing. So the default model is unchanged: every existing
evaluation, golden output and differential observation is the same. `Mem.newAddr`,
`Mem.newNext` and `Mem.afterAlloc` are the address, the next free address and the memory after
an allocation under any policy. `alloc` sets `Mem.afterAlloc`.

## What does not depend on fresh addresses

`ZigLean/Sep/AddrReuse.lean` states the lifetime rules for every reuse policy:

| Theorem | Statement |
| --- | --- |
| `afterAlloc_old` | An allocation, at any address, leaves every existing block (dead or live) unchanged. It never revives a freed block, even one whose address it takes. |
| `alloc_new_id` | The new block's id differs from every existing id. |
| `access_stale` | Use after free: after a free and any sequence of allocations at any addresses, an access through the stale pointer throws `.illegal`. |
| `free_stale`, `rawFree_stale` | Double free: a free of a dead block throws `.illegal`, also when a live block now has its address. |
| `Triple.withReuse`, `TotalTriple.withReuse` | Every separation-logic triple holds from a memory with any reuse oracle and provenance mode. |
| `reuse_witness`, `reuse_stale_load` | Reuse does happen: block 1 gets block 0's address, and a load through block 0's pointer still throws `.illegal`. |

`Triple`, `TotalTriple`, `alloc_run`, `rawAlloc_run` and the other rules of `ZigLean/Sep/`
hold for every `Mem` with the single-thread and address invariant (`Mem.Seq`). That invariant
does not restrict `allocPolicy`. `alloc_run_core` holds for every address the block gets, and
its heap is per block id. `Mem.Seq.alloc` keeps the invariant under reuse, because a reused
block ends below `nextAddr`. So every client proof built from these rules over an arbitrary `Mem` also holds under every
reuse policy, without change: for example `Proofs/Lists` and the arena session client of
`ZigLean/Sep/ArenaClient.lean`. `tutorials/memory-safety/Main.lean` states this for its headline
client (`buildThenFree_address_reuse`: no use after free, no double free, no leak, for every
reuse oracle and provenance mode). `Controls.lean` shows that its double-free and use-after-free
clients still throw `.illegal` under reuse (`doubleFree_reuse`, `useAfterFree_reuse`).

## Audit: where the model uses addresses

| Place | Uses | Under reuse |
| --- | --- | --- |
| `alloc` (`Mem.newAddr`) | fresh address `alignUp nextAddr align` | heap/owned blocks may reuse a valid address; stack blocks stay fresh |
| `Mem.addGlobal` | fresh address at program start | unchanged (nothing to reuse) |
| `Mem.access` | alignment `(blk.addr + off) % align` | `reuseOk` requires an aligned address |
| `ptrAddr` (`@intFromPtr`), `ptrLt`, `ptrLe`, `ptrEqAddr`, `ptrIsNull` | the block's address | a dead and a live pointer can have the same address: address-sensitive |
| `ptrFromAddr` (`@ptrFromInt`) | the block whose range covers the address | ambiguous when two blocks cover it (below) |
| `Mem.byteRemapLast` (in-place growth) | every other block, dead or live, ends below | a reused low block has blocks above it, so growth is refused (a permitted failure) |
| `fixedBufferNext` | padding from the buffer's base address | only the padding; the block address comes from `alloc` |
| footprint, futex waiters, `Io.Group` table | block id and offset (`Ptr`) | unaffected: keyed by provenance |

| Lemma | Freshness use | Status |
| --- | --- | --- |
| `Mem.AddrBelow` (`Mem.Seq.addr`) | live blocks end below `nextAddr` | holds under reuse (`Mem.Seq.alloc`) |
| `alloc_run`, `rawAlloc_run`, `Lists.alloc_run` | stated "the new block lies above every live block" | now "the new block's range is clear of every live block" (`Mem.newAddr_clear`), true under every policy |
| `Lists.append_run` (`Proofs/Lists/Append.lean`) | the `@memcpy` overlap check of `ensureTotalCapacityPrecise` | uses the clearance, not the order: the copy's ranges do not overlap either way |
| `alloc_ok` (`ZigLean/Conc/Lemmas.lean`) | the fresh address | needs `reuseAddr? = none` (by `rfl` for stack blocks and the default policy); `alloc_ok'` holds for every policy |
| `Mem.afterByteRemap` lemmas (`ZigLean/Sep/Remap.lean`) | `nextAddr` grows past the block | unchanged |

The concurrent proofs (`Proofs/Atomics`, `Proofs/Sync`, `Proofs/Threadsync`, `Proofs/Iogroup`,
`Proofs/Threads`) start from a fixed initial memory (`mem0`). So they fix the default policy, as
they fix the failure policy (`ALC-02`). They are not claimed under reuse.

## Stale integer addresses

An integer from `@intFromPtr` carries no provenance. Under reuse, the address of a freed block
can also be the address of a live block. With fresh addresses at most one block covers an
address, and `ptrFromAddr` gives its block (dead or alive), as before. When more than one block
covers it, `AllocPolicy.provenance` decides:

* `.strict` (the default): `.unspecified`. The stale integer does not silently gain the new
  block's provenance. The model does not know whether the integer came from the old block or
  the new one. So it does not pick, and a proof must show that the case does not arise.
* `.liveBlock`: the **address-sensitive contract**. The program declares that an address
  recovers the provenance of the live block that covers it. Live blocks never share an address
  (`Mem.addrFree`), so the block is unique. A program that declares it asserts that each integer
  it converts belongs to that block, also a stale one. This is the PNVI-style choice of C.

Kernel checks (`ZigLean/Sep/AddrReuse.lean`) run the program "allocate `p`, keep `n = @intFromPtr(p)`,
free `p`, allocate `q` (reusing the address), store 7 in `q`, load through `@ptrFromInt(n)`":

| Memory | Result | Theorem |
| --- | --- | --- |
| reuse, `.strict` | `.unspecified`; the naive argument "`n` is `q`'s address, so the load reads 7" is not a theorem | `stale_int_strict` |
| reuse, `.liveBlock` | 7 | `stale_int_liveBlock` |
| fresh addresses | `.illegal` (`n` recovers dead `p`) | `stale_int_fresh` |

`tests/roadmap/address-reuse/Check.lean` adds runtime regressions. A reuse proposal is refused
over a live block, over the one-past byte of a live block, when misaligned, when 0 and when above
`nextAddr`. Stack blocks stay fresh. An arena reuses a reset block's address. `std.mem.Allocator`
use after free and double free stay `.illegal` under reuse. The one-past address of a dead block
that a live block starts at is ambiguous. A dead block alone still recovers its own dangling
provenance.

## Separate contracts for address-sensitive programs

A program whose result depends on addresses needs its own contract. The lifetime theorems above
do not give it one:

* `@ptrFromInt` of an address that two blocks cover: `.unspecified` unless the program declares
  `ProvenanceMode.liveBlock`. A proof under `.liveBlock` holds only for programs that make that
  declaration.
* Address equality and order (`ptrEqAddr`, `ptrLt`, `ptrLe`, hashing `@intFromPtr`): a stale
  pointer can compare equal to a live one. A proof that uses the result of such a comparison
  must quantify over the reuse oracle, or fix the default fresh policy and say so.
* The `@memcpy` overlap check uses only the clearance of live blocks (`Mem.newAddr_clear`), which
  every policy keeps.

## Limits

* The policy keeps a 1-byte gap after every live block and reuses only below `nextAddr`. It does
  not model allocators that place live blocks back to back, or addresses above the fresh range.
* Stack frames get fresh addresses. Real stacks reuse frame addresses. No lifetime lemma depends
  on this (`alloc_run_core` holds for every address), but the stack is not quantified.
* The race check is keyed by block id. A dead block's footprint entries never race with a new
  block at its address. This follows the model's view that `free` and the next allocation are
  ordered by the allocator.
* No claim is made about the native allocator's actual addresses.

## Checks

```sh
bash tests/roadmap/address-reuse/check.sh   # kernel theorems (no sorryAx), runtime regressions
lake env lean tutorials/memory-safety/Main.lean
lake env lean tutorials/memory-safety/Controls.lean
```

Premise: [ALC-08](premises.md#alc-08).
