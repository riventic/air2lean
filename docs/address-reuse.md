# Address reuse and provenance contracts (M05)

A real allocator reuses the address of a freed block. In the model, every block's address is the
placement's (`Mem.place`, [address-placement.md](address-placement.md)), which may be a freed
block's address. This page states why lifetime proofs do not depend on fresh addresses, and the
separate contract for programs whose behavior depends on addresses.

The short answer: lifetime safety does not depend on fresh addresses. A pointer is a block id and
an offset. Block ids are never reused. Every liveness check (`Mem.access`, `free`, `rawFree`,
`poisonFree`, the ownership checks of `ZigLean/Mem/Owned.lean`) looks up the block id, never an
address. Addresses matter only for the operations that observe them: `@intFromPtr`,
`@ptrFromInt`, pointer order and address equality, the alignment check and the `@memcpy`
overlap check.

## Reuse is a placement

The placement oracle `Placement.propose : BlockId → Option Nat` proposes an address for each new
block of every kind. The model takes it when Zig allows it (`Mem.placeOk`: nonzero, aligned,
below 2^64, disjoint from every live block). Dead blocks do not count, so the address of a freed
block is valid; so is an address adjacent to a live block. Otherwise the block goes past every
block (`Mem.top`). Because the oracle is an arbitrary function of the new block id, quantifying
over it covers every sequence of address choices that keeps live blocks apart, including "reuse
the most recently freed block" and "never reuse". `Placement.fresh` proposes nothing: the old
fixed layout, for running programs.

## What does not depend on fresh addresses

`ZigLean/Sep/AddrReuse.lean` states the lifetime rules for every reuse policy:

| Theorem | Statement |
| --- | --- |
| `afterAlloc_old` | An allocation, at any address, leaves every existing block (dead or live) unchanged. It never revives a freed block, even one whose address it takes. |
| `alloc_new_id` | The new block's id differs from every existing id. |
| `access_stale` | Use after free: after a free and any sequence of allocations at any addresses, an access through the stale pointer throws `.illegal`. |
| `free_stale`, `rawFree_stale` | Double free: a free of a dead block throws `.illegal`, also when a live block now has its address. |
| `Triple.withPlacement`, `TotalTriple.withPlacement` | Every separation-logic triple holds from a memory with any placement and provenance mode. |
| `reuse_witness`, `reuse_stale_load` | Reuse does happen: block 1 gets block 0's address, and a load through block 0's pointer still throws `.illegal`. |

`Triple`, `TotalTriple`, `alloc_run`, `rawAlloc_run` and the other rules of `ZigLean/Sep/`
hold for every `Mem` with the single-thread invariant (`Mem.Seq`), which says nothing about
addresses. `alloc_run_core` holds for every address the block gets, and its heap is per block
id. So every client proof built from these rules over an arbitrary `Mem` also holds under every
placement, without change: for example `Proofs/Lists` and the arena session client of
`ZigLean/Sep/ArenaClient.lean`. `tutorials/memory-safety/Main.lean` states this for its headline
client (`buildThenFree_address_reuse`: no use after free, no double free, no leak, for every
placement and provenance mode). `Controls.lean` shows that its double-free and use-after-free
clients still throw `.illegal` under reuse (`doubleFree_reuse`, `useAfterFree_reuse`).

## Audit: where the model uses addresses

| Place | Uses | Under every placement |
| --- | --- | --- |
| `alloc`, `Mem.addGlobal` (`Mem.newAddr`) | the placement's address, else `alignUp Mem.top align` | any valid address, also a dead block's |
| `Mem.access` | alignment `(blk.addr + off) % align` | `placeOk` gives only the declared alignment |
| `ptrAddr` (`@intFromPtr`), `ptrLt`, `ptrLe`, `ptrEqAddr`, `ptrIsNull` | the block's address | a dead and a live pointer can have the same address: address-sensitive |
| `ptrFromAddr` (`@ptrFromInt`) | the block whose range covers the address | ambiguous when two blocks cover it (below) |
| `Mem.growFree` (in-place growth) | the grown range is clear of every other live block | growth succeeds or fails with the placement |
| `fixedBufferNext` | padding from the buffer's base address | only the padding; the block address comes from `alloc` |
| footprint, futex waiters, `Io.Group` table | block id and offset (`Ptr`) | unaffected: keyed by provenance |

| Lemma | Address use | Status |
| --- | --- | --- |
| `alloc_run`, `rawAlloc_run`, `Lists.alloc_run` | "the new block's range is clear of every live block" (`Mem.newAddr_clear`) | true under every placement; no order |
| `Lists.append_run` (`Proofs/Lists/Append.lean`) | the `@memcpy` overlap check of `ensureTotalCapacityPrecise` | uses the clearance, not the order |
| `alloc_ok` (`ZigLean/Conc/Lemmas.lean`) | the new block id and `Mem.afterAlloc` | every placement |

The concurrent proofs (`Proofs/Atomics`, `Proofs/Sync`, `Proofs/Threadsync`, `Proofs/Iogroup`,
`Proofs/Threads`) start from `mem0 σ` and hold for every placement `σ`.

## Stale integer addresses

An integer from `@intFromPtr` carries no provenance. Under reuse, the address of a freed block
can also be the address of a live block. When one block covers an address, `ptrFromAddr` gives its block (dead or alive). When
more than one block covers it (a reused address, or one block's end and an adjacent block's
start), `AllocPolicy.provenance` decides:

* `.strict` (the default): `.unspecified`. The stale integer does not silently gain the new
  block's provenance. The model does not know whether the integer came from the old block or
  the new one. So it does not pick, and a proof must show that the case does not arise.
* `.liveBlock`: the **address-sensitive contract**. The program declares that an address
  recovers the provenance of the live block that covers it. Live blocks never share an address
  (`Mem.addrFree`); at the boundary of two adjacent live blocks it takes the one that contains
  the address. A program that declares it asserts that each integer
  it converts belongs to that block, also a stale one. This is the PNVI-style choice of C.

Kernel checks (`ZigLean/Sep/AddrReuse.lean`) run the program "allocate `p`, keep `n = @intFromPtr(p)`,
free `p`, allocate `q` (reusing the address), store 7 in `q`, load through `@ptrFromInt(n)`":

| Memory | Result | Theorem |
| --- | --- | --- |
| reuse, `.strict` | `.unspecified`; the naive argument "`n` is `q`'s address, so the load reads 7" is not a theorem | `stale_int_strict` |
| reuse, `.liveBlock` | 7 | `stale_int_liveBlock` |
| `Placement.fresh` | `.illegal` (`n` recovers dead `p`) | `stale_int_fresh` |

`tests/roadmap/address-reuse/Check.lean` adds runtime regressions. A proposal is refused over a
live block, when misaligned, when 0 and past 2^64; an adjacent, lower or far address is taken.
Stack blocks are placed the same way. An arena reuses a reset block's address.
`std.mem.Allocator` use after free and double free stay `.illegal` under reuse. The one-past
address of a dead block that a live block starts at is ambiguous. A dead block alone still
recovers its own dangling provenance.

## Separate contracts for address-sensitive programs

A program whose result depends on addresses needs its own contract. The lifetime theorems above
do not give it one:

* `@ptrFromInt` of an address that two blocks cover: `.unspecified` unless the program declares
  `ProvenanceMode.liveBlock`. A proof under `.liveBlock` holds only for programs that make that
  declaration.
* Address equality and order (`ptrEqAddr`, `ptrLt`, `ptrLe`, hashing `@intFromPtr`): a stale
  pointer can compare equal to a live one. A proof that uses the result of such a comparison
  must quantify over the placement.
* The `@memcpy` overlap check uses only the clearance of live blocks (`Mem.newAddr_clear`), which
  every placement keeps.

## Limits

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
