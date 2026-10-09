# Address placement (MM-1, MM-2, MM-4, MM-8)

A Zig program can observe addresses: `@intFromPtr`, pointer order (`<`, `<=`), pointer
equality, `@ptrFromInt`, and the alignment checks of `@alignCast`, `@ptrFromInt` and every
load and store. Natively, the addresses are the linker's, the stack frame's and the allocator's.
The model does not know them, so it must not fix them. Premise: [SEM-06](premises.md#sem-06).

## The placement oracle

`Zig.Placement` (`ZigLean/Mem/Basic.lean`) is an environment parameter of `Mem`
(`Mem.place`): `propose : BlockId → Option Nat`, the address of each block. Every block
kind uses it: globals at program start (`Mem.ofGlobals σ`), stack blocks at function entry,
heap and allocator blocks at `alloc`. The model takes a proposal only if it is what Zig
guarantees for an object (`Mem.placeOk`):

* not 0;
* a multiple of the block's declared alignment;
* the block ends at or below 2^64;
* disjoint from every live block (`Mem.addrFree`). Blocks may be adjacent, in any order, and
  may reuse a dead block's address. A zero-size block constrains nothing.

Otherwise the block goes to `alignUp Mem.top align`, past every block with a 1-byte gap. The
placement that proposes nothing, `Placement.fresh`, gives the old fixed layout (first block at
4096): it is what the differential harness, `#eval` and runtime fixtures run with.

Because a run is deterministic given the placement and the oracle is an arbitrary function of
the block id, quantifying over it covers every address assignment that a native build can
produce, as long as the block's declared alignment is right:

* stack block: the alignment of the `alloc`'s pointer type (`align(N)` or the ABI alignment);
* global: the ABI alignment of its type, capped by the largest alignment of a pointer constant
  into it at an offset that alignment divides (each is a true lower bound). The export does not
  record a global's own `align(N)`, but `&g` of an under-aligned global has the under-aligned
  pointer type;
* heap and allocator block: the requested alignment.

## What a statement can and cannot say

The generated `mem0` takes the placement: `def mem0 (σ : Zig.Placement) : Zig.Mem`. A theorem
about a program run from `mem0 σ` holds for every `σ`; nothing about `σ` is assumed. The only
address facts available are the ones above:

| Lemma | Fact |
| --- | --- |
| `Mem.newAddr_mod`, `Mem.ofGlobals_addr_mod` | a new block or a global is aligned |
| `Mem.newAddr_clear`, `alloc_run` | a new block is clear of every live block (`≤`, no gap) |
| `Mem.ofGlobals_block`, `Mem.ofGlobals_getElem?` | block `k` at program start is global `k` |
| `BlkAt.alloc` (`blkat_alloc`) | a stack block is live, of its size, aligned |

`Mem.Seq` (the invariant of `Triple`) is only the single-thread condition: there is no
address invariant (`Mem.AddrBelow` and `Mem.nextAddr` are gone), so no rule exports an order
between blocks (MM-8). In-place growth (`Mem.growFree`) needs only that the grown range is clear
of the other live blocks.

A result that depends on addresses is therefore not provable as a constant:
`tests/roadmap/architecture-audit/memory-model/Theorems.lean` checks in the kernel that
`addrOfLocal = 4096`, `crossDistance = 9` and "`overAlign` never panics" each fail under some
placement (`addrOfLocal_not_4096`, `crossDistance_not_9`, `overAlign_may_panic`). A kernel
computation of a concrete run (`decide +kernel`) needs a concrete placement; such results are
stated as possibilities (`∃ σ, …`, witnessed by `Placement.fresh`).

## Pointer equality

`==` and `!=` on pointers of every kind compare addresses (`Zig.ptrEqAddr`; `Zig.optPtrEqAddr`
for `?*T`), as LLVM's `icmp` does. Two pointers with different provenance at the same address
are equal (`Proofs/Pointers/Proofs.lean`, `same_address`). Block identity is used only for
liveness and provenance: an access, `free` and `@ptrFromInt`'s provenance recovery
([address-reuse.md](address-reuse.md)).

## Limits

* Out-of-allocation pointer arithmetic (MM-3) is still accepted; LLVM treats it as poison.
* The stack is unbounded (MM-5).
* The fallback address (`alignUp Mem.top align`) is not bounded by 2^64, unlike a placed one; it
  only matters for programs that allocate close to 2^64 bytes.
* `Mem.top` scans every block, so allocation under `Placement.fresh` is linear in the number of
  blocks so far (runtime cost only).
* VC extraction (`vc_gen`) has a pointer `==` contract only for provenance-free pointers
  (`Zig.VC.ptrEqAddr_raw`); comparing pointers into blocks needs a proof by hand.
* A zero-size object may overlap another block in a native layout; the model's `addrFree`
  does not separate them, so `@ptrFromInt` of such an address can be ambiguous (`.unspecified`
  under `.strict` provenance).
