# The generic allocator specification (`AllocSpec`)

Status: proof-only modules, not imported by `ZigLean.lean`. Phase P3 of the translated
allocator plan: allocators are translated from their real Zig code and proved from a trusted
base of `posix.mmap`/`munmap`/`mremap` only. `AllocSpec` is the contract between the two
halves: every allocator is proved to satisfy it, and every client of `std.mem.Allocator` is
proved once from it.

| Module | Contents |
|---|---|
| `ZigLean/Sep/AllocSpec/Region.lean` | region permissions and their algebra |
| `ZigLean/Sep/AllocSpec.lean` | `Logic`, `RawVTable`, `AllocInv`, `granted`, `AllocSpec` |
| `ZigLean/Sep/AllocSpec/Wrappers.lean` | the `std.mem.Allocator` wrappers and their contracts |
| `ZigLean/Sep/AllocSpec/Toy.lean` | a bump allocator that satisfies it; negative checks |

CI builds all four (`Generic allocator specification`).

## Statement

**Regions.** `regionIn p A S K a bs` owns exactly the bytes `bs` at `p` inside one writable block
(address `A`, size `S`, kind `K ≠ .constGlobal`), and the address of `p` is a multiple of `a`.
`region p a bs` hides the block. Unlike the whole-block assertions of the legacy model, a
region can be any byte range of a block: a fixed buffer hands out sub-ranges of its buffer,
a page allocator a prefix of a mapping.

**Logics.** `Logic` packages a Hoare logic over `MemM` with its structural rules
(`ofTotal`, `toPartial`, `conseq`, `frame`, `bind`, `ex`, `lift`, `congr`).
`Logic.partial` is `Triple` (a diverging call satisfies every triple), `Logic.total` is
`TotalTriple`. Every result below is stated for an arbitrary `L`.

**The vtable.** `RawVTable` is the semantics of the four `std.mem.Allocator.VTable` entries
(Zig 0.16.0), each taking the context pointer `ctx` (`Allocator.ptr`), the alignment as the
`log2` value `k` of `mem.Alignment` (byte alignment `2 ^ k`) and `ret_addr`:

```lean
structure RawVTable where
  alloc  : Ptr → BitVec 64 → Nat → BitVec 64 → MemM (Option Ptr)            -- ?[*]u8
  resize : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → MemM Bool            -- bool
  remap  : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → MemM (Option Ptr)    -- ?[*]u8
  free   : Ptr → Slice → Nat → BitVec 64 → MemM Unit
```

**The invariant.** `AllocInv` has `own : Assn`, the allocator's state and the memory it has
not handed out, and `tok : Ptr → Nat → Nat → Assn`, its evidence that it issued the `n`-byte
region at `p` with alignment `k`. `granted I p k bs := region p (2 ^ k) bs ∗ I.tok p bs.size k`.
The token is needed because a free (resize, remap) of memory that the allocator did not issue
is illegal in Zig even when the caller owns those bytes. It is an assertion, so it can be a
pure fact (the region lies in this buffer) or own memory (the rest of a page mapping).

**The contract.** `AllocSpec L vt ctx I`:

| entry | precondition | postcondition |
|---|---|---|
| `alloc ctx len k ra`, `0 < len`, `k < 64` | `I.own` | `null`: `I.own`; `p`: `I.own ∗ ∃ bs, ⌜bs.size = len⌝ ∗ granted I p k bs` |
| `resize ctx s k n ra`, `0 < n` | `I.own ∗ granted I s.ptr k bs`, `s.len = bs.size > 0` | `true`: `I.own ∗ ∃ bs', ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗ granted I s.ptr k bs'`; `false`: unchanged |
| `remap ctx s k n ra`, `0 < n` | same | `null`: unchanged; `q`: `I.own ∗ ∃ bs', ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗ granted I q k bs'` |
| `free ctx s k ra` | same | `I.own` |

`keepsPrefix old new` is `new.extract 0 old.size = old.extract 0 new.size`: the common prefix
is kept, new bytes are unspecified. The contents of a fresh allocation are unspecified (the
wrappers make them undefined). `ret_addr` is unconstrained. A free consumes exactly the region
and its token; the allocator may keep the bytes (an arena), reuse them, or give them back to
the OS, which `I.own` hides.

Closure properties: `AllocSpec.toPartial` (a total allocator is a partial one) and
`AllocSpec.congr` (an allocator whose entries have the same runs from every sequential memory
satisfies the same spec; this is how a translated allocator inherits a proof about its
unfolded step semantics).

## The wrappers

`Wrap.*` are the step semantics of the `std.mem.Allocator` wrapper functions over a
`RawVTable`, byte-level (an item type is its size and the log2 of its alignment), following
`lib/std/mem/Allocator.zig` line by line: zero-length requests return the constant
`zeroAllocPtr (2 ^ k)` without a call, `allocBytesWithAlignment` poisons fresh memory with
`@memset(_, undefined)`, `free` poisons before `rawFree`, `destroy` does not, `realloc`
tries `remap`, then allocates, copies the common prefix, poisons and frees.

| theorem | contract |
|---|---|
| `allocBytes_spec`, `allocItems_spec` | `I.own` ⇒ `.ok p`: `I.own ∗ owned I k p (replicate n undef)`; `.error OutOfMemory`: `I.own` |
| `allocSlice_spec` (`alloc`, `alignedAlloc`) | the same, as a slice of `n` items |
| `create_spec` / `destroy_spec` | one item; `destroy` consumes `owned` |
| `free_spec` | `I.own ∗ owned I k s.ptr bs` ⇒ `I.own` |
| `dupe_spec` | `I.own ∗ region src` ⇒ a fresh copy of the source bytes, source unchanged |
| `allocSentinel_spec` | `n + 1` items, undefined but the last, which is the sentinel |
| `realloc_spec` | a slice of `size * n` bytes that keeps the common prefix, or `OutOfMemory` with the old slice unchanged |

Two simplifications, both preconditions of the theorems rather than modelled behaviour: a
sentinel-terminated slice is passed to `free`/`realloc` with its absorbed length (`len + 1`
items, as `mem.absorbSentinel` computes), and `allocSentinel_spec` assumes `n + 1` does not
overflow (Zig panics there in safe builds).

`owned I k p bs` is `emp` for zero bytes and `granted I p k bs` otherwise. Each proof uses
only `AllocSpec L vt ctx I` and the `Logic` rules, so it holds for every allocator in both
logics.

## Sanity instances and negative checks

* `Bump.allocSpec cap ctx buf : AllocSpec Logic.total (Bump.vtable cap) ctx (Bump.inv cap ctx buf)`:
  a bump allocator in the monadic style of generated code (state in memory, `ptrAddr` and
  `alignUp` for alignment, overflow-free capacity checks), with `noResize`/`noRemap` behaviour
  and a leaking `free`. The spec is satisfiable by an allocator that really allocates, and
  every wrapper contract follows for it (the `realloc` example).
* `Static.not_allocSpec`: an allocator that returns the same buffer on every `alloc` (a
  double issue) satisfies `AllocSpec` for no invariant that holds in some memory, even in the
  partial logic: the second grant would overlap the first.
* `trapFree_alloc_none`: if `free` traps, `AllocSpec` forces `alloc` never to succeed: the
  `free` obligation is not vacuous.

## The region library for allocator proofs

`Region.lean` provides what the allocator proofs need beyond the spec:

* split and join: `bytesAt_append`, `regionIn_split`, `regionIn_join`, `regionIn_weaken`;
* the block of a region in a memory: `bytesAt_block`, `bytesAt_meta_eq` (two ranges of one
  block have the same block data) and `region_reveal`; `region_join_of_heap` rejoins a hidden
  granted region with the explicit range after it (a fixed buffer taking its last allocation
  back, a page allocator rejoining a mapping before `munmap`);
* `regionIn_carve`: padding, an aligned region and the rest of a free range (the bump step of
  `FixedBufferAllocator.alloc`);
* `regionIn_of_block`: a whole aligned block (a fresh `mmap` mapping) is a region;
* total triples for the byte operations of the wrappers: `memsetUndef`, `memcpy` between two
  regions, `storeItem`, `memmoveZero`; and `ptrAddr_regionIn` (Toy).

## What the other phases provide

* P1 (translator, `--allocator-model=translated`): the generated `mem.Allocator` wrappers and
  vtable entries as `MemM` functions. To use the wrapper contracts, show that each generated
  wrapper has the same runs as its `Wrap.*` counterpart for `vt := ⟨fun c len k ra => Gen.alloc c len ⟨BitVec.ofNat 6 k⟩ ra, …⟩`
  (the vtable field loads and the indirect calls reduce to `vt.*`), then apply `Logic.congr`.
  `@returnAddress()` is an oracle value: every contract here holds for every `ra`.
* P2 (posix model): `mmap` returns a fresh `.mapped` block as `bytesAt ⟨some b, 0⟩ A S K bs`
  with `A` page-aligned; `regionIn_of_block`, `regionIn_split` and `region_join_of_heap`
  convert between mappings and granted regions (`tok` of a page allocator owns the mapping's
  tail beyond `len`).
* P4 (PageAllocator), FixedBufferAllocator: prove `AllocSpec Logic.total vt ctx I` for the
  translated vtable with an `I` describing the allocator's state; every wrapper contract then
  follows from this file. For the page allocator this is impossible as stated (atomic locations
  and dead blocks are outside the heap, and `granted` hides the mapping's size):
  [alloc-page.md](alloc-page.md).

## Relation to the legacy models it replaces

* `Zig.Allocator` (a unit struct, `ZigLean/Mem/Alloc.lean`) and its `rawAlloc`/`rawFree`
  model one built-in heap; `AllocSpec` is parametric in the allocator, so a custom allocator
  needs no new model.
* `AllocPolicy` (failure indices, oracles, budgets, byte-remap modes) becomes unnecessary for
  translated allocators: failure is the `null` result that the spec always allows, and the
  OS-level failure oracle lives in the `mmap` model only.
* The M04 vtable contracts (`ZigLean/Sep/RawAlloc.lean`, premise ALC-06) need whole `.heap`
  blocks and specific remap policies; `AllocSpec` states the same four entries over byte
  ranges for any allocator, proved rather than assumed.
* `.owned a` blocks and allocator identities (ALC-07) model arenas and fixed buffers by hand;
  with `AllocSpec` a foreign free is a missing token (a permission violation), and arena reset
  invalidation is a consequence of the translated arena's invariant.
