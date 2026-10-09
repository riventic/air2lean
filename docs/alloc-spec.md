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
| `ZigLean/Sep/AllocSpec/Wrap.lean` | the step semantics `Wrap.*` of the `std.mem.Allocator` wrappers |
| `ZigLean/Sep/AllocSpec/Wrappers.lean` | the wrappers' contracts |
| `ZigLean/Sep/AllocSpec/Ops.lean` | triples for `@returnAddress`, `@intFromPtr`, pointer `<=`, read-only and explicit-block `pts`, coverage |
| `ZigLean/Sep/AllocSpec/Norm.lean` | normalizing generated code (`MM σ` bodies) to `MemM` programs |
| `ZigLean/Sep/AllocSpec/Dispatch.lean` | the vtable dispatch of translated wrappers and `dispatch_allocSpec` |
| `ZigLean/Sep/AllocSpec/Toy.lean` | a bump allocator that satisfies it; negative checks |

CI builds all of them (`Generic allocator specification`). The translated
`FixedBufferAllocator` instance, the wrapper bridge and a proved client are in
`tests/roadmap/alloc-fba` (`Translated FixedBufferAllocator against AllocSpec`).

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
not handed out; `tok : Ptr → Nat → Nat → Nat → Nat → BlockKind → Assn`, its evidence `tok p n k
A S K` that it issued the `n`-byte region at `p` with alignment `k` from the block with address
`A`, size `S` and kind `K`; and `fits : Nat → Nat → Prop` (default: every request), the requests
within its arithmetic range. `granted I p k bs := ∃ A S K, regionIn p A S K (2 ^ k) bs ∗
I.tok p bs.size k A S K`. The token is needed because a free (resize, remap) of memory that the
allocator did not issue is illegal in Zig even when the caller owns those bytes. It is an
assertion, so it can be a pure fact (the region lies in this buffer) or own memory (the rest of a
page mapping); it sees the region's block so that it can pin which block a free releases (a page
allocator unmaps the whole mapping: obstruction O2 of the PageAllocator work).

**The contract.** `AllocSpec L vt ctx I`:

| entry | precondition | postcondition |
|---|---|---|
| `alloc ctx len k ra`, `0 < len`, `k < 64`, `I.fits len k` | `I.own` | `null`: `I.own`; `p`: `I.own ∗ ∃ bs, ⌜bs.size = len⌝ ∗ granted I p k bs` |
| `resize ctx s k n ra`, `0 < n`, `I.fits n k` | `I.own ∗ granted I s.ptr k bs`, `s.len = bs.size > 0` | `true`: `I.own ∗ ∃ bs', ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗ granted I s.ptr k bs'`; `false`: unchanged |
| `remap ctx s k n ra`, `0 < n`, `I.fits n k` | same | `null`: unchanged; `q`: `I.own ∗ ∃ bs', ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗ granted I q k bs'` |
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
`RawVTable`, byte-level (an item type is its size and the log2 of its alignment). They follow
the code that the compiler emits for `lib/std/mem/Allocator.zig`, which is the ground truth:
`tests/roadmap/alloc-fba/AllocFba/Bridge.lean` proves each generated wrapper equal to its
`Wrap.*`.

* Zero-length requests return the constant `zeroPtr (2 ^ k) = ⟨none, 2^64 - 2^k⟩` without a call
  (the translator's integer pointer constant `⟨none, addr⟩` is exactly this).
* `@returnAddress()` is read where the source reads it: first in `alloc`, `alignedAlloc`,
  `create`, `allocSentinel` and `realloc`, after the `@memset` in `free`, not at all for a
  zero-sized `create`/`destroy` or an empty `free`.
* `allocBytesWithAlignment` poisons fresh memory with `@memset(_, undefined)` and then checks
  the `@alignCast` of the result (`alignCast`) when the alignment is above 1.
* `free` poisons before `rawFree`, `destroy` does not; `free` of a sentinel-terminated slice
  absorbs the sentinel with an overflow-checked `len + 1` (`freeSentinel`).
* `dupe` and the copying path of `realloc` check the `@memcpy`: the lengths agree and the two
  address ranges do not overlap (two `ptrLe`, `copyChecked`).
* `allocSentinel` computes `n + 1` with an overflow check, stores the sentinel and reads it back
  when it slices `ptr[0..n :sentinel]`.

| theorem | contract |
|---|---|
| `allocBytes_spec`, `allocItems_spec`, `allocAdvanced_spec` | `I.own` ⇒ `.ok p`: `I.own ∗ owned I k p (replicate n undef)`; `.error OutOfMemory`: `I.own` |
| `allocSlice_spec` (`alloc`, `alignedAlloc`) | the same, as a slice of `n` items |
| `create_spec` / `destroy_spec` | one item; `destroy` consumes `owned` |
| `freeBytes_spec`, `free_spec`, `freeSentinel_spec` | `I.own ∗ owned I k s.ptr bs` ⇒ `I.own` |
| `copyChecked_spec` | the checked `@memcpy` between two regions with disjoint address ranges |
| `dupe_spec` | `I.own ∗ regionIn src` ⇒ a fresh copy of the (nonempty) source bytes, source unchanged |
| `allocSentinel_spec` | `n + 1` items, undefined but the last, which is the sentinel |
| `reallocAdvanced_spec`, `realloc_spec` | a slice of `size * n` bytes that keeps the common prefix, or `OutOfMemory` with the old slice unchanged |

Premises beyond `AllocSpec`, each a check in the generated code: `Wrap.Fits I n k` for every
request that reaches the allocator; for `realloc`'s copying path `GrantSep I k` (two grants have
disjoint address ranges: provable for an allocator whose token fixes the block, as the
`FixedBufferAllocator`'s does); for `dupe` `SrcSep` (the source's address range is disjoint from
every grant). The memory model does not give address disjointness of two live blocks (`Mem.Seq`
says nothing about addresses), so across blocks it is a placement fact that the client states.

`owned I k p bs` is `emp` for zero bytes and `granted I p k bs` otherwise. Each proof uses only
`AllocSpec L vt ctx I` and the `Logic` rules, so it holds for every allocator in both logics.

## Translated allocators: dispatch and the FixedBufferAllocator

A translated wrapper loads the function pointer from the `VTable` constant and calls it if it is
one of the program's allocator functions (`.illegal` otherwise). `dispatch impl fns vtp` is that
`RawVTable`; `dispatch_allocSpec : AllocSpec L impl ctx I → AllocSpec L (dispatch impl fns vtp)
ctx (I.withVTable vtp fns)` adds the read-only vtable (`vtR`) to the invariant.

`tests/roadmap/alloc-fba` proves `FBA.allocSpec : AllocSpec Logic.total impl ctx (FBA.inv ctx B)`
for the translated `std.heap.FixedBufferAllocator` (Zig 0.16.0), for every struct and buffer:
alignment padding (`alignPointerOffset` on the 64-bit address read from the block), out of
memory, the last allocation shrinking, growing and being given back, a non-last allocation
shrinking in place and leaking on free. Findings that shaped the specification:

* `alloc` computes `end_index + adjust_off + n` and `resize` computes `new_len - len + end_index`
  with overflow checks: a large request panics. Hence `AllocInv.fits`
  (`FBA.fits n k := cap + 2^k + n ≤ 2^64`).
* `alloc` with an alignment above 1 evaluates `@intFromPtr(buffer.ptr + end_index)` also when
  every buffer byte is lent out. The model's `ptrAddr` needs the block to exist in the memory,
  and an invariant that owns no byte of the block cannot say so; the invariant keeps one byte of
  the buffer's block outside the buffer (`pin`). A total `ptrAddr` or persistent block metadata
  (the core gap of obstruction O1) would remove it. The allocator has no atomics (O3) and reads
  no dead block.
* `reset` makes every buffer byte free again. Without ghost state, its specification
  (`reset_spec`) asks that the caller's heap has every buffer byte (`Covers`); a caller that
  still holds a grant would see its bytes reused.

`AllocFba/Client.lean` proves a client (alloc, write, realloc, an allocation that does not fit,
free of the last allocation, reset, a fresh allocation) from these contracts only; `mutant.sh`
shows that an `alloc` that does not advance `end_index` fails the proof.

## Sanity instances and negative checks

* `Bump.allocSpec cap ctx buf : AllocSpec Logic.total (Bump.vtable cap) ctx (Bump.inv cap ctx buf)`:
  a bump allocator in the monadic style of generated code (state in memory, `ptrAddr` and
  `alignUp` for alignment, overflow-free capacity checks), with `noResize`/`noRemap` behaviour
  and a leaking `free`. The spec is satisfiable by an allocator that really allocates, and
  every wrapper contract follows for it (the `alloc` example).
* `Static.not_allocSpec`: an allocator that returns the same buffer on every `alloc` (a
  double issue) satisfies `AllocSpec` for no invariant that holds in some memory and admits a
  one-byte request (`I.fits 1 0`), even in the partial logic: the second grant would overlap the
  first.
* `trapFree_alloc_none`: if `free` traps, `AllocSpec` forces `alloc` never to succeed (for a
  request within `fits`): the `free` obligation is not vacuous.

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
  vtable entries as `MemM` functions. The generated wrappers are equal to `Wrap.*` over
  `dispatch impl fns vtp` with `impl := ⟨fun c len k ra => Gen.alloc c len ⟨BitVec.ofNat 6 k⟩ ra, …⟩`
  (`tests/roadmap/alloc-fba/AllocFba/Bridge.lean`, normalized with `Norm.lean`).
  `@returnAddress()` is an oracle value: every contract here holds for every `ra`.
* P2 (posix model): `mmap` returns a fresh `.mapped` block as `bytesAt ⟨some b, 0⟩ A S K bs`
  with `A` page-aligned; `regionIn_of_block`, `regionIn_split` and `region_join_of_heap`
  convert between mappings and granted regions (`tok` of a page allocator owns the mapping's
  tail beyond `len`).
* P4 (PageAllocator), FixedBufferAllocator (done, `tests/roadmap/alloc-fba`): prove
  `AllocSpec Logic.total vt ctx I` for the translated vtable with an `I` describing the
  allocator's state; every wrapper contract then follows. For the page allocator this is
  impossible as stated (atomic locations and dead blocks are outside the heap, and `granted`
  hides the mapping's size): [alloc-page.md](alloc-page.md).
* Full-state restatement: `FAllocSpec` (`ZigLean/Sep/Full/AllocSpec.lean`,
  [sep-full-state.md](sep-full-state.md)) has the same entries and conditions over full-state
  assertions. `FAllocSpec.ofTotal` lifts a total `AllocSpec` of a vtable whose entries are `Tame`
  (the FixedBufferAllocator: `FBA.fallocSpec`). The page allocator's `free`, `resize` and `remap`
  are proved against it; its `alloc` is blocked by O4 ([alloc-page.md](alloc-page.md)). The
  wrapper contracts are still stated over `AllocSpec`.

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
