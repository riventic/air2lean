# Proving memory safety: no use after free, no double free, no leak

This tutorial proves three memory-safety properties of translated Zig, end to end, for every
allocator that meets the `std.mem.Allocator` contract, and so for every allocation-failure
pattern that the contract allows:

1. **no use after free, no double free, no invalid free**: the run throws no error but running
   out of stack, in particular never `.illegal`;
2. **no leak**: after the run the caller owns exactly what it owned before (the allocator's
   state, one fee per item and the vtable), on success and on every out-of-memory path, and
   nothing else the program owns changed;
3. **functional result**: on success the list holds the pushed items, in order.

## Steps

```sh
lake build Proofs.Lists.Alloc
lake env lean tutorials/memory-safety/Main.lean       # the client and its three properties
lake env lean tutorials/memory-safety/Solution.lean   # the exercise, solved
lake env lean tutorials/memory-safety/Negative.lean   # must fail
```

Lean exits with no output when every proof of `Main.lean` and `Solution.lean` checks. No file
uses `sorry` or `native_decide`. `#print axioms` on the theorems lists only `propext`,
`Classical.choice` and `Quot.sound`. `python3 scripts/tutorials.py check` runs the `Main`,
`Solution` and `Negative` checks with the other tutorials.

## Exercise

Prove that reversing a list with the generated `reverse` and then freeing it with the
generated `freeAll` leaks nothing: from the list and the allocator's state, the run ends with
the allocator's state and the fee of every node only.

```lean
def reverseThenFree (a : mem_Allocator) (hd : Option Ptr) : ConcM Tgt Unit :=
  ConcM.liftMem (reverse hd) >>= fun r => freeAll a r

theorem reverseThenFree_spec (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt)
    (φ : Frac) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) (hd : Option Ptr)
    (xs : List (BitVec 32)) :
    CTriple (I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList)) (reverseThenFree ⟨ctx, vtp⟩ hd)
      (fun _ => I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList))
```

Hint: compose `Lists.Linked.reverse_thread` (`reverse` as a step of the thread that owns the
list, lifted with `CTriple.liftMem`) and `freeAll_spec`
with `CTriple.bind`. A solution is in [`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) claims that a client that pushes a node and never frees it
ends owning only the allocator's state and the fee. On success, `push_spec`'s post-condition owns
the new node (which holds the fee) besides the state, so Lean must reject the proof with a type
mismatch
(`python3 scripts/tutorials.py check` requires that error in the last theorem).

## The code

[`examples/lists/lists.zig`](../../examples/lists/lists.zig) is translated to
[`Proofs/Lists/Open.lean`](../../Proofs/Lists/Open.lean) (Zig 0.17.0) with its
`std.mem.Allocator` parameter as an open interface ([docs/interfaces.md](../../docs/interfaces.md)):
every call through the allocator reaches the environment, which can be any allocator. The
tutorial uses three of its generated functions unchanged: `push` (`a.create(Node)`, then two
stores), `reverse` and `freeAll` (a loop of `a.destroy(n)`).
[`Proofs/Lists/Alloc.lean`](../../Proofs/Lists/Alloc.lean) proves `push_spec` and `freeAll_spec`
for every allocator whose entries meet `CAllocSpec` (the contract with invariant `I`), and
[`Proofs/Lists/Linked.lean`](../../Proofs/Lists/Linked.lean) proves `reverse_spec` (and
`reverse_thread`, the same in a thread) for nodes with any owner. An allocation takes a fee `I.fee φ` (`emp` for most allocators, a fraction of an
arena's epoch token; [docs/sep-full-state.md](../../docs/sep-full-state.md), "The fee of a
grant"): `push` takes one and keeps it in the node's token, or gives it back with
`error.OutOfMemory`; `freeAll` gives back one per node (`fees I φ n`, `n` fees).

[`Main.lean`](Main.lean) composes them in a Lean client, `buildThenFree`, the Lean form of:

```zig
fn buildThenFree(a: Allocator, xs: []const u32) !void {
    var head: ?*Node = null;
    for (xs) |x| head = push(a, head, x) catch |e| { freeAll(a, head); return e; };
    head = reverse(head);
    freeAll(a, head);
}
```

## The theorems

Each theorem holds for every `ctx`, vtable `vtp` with entries `fns`, invariant `I`, fee `φ` and
environment `e` such that `CAllocSpec (CVTable.env (env e) fns) ctx I` (the allocator meets the
contract) and `I.fits 16 3` (it can serve a 16-byte request). `F` stands for
`fees I φ xs.length`, one fee per item. `push` keeps the result of `a.create` in a stack local,
so the client runs in the plain mode `plain` (no step meter, no stack budget;
[docs/sep-full-state.md](../../docs/sep-full-state.md), "Plain mode").

| Theorem | Statement |
|---|---|
| `build_spec` | `CTriple (I.own ⋆ (F ⋆ vtR vtp fns.toList) ⋆ plain) (build ⟨ctx, vtp⟩ xs) (fun r => I.own ⋆ (built I φ xs r ⋆ vtR …) ⋆ plain)`: `build` returns `list I φ hd xs` (the items of `xs`, in order), or `error.OutOfMemory` and the fees back, nothing new |
| `buildThenFree_spec` | `CTriple (I.own ⋆ (F ⋆ vtR …) ⋆ plain) (buildThenFree ⟨ctx, vtp⟩ xs) (fun r => ⟪Ended r⟫ ⋆ (I.own ⋆ (F ⋆ vtR …) ⋆ plain))`: returns `ok` or `error.OutOfMemory` and owns what it owned before |
| `buildThenFree_memory_safe` | for every depth `n`, memory `m` and frame `rF` with `Holds m r rF`, `(I.own ⋆ (F ⋆ vtR …) ⋆ plain) r` and `m.FSeq`: the run throws only `.stackOverflow`, and a result `v, m'` has `Ended v` and `Holds m' r' rF` with `(I.own ⋆ (F ⋆ vtR …) ⋆ plain) r'` |
| `buildThenFree_no_illegal` | the run is never `some (.error .illegal)` |
| `buildThenFree_no_leak` | a run that returns ends holding `I.own ⋆ (F ⋆ vtR …) ⋆ plain` again, with the same frame `rF` |

## How each property maps to the model

**No use after free, no double free, no invalid free.** The model is described in
[docs/generated-code.md §Memory](../../docs/generated-code.md#memory). Memory is a list of
blocks; every load and store goes through `Mem.access`, which throws `.illegal` on a dead block,
out of bounds or misaligned. A full-state triple (`FTriple`, read in one thread by `CTriple`,
[docs/sep-full-state.md](../../docs/sep-full-state.md)) allows no error but `.stackOverflow`, so
the run never throws `.illegal`. The allocator's own checks are its contract: `free` takes the
grant that `alloc` handed out (`FAllocInv.granted`), so a second free or a free of a pointer that
was never granted has no precondition to meet.

**No leak.** Every byte the client owns is part of its resource: a node is its two fields and
the rest of its grant (`Lists.Alloc.node`), the allocator's state is `I.own`. `buildThenFree_spec`
ends owning `I.own ⋆ (F ⋆ vtR …) ⋆ plain` only, the same as before, so every grant went back to the
allocator (and with it the fee it took). On the out-of-memory path `pushAll` frees the partial
list with the generated `freeAll` before it returns the error; without that free, `build_spec`'s
post-condition for `.error` (`⟪e = "OutOfMemory"⟫` and the fees, nothing new) would not hold. The frame `rF` (everything else
the program owns) is held unchanged by every triple.

**Every allocation-failure pattern.** `CAllocSpec`'s `alloc` may return `null` at every call
(`FAllocInv.allocPost none`), so the theorems hold for every allocator that fails at any of its
calls, or never. Every allocator that meets the contract is covered; the translated
`FixedBufferAllocator`, page allocator and arena prove the contract's entries (`FAllocSpec`,
`docs/alloc-spec.md`), and enter only through it.

**Every address placement.** The theorems hold for every memory with `m.FSeq`, whatever its
placement oracle chose for its blocks' addresses (`docs/address-placement.md`); the
allocator's contract, not fresh addresses, keeps the nodes apart.

**Values.** `list I φ hd xs` (`Lists.Linked.list` with the rest of each node's grant) owns the
chain of nodes from `hd`, with `val` fields `xs`. `build_spec` gives it for the items in order:
`pushAll` gives them reversed, and the generated `reverse` turns them around.

## Assumptions and remaining obligations

The theorems of `Main.lean` hold in the model under the premises of
[docs/premises.md](../../docs/premises.md). The per-theorem list is in
[docs/premise-index.md](https://github.com/riventic/air2lean/blob/generated/docs/premise-index.md#tutorialsmemory-safetymainlean)
(`python3 scripts/premises.py explain MemorySafety.buildThenFree_memory_safe`):

* [EXT-05](../../docs/premises.md#ext-05): the allocator parameter's entries are the
  environment's implementations (`Ext`); the theorems assume their contract `CAllocSpec`.
* [ALC-01](../../docs/premises.md#alc-01), [ALC-03](../../docs/premises.md#alc-03): the
  allocator vocabulary of the model (the translation also carries `std`'s `remap` entry).
* [THR-01](../../docs/premises.md#thr-01), [ORD-01](../../docs/premises.md#ord-01),
  [ORD-02](../../docs/premises.md#ord-02), [ORD-06](../../docs/premises.md#ord-06): the
  concurrent semantics in which an open call is read (`ConcM`, read in one thread by `CTriple`).
* [ORD-05](../../docs/premises.md#ord-05), [THR-08](../../docs/premises.md#thr-08): the
  pointer-atomic and protocol rules among `fsym`'s rules (`ZigLean.Sep.Full.AutoAll`), which the
  index counts for every proof that `fsym` walks.
* [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02): safety
  checks are `Zig.Error`s, and memory is the byte-level block model. A dead access is
  `.illegal`.
* [SEM-03](../../docs/premises.md#sem-03), [SEM-04](../../docs/premises.md#sem-04): loops are
  `partial_fixpoint`s; the client's statements are partial correctness (`CTriple`), the
  library's total rules are used inside.
* [SEM-07](../../docs/premises.md#sem-07): block addresses are the environment's placement;
  the theorems hold for every placement.
* [STK-01](../../docs/premises.md#stk-01): the native stack holds every call chain.
* [OSM-01](../../docs/premises.md#osm-01): the mapping primitives of the library's allocator
  rules.
* [TRU-01](../../docs/premises.md#tru-01): the Lean kernel and its standard axioms.

The hypothesis `m.FSeq` says that one thread runs and the memory is well formed. It says nothing
about addresses, which the placement chooses.

## Limits

* **The client is Lean, not translated Zig.** `pushAll`, `build` and `buildThenFree` are
  handwritten Lean that calls generated functions. `push`, `reverse` and `freeAll` are
  translated Zig, and so are their loops and allocator calls. `lists.zig`'s own build-then-free
  function, `listSum` (with `defer freeAll`), is not proved here.
* **Per function, compositional.** Each generated function has its own spec. The client is
  proved from those specs with the frame rule, not by unfolding the whole program.
* **Partial correctness.** The allocator contract is a `CTriple`, so a client of an arbitrary
  allocator gets no termination guarantee from it; `reverse` alone is total
  (`Lists.Linked.reverse_total`).
* **Contract, not native allocator.** "No leak" is ownership: every grant returned. What the
  allocator does with returned bytes (reuse, metadata, fragmentation) is the allocator's own
  proof.
* **Single-threaded.** `CTriple` reads the run in one thread; concurrent clients use the
  schedule-quantified proofs of [docs/proofs.md](../../docs/proofs.md#proofs-over-all-schedules).
* **Supported versions.** The proofs are about the committed 0.17.0 translation
  `Proofs/Lists/Open.lean`; `tests/roadmap/interfaces` translates the same functions for 0.16.0,
  0.15.2 and 0.14.1. Only code in the [supported subset](../../README.md#scope) translates.
* **Refuted clients.** [`Controls.lean`](Controls.lean) still shows, for the legacy `std`
  translation (`Proofs/Lists/Gen.lean`) and its model allocator, that a double free and a read
  after free throw `.illegal` and that a client without the free leaks. It moves to the
  translated `PageAllocator` (a freed node's page is unmapped, so both bugs are `.illegal` there
  too) once that allocator is an environment of `Proofs/Lists/Open.lean` meeting `CAllocSpec`.
* **Trust base.** The kernel checks the proofs about the generated Lean. The step to compiled
  Zig trusts the exporter, the translator and the `ZigLean` semantics
  ([What a proof covers](../../README.md#what-a-proof-covers)).
