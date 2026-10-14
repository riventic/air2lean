# Tutorial: generic containers

Use the proved specification of a generic std container, `std.ArrayListUnmanaged(u32)`, whose
methods are translated from the Zig std source at the `u32` instance, for every allocator that
meets the allocator contract.

Source ([`examples/lists/lists.zig`](../../examples/lists/lists.zig)):

```zig
pub fn evens(a: Allocator, xs: []const u32) ![]u32 {
    var list: std.ArrayListUnmanaged(u32) = .empty;
    errdefer list.deinit(a);
    for (xs) |x| {
        if (x % 2 == 0) try list.append(a, x);
    }
    return list.toOwnedSlice(a);
}
```

Each generic instance is a separate translated function: `list.append` becomes
`Lists.Open.array_list_Aligned_u32_null_append` in
[`Proofs/Lists/Open.lean`](../../Proofs/Lists/Open.lean), including the std code that grows the
buffer (`ensureTotalCapacityPrecise`: `remap`, else a new buffer, the `@memcpy` and the free of
the old buffer). Every call through the `std.mem.Allocator` parameter reaches the environment's
allocator (`Ext`), so [`Proofs/Lists/Append.lean`](../../Proofs/Lists/Append.lean) proves
`append_spec` from the allocator contract `CAllocSpec` alone: `append` takes a fee `I.fee φ`
(what the allocator charges for a grant, `emp` for most allocators;
[docs/sep-full-state.md](../../docs/sep-full-state.md), "The fee of a grant"), gives `xs ++ [v]`,
or `error.OutOfMemory` and the same list, and gives the fee back, for every allocator that meets
the contract. `alist I φ p xs` owns the 32-byte list header at `p` and the buffer, a grant of the
allocator with invariant `I` for the fee `φ` whose first items are `xs` (or, for `.empty`, no
bytes and the unspent fee).

## Steps

```sh
lake build Proofs.Lists.Append
lake env lean tutorials/generic-containers/Main.lean
```

[`Main.lean`](Main.lean) proves `append_success`: if `append` returns success, the list holds
`xs ++ [v]` (possibly in a new buffer with a new capacity). It is `append_spec` with a weaker
postcondition (`CTriple.post`), one case per result.

## Exercise

Prove the failure case: a failed `append` reports `error.OutOfMemory` and keeps the old list.

```lean
theorem append_failure ... :
    CTriple (I.own ⋆ (I.fee φ ⋆ (alist I φ p xs ⋆ vtR vtp fns.toList)))
      (array_list_Aligned_u32_null_append p ⟨ctx, vtp⟩ v)
      (fun r => I.own ⋆ (I.fee φ ⋆ ((FAssn.ex fun ys =>
        ⟪∀ err, r = .error err → err = "OutOfMemory" ∧ ys = xs⟫ ⋆ alist I φ p ys) ⋆
        vtR vtp fns.toList)))
```

A solution, with the full hypotheses, is in [`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) keeps the proof of `append_success` but claims `v` is put at
the front (`v :: xs`). Lean must reject it with a type mismatch:

```sh
lake env lean tutorials/generic-containers/Negative.lean   # must fail
```

## Assumptions and remaining obligations

The theorems of `Main.lean` hold in the model under the premises of
[docs/premises.md](../../docs/premises.md). The per-theorem list is in
[docs/premise-index.md](https://github.com/riventic/air2lean/blob/generated/docs/premise-index.md#tutorialsgeneric-containersmainlean)
(`python3 scripts/premises.py explain GenericContainers.append_success`):

* [EXT-05](../../docs/premises.md#ext-05): the allocator parameter's entries are the
  environment's implementations (`Ext`); the theorems assume their contract `CAllocSpec`.
* [ALC-01](../../docs/premises.md#alc-01), [ALC-03](../../docs/premises.md#alc-03): the
  allocator vocabulary of the model (`remap` included).
* [THR-01](../../docs/premises.md#thr-01), [ORD-01](../../docs/premises.md#ord-01),
  [ORD-02](../../docs/premises.md#ord-02), [ORD-06](../../docs/premises.md#ord-06): the
  concurrent semantics in which an open call is read (`ConcM`, read in one thread by `CTriple`).
* [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02): safety
  checks are `Zig.Error`s, and memory is the byte-level block model.
* [SEM-03](../../docs/premises.md#sem-03), [SEM-04](../../docs/premises.md#sem-04): partial
  correctness (`CTriple`), the library's total rules inside.
* [SEM-07](../../docs/premises.md#sem-07): block addresses are the environment's placement;
  the theorems hold for every placement (the `@memcpy` alias check reads the addresses of two
  disjoint grants).
* [STK-01](../../docs/premises.md#stk-01): the native stack holds every call chain.
* [OSM-01](../../docs/premises.md#osm-01): the mapping primitives of the library's allocator
  rules.
* [TRU-01](../../docs/premises.md#tru-01): the Lean kernel and its standard axioms.

Remaining obligations: the caller supplies the list `alist I φ p xs`, the allocator's state
`I.own`, a fee `I.fee φ`, its vtable `vtR vtp fns.toList`, the contract of the environment's entries at that
vtable, and the room the grown buffer's request needs of the contract (`I.fits`). Only the `u32`
instance is proved; another element type is another translated function with its own proof
obligation. The proofs are about the committed 0.17.0 translation `Proofs/Lists/Open.lean`.
