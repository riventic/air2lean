# Tutorial: generic containers

Use the proved specification of a generic std container, `std.ArrayListUnmanaged(u32)`, whose
methods are translated from the Zig std source at the `u32` instance.

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
`Lists.array_list_Aligned_u32_null_append` in [`Proofs/Lists/Gen.lean`](../../Proofs/Lists/Gen.lean),
including the std code that grows the buffer (`ensureTotalCapacityPrecise`, the `@memcpy` and
the free of the old buffer). [`Proofs/Lists/Append.lean`](../../Proofs/Lists/Append.lean)
proves `append_run`: `append` gives `xs ++ [v]`, or `error.OutOfMemory` and the same list.
`alist p ptr cap xs` owns the 24-byte list header at `p` and the buffer at `ptr` with capacity
`cap` whose first items are `xs`.

## Steps

```sh
lake build Proofs.Lists.Append
lake env lean tutorials/generic-containers/Main.lean
```

[`Main.lean`](Main.lean) proves `append_success`: if `append` returns success, the final heap
splits into the frame `hF`, unchanged, and a list `xs ++ [v]` (possibly in a new buffer with a
new capacity). The proof destructures `append_run` and matches its result with the run.

## Exercise

Prove the failure case: a failed `append` reports `error.OutOfMemory` and keeps the old list,
with the same buffer and capacity.

```lean
theorem append_failure ... (run : (array_list_Aligned_u32_null_append p a v).run m = pure (.error e, m')) :
    e = "OutOfMemory" ∧ ∃ hL', m'.heap = hL' ∪ hF ∧ alist p ptr cap xs hL'
```

A solution, with the full hypotheses, is in [`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) keeps the proof of `append_success` but claims `v` is put at
the front (`v :: xs`). Lean must reject it with an application type mismatch:

```sh
lake env lean tutorials/generic-containers/Negative.lean   # must fail
```

## Assumptions and remaining obligations

[`docs/premise-index.md`](../../docs/premise-index.md) derives these premises for `Main.lean`
(definitions in [`docs/premises.md`](../../docs/premises.md)):

- [PRF-01](../../docs/premises.md#prf-01): the legacy 64-bit little-endian reference model.
- [ALC-01](../../docs/premises.md#alc-01), [ALC-02](../../docs/premises.md#alc-02),
  [ALC-03](../../docs/premises.md#alc-03): one modelled allocator; `OutOfMemory` is decided by
  the allocation policy (the theorem holds for every policy); the remap policy.
- [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02),
  [SEM-03](../../docs/premises.md#sem-03): value/safety semantics, block memory, partial
  correctness.
- [SEM-06](../../docs/premises.md#sem-06): block addresses are the environment's placement
  (`docs/address-placement.md`); the result holds for every placement.
- [SEM-05](../../docs/premises.md#sem-05): `Proofs/Lists/Append.lean` imports the P06 cost
  layer (`ZigLean.Sep.Cost`) for `append`'s model allocation count; such a count is a model
  count, not a time or memory measurement.
- [TRU-01](../../docs/premises.md#tru-01), [TRU-02](../../docs/premises.md#tru-02),
  [TRU-03](../../docs/premises.md#tru-03): Lean kernel, the translation of the std source, and
  native lowering.

Remaining obligations: the caller supplies the list `alist p ptr cap xs` with the frame
disjoint from it, a sequential memory (`m.Seq`), and `ptrOk m ptr` for the items pointer (an
empty list's pointer points into a zero-byte block, which no assertion can own). Only the
`u32` instance is proved; another element type is another translated function with its own
proof obligation.
