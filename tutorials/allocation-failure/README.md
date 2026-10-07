# Tutorial: allocation failure

Prove that a function handles `error.OutOfMemory` without leaking or panicking.

Source ([`examples/lists/lists.zig`](../../examples/lists/lists.zig)):

```zig
pub fn push(a: Allocator, next: ?*Node, val: u32) !*Node {
    const n = try a.create(Node);
    n.* = .{ .val = val, .next = next };
    return n;
}
```

The translation is `Lists.push` in [`Proofs/Lists/Gen.lean`](../../Proofs/Lists/Gen.lean). In
the allocator model, any allocation may fail: the allocation policy in the memory decides
(see [allocation policy](../../docs/allocation-policy.md)). Theorems over an arbitrary `Mem`
therefore cover both outcomes. [`Proofs/Lists/Sep.lean`](../../Proofs/Lists/Sep.lean) proves:

```lean
theorem push_spec (a : Allocator) (q : Option Ptr) (v : BitVec 32) :
    Triple emp (push a q v) (pushed v q)
```

where `pushed v q (.ok p)` is a new `node p v q`, and `pushed v q (.error e)` is
`⌜e = "OutOfMemory"⌝`: the error is `OutOfMemory` and the function owns no bytes.

## Steps

```sh
lake build Proofs.Lists.Sep
lake env lean tutorials/allocation-failure/Main.lean
```

[`Main.lean`](Main.lean) proves `push_failure_keeps_heap`: for any initial memory, if `push`
returns an error, the error is `OutOfMemory` and the final heap equals the initial heap. The
proof applies `push_spec` with an empty owned part and the whole initial heap as frame.

## Exercise

Prove the success case: a successful `push` adds exactly one node, disjoint from the old heap.

```lean
theorem push_success_adds_node (a : Allocator) (q : Option Ptr) (v : BitVec 32)
    (m m' : Mem) (hst : m.Seq) (p : Ptr)
    (run : ((push a q v).run m).run = some (.ok (.ok p, m'))) :
    ∃ hN, Heap.Disjoint hN m.heap ∧ m'.heap = hN ∪ m.heap ∧ node p v q hN
```

A solution is in [`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) claims that a failing run is impossible (`False`). The failure
branch of `push_spec` only says the error is `OutOfMemory`, so Lean must reject it with a type
mismatch:

```sh
lake env lean tutorials/allocation-failure/Negative.lean   # must fail
```

## Assumptions and remaining obligations

[`docs/premise-index.md`](../../docs/premise-index.md) derives these premises for `Main.lean`
(definitions in [`docs/premises.md`](../../docs/premises.md)):

- [PRF-01](../../docs/premises.md#prf-01): the legacy 64-bit little-endian reference model.
- [ALC-01](../../docs/premises.md#alc-01): one modelled allocator; each allocation is a fresh
  heap block. Native allocator addresses and reuse are not modelled.
- [ALC-02](../../docs/premises.md#alc-02): `OutOfMemory` is decided by `Mem.allocPolicy`. The
  theorem quantifies over every policy, but the policy is not a resource guarantee of the
  host: a real allocator may fail in other places, which the model also allows.
- [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02),
  [SEM-03](../../docs/premises.md#sem-03): value/safety semantics, block memory, partial
  correctness.
- [TRU-01](../../docs/premises.md#tru-01), [TRU-02](../../docs/premises.md#tru-02),
  [TRU-03](../../docs/premises.md#tru-03): Lean kernel, translation and native lowering.

Remaining obligations: the initial memory must be sequential (`m.Seq`, no other threads). The
caller of `push` must propagate the error; this theorem covers `push` alone, not callers.
