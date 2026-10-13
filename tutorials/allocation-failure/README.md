# Tutorial: allocation failure

Prove that a function handles `error.OutOfMemory` without leaking or panicking, for every
allocator that meets the `std.mem.Allocator` contract.

Source ([`examples/lists/lists.zig`](../../examples/lists/lists.zig)):

```zig
pub fn push(a: Allocator, next: ?*Node, val: u32) !*Node {
    const n = try a.create(Node);
    n.* = .{ .val = val, .next = next };
    return n;
}
```

The translation is `Lists.Open.push` in [`Proofs/Lists/Open.lean`](../../Proofs/Lists/Open.lean)
(Zig 0.17.0), with the `Allocator` parameter as an open interface
([docs/interfaces.md](../../docs/interfaces.md)): `a.create` calls the environment's `alloc`
entry, which can be any allocator. The theorems assume only that it meets the contract
`CAllocSpec`, whose `alloc` may always return `null`, so they cover both outcomes.
[`Proofs/Lists/Alloc.lean`](../../Proofs/Lists/Alloc.lean) proves:

```lean
theorem push_spec (next : Option Ptr) (v : BitVec 32) (hfit : I.fits (16 : BitVec 64).toNat 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ vtR vtp fns.toList) (push ⟨ctx, vtp⟩ next v)
      (fun r => I.own ⋆ (pushed I next v r ⋆ vtR vtp fns.toList))
```

where `pushed I next v (.ok p)` is a new `node I p v next` (its fields and the rest of its
grant), and `pushed I next v (.error e)` is `⟪e = "OutOfMemory"⟫`: the error is `OutOfMemory`
and the caller owns nothing new.

## Steps

```sh
lake build Proofs.Lists.Alloc
lake env lean tutorials/allocation-failure/Main.lean
```

[`Main.lean`](Main.lean) proves `push_failure_keeps_state`: from any memory that holds the
allocator's state and the vtable with any frame, if `push` returns an error, the error is
`OutOfMemory` and the memory after it holds the same resources with the same frame. The proof
applies `push_spec` at the run's depth and memory.

## Exercise

Prove the success case: a successful `push` adds exactly one node, next to what the caller
owned before.

```lean
theorem push_success_adds_node (q : Option Ptr) (v : BitVec 32) (n : Nat) (m m' : Mem)
    (r rF : Res) (hh : Holds m r rF) (hr : (I.own ⋆ vtR vtp fns.toList) r) (hs : m.FSeq) (p : Ptr)
    (run : ((Sched.soloRun n (push ⟨ctx, vtp⟩ q v)).run m).run = some (.ok (.ok p, m'))) :
    ∃ r', Holds m' r' rF ∧ (I.own ⋆ (node I p v q ⋆ vtR vtp fns.toList)) r'
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

[`docs/premise-index.md`](https://github.com/riventic/air2lean/blob/generated/docs/premise-index.md) derives these premises for `Main.lean`
(definitions in [`docs/premises.md`](../../docs/premises.md)):

- [EXT-05](../../docs/premises.md#ext-05): the allocator parameter's entries are the
  environment's implementations; the theorem assumes their contract `CAllocSpec`. The contract
  lets every allocation fail, so the theorem covers every failure pattern of every allocator
  that meets it.
- [ALC-01](../../docs/premises.md#alc-01), [ALC-03](../../docs/premises.md#alc-03): the
  allocator vocabulary of the model (the translation also carries `std`'s `remap` entry).
- [THR-01](../../docs/premises.md#thr-01), [ORD-01](../../docs/premises.md#ord-01),
  [ORD-02](../../docs/premises.md#ord-02), [ORD-06](../../docs/premises.md#ord-06): the
  concurrent semantics in which an open call is read (`ConcM`, read in one thread by `CTriple`).
- [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02),
  [SEM-03](../../docs/premises.md#sem-03): value/safety semantics, block memory, partial
  correctness.
- [SEM-04](../../docs/premises.md#sem-04): the library's total step rules inside the proof.
- [SEM-07](../../docs/premises.md#sem-07): block addresses are the environment's placement
  (`docs/address-placement.md`); the result holds for every placement.
- [STK-01](../../docs/premises.md#stk-01): the native stack holds every call chain.
- [OSM-01](../../docs/premises.md#osm-01): the mapping primitives of the library's allocator
  rules.
- [TRU-01](../../docs/premises.md#tru-01): the Lean kernel and its standard axioms.

Remaining obligations: the initial memory must be sequential (`m.FSeq`, no other threads). The
caller of `push` must propagate the error; this theorem covers `push` alone, not callers
(`tutorials/memory-safety` composes it into a client).
