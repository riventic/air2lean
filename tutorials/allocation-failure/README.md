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
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (push ⟨ctx, vtp⟩ next v)
      (fun r => I.own ⋆ (pushed I φ next v r ⋆ vtR vtp fns.toList) ⋆ plain)
```

`plain` is the plain mode (no step meter, no stack budget): `a.create` keeps its result in a
stack local, which needs it ([docs/sep-full-state.md](../../docs/sep-full-state.md), "Plain
mode").

`I.fee φ` is what the allocator charges for a grant (`emp` for most allocators, a fraction of an
arena's epoch token; [docs/sep-full-state.md](../../docs/sep-full-state.md), "The fee of a
grant"). `pushed I φ next v (.ok p)` is a new `node I φ p v next` (its fields and the rest of
its grant, whose token records the fee), and `pushed I φ next v (.error e)` is
`⟪e = "OutOfMemory"⟫ ⋆ I.fee φ`: the error is `OutOfMemory`, the fee is back and the caller owns
nothing new.

## Steps

```sh
lake build Proofs.Lists.Alloc
lake env lean tutorials/allocation-failure/Main.lean
```

[`Main.lean`](Main.lean) proves `push_failure_keeps_state`: from any memory that holds the
allocator's state, a fee and the vtable with any frame, if `push` returns an error, the error is
`OutOfMemory` and the memory after it holds the same resources with the same frame. The proof
applies `push_spec` at the run's depth and memory.

## Exercise

Prove the success case: a successful `push` adds exactly one node, next to what the caller
owned before.

```lean
theorem push_success_adds_node (q : Option Ptr) (v : BitVec 32) (n : Nat) (m m' : Mem)
    (r rF : Res) (hh : Holds m r rF) (hr : (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) r)
    (hs : m.FSeq) (p : Ptr)
    (run : ((Sched.soloRun n (push ⟨ctx, vtp⟩ q v)).run m).run = some (.ok (.ok p, m'))) :
    ∃ r', Holds m' r' rF ∧ (I.own ⋆ (node I φ p v q ⋆ vtR vtp fns.toList) ⋆ plain) r'
```

A solution is in [`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) claims that a failing run is impossible (`False`). The failure
branch of `push_spec` only says the error is `OutOfMemory` (with the fee back), so Lean must
reject it with a type
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
- [ORD-05](../../docs/premises.md#ord-05), [THR-08](../../docs/premises.md#thr-08): the
  pointer-atomic and protocol rules among `fsym`'s rules (`ZigLean.Sep.Full.AutoAll`), which the
  index counts for every proof that `fsym` walks.
- [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02),
  [SEM-03](../../docs/premises.md#sem-03): value/safety semantics, block memory, partial
  correctness.
- [SEM-04](../../docs/premises.md#sem-04): the library's total step rules inside the proof.
- [SEM-07](../../docs/premises.md#sem-07): block addresses are the environment's placement
  (`docs/address-placement.md`); the result holds for every placement.
- [STD-01](../../docs/premises.md#std-01): the hand model of the `std.mem.Allocator` wrappers
  (transitional; `docs/std-models.md` §Retiring the hand models).
- [STK-01](../../docs/premises.md#stk-01): the native stack holds every call chain.
- [OSM-01](../../docs/premises.md#osm-01): the mapping primitives of the library's allocator
  rules.
- [TRU-01](../../docs/premises.md#tru-01): the Lean kernel and its standard axioms.

The source runtime fallback additionally reports these conservative attributions from
reachable runtime declarations and their imports: ALC-02, ALC-04, ALC-05, ALC-06, ALC-08,
ALC-10, DEV-01, ENV-02, EXT-01, EXT-04, EXT-06, MTH-01, ORD-03, ORD-04, OSK-01, OSM-02,
OST-01, OST-03, PRF-04, SEM-05, STD-02, STD-03, STD-05, STD-06, STD-08, STK-02, THR-02,
THR-03, THR-04, THR-05, THR-06 and THR-10. Their definitions are in the
[premise catalog](../../docs/premises.md); declaration-level precision requires separate
review of the underlying semantic families.

Remaining obligations: the initial memory must be sequential (`m.FSeq`, no other threads). The
caller of `push` must propagate the error; this theorem covers `push` alone, not callers
(`tutorials/memory-safety` composes it into a client).
