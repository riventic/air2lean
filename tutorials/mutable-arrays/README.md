# Tutorial: mutable arrays

Prove a property of a function that changes a slice in place, using the separation-logic
specification of the committed translation.

Source ([`examples/slices/slices.zig`](../../examples/slices/slices.zig)):

```zig
pub fn reverse(s: []u32) void {
    if (s.len == 0) return;
    var i: usize = 0;
    var j: usize = s.len - 1;
    while (i < j) : ({ i += 1; j -= 1; }) {
        const t = s[i];
        s[i] = s[j];
        s[j] = t;
    }
}
```

The translation is `Slices.reverse` in [`Proofs/Slices/Gen.lean`](../../Proofs/Slices/Gen.lean).
[`Proofs/Slices/Sep.lean`](../../Proofs/Slices/Sep.lean) proves, with a loop invariant and a
measure (`fsym` walks the loop body):

```lean
theorem reverse_spec (sl : Slice) (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length) :
    FTotalTriple (up (arr sl.ptr vs)) (reverse sl) (fun _ => up (arr sl.ptr vs.reverse))
```

`arr p vs` owns the bytes of the items `vs` at `p` (`up` lifts it to the full-state logic). An
`FTotalTriple P c Q` says: run `c` in any memory that holds `P` beside a frame; the run returns
without a safety error, the frame is unchanged and the new state holds `Q`.

## Steps

```sh
lake build Proofs.Slices.Sep
lake env lean tutorials/mutable-arrays/Main.lean
```

[`Main.lean`](Main.lean) proves `reverse_twice`: reversing a slice twice restores its items. It
chains two `reverse_spec` triples with `FTotalTriple.bind`; the second is instantiated at
`vs.reverse` and rewritten with `List.reverse_reverse`.

## Exercise

Prove that reversing a one-item slice leaves it unchanged:

```lean
theorem reverse_one (sl : Slice) (x : BitVec 32) (hlen : sl.len.toNat = 1) :
    FTotalTriple (up (arr sl.ptr [x])) (reverse sl) (fun _ => up (arr sl.ptr [x]))
```

Hint: `reverse_spec sl [x] hlen` and `simp` (`[x].reverse = [x]`). A solution is in
[`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) keeps the proof of `reverse_twice` but claims the items end
up reversed. Lean must reject it with a type mismatch:

```sh
lake env lean tutorials/mutable-arrays/Negative.lean   # must fail
```

## Assumptions and remaining obligations

[`docs/premise-index.md`](https://github.com/riventic/air2lean/blob/generated/docs/premise-index.md) derives these premises for `Main.lean`
(definitions in [`docs/premises.md`](../../docs/premises.md)):

- [PRF-01](../../docs/premises.md#prf-01): the legacy 64-bit little-endian reference model
  (the committed `Proofs/Slices/Gen.lean` has no profile header).
- [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02): Zig
  value/safety semantics and the byte-level block memory model.
- [SEM-07](../../docs/premises.md#sem-07): block addresses are the environment's placement
  (`docs/address-placement.md`); the result holds for every placement.
- [SEM-03](../../docs/premises.md#sem-03): the loop is a `partial_fixpoint`; the proof walks
  it with `FTotalTriple.loop_measure`, whose measure shows that it ends.
- [SEM-04](../../docs/premises.md#sem-04): `FTotalTriple` is total correctness: the run
  returns an actual result.
- [STK-01](../../docs/premises.md#stk-01): the loop is a `partial_fixpoint` and a stack
  allocation can throw `.stackOverflow`; `reverse_spec`'s total result shows the room.
- [THR-01](../../docs/premises.md#thr-01), [THR-08](../../docs/premises.md#thr-08),
  [ORD-01](../../docs/premises.md#ord-01), [ORD-02](../../docs/premises.md#ord-02),
  [ORD-05](../../docs/premises.md#ord-05), [ORD-06](../../docs/premises.md#ord-06),
  [OSM-01](../../docs/premises.md#osm-01): not used by this sequential proof. `reverse_spec` is
  proved with `fsym`, and the index conservatively assumes every `@[fsym]` rule module
  (`tactic_modules`, `ZigLean.Sep.Full.AutoAll`) was applied, including the concurrent and mmap rules.
- [TRU-01](../../docs/premises.md#tru-01): the Lean kernel and standard axioms.
- [TRU-02](../../docs/premises.md#tru-02), [TRU-03](../../docs/premises.md#tru-03): the
  translation models the analyzed AIR, and the backend preserves it in the native binary.

The source runtime fallback additionally reports these conservative attributions from
reachable runtime declarations and their imports: ALC-01, ALC-02, ALC-03, ALC-04, ALC-05,
ALC-06, ALC-08, ALC-10, DEV-01, ENV-02, EXT-01, EXT-04, EXT-05, EXT-06, MTH-01, ORD-03,
ORD-04, OSK-01, OSM-02, OST-01, OST-03, SEM-05, STD-01, STD-02, STD-03, STD-05, STD-06,
STD-08, STK-02, THR-02, THR-03, THR-04, THR-05, THR-06 and THR-10. Their definitions are
in the [premise catalog](../../docs/premises.md); declaration-level precision requires
separate review of the underlying semantic families.

Remaining obligations for a caller: the slice length must match the owned items
(`hlen`), and the caller must own the items exclusively (`arr sl.ptr vs` in the precondition;
aliasing slices are excluded by the separating conjunction).
