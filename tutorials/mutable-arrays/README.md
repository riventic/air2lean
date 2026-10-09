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
[`Proofs/Slices/Sep.lean`](../../Proofs/Slices/Sep.lean) proves, with a loop invariant:

```lean
theorem reverse_spec (sl : Slice) (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length) :
    Triple (arr sl.ptr vs) (reverse sl) (fun _ => arr sl.ptr vs.reverse)
```

`arr p vs` owns the bytes of the items `vs` at `p`. A `Triple P c Q` says: run `c` in any
memory whose heap splits into a part satisfying `P` and a frame; if the run finishes, it raised
no safety error, the frame is unchanged and the new part satisfies `Q`.

## Steps

```sh
lake build Proofs.Slices.Sep
lake env lean tutorials/mutable-arrays/Main.lean
```

[`Main.lean`](Main.lean) proves `reverse_twice`: reversing a slice twice restores its items. It
chains two `reverse_spec` triples with `Triple.bind`; the second is instantiated at
`vs.reverse` and rewritten with `List.reverse_reverse`.

## Exercise

Prove that reversing a one-item slice leaves it unchanged:

```lean
theorem reverse_one (sl : Slice) (x : BitVec 32) (hlen : sl.len.toNat = 1) :
    Triple (arr sl.ptr [x]) (reverse sl) (fun _ => arr sl.ptr [x])
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

[`docs/premise-index.md`](../../docs/premise-index.md) derives these premises for `Main.lean`
(definitions in [`docs/premises.md`](../../docs/premises.md)):

- [PRF-01](../../docs/premises.md#prf-01): the legacy 64-bit little-endian reference model
  (the committed `Proofs/Slices/Gen.lean` has no profile header).
- [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02): Zig
  value/safety semantics and the byte-level block memory model.
- [SEM-06](../../docs/premises.md#sem-06): block addresses are the environment's placement
  (`docs/address-placement.md`); the result holds for every placement.
- [SEM-03](../../docs/premises.md#sem-03): `Triple` is partial correctness. The theorem says
  nothing about runs that do not finish; it does not prove termination.
- [TRU-01](../../docs/premises.md#tru-01): the Lean kernel and standard axioms.
- [TRU-02](../../docs/premises.md#tru-02), [TRU-03](../../docs/premises.md#tru-03): the
  translation models the analyzed AIR, and the backend preserves it in the native binary.

Remaining obligations for a caller: the slice length must match the owned items
(`hlen`), and the caller must own the items exclusively (`arr sl.ptr vs` in the precondition;
aliasing slices are excluded by the separating conjunction).
