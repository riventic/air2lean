# Tutorial: first proof (pure arithmetic)

[Getting started](../../docs/getting-started.md) walks through this tutorial: the Zig source
`tardiness`, its translation in [`Proofs/Basic/Gen.lean`](../../Proofs/Basic/Gen.lean) and the
proved specification `tardiness_spec`.

## Steps

```sh
lake build Proofs.Basic.Proofs
lake env lean tutorials/first-proof/Main.lean
```

[`Main.lean`](Main.lean) proves `on_time_zero`: an on-time job has zero tardiness.

## Exercise

Add `exactly_on_time` (a job finishing exactly at its due time) by applying `on_time_zero`.
A solution is in [`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) changes the conclusion to `pure 1`; Lean must reject it:

```sh
lake env lean tutorials/first-proof/Negative.lean   # must fail
```

## Assumptions and remaining obligations

[`docs/premise-index.md`](../../docs/premise-index.md) derives these premises for `Main.lean`
(definitions in [`docs/premises.md`](../../docs/premises.md)):

- [PRF-01](../../docs/premises.md#prf-01): the legacy 64-bit little-endian reference model.
- [SEM-01](../../docs/premises.md#sem-01): Zig value and safety semantics (the checked
  subtraction).
- [TRU-01](../../docs/premises.md#tru-01), [TRU-02](../../docs/premises.md#tru-02),
  [TRU-03](../../docs/premises.md#tru-03): Lean kernel, translation and native lowering.

No remaining obligations beyond the hypothesis `onTime`: the theorem covers all 32-bit inputs
that satisfy it, and `tardiness` has no loops or memory.
