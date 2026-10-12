# Soundness finding: `@intCast` to a zero-bit signed integer accepted -1

Class: SOUNDNESS (model more permissive than native Zig). Status: fixed (branch
`codex/zero-width-int`). Severity: latent (see "Reachability").

## Finding

`Zig.intCast` computed the target range as `lo = -(2 ^ (m - 1))`, `hi = 2 ^ (m - 1) - 1` with
Nat subtraction. At `m = 0` (`i0`), `m - 1 = 0`, so `lo = -1` and `hi = 0`: the range was `[-1, 0]`
instead of `[0, 0]` (`i0` has the single value 0).

Counterexample (before the fix):

```lean
#eval (match (Zig.intCast true true 0 (BitVec.ofInt 8 (-1))).run with
       | some (.ok _) => "ok" | _ => "err")   -- "ok"; native Zig panics (integer does not fit)
```

The cast "succeeded" and returned `0`, so a proof could assume `@intCast(@as(i8, -1))` to `i0`
is defined and equals the source value, which is false. The same expression sat in `Zig.clamp`
(saturating arithmetic into `i0`: no visible effect, `ofInt 0 _ = 0`), in `Float.toInt`
(`@intFromFloat` of `-1.0` to `i0` returned `0` instead of `.overflow`), in the lemma statements
that restate them (`intCast_range`, `toInt_of_finite`, `toInt_of_toRat`).

## Fix

One shared range definition, `Zig.intLo s n` / `Zig.intHi s n` (`ZigLean/Basic.lean`), for
signed and unsigned types of every width including 0, with `intLo s n = if s ∧ 0 < n then
-(2^(n-1)) else 0`. `Zig.clamp`, `Zig.intCast`, `Float.toInt` and the restating lemmas use it.
(`intHi` needs no guard: `2^(0-1) - 1 = 0` and `2^0 - 1 = 0`.)

Regressions (kernel-checked, `ZigLean/Lemmas.lean`, `ZigLean/Float/Lemmas.lean`), generic over the
width and then the concrete `i0` instances:

- `val_mem_range`, `val_ofInt_of_range`, `intLo_le_intHi`, `val_clamp`: for all `s`, `n`.
- `intCast_val`: for all widths, a successful `@intCast` preserves the mathematical value
  (this fails at `i0` with the old bound: -1 cast to 0).
- `intCast_i0_rejects_neg_one`, `intCast_zero_width_range`, `Float.toInt_i0_rejects_neg_one`.

## Audit of the other width-generic helpers

Checked at `n = 0`: `add/sub/mul` (`BitVec.s*Overflow` are false at width 0 and the only value
is 0, matching native: no overflow); `divTrunc/divFloor/divCeil/divExact/rem/mod` (the divisor
is always 0, so `.divByZero`/`.illegal`, as native); `addSat/subSat/mulSat/shlSat` (through
`clamp`, now `[0, 0]`); `addWithOverflow` & co. (flag 0); `absInt` (`msb` is false);
`remOverflows` (`intMin 0 = 0`, `-1 = 0`, but `b = 0` is rejected first); shifts
(`shiftCountOk` already admits the zero count at width 0); `trunc` (`setWidth`); the
float-to-int and int-to-float paths (`Float.toInt` fixed, `Float.ofInt` uses `toInt`/`toNat`).
No other helper had the `m - 1` truncation. `Proofs/` and `tests/` only use the generic
helpers.

## Reachability

The checker accepts zero-bit integer types (`integerFits` handles `bits = 0`; `Check.lean`
has no rejection of width-0 `intCast`), so the emitter can produce
`Zig.intCast _ _ 0 ...`. Whether Sema ever emits a runtime `intcast` to `i0` (rather than
folding the result to the comptime-known 0 after its safety check) was not established; the
bug is therefore latent, and the model is now correct either way. Not checked per Zig version
beyond the shared translator path (all four versions share `Zig.intCast` and `Check.lean`).
