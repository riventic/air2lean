# A shift-amount check in one scope makes every shift of that count total (2026-11-26)

Class: SOUNDNESS. Status: **fixed** (option 2 below; see "Fix"). Lane `checker-queue`; found
while reading `Air2Lean/Emit.lean` for the pointer-alignment rule of PR #914, confirmed with the
translator of main `1847099ab` (plus PR #910, which leaves `Emit.lean` alone) on Zig 0.17.1,
0.16.0 and 0.14.1 (x86_64-linux, ReleaseSafe). The sections up to "Options" describe the
translator before the fix.

## Fix

`FCtx.shiftCountGuarded` is decided per shift instruction. Sema's check is a block whose only
instruction branches on `count < width` and whose false branch only calls `shiftRhsTooBig`. It
guards a shift in two places of the shift's own instruction list, the two shapes Sema emits on
0.14.1–0.17.1:

- the check block comes before the shift (`<<`): the shift runs only when the check passed;
- the shift comes first and the check block is the next instruction, with only the comparison
  of this amount between (`>>`): the out-of-range result is unused when the handler runs.

Every other shift is `Zig.shlChk`/`Zig.shrChk`. A check in another scope, on another branch, of
another amount, or later with other instructions between does not count. No committed
translation changes (`scripts/gen-integrity.py check`). `tests/roadmap/illegal-behavior/
shiftguard.zig` holds the counterexample below and its variants, exported by every supported
version; `ShiftCases.lean` runs each translation.

## The fact

A shift of an integer whose width is not a power of two is illegal behaviour when the amount
reaches the width (`docs/illegal-behavior.md` row 14). The translation is `Zig.shlChk`/`shrChk`
(`.illegal` for such an amount) unless Sema's safety check guards the amount; then it is the
total `Zig.shl`/`Zig.shr`, since Sema may emit the shift before its check.

`FCtx.shiftCountGuarded` (`Air2Lean/Emit.lean`) decides "guarded" for the whole function: the
function calls the `shiftRhsTooBig` handler somewhere, and some instruction compares this amount
`< width`. It does not ask whether that check is on the path of this shift.

## Counterexample

```zig
pub fn mixed(x: u24, c: u5, flag: bool) u24 {
    if (flag) {
        @setRuntimeSafety(false);
        return x << c;
    }
    return x << c;
}
```

Accepted by main in both allocator models. The translation (0.17.1; the same lines on 0.16.0 and
0.14.1):

```lean
      if p2 then (do
        let i5 ← pure (Zig.shl p0 p1)
        …
      else (do
        …                              -- `c < 24`, else `shiftRhsTooBig`
        let i14 ← pure (Zig.shl p0 p1)
```

`mixed x 24 true` is illegal behaviour natively (the first shift has no check; LLVM's `shl` by
the width or more is poison), and a value in the model. With the safe shift removed the same
function translates to `Zig.shlChk p0 p1`, as it must: the second, unrelated shift is what
makes the first one total.

The same holds for `>>`, and for two shifts of one amount whenever the checked one is not on
every path to the unchecked one.

## Options

1. **Always the checked op for a width that is not a power of two.** Sound without any analysis.
   Where Sema emits the shift before its check, the model then says `.illegal` for an amount the
   native program answers with a panic: a conservative over-approximation (CLAUDE.md, "Fail
   closed"), to be documented in row 14. Every committed translation with such a shift changes,
   and a proof that such a function panics becomes a proof that it is illegal or needs the
   amount bound as a precondition.
2. **Tie the check to the shift.** "Guarded" only when the comparison and the shift are in the
   same straight-line body and nothing between them leaves it, with the handler call in the
   comparison's false branch. Keeps today's translations of safe code; needs the exact shapes
   Sema emits per version (check before the shift in the 0.14.1–0.17.1 exports above; the code
   comment says it may also follow).
3. **An exporter fact**, as for `for_len` (`unchecked_ib`): the patched compiler records which
   shifts Sema checked. Exact, but a schema change and a re-export of every fixture.

Not decided here. Option 1 is the one rule without a heuristic; option 2 keeps the goldens.

## Related

PR #914 (pointer casts to a stricter alignment in a `@setRuntimeSafety(false)` scope) is the
same family: a qualified ReleaseSafe build still has scopes without Sema's checks, so a rule
that relies on "Sema checked it" must find that check on the path, or check itself.
