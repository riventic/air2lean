# A flag byte other than 0 or 1 in `?T` decodes to `.illegal` (2026-11-26)

Status: open, a maintainer decision. Found while preparing PR #870 (L07, optional items in
representation casts). The core instance is not changed by that PR.

## The fact

`Enc (Option α)` (`ZigLean/Mem/Enc.lean`, `?T` for a `T` that is not a pointer) decodes the flag
byte at the payload's size: 0 is `none`, 1 is `some`, any other defined byte throws `.illegal`,
an undefined byte throws `.unspecified`.

`Error.nativeStops .illegal` is true (`ZigLean/Basic.lean`): a partial-correctness statement may
drop a run that ends in `.illegal`, as it drops a run that does not terminate, because illegal
behaviour carries no promise about the native run. `.unspecified` is not droppable: the native
program goes on with some value, so every statement has to exclude it (audit
soundness-2026-10-14 S4).

Native code does go on for such a flag. The LLVM and the self-hosted x86_64 backend test the
flag byte against 0, so a flag of 2 reads as non-null and the payload bytes are used. The Zig
language reference does not make a flag byte other than 0 or 1 illegal behaviour; it gives `?T`
no in-memory layout at all.

## Failure scenario

1. PR #870, before its fix: `intToU8s` of `tests/roadmap/packed-casts/opt_items.zig`
   (`const a: [2]?u8 = @bitCast(x); return if (a[1]) |v| v else 0x100;`, Zig 0.14.1/0.15.2)
   with `x = 0x02340012`. Item 1 is the bytes `34 02`. The model gave `.illegal`; the native
   program returns a value (`native.zig`, line `opt_intToU8sBadFlag`). A partial-correctness
   statement about `intToU8s x` with any postcondition, also a false one, holds on that input in
   the model, while the native run produces a result the proof never looked at.
2. On main, by the model: every `Zig.load (Option α)` decodes whatever bytes the block holds.
   Bytes written through a pointer of another type (`@ptrCast` of `*[2]u8` to `*?u8`, a byte
   store through `[*]u8`, `@memcpy`/`@memset` over the optional's bytes, a field of a bare union
   read after another field was written) reach the same decode with a flag of 2 and give
   `.illegal`. These paths were derived from the model; no translated example was run for this
   note, so which of them the checker admits today is not established here.

## Options

- **A. `.unspecified` in the core instance.** A flag byte other than 0 or 1 throws
  `.unspecified`. Always in the safe direction: it turns a droppable outcome into one every
  proof must exclude, so no theorem becomes false, but a partial proof that relied on dropping
  such a run must now show the flag is 0 or 1 (it follows wherever the optional was stored by
  the model's own encode). Expected cost, not measured here: `decode (encode v)` never has
  such a flag, so round-trip lemmas should stand; kernel-checked examples that state `.illegal`
  for a bad flag change.
- **B. Keep `.illegal` with a recorded justification**, as for `bool` (`Enc Bool`: "a byte
  other than 0 or 1 is not a `bool`: illegal behaviour"). This needs a source: for `bool` the
  compilers assume the range (LLVM `i1`/range metadata, so the native run is not predictable);
  for the optional flag the compilers emit a plain byte test and the language gives no rule, so
  the justification would be a premise about every backend, with an ID in `docs/premises.md`.

Recommendation: A.

## What PR #870 does

The new path (integer bits to an array of optionals) decodes optional array items, and such an
item's optional payload, with the cast's own dictionary `Zig.Enc.optionRepr`
(`ZigLean/Mem/Repr.lean`): the core instance with a bad flag as `.unspecified`. An optional
anywhere else in such a cast (a field of an `auto` struct item, which is decoded by the struct's
own instance) is rejected. If option A is taken, `Zig.Enc.optionRepr` equals the core instance
and is deleted, with the emitter's `reprOpt` switch and that rejection.
