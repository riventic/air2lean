# Error-code widths (`--error-limit`, L10)

Zig stores errors as `u<error_set_bits>`, where the width is `log2(--error-limit) + 1` and
16 is the default. The model and translator take the width from the profile
([profiles.md §Error-code width](../../../docs/profiles.md#error-code-width---error-limit)).
This case checks four widths:

| Directory | `--error-limit` | Bits | Code bytes | `E!u8` | Evidence |
| --- | --- | --- | --- | --- | --- |
| `air/bits16` | 65534 (default) | 16 | 2 | 4 bytes, code first | Qualified: hand-written fixture plus the existing native gate ([error-storage](../error-storage/README.md)) |
| `air/bits8` | 255 | 8 | 1 | 2 bytes, payload first | Model only |
| `air/bits10` | 1000 | 10 | 2 | 4 bytes | Model only |
| `air/bits17` | 100000 | 17 | 4 | 8 bytes | Model only |

The fixtures are hand-written, not exported. `make-fixtures.py` writes them from
`error_width.zig`'s shape using Zig 0.16's layout rules (`Zcu.errorSetBits`, `intByteSize`,
`intAlignment` and the error-union `abiSize`). The same seven functions are written for each
width: storing and loading `E`, `?E`, `E!u8` and `E!u64`; pointer-form `try`;
`errunion_payload_ptr_set`; and `is_err_ptr`. No non-default width has a compiler export or a
native observation, so those widths are model-qualified only.

`check.sh` runs these steps:

1. Checks that the committed fixtures are current (`make-fixtures.py check`).
2. Translates each width and compares the output byte-for-byte with `expected/ErrorWidth<N>.lean`,
   then elaborates it.
3. Checks that the 16-bit output uses the original 2-byte operations (no `…W 16`) and that the
   other widths use `…W <bits>`.
4. Runs `Runtime.lean`, which executes every generated function with each width's own
   dictionaries. Errors, `null`, success payloads and the zero code written by
   `errunion_payload_ptr_set` all survive. A foreign name and a narrower code do not reload
   as members.
5. Runs `negatives.py`, which requires rejection of width 0, width 33, a profile/layout
   disagreement in either direction, a domain wider than the width (`--error-limit 1`) and a
   program that mixes widths.

The universal statements (store/load, wrap/unwrap, code slices, integer/error casts and
out-of-range codes, for every width from 1 to 32 bits) are in `ZigLean/Mem/ErrWidthLemmas.lean`.

```sh
lake build ZigLean ZigLean.Mem.ErrWidthLemmas Air2Lean air2lean
bash tests/roadmap/error-width/check.sh
```

`AIR2LEAN_ERROR_WIDTH_UPDATE=1` rewrites `expected/` after a deliberate emitter change.
Integer/error casts remain rejected by the translator. Their semantics are stated over an
explicit compilation numbering (`ErrorTable`), which AIR does not export.
