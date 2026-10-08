# L02 native differential qualification of the wide bit-operation cases

`tests/roadmap/bitops` proves and tests the bit operations on synthetic and narrow-width
translations. This package qualifies the **wide and odd widths** (u3, u7, u24, u40, u65, u72,
u100, u127, u128, u129, u200, and the signed iN of each) by differential execution on every
supported Zig version and target.

## What is compared

`gen.py` writes four files from one row table (`gen.py --check` rejects stale copies):

* `wide.zig` has one exported function per width and signedness, `ops_<u|i>W(sel, hi, lo, k) u128`.
  `sel` selects `@clz`, `@ctz`, `@popCount`, `<<`, `@shlWithOverflow` (value and overflow
  flag), `>>` (arithmetic for signed), `@byteSwap` (widths divisible by 8) and `@bitReverse`; the
  operand is the low W bits of `hi:lo`; results are zero-extended bit patterns, with `sel + 16`
  returning bits 128 and up (widths 129 and 200).
* `native.zig` calls it over the row table and prints one line per row.
* `panics.zig` calls it with shift counts at or above the width (see below), with a panic
  handler that prints the row and the check that tripped, then resumes with the next row.
* `Diff.lean.inc` is appended to the translation of the **patched-compiler AIR** of `wide.zig`
  and prints the same rows from the Lean evaluation.

Each width has 13-17 operands (zero, one, maximum, sign boundary and its neighbours, alternating
patterns, half-width masks, pseudo-random patterns). Shift counts are exhaustive up to width 40
and boundary-dense above it. The corpus has 31,366 rows.

`wide.zig` keeps runtime safety on. For a width that is not a power of two the count type
(`u<log2 W>`) also holds counts W..2^log2-1; Zig 0.14.1, 0.15.2 and 0.16.0 guard `<<` and `>>`
with the `shiftRhsTooBig` safety check, which the translator maps to `Zig.Error.overflow` like
the `shlOverflow`/`shrOverflow` checks of the same shift path (`docs/generated-code.md`
§Panics, `scripts/panic-policy.tsv`). Those counts are illegal behavior in ReleaseFast and
ReleaseSmall, so they are not in the main corpus; the **panic lane** (`panics.zig`, Debug and
ReleaseSafe only) has 408 rows: for each non-power-of-two width and signedness, `<<` and `>>`
(and their high halves above 128 bits) on two operands with W - 1 (a legal control) and up to
four illegal counts (W, W + 1, the midpoint and the maximum). Each of the 312 illegal rows must
panic natively with `shiftRhsTooBig` exactly where the Lean evaluation throws `.overflow`, and
each control row must agree in value. `@shlWithOverflow` has no count check (an oversized count
stays unchecked illegal behavior, `.illegal` in the model) and is not in the lane.
`shift-panic/test_cli.py` is the translator regression for the mapping on committed
patched-compiler AIR of `shift-panic/shift.zig` for all three versions.

`qualify.py run` exports AIR per target (`-OReleaseSafe -target T`), checks the export inventory
(22 functions), translates it, evaluates it in Lean, builds the corpus with **stock** Zig for the
target in Debug, ReleaseSafe, ReleaseFast and ReleaseSmall (static musl on Linux, baseline CPU),
runs it, and compares every line; in Debug and ReleaseSafe it does the same for the panic lane.
Any difference, a short stream, or a missing panic fails the run; the
evidence file records rows, mismatches (with the first five) and SHA-256 digests of the AIR
set, the Lean stream, and each native stream.

## Evidence

`evidence/<version>.json` is committed for 0.14.1, 0.15.2 and 0.16.0, with the three targets
`x86_64-linux`, `aarch64-linux` and `aarch64-macos`. `qualify.py check` (offline, in CI) fails
unless every version, target and mode is present for the current corpus with 0 mismatches and the
full row count.

| Lane | Executed where |
| --- | --- |
| aarch64-macos | natively on the macOS arm64 host |
| aarch64-linux | locally `docker run --platform linux/arm64` (native on an arm64 host); CI `ubuntu-24.04-arm` natively, and qemu-user in the x86_64 job |
| x86_64-linux | locally `docker run --platform linux/amd64` (emulated on an arm64 host); CI natively on `ubuntu-24.04` |

The committed 0.14.1 evidence was exported with a locally built macOS patched 0.14.1 compiler
(`compatibility.json` lists no macOS host for 0.14.1, so CI's macOS job covers 0.15.2 and 0.16.0
only); a Linux patched compiler can be given instead (`docker:<platform>:<install dir>`). The native
0.14.1 run on macOS uses the stock aarch64-macos release.

## Reproducing

```sh
python3 tests/roadmap/bitops-native/qualify.py run --version 0.16.0 \
  --zig-air "$PWD/zig-air-0.16.0/bin/zig" --zig /path/to/stock/zig \
  --exec x86_64-linux=docker:linux/amd64,aarch64-linux=docker:linux/arm64,aarch64-macos=host \
  --evidence tests/roadmap/bitops-native/evidence/0.16.0.json
```

Executors are `host`, `docker:<platform>` (image `alpine:3.21`) and `qemu:<binary>`. A patched
Linux compiler can be given as `docker:<platform>:<install dir>`. Run the whole command under
`scripts/build-guard.py`, which serializes Zig, Lake and Docker work.
`qualify.py native` runs only the native side and compares it with the Lean digest recorded in
the committed evidence, for runners without Lean (the CI arm64 job). `qualify.py verify` checks a
fresh run against the committed digests.
