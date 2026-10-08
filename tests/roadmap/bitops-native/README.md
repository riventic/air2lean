# L02 native differential qualification of the wide bit-operation cases

`tests/roadmap/bitops` proves and tests the bit operations on synthetic and narrow-width
translations. This package qualifies the **wide and odd widths** (u3, u7, u24, u40, u65, u72,
u100, u127, u128, u129, u200, and the signed iN of each) by differential execution on every
supported Zig version and target.

## What is compared

`gen.py` writes three files from one row table (`gen.py --check` rejects stale copies):

* `wide.zig` has one exported function per width and signedness, `ops_<u|i>W(sel, hi, lo, k) u128`.
  `sel` selects `@clz`, `@ctz`, `@popCount`, `<<`, `@shlWithOverflow` (value and overflow
  flag), `>>` (arithmetic for signed), `@byteSwap` (widths divisible by 8) and `@bitReverse`; the
  operand is the low W bits of `hi:lo`; results are zero-extended bit patterns, with `sel + 16`
  returning bits 128 and up (widths 129 and 200).
* `native.zig` calls it over the row table and prints one line per row.
* `Diff.lean.inc` is appended to the translation of the **patched-compiler AIR** of `wide.zig`
  and prints the same rows from the Lean evaluation.

Each width has 13-17 operands (zero, one, maximum, sign boundary and its neighbours, alternating
patterns, half-width masks, pseudo-random patterns). Shift counts are exhaustive up to width 40
and boundary-dense above it. Counts at or above the width are excluded (illegal behavior;
widths that are not powers of two also have representable illegal counts, tested in
`tests/roadmap/bitops`). `wide.zig` disables runtime safety per function, so the shift-count
panic branch (`shiftRhsTooBig`, which the translator does not map) is absent from the AIR; the
legal domain is unaffected. The corpus has 31,366 rows.

`qualify.py run` exports AIR per target (`-OReleaseSafe -target T`), checks the export inventory
(22 functions), translates it, evaluates it in Lean, builds the corpus with **stock** Zig for the
target in Debug, ReleaseSafe, ReleaseFast and ReleaseSmall (static musl on Linux, baseline CPU),
runs it, and compares every line. Any difference, or a short stream, fails the run; the
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

0.14.1 has no macOS patched compiler (`compatibility.json` hosts), so its AIR is exported by the
Linux/arm64 patched compiler for each target; the native 0.14.1 run on macOS uses the stock
aarch64-macos release.

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
