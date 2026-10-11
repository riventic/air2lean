# aarch64-linux: floatops and floatconv are outside the float model

`scripts/diff.sh` compares native Zig with the committed translation of each example. That
translation follows the float rules of one target (`docs/floats.md` section Targets): the CI
reference x86_64-linux, or aarch64-macos for the translation `scripts/check.sh` makes on that
host (its `Gen-darwin.lean` goldens and `unspecified.Darwin-arm64.txt` pins). The translator has
no aarch64-linux profile, so a run on aarch64-linux compares aarch64 hardware and soft-float
results with the x86_64 rules. For `floatops` and `floatconv` that is 586 typed mismatches per
run (identical in ReleaseSafe and Debug, ReleaseFast and ReleaseSmall):

* `floatconv.f80ToF64`, 63: `f80` pseudo-denormal and unnormal encodings. Input
  `["0x00010000000000000001"]`: Zig `{"ok":"0x0000000000000000"}`, model `{"ok":"nan"}`.
* `floatops.op80`, 500: operations on invalid `f80` encodings, for example
  `[17,"0x4dab0aaefda4eedf67d0","0xfeb579e7cc3e67092c09","0x00000000000000000000"]`: Zig returns the
  first operand, the model `nan`.
* `floatops.op64`, 23: fused operations on subnormal operands, for example
  `[4,"0x0000000000000001","0x3ff0000000000000","0x3ff8000000000000"]`.

Reproduce on an aarch64-linux host with a stock Zig 0.16.0 and a built tree:

    AIR2LEAN_EXAMPLES="floatops floatconv" AIR2LEAN_DIFF_OPTIMIZE=ReleaseSafe AIR2LEAN_DIFF_BACKEND=llvm \
      AIR2LEAN_DIFF_REPORT=/tmp/float.json scripts/diff.sh

The runs in `assurance/build-mode-runs/*--aarch64-linux--*` therefore leave both examples out
(`excluded_examples`). The aarch64 float rules are checked on aarch64-macos only.
