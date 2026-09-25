#!/usr/bin/env bash
# TEMPORARY (F0 libm spike): does libm.a, linked into a Lean exe, give the bits that @sin etc.
# give inline in a Zig executable?
set -euo pipefail
cd "$(dirname "$0")"
lib_dir=$(zig env | sed -n 's/^ *\.lib_dir = "\([^"]*\)".*/\1/p')
rm -rf crt && cp -R "$lib_dir/compiler_rt" crt
printf 'pub const sin = @import("sin.zig");\npub const exp = @import("exp.zig");\npub const log = @import("log.zig");\n' > crt/air2lean_root.zig
zig build-lib -static -fcompiler-rt -fPIC -OReleaseSafe -mcpu=baseline --name libm \
  --dep crt -Mroot=libm.zig -Mcrt=crt/air2lean_root.zig
nm liblibm.a | grep -E ' [TWtw] _?(sin|sinq|__sinx|air2lean_libm_sin_f64)$' || true
zig build-exe -OReleaseSafe -mcpu=baseline zigside.zig
./zigside > zig.out
lake build
.lake/build/bin/spike zig.out > lean.out
if diff zig.out lean.out > spike.diff; then echo "libm spike: all $(wc -l < zig.out) lines equal"
else echo "libm spike: $(grep -c '^<' spike.diff) of $(wc -l < zig.out) lines differ"; head -12 spike.diff; exit 1; fi
