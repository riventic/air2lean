#!/usr/bin/env bash
# A02 probes (docs/research/A02.md): allowlisted and candidate instructions run natively, and the
# backend asymmetry for inline asm, compared with the recorded observations.
#
#   check.sh [ZIG]   ZIG is a stock Zig 0.17.0 (default: `scripts/cas.py host-zig 0.17.0`).
#
# x86_64-linux runs in `docker run --platform linux/amd64` (Rosetta on an aarch64 Mac); the
# aarch64 probe runs on an aarch64 host (skipped elsewhere). Not part of any proof.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
dir=$repo_root/tests/roadmap/asm-semantics
zig=${1:-$(python3 "$repo_root/scripts/cas.py" host-zig 0.17.0)}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

"$zig" build-exe "$dir/probe_x86_64.zig" -target x86_64-linux-musl -mcpu=x86_64_v2 -OReleaseSafe \
  -femit-bin="$out/probe_x86_64"
docker run --rm --platform linux/amd64 -v "$out":/w:ro alpine:3 /w/probe_x86_64 2>&1 \
  | diff - "$dir/expected_x86_64.txt"
echo "x86_64-linux probe matches expected_x86_64.txt"

# The self-hosted x86_64 backend has its own encoder: a feature-gated instruction that LLVM
# assembles for any CPU is "emit MIR failed ... (Zig compiler bug)" at the baseline CPU
# (docs/upstream/05-stage2-x86_64-asm-popcnt-lzcnt.md). The same translation unit means two
# different assemblers: an instruction table keys on the decoded instruction, not the template.
for fn in lzcnt popcnt; do
  src=$out/t_$fn.zig
  sed '/^pub fn main/,$d' "$dir/probe_x86_64.zig" > "$src"
  printf 'var input: u64 = 5;\npub fn main() void {\n    _ = %s(input);\n}\n' "$fn" >> "$src"
  "$zig" build-exe "$src" -target x86_64-linux-musl -fllvm -femit-bin="$out/llvm_$fn" 2> /dev/null
  if "$zig" build-exe "$src" -target x86_64-linux-musl -fno-llvm -femit-bin="$out/self_$fn" \
      2> "$out/err_$fn"; then
    echo "unexpected: self-hosted backend assembled $fn at the baseline CPU" >&2; exit 1
  fi
  grep -q "no encoding found for: none $fn" "$out/err_$fn"
  echo "$fn at baseline: -fllvm assembles it, -fno-llvm rejects it (no encoding)"
done

if [ "$(uname -m)" = arm64 ] || [ "$(uname -m)" = aarch64 ]; then
  "$zig" build-exe "$dir/probe_aarch64.zig" -OReleaseSafe -femit-bin="$out/probe_aarch64"
  "$out/probe_aarch64" 2>&1 | diff - "$dir/expected_aarch64.txt"
  echo "aarch64 probe matches expected_aarch64.txt"
else
  echo "aarch64 probe skipped (not an aarch64 host)"
fi
