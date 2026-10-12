#!/usr/bin/env bash
# Encode/decode exactness (docs/architecture-audit/enc-exactness.md, README.md).
#
#   check.sh [--check]            translate each retained export (0.14.1 0.15.2 0.16.0 0.17.0),
#                                 compare with gen/<version>/, build the translation, check the
#                                 kernel proofs of Model.lean and Rows.lean, and compare the model's
#                                 lines with the recorded ReleaseSafe (LLVM) native outputs
#                                 expected/<version>-{x86_64,aarch64}-ReleaseSafe.txt
#   check.sh --native VERSION     build native.zig with a stock Zig VERSION (AIR2LEAN_ZIG_NATIVE)
#                                 for x86_64-linux-musl and aarch64-linux-musl (ReleaseSafe and
#                                 Debug), run them (Docker linux/amd64 and linux/arm64, unless
#                                 AIR2LEAN_X86_64_RUN / AIR2LEAN_AARCH64_RUN is set; empty: the
#                                 host), and compare with expected/VERSION-<arch>-<mode>.txt
#                                 (Debug x86_64 from 0.15.2 is the self-hosted backend, which
#                                 the model does not translate: recorded as evidence only)
#   check.sh --export VERSION DIR write fresh AIR with a patched Zig VERSION (AIR2LEAN_ZIG_AIR)
#
# A model line `unspecified` matches any native value. Needs
# `lake build ZigLean Air2Lean air2lean`; run in the serialized build queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/enc-exactness
versions=(0.14.1 0.15.2 0.16.0 0.17.0)
arches=(x86_64:amd64 aarch64:arm64)

# `model` against `native`: equal lines, except that `unspecified` matches any value.
compare() {
  python3 - "$1" "$2" <<'PY'
import sys
model, native = (open(p).read().splitlines() for p in sys.argv[1:3])
ok = len(model) == len(native)
for m, n in zip(model, native):
    mn, _, mv = m.partition(": ")
    nn, _, nv = n.partition(": ")
    if mn != nn or (mv != "unspecified" and mv != nv):
        print(f"model {m!r} != native {n!r}", file=sys.stderr); ok = False
if not ok:
    sys.exit(f"{sys.argv[1]} does not match {sys.argv[2]}")
PY
}

case "${1:---check}" in
  --export)
    [ "$#" -eq 3 ] || { echo 'usage: check.sh --export VERSION DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a patched Zig with the repository exporter}"
    for name in enc_exactness opaque_bytes; do
      out="$3/$name"
      mkdir -p "$out"
      [ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo "$out must be empty" >&2; exit 1; }
      ZIG_AIR_JSON_DIR="$(cd -- "$out" && pwd)" ZIG_AIR_JSON_FILTER="$name." \
        "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
        -target x86_64-linux -mcpu=baseline "$dir/$name.zig"
    done
    exit ;;
  --native)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --native VERSION' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig of that version}"
    work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-enc-exactness.XXXXXX")
    trap 'rm -rf "$work"' EXIT
    for entry in "${arches[@]}"; do
      IFS=: read -r arch platform <<<"$entry"
      for mode in ReleaseSafe Debug; do
        exe="native-$arch-$mode"
        "$AIR2LEAN_ZIG_NATIVE" build-exe "-O$mode" -target "$arch-linux-musl" \
          -femit-bin="$work/$exe" "$dir/native.zig"
        runner_var="AIR2LEAN_$(tr '[:lower:]' '[:upper:]' <<<"$arch")_RUN"
        if [ -n "${!runner_var+set}" ]; then
          # shellcheck disable=SC2086
          ${!runner_var} "$work/$exe" 2> "$work/$exe.txt"
        else
          docker run --rm --platform "linux/$platform" -v "$work:/w:ro" alpine:3 \
            sh -c "/w/$exe 2>&1" > "$work/$exe.txt"
        fi
        cmp "$dir/expected/$2-$arch-$mode.txt" "$work/$exe.txt" ||
          { echo "native $arch-linux-musl $mode ($2) differs from expected/$2-$arch-$mode.txt" >&2; exit 1; }
        echo "native $arch-linux-musl $mode ($2) matches expected/$2-$arch-$mode.txt"
      done
    done
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check|--native VERSION|--export VERSION DIR]' >&2; exit 2 ;;
esac

translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-enc-exactness.XXXXXX")
trap 'rm -rf "$work"' EXIT
for v in "${versions[@]}"; do
  w="$work/$v"
  mkdir -p "$w/EncExactness"
  "$translator" "$dir/air/$v/enc_exactness" -o "$w/EncExactness/Gen.lean" --namespace EncExactness --prefix enc_exactness.
  cmp "$w/EncExactness/Gen.lean" "$dir/gen/$v/EncExactness.lean"
  lp="$w:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
  LEAN_PATH="$lp" "${lean_cmd[@]}" -R "$w" -o "$w/EncExactness/Gen.olean" "$w/EncExactness/Gen.lean"
  cp "$dir/Model.lean" "$w/"
  LEAN_PATH="$lp" "${lean_cmd[@]}" -R "$w" --run "$w/Model.lean" > "$w/Model.txt" ||
    { cat "$w/Model.txt" >&2; exit 1; }
  # Compiled and audited (axioms, sorry, kernel replay), not only run: it is indexed (F2).
  python3 -B scripts/theorem_universe.py gate "$w/Model.lean" --root "$w" --lean-path "$w" \
    --output-dir "$w/universe" > /dev/null
  # Model-handle bytes: the translator rejects every pointer cast that exposes them.
  if out=$("$translator" "$dir/air/$v/opaque_bytes" -o "$w/Opaque.lean" --namespace Opaque \
      --prefix opaque_bytes. 2>&1); then
    echo "$v: opaque_bytes.zig was translated; its model-handle bytes must be rejected" >&2; exit 1
  fi
  grep -q 'exposing the bytes of a std.mem.Allocator, std.Thread or std.Io' <<<"$out" ||
    { echo "$v: opaque_bytes.zig rejected for another reason:" >&2; echo "$out" >&2; exit 1; }
  # The model's lines against the retained native observations of both targets.
  for entry in "${arches[@]}"; do
    compare "$w/Model.txt" "$dir/expected/$v-${entry%%:*}-ReleaseSafe.txt"
  done
  echo "$v: translation, kernel proofs and $(wc -l < "$w/Model.txt" | tr -d ' ') model lines match x86_64 and aarch64"
done
# One regression row per value kind (exact round trip, foreign bytes), version-independent.
w="$work/rows"; mkdir -p "$w"; cp "$dir/Rows.lean" "$w/"
LEAN_PATH="$w:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}" "${lean_cmd[@]}" "$w/Rows.lean"
python3 -B scripts/theorem_universe.py gate "$w/Rows.lean" --root "$w" --lean-path "$w" \
  --output-dir "$w/universe" > /dev/null
echo 'enc-exactness translation, proof and native-agreement gates passed'
