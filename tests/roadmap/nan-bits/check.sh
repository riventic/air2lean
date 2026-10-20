#!/usr/bin/env bash
# NaN bits observed through memory (docs/architecture-audit/nan-bits.md, README.md).
#
#   check.sh [--check]            translate each retained export (0.14.1 0.15.2 0.16.0 0.17.0),
#                                 compare with NanBits/<version>/Gen.lean, check that each
#                                 version's Model.lean is the 0.17.0 one with the version renamed,
#                                 build the library NanBits (tests/roadmap/lakefile.toml: the
#                                 translations and the kernel proofs of the models), audit the
#                                 models' axioms, and compare the lines each model's `main` prints
#                                 with the recorded native outputs expected/<version>-{x86_64,aarch64}.txt
#   check.sh --native VERSION     build native.zig with a stock Zig VERSION (AIR2LEAN_ZIG_NATIVE)
#                                 for x86_64-linux-musl and aarch64-linux-musl (ReleaseSafe and
#                                 Debug), run them (Docker linux/amd64 and linux/arm64, unless
#                                 AIR2LEAN_X86_64_RUN / AIR2LEAN_AARCH64_RUN is set; empty: the
#                                 host), and compare with expected/VERSION-<arch>.txt
#   check.sh --export VERSION DIR write fresh AIR with a patched Zig VERSION (AIR2LEAN_ZIG_AIR)
#
# A model line `unspecified` matches any native value (a NaN's bits). Needs a built translator;
# Lake builds the library with what it imports (scripts/fixtures.py; run it under
# scripts/build-guard.py).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/nan-bits
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
    out="$3/nan_bits"
    mkdir -p "$out"
    [ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo "$out must be empty" >&2; exit 1; }
    ZIG_AIR_JSON_DIR="$(cd -- "$out" && pwd)" ZIG_AIR_JSON_FILTER="nan_bits." \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline "$dir/nan_bits.zig"
    exit ;;
  --native)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --native VERSION' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig of that version}"
    work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-nan-bits.XXXXXX")
    trap 'rm -rf "$work"' EXIT
    for entry in "${arches[@]}"; do
      IFS=: read -r arch platform <<<"$entry"
      for mode in ReleaseSafe Debug; do
        exe="native-$arch-$mode"
        "$AIR2LEAN_ZIG_NATIVE" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} "-O$mode" -target "$arch-linux-musl" \
          -femit-bin="$work/$exe" "$dir/native.zig"
        runner_var="AIR2LEAN_$(tr '[:lower:]' '[:upper:]' <<<"$arch")_RUN"
        if [ -n "${!runner_var+set}" ]; then
          # shellcheck disable=SC2086
          ${!runner_var} "$work/$exe" > "$work/$exe.txt" 2>&1 ||
            { echo "native $arch-linux-musl $mode ($2) failed:" >&2; cat "$work/$exe.txt" >&2; exit 1; }
        else
          docker run --rm --platform "linux/$platform" -v "$work:/w:ro" alpine:3 \
            sh -c "/w/$exe 2>&1" > "$work/$exe.txt"
        fi
        cmp "$dir/expected/$2-$arch.txt" "$work/$exe.txt" ||
          { echo "native $arch-linux-musl $mode ($2) differs from expected/$2-$arch.txt" >&2; exit 1; }
        echo "native $arch-linux-musl $mode ($2) matches expected/$2-$arch.txt"
      done
    done
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check|--native VERSION|--export VERSION DIR]' >&2; exit 2 ;;
esac
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-nan-bits.XXXXXX")
trap 'rm -rf "$work"' EXIT
primary="$dir/NanBits/V0_17_0/Model.lean"
models=() mains=() theorems=()
for v in "${versions[@]}"; do
  t="V${v//./_}"
  # The retained translation is the fresh one, byte for byte (Lake builds the retained file).
  "$translator" "$dir/air/$v/nan_bits" -o "$work/$t.lean" --namespace "NanBits.$t" --prefix nan_bits.
  cmp "$work/$t.lean" "$dir/NanBits/$t/Gen.lean"
  # Every version's model states the same theorems: the 0.17.0 one, the version renamed.
  [ "$t" = V0_17_0 ] || python3 -B scripts/fixtures.py instance "$primary" --subst "V0_17_0=$t"
  models+=("NanBits.$t.Model")
  mains+=("NanBits.$t.Model:NanBits.$t.Model.main")
  theorems+=(--declaration "NanBits.$t.Model.storeLoad_nan" --declaration "NanBits.$t.Model.f32_nan_u32")
done
python3 -B scripts/fixtures.py build NanBits
# Compiled and audited (axioms, sorry, kernel replay), not only run: they are indexed (F2).
python3 -B scripts/fixtures.py audit "${models[@]}" "${theorems[@]}"
# Each model's lines against the retained native observations of both targets.
python3 -B scripts/fixtures.py run "$work/lines" "${mains[@]}"
for v in "${versions[@]}"; do
  lines="$work/lines/NanBits.V${v//./_}.Model.main.txt"
  for entry in "${arches[@]}"; do
    compare "$lines" "$dir/expected/$v-${entry%%:*}.txt"
  done
  echo "$v: translation, kernel proofs and $(wc -l < "$lines" | tr -d ' ') model lines match x86_64 and aarch64"
done
echo 'nan-bits translation, proof and native-agreement gates passed'
