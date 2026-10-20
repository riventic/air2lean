#!/usr/bin/env bash
# Encode/decode exactness (docs/architecture-audit/enc-exactness.md, README.md).
#
#   check.sh [--check]            translate each retained export (0.14.1 0.15.2 0.16.0 0.17.0) of
#                                 enc_exactness.zig and opaque_bytes.zig, compare with
#                                 EncExactness/<version>/{Gen,Opaque}.lean, check that each
#                                 version's Model.lean is the 0.17.0 one with the version renamed,
#                                 build the library EncExactness (tests/roadmap/lakefile.toml: the
#                                 translations, the kernel proofs of the models and of
#                                 EncExactness/Rows.lean), audit their axioms, and compare each
#                                 model's lines with the recorded ReleaseSafe (LLVM) native outputs
#                                 expected/<version>-{x86_64,aarch64}-ReleaseSafe.txt
#   check.sh --native VERSION     build native.zig with a stock Zig VERSION (AIR2LEAN_ZIG_NATIVE)
#                                 for x86_64-linux-musl and aarch64-linux-musl (ReleaseSafe and
#                                 Debug), run them (Docker linux/amd64 and linux/arm64, unless
#                                 AIR2LEAN_X86_64_RUN / AIR2LEAN_AARCH64_RUN is set; empty: the
#                                 host), and compare with expected/VERSION-<arch>-<mode>.txt
#                                 (Debug x86_64 from 0.15.2 is the self-hosted backend; the
#                                 exports are LLVM, so those lines are the native evidence for
#                                 `Dialect.intExtOrder?` on that backend)
#   check.sh --export VERSION DIR write fresh AIR with a patched Zig VERSION (AIR2LEAN_ZIG_AIR)
#
# A model line `unspecified` matches any native value. Needs a built translator; Lake builds the
# library with what it imports (scripts/fixtures.py; run it under scripts/build-guard.py).
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
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-enc-exactness.XXXXXX")
trap 'rm -rf "$work"' EXIT
primary="$dir/EncExactness/V0_17_0/Model.lean"
modules=(EncExactness.Rows) mains=() theorems=()
for v in "${versions[@]}"; do
  t="V${v//./_}"
  w="$work/$v"
  mkdir -p "$w"
  # The retained translations are the fresh ones, byte for byte (Lake builds the retained files).
  "$translator" "$dir/air/$v/enc_exactness" -o "$w/Gen.lean" --namespace "EncExactness.$t" --prefix enc_exactness.
  cmp "$w/Gen.lean" "$dir/EncExactness/$t/Gen.lean"
  # Model-handle bytes (docs/architecture-audit/model-handle-bytes.md): translated, read as no value.
  "$translator" "$dir/air/$v/opaque_bytes" -o "$w/Opaque.lean" \
    --namespace "EncExactness.$t.Opaque" --prefix opaque_bytes.
  cmp "$w/Opaque.lean" "$dir/EncExactness/$t/Opaque.lean"
  # Every version's model states the same theorems: the 0.17.0 one, the version renamed.
  [ "$t" = V0_17_0 ] || python3 -B scripts/fixtures.py instance "$primary" --subst "V0_17_0=$t"
  modules+=("EncExactness.$t.Model")
  mains+=("EncExactness.$t.Model:EncExactness.$t.Model.main")
  theorems+=(--declaration "EncExactness.$t.Model.i24RoundTrip_exact"
             --declaration "EncExactness.$t.Model.allocatorWord_unspecified")
done
# The library: the translations, the models and the version-independent regression rows
# (EncExactness/Rows.lean: one row per value kind, exact round trip and foreign bytes).
python3 -B scripts/fixtures.py build EncExactness
# Compiled and audited (axioms, sorry, kernel replay), not only run: they are indexed (F2).
python3 -B scripts/fixtures.py audit "${modules[@]}" "${theorems[@]}" \
  --declaration EncRows.row_f32_exact --declaration EncRows.row_f80_padding
python3 -B scripts/fixtures.py run "$work/lines" "${mains[@]}"
for v in "${versions[@]}"; do
  w="$work/$v"
  lines="$work/lines/EncExactness.V${v//./_}.Model.main.txt"
  # The model's lines against the retained native observations of both targets.
  for entry in "${arches[@]}"; do
    compare "$lines" "$dir/expected/$v-${entry%%:*}-ReleaseSafe.txt"
  done
  echo "$v: translation, kernel proofs and $(wc -l < "$lines" | tr -d ' ') model lines match x86_64 and aarch64"
  # The same AIR under a profile whose backend has no known padding encoding (`Dialect.intPadding`
  # `unknown`): a legacy profile (no backend) and a backend other than LLVM and self-hosted
  # x86_64. Both reject the integers with padding bits in memory instead of guessing an encoding.
  for relabel in legacy foreign; do
    python3 - "$dir/air/$v/enc_exactness" "$w/$relabel" "$relabel" <<'PY'
import json, pathlib, sys
source, out, relabel = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3]
out.mkdir()
for path in source.glob("*.json"):
    doc = json.loads(path.read_text())
    if relabel == "legacy":
        del doc["profile"]
        doc["schema"] = 11
    else:
        doc["profile"]["backend"] = "stage2_aarch64"
    (out / path.name).write_text(json.dumps(doc))
PY
    args=(--profile legacy-abi64-le)
    [ "$relabel" = legacy ] || args=(--allow-unqualified-build-mode)
    if "$translator" "$w/$relabel" -o "$w/$relabel.lean" --namespace EncExactness \
        --prefix enc_exactness. "${args[@]}" 2> "$w/$relabel.err"; then
      echo "$v: the $relabel profile translated integers with padding bits" >&2; exit 1
    fi
    grep -q 'an integer with padding bits in memory' "$w/$relabel.err" ||
      { cat "$w/$relabel.err" >&2; exit 1; }
  done
  echo "$v: a legacy profile and an unknown backend reject integers with padding bits in memory"
done
echo 'enc-exactness translation, proof and native-agreement gates passed'
