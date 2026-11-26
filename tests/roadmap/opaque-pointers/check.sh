#!/usr/bin/env bash
# Pointers to opaque types (`*anyopaque`, `*T` of a declared `opaque {}`): the checker controls
# (Checker.lean), then the committed compiler exports of every supported version
# (exports.lock.json): air/<version> translates in the default allocator model and
# air-recover/<version> under `--allocator-model translated`, their model runs print
# expected.txt (the native `main`'s transcript plus the `model` lines), and the rejections hold:
# air-recover in the default allocator model, the compiler rejection roots (air-reject/<version>)
# and the changed type tables of negatives.py.
#   check.sh                 the gate above (needs a built translator and `lake`; no compiler)
#   check.sh --export [V..]  scripts/fixture-exports.py verify: a fresh export with the patched
#                            compilers of versions V (default all) equals the committed one
#   check.sh --native ZIG    run opaque_ptrs.zig with a stock Zig on this host and compare its
#                            transcript with expected.txt (without the `model` lines)
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/opaque-pointers
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-opaque-pointers.XXXXXX")
trap 'rm -rf "$work"' EXIT
case "${1:-}" in
  --export)
    shift
    versions=()
    for version in "$@"; do versions+=(--version "$version"); done
    exec python3 -B scripts/fixture-exports.py verify opaque-pointers ${versions[@]+"${versions[@]}"} ;;
  --native)
    zig=${2:?usage: check.sh --native ZIG}
    # shellcheck source=scripts/rosetta.sh
    . scripts/rosetta.sh
    "$zig" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} -OReleaseSafe -fno-error-tracing "$here/opaque_ptrs.zig" \
      -femit-bin="$work/native" --cache-dir "$work/cache" --global-cache-dir "$work/global-cache"
    "$work/native" > "$work/stdout" 2> "$work/transcript.txt"
    [ ! -s "$work/stdout" ] || { echo 'unexpected native stdout' >&2; exit 1; }
    grep -v '^model ' "$here/expected.txt" | diff -u - "$work/transcript.txt"
    echo "opaque pointer native: Zig $("$zig" version), $(wc -l < "$work/transcript.txt" | tr -d ' ') lines match"
    exit 0 ;;
esac
python3 -B scripts/lean-deps.py --build "$here"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
# The committed exports are the recorded compiler outputs (no compiler runs here).
python3 -B scripts/fixture-exports.py check opaque-pointers
"${lean_cmd[@]}" --run "$here/Checker.lean"
rejected() { # rejected WHAT MESSAGE TRANSLATOR-ARGS...: the translation fails with MESSAGE
  local what=$1 message=$2
  shift 2
  if "$translator" "$@" -o "$work/rejected.lean" --namespace Rejected > "$work/reject.log" 2>&1; then
    echo "accepted: $what" >&2; exit 1
  fi
  grep -qF -- "$message" "$work/reject.log" || { echo "wrong rejection ($what): $(cat "$work/reject.log")" >&2; exit 1; }
}
for version in 0.17.1 0.16.0 0.15.2 0.14.1; do
  "$translator" "$here/air/$version" -o "$work/Gen-$version.lean" --namespace OpaquePtrs \
    --prefix opaque_ptrs. --profile abi64-le-v1
  cat "$here/Runner.lean" >> "$work/Gen-$version.lean"
  "${lean_cmd[@]}" --run "$work/Gen-$version.lean" > "$work/lean-$version.txt"
  "$translator" "$here/air-recover/$version" -o "$work/Recover-$version.lean" --namespace OpaquePtrs \
    --prefix opaque_ptrs. --profile abi64-le-v1 --allocator-model translated
  cat "$here/RunnerRecover.lean" >> "$work/Recover-$version.lean"
  "${lean_cmd[@]}" --run "$work/Recover-$version.lean" >> "$work/lean-$version.txt"
  diff -u "$here/expected.txt" "$work/lean-$version.txt"
  # Recovering the typed pointer from the handle needs the translated allocator model.
  rejected "$version: recovery in the default allocator model" \
    'a pointer cast has unresolved or cyclic symbolic storage provenance' \
    "$here/air-recover/$version" --profile abi64-le-v1
  for spec in 'externHandle|`extern` global global_handle: its type can hold' \
      'fromInt|recovering a symbolic error pointer from an integer or opaque value' \
      'globalHandle|global alias has unresolved or cyclic symbolic storage provenance' \
      'setGlobal|global alias has unresolved or cyclic symbolic storage provenance' \
      'getGlobal|global alias has unresolved or cyclic symbolic storage provenance' \
      'eraseError|a pointer cast has unresolved or cyclic symbolic storage provenance'; do
    name=${spec%%|*} expected=${spec#*|}
    mkdir -p "$work/reject-$version-$name"
    cp "$here/air-reject/$version/reject.$name.json" "$work/reject-$version-$name/"
    for model in std translated; do
      rejected "$version: $name ($model)" "$expected" "$work/reject-$version-$name" \
        --profile abi64-le-v1 --allocator-model "$model"
    done
  done
done
# An opaque type of the standard library (std_handles.zig; `Io` is 0.16.0 and later): the handle
# of the hand-modelled `Io.Future` and the type alone, in both allocator models.
for version in 0.17.1 0.16.0; do
  for name in peek pending isNull; do
    mkdir -p "$work/std-$version-$name"
    cp "$here/air-std/$version/std_handles.$name.json" "$here/air-std/$version/std_handles.square.json" \
      "$work/std-$version-$name/"
    for model in std translated; do
      rejected "$version: std handle $name ($model)" \
        "opaque type 'Io.AnyFuture' is declared in the standard library" "$work/std-$version-$name" \
        --profile abi64-le-v1 --allocator-model "$model"
    done
  done
done
python3 -B "$here/negatives.py" "$translator"
echo "opaque pointer gate passed: checker controls, 4 versions x $(wc -l < "$here/expected.txt" | tr -d ' ') model lines (expected.txt), 13 compiler rejections per version, the std handles of 0.17.1 and 0.16.0, and the negatives per version"
