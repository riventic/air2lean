#!/usr/bin/env bash
# Fast local pre-flight before a push: every staleness check of a committed generated file or
# record that CI gates on, in a few minutes, so that a round does not fail on a file that only
# needed regenerating. It runs no proof, differential test or mutation; CI still runs everything.
#
#   scripts/preflight.sh [--no-translator] [--no-sources]
#
# Checks (each one's own error names the regeneration command):
#   CI matrix, compatibility and pins     ci-matrix.py, compat.py, build-modes.py, perf-budgets.py
#   support and target matrices           support-matrix.py, target-matrix.py --strict
#   premise index and theorem inventory   premises.py, theorem-inventory.py, no-sorry.sh
#   provenance fixture, AIR and trust     provenance-evidence.py, validate-air.py, trust-report.py,
#                                         float-semantics.py, mutation-map.py, model inclusion
#   review ledger (structure only)        release-record.py ledger --allow-unfetched
#   coverage inventories                  coverage.py l14, and coverage.py check per version
#                                         against the pinned pristine source (cached in
#                                         $AIR2LEAN_CACHE as zig-patch/build.sh does; skipped by
#                                         --no-sources)
#   C front-end record                    tests/roadmap/c-frontend/check.sh --light
#   generated modules                     gen-integrity.py check, after `lake build air2lean`
#                                         under scripts/build-guard.py (skipped by --no-translator)
#
# Exit 0: every check passed; 1: a check failed (all are run; failures are listed at the end).
set -uo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root" || exit 2
export PYTHONDONTWRITEBYTECODE=1
translator=1 sources=1
for arg in "$@"; do
  case "$arg" in
    --no-translator) translator=0 ;;
    --no-sources) sources=0 ;;
    *) echo "usage: scripts/preflight.sh [--no-translator] [--no-sources]" >&2; exit 2 ;;
  esac
done

failed=()
check() {
  local label=$1
  shift
  printf '== %s\n' "$label"
  if ! "$@"; then failed+=("$label"); fi
}

check 'CI matrix derived from compatibility.json' python3 scripts/ci-matrix.py check
check 'release compatibility metadata' python3 scripts/compat.py check
check 'build-mode qualification records' python3 -B scripts/build-modes.py check
check 'performance budgets' python3 scripts/perf-budgets.py validate
check 'support matrix' python3 scripts/support-matrix.py check
check 'declared target matrix' python3 scripts/target-matrix.py check --strict
check 'theorem premise index' python3 -B scripts/premises.py check
check 'theorem inventory' python3 -B scripts/theorem-inventory.py check
check 'sorry/admit/native_decide and kernel escape hatches' scripts/no-sorry.sh
check 'provenance fixture' python3 scripts/provenance-evidence.py check
check 'golden AIR export validation' python3 -B scripts/validate-air.py
check 'stage trust report' python3 -B scripts/trust-report.py check
check 'float-semantics labels' python3 scripts/float-semantics.py check
check 'mutation map' python3 -B scripts/mutation-map.py check
check 'model inclusion evidence' python3 -B tests/roadmap/model-inclusion/inclusion.py validate
check 'review ledger (structure)' python3 scripts/release-record.py ledger --allow-unfetched
check 'runtime tag fixtures (L14)' python3 scripts/coverage.py l14 coverage/0.14.1.json coverage/0.15.2.json coverage/0.16.0.json
check 'C front-end coverage record' tests/roadmap/c-frontend/check.sh --light

scratch=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-preflight.XXXXXX") || exit 2
trap 'rm -rf "$scratch"' EXIT

# The pinned pristine compiler source of each version, as zig-patch/build.sh fetches it.
coverage_check() {
  local version=$1 cache=${AIR2LEAN_CACHE:-"$HOME/.cache/air2lean"} url sha256 tarball
  url=$(zig-patch/toml-get.sh "[\"$version\"]" url) && sha256=$(zig-patch/toml-get.sh "[\"$version\"]" sha256) || return 1
  tarball="$cache/zig-$version.tar.xz"
  if [ ! -f "$tarball" ]; then
    local part
    mkdir -p "$cache" && part=$(mktemp "$cache/zig-$version.part.XXXXXX") \
      && curl -fsSL --output "$part" "$url" && mv "$part" "$tarball" || return 1
  fi
  echo "$sha256  $tarball" | shasum -a 256 -c - >/dev/null || return 1
  mkdir "$scratch/$version" && tar -xJf "$tarball" -C "$scratch/$version" --strip-components=1 || return 1
  python3 scripts/coverage.py check --version "$version" --source "$scratch/$version" --os linux \
    --inventory "coverage/$version.json"
}
if [ "$sources" = 1 ]; then
  for version in $(python3 -c 'import json; print(" ".join(v["version"] for v in json.load(open("compatibility.json"))["zig"]["versions"]))'); do
    check "compiler-derived coverage inventory ($version)" coverage_check "$version"
  done
fi

if [ "$translator" = 1 ]; then
  check 'translator build (lake build air2lean)' python3 scripts/build-guard.py \
    --report "$scratch/guard.json" --log "$scratch/lake.log" --timeout 1800 -- lake build air2lean
  check 'generated modules are fresh translations' python3 -B scripts/gen-integrity.py check
fi

if [ "${#failed[@]}" -gt 0 ]; then
  printf '\npreflight: %d check(s) failed:\n' "${#failed[@]}" >&2
  printf '  %s\n' "${failed[@]}" >&2
  exit 1
fi
printf '\npreflight: all checks passed\n'
