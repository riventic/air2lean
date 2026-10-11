#!/usr/bin/env bash
# Fast local pre-flight before a push: every staleness check of a committed generated file or
# record that CI gates on, in a few minutes, so that a round does not fail on a file that only
# needed regenerating. It runs no proof, differential test or mutation; CI still runs everything.
#
#   scripts/preflight.sh [--no-translator] [--no-sources] [--pr]
#
# scripts/regen.sh regenerates what these checks find stale (`scripts/regen.sh --check` runs this).
# --pr skips the whole-tree generated files that the merge queue regenerates on the merge result
# (scripts/regen.sh --list, scope `tree`). With AIR2LEAN_CAS_DIR set, the translator build and
# the pristine compiler sources come from the shared cache (docs/build-cache.md).
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
translator=1 sources=1 tree=1
for arg in "$@"; do
  case "$arg" in
    --no-translator) translator=0 ;;
    --no-sources) sources=0 ;;
    --pr) tree=0 ;;
    *) echo "usage: scripts/preflight.sh [--no-translator] [--no-sources] [--pr]" >&2; exit 2 ;;
  esac
done

failed=()
check() {
  local label=$1
  shift
  printf '== %s\n' "$label"
  if ! "$@"; then failed+=("$label"); fi
}
# A whole-tree generated file: skipped by --pr (the merge queue regenerates it).
tree_check() {
  if [ "$tree" = 1 ]; then check "$@"; else printf '== %s (skipped: --pr)\n' "$1"; fi
}

check 'CI matrix derived from compatibility.json' python3 scripts/ci-matrix.py check
check 'release compatibility metadata' python3 scripts/compat.py check
check 'build-mode qualification records' python3 -B scripts/build-modes.py check
check 'performance budgets' python3 scripts/perf-budgets.py validate
tree_check 'support matrix' python3 scripts/support-matrix.py check
check 'declared target matrix' python3 scripts/target-matrix.py check --strict
tree_check 'theorem premise index' python3 -B scripts/premises.py check
tree_check 'theorem inventory' python3 -B scripts/theorem-inventory.py check
check 'sorry/admit/native_decide and kernel escape hatches' scripts/no-sorry.sh
tree_check 'provenance fixture' python3 scripts/provenance-evidence.py check
check 'golden AIR export validation' python3 -B scripts/validate-air.py
check 'stage trust report' python3 -B scripts/trust-report.py check
check 'float-semantics labels' python3 scripts/float-semantics.py check
check 'mutation map' python3 -B scripts/mutation-map.py check
check 'model inclusion evidence' python3 -B tests/roadmap/model-inclusion/inclusion.py validate
check 'review ledger (structure)' python3 scripts/release-record.py ledger --allow-unfetched
tree_check 'runtime tag fixtures (L14)' python3 scripts/coverage.py l14 coverage/0.14.1.json coverage/0.15.2.json coverage/0.16.0.json
check 'C front-end coverage record' tests/roadmap/c-frontend/check.sh --light

scratch=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-preflight.XXXXXX") || exit 2
trap 'rm -rf "$scratch"' EXIT

# The pinned pristine compiler source of each version, as zig-patch/build.sh fetches it.
coverage_check() {
  local version=$1 source
  source=$(python3 -B scripts/cas.py src "$version" --scratch "$scratch/$version") || return 1
  python3 scripts/coverage.py check --version "$version" --source "$source" --os linux \
    --inventory "coverage/$version.json"
}
if [ "$sources" = 1 ] && [ "$tree" = 1 ]; then
  for version in $(python3 -c 'import json; print(" ".join(v["version"] for v in json.load(open("compatibility.json"))["zig"]["versions"]))'); do
    check "compiler-derived coverage inventory ($version)" coverage_check "$version"
  done
fi

if [ "$translator" = 1 ]; then
  # `cas.py run`: Lake's shared artifact cache when AIR2LEAN_CAS_DIR is set, else a plain exec.
  check 'translator build (lake build air2lean)' python3 -B scripts/cas.py run -- python3 scripts/build-guard.py \
    --report "$scratch/guard.json" --log "$scratch/lake.log" --timeout 1800 \
    --lock-wait "${AIR2LEAN_LOCK_WAIT:-3600}" -- lake build air2lean
  check 'generated modules are fresh translations' python3 -B scripts/gen-integrity.py check
fi

if [ "${#failed[@]}" -gt 0 ]; then
  printf '\npreflight: %d check(s) failed:\n' "${#failed[@]}" >&2
  printf '  %s\n' "${failed[@]}" >&2
  exit 1
fi
printf '\npreflight: all checks passed\n'
