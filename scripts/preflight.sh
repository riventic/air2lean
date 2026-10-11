#!/usr/bin/env bash
# Fast local pre-flight before a push: every staleness check of a committed generated file or
# record that CI gates on, in a few minutes, so that a round does not fail on a file that only
# needed regenerating. It runs no proof, differential test or mutation; CI still runs everything.
#
#   scripts/preflight.sh [--no-translator] [--no-sources] [--no-materialize] [--pr]
#
# scripts/regen.sh regenerates what these checks find stale (`scripts/regen.sh --check` runs this).
# First it materializes the whole-tree generated files (assurance/generated.json; not committed,
# docs/ci.md#whole-tree-generated-files): `scripts/generated.py materialize` regenerates the
# coverage inventories (pinned pristine compiler sources, scripts/cas.py) and the premise index,
# and fetches the provenance fixtures from the `generated` branch when it is reachable (CI
# regenerates and strictly checks them on the PR's tree; --pr skips that fetch).
# --no-materialize uses the files already in the checkout (CI installs its own); --no-sources
# regenerates only the premise index. With AIR2LEAN_CAS_DIR set, the translator build and the
# pristine compiler sources come from the shared cache (docs/build-cache.md).
#
# Checks (each one's own error names the regeneration command):
#   CI matrix, compatibility and pins     ci-matrix.py, ci-reuse.py check-workflow, compat.py,
#                                         build-modes.py, perf-budgets.py
#   support and target matrices           support-matrix.py, target-matrix.py --strict
#   premise index and theorem inventory   premises.py, theorem-inventory.py, no-sorry.sh
#   AIR and trust                         validate-air.py, trust-report.py,
#                                         float-semantics.py, mutation-map.py, model inclusion
#   review ledger (structure only)        release-record.py ledger --allow-unfetched
#   coverage inventories                  coverage.py l14 over the regenerated inventories
#   C front-end record                    tests/roadmap/c-frontend/check.sh --light
#   generated modules                     gen-integrity.py check, after `lake build air2lean`
#                                         under scripts/build-guard.py (skipped by --no-translator)
#
# Exit 0: every check passed; 1: a check failed (all are run; failures are listed at the end).
set -uo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root" || exit 2
export PYTHONDONTWRITEBYTECODE=1
translator=1 sources=1 materialize=1 heavy=fetch
for arg in "$@"; do
  case "$arg" in
    --no-translator) translator=0 ;;
    --no-sources) sources=0 ;;
    --no-materialize) materialize=0 ;;
    --pr) heavy=skip ;;
    *) echo "usage: scripts/preflight.sh [--no-translator] [--no-sources] [--no-materialize] [--pr]" >&2; exit 2 ;;
  esac
done

failed=()
check() {
  local label=$1
  shift
  printf '== %s\n' "$label"
  if ! "$@"; then failed+=("$label"); fi
}

if [ "$materialize" = 1 ]; then
  if [ "$sources" = 1 ]; then
    check 'whole-tree generated files (materialize)' python3 -B scripts/generated.py materialize --heavy "$heavy"
  else
    check 'premise index (regenerate)' python3 -B scripts/generated.py regen --group premise-index
  fi
fi
check 'CI matrix derived from compatibility.json' python3 scripts/ci-matrix.py check
check 'CI parts declared and guarded for reuse' python3 scripts/ci-reuse.py check-workflow
check 'release compatibility metadata' python3 scripts/compat.py check
check 'build-mode qualification records' python3 -B scripts/build-modes.py check
check 'performance budgets' python3 scripts/perf-budgets.py validate
check 'support matrix' python3 scripts/support-matrix.py check
check 'declared target matrix' python3 scripts/target-matrix.py check --strict
check 'theorem premise index' python3 -B scripts/premises.py check
check 'theorem inventory' python3 -B scripts/theorem-inventory.py check
check 'sorry/admit/native_decide and kernel escape hatches' scripts/no-sorry.sh
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
