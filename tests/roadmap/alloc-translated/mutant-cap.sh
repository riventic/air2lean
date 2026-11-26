#!/usr/bin/env bash
# Negative check (M03, the designated mutant of its second acceptance clause): a model whose
# default allocation policy has the old fixed request cap again (`AllocPolicy.maxBytes` defaults
# to `maxAllocBytes`, 1 MiB, in ZigLean/Mem/Basic.lean) must fail the large fixture. The mutated
# model replaces the file in a check tree (scripts/check-tree.py); the compiled runner
# `alloc-translated-large` is built there over the retained Zig 0.17.1 translations, through the
# translated `PageAllocator` and no `std` allocator model. Its `page_large` lines must differ from
# the expected ones, the lines check.sh compares the unmutated runner with: under the cap both
# requests are denied (`page_large ok 0 0`).
#
#   mutant-cap.sh ARCHIVE    ARCHIVE: the float library's archive (scripts/diff.sh --build-only)
#
# Run by check.sh in its native part (the archive needs a stock Zig), under scripts/build-guard.py.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-translated
archive=${1:?usage: mutant-cap.sh ARCHIVE}
model=ZigLean/Mem/Basic.lean
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-translated-cap.XXXXXX")
trap 'rm -rf "$work"' EXIT
sed 's/^  maxBytes : Nat := unboundedAllocBytes$/  maxBytes : Nat := maxAllocBytes/' "$model" > "$work/Basic.lean"
if cmp -s "$model" "$work/Basic.lean"; then
  echo "alloc-translated mutant: the default of AllocPolicy.maxBytes in $model is not the line this mutant changes" >&2
  exit 1
fi
tree=$repo_root/.lake/check-tree/alloc-translated-cap
python3 -B scripts/check-tree.py create "$tree" --replace "$model=$work/Basic.lean"
mkdir -p "$tree/tests/diff/out/libm"
cp "$archive" "$tree/tests/diff/out/libm/air2lean_libm.a"
(cd "$tree" && python3 -B scripts/fixtures.py build alloc-translated-large)
runner=$tree/tests/roadmap/.lake/build/bin/alloc-translated-large
for pair in linux:expected-linux.txt macos:expected.txt; do
  line=$("$runner" "${pair%%:*}")
  if [ "$line" != 'page_large ok 0 0' ] || grep -qxF "$line" "$here/${pair#*:}"; then
    echo "alloc-translated mutant: a capped default policy survives the large fixture (${pair%%:*}: $line)" >&2
    exit 1
  fi
done
echo "alloc-translated mutant: rejected (with the old cap in the default policy the requests above 1 MiB are denied)"
# Q02: the kill of the designated mutant (assurance/mutation-map.json, M03).
python3 -B scripts/mutation_kill_log.py --check "$here/check.sh" "$here/mutant-cap.sh" 'default-policy-capped'
