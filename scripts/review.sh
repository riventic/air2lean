#!/usr/bin/env bash
# Reproduce the focused 1.0 review regressions using an existing patched compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

# This suite spans the review PR stack. A missing dependency is a failure, not a skipped test.
for required in scripts/review-checks.sh tests/review/AllProofs.lean \
    tests/review/Concurrency.lean tests/review/Emitter.lean tests/review/Floats.lean tests/review/Memory.lean \
    tests/review/Parser.lean tests/review/inputs.py tests/review/emitter.sh \
    tests/review/exporter-checks.sh tests/review/exporter.zig; do
  if [ ! -f "$required" ]; then
    echo "review regressions: required file missing: $required" >&2
    exit 1
  fi
done

bash scripts/review-checks.sh
lake build Proofs air2lean
for source in tests/review/AllProofs.lean tests/review/Floats.lean; do
  echo "== $source ==" >&2
  lake env lean "$source"
done
for source in tests/review/Concurrency.lean tests/review/Memory.lean; do
  echo "== $source ==" >&2
  lake env lean --run "$source"
done
# Generators only write source files. Their elaboration happens in the serial emitter driver.
generated=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-review-generated.XXXXXX")
trap 'rm -rf "$generated"' EXIT
lake env lean --run tests/review/Parser.lean "$generated"
python3 tests/review/inputs.py
bash tests/review/emitter.sh "$generated"
bash tests/review/exporter-checks.sh
