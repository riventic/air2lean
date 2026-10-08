#!/usr/bin/env bash
# C front-end coverage (docs/c-frontend.md).
#   --light            record check: committed record.json matches the corpus, its summary and
#                      the generated tables in docs/c-frontend.md; generator invariants. No tools.
#   --heavy OUT_DIR [FILE...]
#                      every stage for the corpus (or the named corpus stems): zig cc, translate-c,
#                      native zig test, AIR export, air2lean diagnostics, Lean #guard; rewrites
#                      record.json. Needs AIR2LEAN_ZIG_NATIVE (stock 0.16.0) and AIR2LEAN_ZIG_AIR
#                      (patched 0.16.0); AIR2LEAN_ZIG_NATIVE_0152 adds the 0.15.2 translate-c column.
#                      Runs compilers and Lean sequentially; wrap it in one scripts/build-guard.py.
#   --generated OUT_DIR START COUNT
#                      cgen.py programs through the same stages into OUT_DIR/record.json.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/c-frontend
export PYTHONDONTWRITEBYTECODE=1

case "${1:-}" in
  --light)
    python3 "$here/run.py" check
    python3 "$here/cgen.py" light --seeds 300
    ;;
  --heavy)
    [ "$#" -ge 2 ] || { echo 'usage: check.sh --heavy OUT_DIR [FILE...]' >&2; exit 2; }
    out=$2; shift 2
    files=()
    if [ "$#" -gt 0 ]; then files=(--files "$@"); fi
    python3 "$here/run.py" heavy --out "$out" ${files[@]+"${files[@]}"}
    python3 "$here/run.py" check || echo 'record changed: update docs/c-frontend.md from run.py tables' >&2
    ;;
  --generated)
    [ "$#" -eq 4 ] || { echo 'usage: check.sh --generated OUT_DIR START COUNT' >&2; exit 2; }
    mkdir -p "$2/corpus"
    python3 "$here/cgen.py" emit "$3" "$4" "$2/corpus" >/dev/null
    python3 "$here/run.py" heavy --corpus "$2/corpus" --out "$2/work" --record "$2/record.json"
    ;;
  *)
    echo 'usage: check.sh --light | --heavy OUT_DIR [FILE...] | --generated OUT_DIR START COUNT' >&2
    exit 2
    ;;
esac
