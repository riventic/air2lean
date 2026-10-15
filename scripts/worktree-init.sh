#!/usr/bin/env bash
# One command to make a fresh worktree ready to work in (CLAUDE.md, Workflow; docs/build-cache.md).
#
#   scripts/worktree-init.sh [--zig VERSION ...] [--no-lean] [--no-generated]
#
# 1. Lean: the full build (scripts/full-build.sh: what CI's `lake` job builds and the tests/diff
#    Lean libraries; without its fixture-check phase, which tests rather than prepares). With
#    AIR2LEAN_CAS_DIR set, the build goes through `scripts/cas.py run`: Lake's artifact cache,
#    keyed by each module's input hash (source, the traces of its imports, toolchain, options), so
#    a module whose inputs some other worktree already built is restored as hard links, and
#    anything that differs is built and published for the next worktree. A stale artifact cannot
#    be hit: a changed input is a different key. Unset, it is a plain `lake build`.
# 2. --zig VERSION (repeatable): the patched compiler of VERSION (scripts/zig-air.sh; from the
#    cache when AIR2LEAN_CAS_DIR is set, else built into zig-air-VERSION/).
# 3. The whole-tree generated files (`scripts/generated.py materialize`).
#
# Heavy builds run under scripts/build-guard.py (lock AIR2LEAN_BUILD_LOCK, waits up to
# AIR2LEAN_LOCK_WAIT seconds, default 3600). Prints the time of each phase.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

lean=1 generated=1 versions=()
while [ $# -gt 0 ]; do
  case $1 in
    --zig) versions+=("${2:?--zig needs a version}"); shift 2 ;;
    --no-lean) lean=0; shift ;;
    --no-generated) generated=0; shift ;;
    -h|--help) sed -n '2,19p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "worktree-init: unknown argument $1" >&2; exit 2 ;;
  esac
done

if [ -n "${AIR2LEAN_CAS_DIR:-}" ]; then
  echo "worktree-init: shared cache $AIR2LEAN_CAS_DIR"
else
  echo "worktree-init: AIR2LEAN_CAS_DIR unset: plain builds, nothing shared (docs/build-cache.md)"
fi
logs=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-worktree-init.XXXXXX")

phase() {  # phase NAME CMD...: run CMD, print its wall time
  local name=$1 start=$SECONDS
  shift
  if ! "$@"; then
    echo "worktree-init: $name failed (logs: $logs)" >&2
    exit 1
  fi
  echo "worktree-init: $name $((SECONDS - start)) s"
}

if [ "$lean" = 1 ]; then
  phase 'lean (full build)' scripts/full-build.sh --no-fixtures --logs "$logs"
fi
for version in ${versions[@]+"${versions[@]}"}; do
  phase "patched zig $version" scripts/zig-air.sh "$version"
done
if [ "$generated" = 1 ]; then
  phase 'generated files' python3 -B scripts/generated.py materialize
fi
echo "worktree-init: ready ($SECONDS s)"
