#!/usr/bin/env bash
# Allocator milestone 2: std.heap.ArenaAllocator (Zig 0.16.0, lock-free) translated from its AIR with
# its child allocators (FixedBufferAllocator, page_allocator) down to posix.mmap/munmap/mremap
# (`--allocator-model translated`, docs/alloc-arena.md). Checks: the retained translations are the
# fresh ones; they elaborate; the one-thread results equal the native ones (Eval.lean); obstructions
# O-A and O-E are kernel-checked (ArenaObstruction.lean); an alloc that reserves nothing is rejected
# (mutant.sh); the admissions fail closed (test_cli.py).
# Needs a built translator and `lake build ZigLean ZigLean.Sep.Full.Conc`; runs no compiler. With
# AIR2LEAN_NATIVE_ZIG (a stock Zig 0.16.0), also builds and runs native.zig against expected.txt.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-arena
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-arena.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocArena"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
python3 - "$here" <<'EOF'
import hashlib, json, pathlib, sys
here = pathlib.Path(sys.argv[1])
record = json.loads((here / 'provenance.json').read_text())
for name, digest in record['source_sha256'].items():
    assert hashlib.sha256((here / name).read_bytes()).hexdigest() == digest, name
files = {str(p.relative_to(here / 'air')): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in sorted((here / 'air').rglob('*.json'))}
assert files == record['air_sha256'], 'AIR fixtures differ from provenance.json'
EOF
for os in linux macos; do
  Os="$(printf '%s' "${os:0:1}" | tr '[:lower:]' '[:upper:]')${os:1}"
  module="Arena$Os"
  # The retained translation is the fresh one, byte for byte.
  "$translator" "$here/air/0.16.0/arena-$os" -o "$work/AllocArena/$module.lean" \
    --namespace "AllocArena.$module" --prefix "arena." --allocator-model translated
  cmp "$work/AllocArena/$module.lean" "$here/AllocArena/$module.lean"
  "${lean_cmd[@]}" -R "$work" -o "$work/AllocArena/$module.olean" "$work/AllocArena/$module.lean"
done
"${lean_cmd[@]}" "$here/Eval.lean"
"${lean_cmd[@]}" -R "$here" -o "$work/ArenaObstruction.olean" "$here/ArenaObstruction.lean"
cat > "$work/Axioms.lean" <<'AX'
import ArenaObstruction
#print axioms AllocArena.ArenaObstruction.foreign_free_panics
#print axioms AllocArena.ArenaObstruction.oob_free_illegal
AX
"${lean_cmd[@]}" "$work/Axioms.lean" > "$work/axioms.txt"
# Only the standard axioms (any subset of propext, Classical.choice, Quot.sound).
python3 - "$work/axioms.txt" <<'EOF'
import re, sys
text = open(sys.argv[1]).read()
used = {a.strip() for group in re.findall(r'axioms: \[([^\]]*)\]', text) for a in group.split(',')}
assert text.strip() and used <= {'propext', 'Classical.choice', 'Quot.sound'}, text
EOF
bash "$here/mutant.sh"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  cp "$here/arena.zig" "$here/native.zig" "$work/"
  "$AIR2LEAN_NATIVE_ZIG" build-exe -OReleaseSafe "$work/native.zig" --cache-dir "$work/cache" \
    --global-cache-dir "$work/cache" -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  diff "$here/expected.txt" "$work/native.txt"
fi
echo "alloc-arena: ok"
