#!/usr/bin/env bash
# Allocator milestone 2: std.heap.ArenaAllocator (Zig 0.16.0, lock-free) translated from its AIR with
# its child allocators (FixedBufferAllocator, page_allocator) down to posix.mmap/munmap/mremap
# (`--allocator-model translated`, docs/alloc-arena.md). Checks: the retained translations are the
# fresh ones (the stock arena on both targets, the patched one of upstream/arena-fix.patch on
# x86_64-linux); they elaborate; the one-thread results equal the native ones (Eval.lean; the stock
# arena's O-E run is illegal where native code has undefined behaviour); obstructions
# O-A and O-E are kernel-checked (ArenaObstruction.lean); `free` is proved against
# FAllocSpec (ArenaSpec.lean); an alloc that reserves nothing is rejected (mutant.sh); the admissions
# fail closed (test_cli.py).
# Needs a built translator and `lake build ZigLean ZigLean.Sep.Full.Conc ZigLean.Sep.Full.AtomicRules
# ZigLean.Sep.Full.Ghost ZigLean.Sep.Full.AllocSpec ZigLean.Sep.AllocSpec.Ops`; runs no compiler. With
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
# The stock arena (both targets) and the patched one (upstream/arena-fix.patch, x86_64-linux).
for pair in "arena-linux ArenaLinux" "arena-macos ArenaMacos" "arena-fixed-linux ArenaFixedLinux"; do
  dir=${pair% *}
  module=${pair#* }
  # The retained translation is the fresh one, byte for byte.
  "$translator" "$here/air/0.16.0/$dir" -o "$work/AllocArena/$module.lean" \
    --namespace "AllocArena.$module" --prefix "arena." --allocator-model translated
  cmp "$work/AllocArena/$module.lean" "$here/AllocArena/$module.lean"
  "${lean_cmd[@]}" -R "$work" -o "$work/AllocArena/$module.olean" "$work/AllocArena/$module.lean"
done
"${lean_cmd[@]}" "$here/Eval.lean"
# ArenaObstruction.lean prints the axioms of its two theorems.
"${lean_cmd[@]}" "$here/ArenaObstruction.lean" > "$work/axioms.txt"
# Only the standard axioms (any subset of propext, Classical.choice, Quot.sound).
python3 - "$work/axioms.txt" <<'EOF'
import re, sys
text = open(sys.argv[1]).read()
used = {a.strip() for group in re.findall(r'axioms: \[([^\]]*)\]', text) for a in group.split(',')}
assert text.count('depends on axioms') == 2 and used <= {'propext', 'Classical.choice', 'Quot.sound'}, text
EOF
# ArenaSpec.lean: `free`, `resize` and `remap` against FAllocSpec over the ghost-epoch invariant; it
# prints the axioms of `free_spec`, `resize_spec` and `remap_spec`.
"${lean_cmd[@]}" "$here/ArenaSpec.lean" > "$work/spec.txt"
python3 - "$work/spec.txt" <<'EOF'
import re, sys
text = open(sys.argv[1]).read()
used = {a.strip() for group in re.findall(r'axioms: \[([^\]]*)\]', text) for a in group.split(',')}
assert 'sorryAx' not in text and text.count('depends on axioms') == 3, text
assert used <= {'propext', 'Classical.choice', 'Quot.sound'}, text
EOF
bash "$here/mutant.sh"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  cp "$here/arena.zig" "$here/native.zig" "$work/"
  "$AIR2LEAN_NATIVE_ZIG" build-exe -OReleaseSafe "$work/native.zig" --cache-dir "$work/cache" \
    --global-cache-dir "$work/cache" -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  diff "$here/expected.txt" "$work/native.txt"
  # The patched arena: the same clients over a standard library with upstream/arena-fix.patch.
  cp -R "$("$AIR2LEAN_NATIVE_ZIG" env | sed -n 's/^ *\.lib_dir = "\(.*\)",$/\1/p')" "$work/lib"
  chmod -R u+w "$work/lib"
  patch -s -d "$work/lib" -p1 < "$here/upstream/arena-fix.patch"
  "$AIR2LEAN_NATIVE_ZIG" build-exe -OReleaseSafe --zig-lib-dir "$work/lib" "$work/native.zig" \
    --cache-dir "$work/cache-fixed" --global-cache-dir "$work/cache-fixed" -femit-bin="$work/native-fixed"
  "$work/native-fixed" 2> "$work/native-fixed.txt"
  diff "$here/expected-fixed.txt" "$work/native-fixed.txt"
fi
echo "alloc-arena: ok"
