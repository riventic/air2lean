#!/usr/bin/env bash
# Negative check: an ArenaAllocator whose `alloc` reserves nothing (the atomic `end_index += n +
# alignment - 1` of the fast path adds 0, in the translated code) hands out the same bytes twice.
# AllocArena/Eval.lean, rechecked against the mutated translation, must fail at `arena_three`: the
# third allocation gets the second one's bytes (331, not 321). The mutant is built by Lake apart
# from the fixture (scripts/fixtures.py mutant); run from anywhere, under scripts/build-guard.py.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-arena
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-arena-mutant.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocArena"
python3 - "$here/AllocArena/ArenaLinux.lean" "$work/AllocArena/ArenaLinux.lean" <<'EOF'
import re, sys
src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
start = text.index("def heap_ArenaAllocator_alloc.loop")
bump = re.compile(r"(Zig\.atomicRmwC Zig\.RmwOp\.add false Zig\.AtomicOrder\.acquire 8 i\d+) i\d+\n")
hits = list(bump.finditer(text, start))
assert len(hits) == 1, "expected exactly one end_index bump in alloc"
m = hits[0]
open(dst, "w").write(text[:m.start()] + m.group(1) + " 0\n" + text[m.end():])
EOF
# Only the Linux module is mutated: the guard that sees the overlap is a Linux one.
cp "$here/AllocArena/ArenaMacos.lean" "$here/AllocArena/ArenaFixedLinux.lean" "$here/AllocArena/Eval.lean" \
  "$work/AllocArena/"
# A #guard fails in Eval itself (its imports build).
python3 -B scripts/fixtures.py mutant alloc-arena --src "$work" --fails AllocArena.Eval \
  --expect "did not evaluate to" --expect arena_three
echo "alloc-arena mutant: rejected (arena_three: two allocations overlap)"
