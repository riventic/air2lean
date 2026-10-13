#!/usr/bin/env bash
# Negative check: an ArenaAllocator whose `alloc` reserves nothing (the atomic `end_index += n +
# alignment - 1` of the fast path adds 0, in the translated code) hands out the same bytes twice.
# Eval.lean, rechecked against the mutated translation, must fail at `arena_three`: the third
# allocation gets the second one's bytes (331, not 321). Needs `lake build ZigLean ZigLean.Sep.Full.Conc` (check.sh lists the full set).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-arena
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-arena-mutant.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocArena"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
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
for module in ArenaMacos ArenaFixedLinux; do
  cp "$here/AllocArena/$module.lean" "$work/AllocArena/$module.lean"
done
for module in ArenaLinux ArenaMacos ArenaFixedLinux; do
  "${lean_cmd[@]}" -R "$work" -o "$work/AllocArena/$module.olean" "$work/AllocArena/$module.lean" > /dev/null
done
if "${lean_cmd[@]}" "$here/Eval.lean" > "$work/eval.log" 2>&1; then
  echo "alloc-arena mutant: Eval.lean still checks for an alloc that reserves nothing" >&2
  exit 1
fi
# A #guard fails; a missing import (an unbuilt prerequisite) is not a rejection of the mutant.
if grep -Eq "unknown module prefix|object file .* does not exist|unknown package" "$work/eval.log" ||
    ! grep -q "did not evaluate to" "$work/eval.log" || ! grep -q "arena_three" "$work/eval.log"; then
  cat "$work/eval.log" >&2; echo "alloc-arena mutant: Eval.lean failed for another reason" >&2; exit 1
fi
echo "alloc-arena mutant: rejected (arena_three: two allocations overlap)"
