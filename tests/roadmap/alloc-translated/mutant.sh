#!/usr/bin/env bash
# Negative check: a PageAllocator whose `realloc` shrinks a mapping's page count without unmapping
# the cut pages (the tail `munmap` is deleted from the translated code) must not satisfy the
# full-state specification: PageSpec.lean, rechecked against the mutated translation, fails. The
# mutant runs without an error (it only leaks pages), so the token that pins the mapping's size
# (`PageSpec.tok`) is what rejects it.
# Needs `lake build ZigLean ZigLean.Sep.Mmap ZigLean.Sep.AllocSpec.Ops ZigLean.Sep.AllocSpec.Norm
# ZigLean.Sep.Full.AllocSpec ZigLean.Sep.Full.Tame`; run from anywhere.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-translated
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-translated-mutant.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocTranslated"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
python3 - "$here/AllocTranslated/PageLinux.lean" "$work/AllocTranslated/PageLinux.lean" <<'EOF'
import sys
src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
start = text.index("def heap_PageAllocator_realloc ")
unmap = "                    let _i90 ← Zig.callM (Zig.Os.munmap Zig.Os.Target.linux i89)\n"
at = text.index(unmap, start)
assert at < text.index("\ndef ", start + 1), "the shrink munmap is not in realloc"
open(dst, "w").write(text[:at] + text[at + len(unmap):])
EOF
"${lean_cmd[@]}" -R "$work" -o "$work/AllocTranslated/PageLinux.olean" \
  "$work/AllocTranslated/PageLinux.lean" > /dev/null
cp "$here/PageSpec.lean" "$work/PageSpec.lean"
if "${lean_cmd[@]}" -R "$work" "$work/PageSpec.lean" > "$work/spec.log" 2>&1; then
  echo "alloc-translated mutant: PageSpec still checks for a realloc that leaks the cut pages" >&2
  exit 1
fi
grep -q "error" "$work/spec.log"
# A missing import (an unbuilt prerequisite) is not a rejection of the mutant.
if grep -Eq "unknown module prefix|object file .* does not exist|unknown package" "$work/spec.log"; then
  cat "$work/spec.log" >&2; echo "alloc-translated mutant: PageSpec failed to import, not on the proof" >&2
  exit 1
fi
echo "alloc-translated mutant: rejected (the resize proof fails for the leaking shrink)"
