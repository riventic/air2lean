#!/usr/bin/env bash
# Negative check: a PageAllocator whose `realloc` shrinks a mapping's page count without unmapping
# the cut pages (the tail `munmap` is deleted from the translated code) must not satisfy the
# full-state specification: PageSpec.lean, rechecked against the mutated translation, fails. The
# mutant runs without an error (it only leaks pages), so the token that holds the mapping's
# extent authority (`PageTok.ptok`) is what rejects it: the shrunk grant's token needs the
# mapping's extent at the new page end, which only the tail `munmap` gives. The mutant is built by
# Lake apart from the fixture (scripts/fixtures.py mutant); run from anywhere, under
# scripts/build-guard.py.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-translated
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-translated-mutant.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocTranslated"
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
cp "$here/PageTok.lean" "$here/PageSpec.lean" "$work/"
# The proof fails in PageSpec itself (the mutated translation and PageTok build).
python3 -B scripts/fixtures.py mutant alloc-translated --src "$work" --fails PageSpec
echo "alloc-translated mutant: rejected (the resize proof fails for the leaking shrink)"
