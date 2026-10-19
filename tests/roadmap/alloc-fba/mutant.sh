#!/usr/bin/env bash
# Negative check: a FixedBufferAllocator whose `alloc` does not advance `end_index` (the store of
# the new end index is deleted from the translated code) must satisfy neither `AllocSpec` nor the
# full-state `FAllocSpec`: the proofs in AllocFba/Fba.lean (`FBA.allocSpec`) and AllocFba/Full.lean
# (`FBA.fallocSpec`), rechecked against the mutated translation, fail. Two allocations would grant
# the same bytes. The mutant is built by Lake apart from the fixture (scripts/fixtures.py mutant);
# run from anywhere, under scripts/build-guard.py.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-fba
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-fba-mutant.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocFba"
python3 - "$here/AllocFba/Gen.lean" "$work/AllocFba/Gen.lean" <<'EOF'
import sys
src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
start = text.index("def heap_FixedBufferAllocator_alloc ")
store = "          Zig.store (α := BitVec 64) 8 i41 i30\n"
at = text.index(store, start)
assert at < text.index("\ndef ", start + 1), "the end_index store is not in alloc"
open(dst, "w").write(text[:at] + text[at + len(store):])
EOF
cp "$here/AllocFba/Impl.lean" "$here/AllocFba/Bridge.lean" "$here/AllocFba/Fba.lean" \
  "$here/AllocFba/Full.lean" "$work/AllocFba/"
# Each proof fails in its own module (Gen, Impl and Bridge build).
python3 -B scripts/fixtures.py mutant alloc-fba --src "$work" --fails AllocFba.Fba --fails AllocFba.Full
echo "alloc-fba mutant: rejected (the AllocSpec and FAllocSpec proofs fail for the non-advancing alloc)"
