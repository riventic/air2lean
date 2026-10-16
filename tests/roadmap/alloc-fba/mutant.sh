#!/usr/bin/env bash
# Negative check: a FixedBufferAllocator whose `alloc` does not advance `end_index` (the store of
# the new end index is deleted from the translated code) must satisfy neither `AllocSpec` nor the
# full-state `FAllocSpec`: the proofs in AllocFba/Fba.lean (`FBA.allocSpec`) and AllocFba/Full.lean
# (`FBA.fallocSpec`), rechecked against the mutated translation, fail. Two allocations would grant
# the same bytes.
# Needs the modules that Fba.lean and Full.lean import built (check.sh builds them); run from anywhere.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-fba
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-fba-mutant.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocFba"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
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
for m in Gen Impl Bridge; do
  "${lean_cmd[@]}" -R "$work" -o "$work/AllocFba/$m.olean" "$work/AllocFba/$m.lean" > /dev/null
done
for m in Fba Full; do
  if "${lean_cmd[@]}" -R "$work" "$work/AllocFba/$m.lean" > "$work/$m.log" 2>&1; then
    echo "alloc-fba mutant: $m.lean still checks for an alloc that does not advance end_index" >&2
    exit 1
  fi
  grep -q "error" "$work/$m.log"
  # A missing import (an unbuilt prerequisite) is not a rejection of the mutant.
  if grep -Eq "unknown module prefix|object file .* does not exist|unknown package" "$work/$m.log"; then
    cat "$work/$m.log" >&2; echo "alloc-fba mutant: $m.lean failed to import, not on the proof" >&2
    exit 1
  fi
done
echo "alloc-fba mutant: rejected (the AllocSpec and FAllocSpec proofs fail for the non-advancing alloc)"
