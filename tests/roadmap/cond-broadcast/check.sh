#!/usr/bin/env bash
# C14 condition broadcast: the committed export of every supported version (air/<version>,
# exports.json) translates, and its broadcast is the code that the condition contract's
# implementations prove (`CondImpl.broadcast_wp`): each function of the translation equals, line
# for line, the same function in the proved program's translation (0.14.1 and 0.15.2:
# `Thread.Condition.broadcast` of Proofs/Threadsync/Gen.lean; 0.16.0: `Io.Condition.broadcast` of
# Proofs/Sync/Gen.lean; 0.17.1: of tests/golden/0.17.1/sync/Gen.lean, the 0.17.1 translation
# that Proofs/Sync/Cond.lean is checked against).
#   check.sh                 the gate above (needs a built translator; no compiler, no Lean)
#   check.sh --export [V..]  scripts/fixture-exports.py verify: a fresh export with the patched
#                            compilers of versions V (default all) equals the committed one
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/cond-broadcast
if [ "${1:-}" = --export ]; then
  shift
  versions=()
  for version in "$@"; do versions+=(--version "$version"); done
  exec python3 -B scripts/fixture-exports.py verify cond-broadcast ${versions[@]+"${versions[@]}"}
fi
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first: lake build air2lean' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-cond-broadcast.XXXXXX")
trap 'rm -rf "$work"' EXIT
python3 -B scripts/fixture-exports.py check cond-broadcast
for pair in 0.14.1:Proofs/Threadsync/Gen.lean 0.15.2:Proofs/Threadsync/Gen.lean \
    0.16.0:Proofs/Sync/Gen.lean 0.17.1:tests/golden/0.17.1/sync/Gen.lean; do
  version=${pair%%:*} proved=${pair#*:}
  "$translator" "$here/air/$version" -o "$work/Gen-$version.lean" --namespace CondBroadcast \
    --prefix cond_broadcast.
  python3 -B - "$work/Gen-$version.lean" "$proved" "$version" <<'PY'
import re
import sys

fresh, proved, version = sys.argv[1], sys.argv[2], sys.argv[3]


def block(lines, name):
    """A translated function's declarations: from its `<name>Locals` structure to the
    `attribute [zig_run]` line that ends with its name."""
    start = next((i for i, line in enumerate(lines) if line == f'structure {name}Locals where'), None)
    if start is None:
        return None
    for end in range(start, len(lines)):
        if lines[end].startswith('attribute [zig_run] ') and lines[end].split()[-1] == name:
            return lines[start:end + 1]
    return None


fresh_lines = open(fresh, encoding='utf-8').read().splitlines()
proved_lines = open(proved, encoding='utf-8').read().splitlines()
names = sorted({m.group(1) for line in fresh_lines
                for m in [re.match(r'def ([A-Za-z0-9_]+) \(p0 : Zig\.Ptr\)', line)] if m})
broadcast = [n for n in names if n.endswith('Condition_broadcast')]
if len(broadcast) != 1:
    sys.exit(f'{version}: expected one broadcast function in the translation, got {names}')
for name in names:
    mine, theirs = block(fresh_lines, name), block(proved_lines, name)
    if mine is None:
        sys.exit(f'{version}: no declarations of {name} in the translation')
    if theirs is None:
        sys.exit(f'{version}: {name} is not in {proved}')
    if mine != theirs:
        sys.exit(f'{version}: {name} differs from {proved}')
print(f'cond-broadcast {version}: {", ".join(names)} equal {proved}')
PY
done
echo 'condition broadcast gate passed: 4 versions translate to the proved broadcast'
