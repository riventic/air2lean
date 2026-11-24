#!/usr/bin/env bash
# Negative checks of the queue fixture (Q02: assurance/mutation-map.json, P04 and P06). Each
# seeded mutant changes one place of the translation or of a statement, and the proof that
# covers it, rechecked against the mutant, must fail in its own module:
#
#   "ring-push-no-wrap"                 push writes cell `len` instead of `len - room` when the
#                                       back is around the end of the buffer (Gen.lean): the
#                                       ring is no queue, QueueAdt.Ring's push_spec fails.
#   "ring-pop-no-wrap"                  pop moves `head` to `head + 1` after the last cell
#                                       instead of 0 (Gen.lean): QueueAdt.Ring's pop_spec fails.
#   "pushall-capacity-premise-dropped"  the capacity premise of pushAll's bound is weakened from
#                                       `xs.length + ys.length ≤ C` to `xs.length ≤ C`
#                                       (Clients.lean): a push may fail, the exact count
#                                       `ys.length + 1` is not provable, QueueAdt.Clients fails.
#
# The mutants are built by Lake apart from the fixture (scripts/fixtures.py mutant); run from
# anywhere, under scripts/build-guard.py.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/queue-adt
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-queue-adt-mutants.XXXXXX")
trap 'rm -rf "$work"' EXIT

# mutate FILE FUNCTION OLD NEW DEST: FILE with the one occurrence of OLD after "def FUNCTION "
# (the whole file if FUNCTION is empty: then every occurrence, at least one) replaced by NEW.
mutate() {
  python3 - "$@" <<'EOF'
import sys
src, function, old, new, dst = sys.argv[1:]
text = open(src).read()
if function:
    start = text.index("def " + function + " ")
    end = text.index("\ndef ", start + 1) if "\ndef " in text[start + 1:] else len(text)
    assert text.count(old, start, end) == 1, (function, old, text.count(old, start, end))
    at = text.index(old, start)
    text = text[:at] + new + text[at + len(old):]
else:
    assert old in text, old
    text = text.replace(old, new)
open(dst, "w").write(text)
EOF
}

# 1. push without the wrap-around of the write index
mkdir -p "$work/push/QueueAdt"
mutate "$here/QueueAdt/Gen.lean" Ring_push \
  $'          let i32 ← Zig.sub false i31 i16\n          pure (.br17 i32)))' \
  $'          pure (.br17 i31)))' "$work/push/QueueAdt/Gen.lean"
cp "$here/QueueAdt/Window.lean" "$here/QueueAdt/Ring.lean" "$work/push/QueueAdt/"
python3 -B scripts/fixtures.py mutant "ring-push-no-wrap" --src "$work/push" --fails QueueAdt.Ring
echo "queue-adt mutant: ring-push-no-wrap rejected (the ring's push_spec fails for a push that does not wrap)"

# 2. pop without the wrap-around of the front index
mkdir -p "$work/pop/QueueAdt"
mutate "$here/QueueAdt/Gen.lean" Ring_pop \
  $'            pure (.br25 (0 : BitVec 64)))' \
  $'            pure (.br25 i23))' "$work/pop/QueueAdt/Gen.lean"
cp "$here/QueueAdt/Window.lean" "$here/QueueAdt/Ring.lean" "$work/pop/QueueAdt/"
python3 -B scripts/fixtures.py mutant "ring-pop-no-wrap" --src "$work/pop" --fails QueueAdt.Ring
echo "queue-adt mutant: ring-pop-no-wrap rejected (the ring's pop_spec fails for a pop that does not wrap)"

# 3. the bound of pushAll without its capacity premise
mkdir -p "$work/room/QueueAdt"
mutate "$here/QueueAdt/Clients.lean" "" '(hroom : xs.length + ys.length ≤ C)' '(hroom : xs.length ≤ C)' \
  "$work/room/QueueAdt/Clients.lean"
cp "$here/QueueAdt/Gen.lean" "$work/room/QueueAdt/"
python3 -B scripts/fixtures.py mutant "pushall-capacity-premise-dropped" --src "$work/room" \
  --fails QueueAdt.Clients
echo "queue-adt mutant: pushall-capacity-premise-dropped rejected (pushAll's step count needs the capacity premise)"
echo "queue-adt mutants: ok"
