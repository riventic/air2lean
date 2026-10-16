#!/usr/bin/env bash
# The general symbolic executor `fsym` (ZigLean/Sep/Full/Auto.lean, docs/proof-automation.md) on
# small library-only examples: the arithmetic solver, walks/returns, the concurrent backend,
# variable pointers (Facts), a large generated body (Large), and the scenarios of the retired
# step/frame tactics and total-correctness checks (Steps, Frame, Total), range laws (Plan), the
# region library (Region) and providers over the whole precondition (Providers: tagged shares,
# pointer `==` across live blocks, `Within`) and the planning order with terms equal up to
# arithmetic (Unify: a grant whose bytes changed, hypotheses up to arithmetic) and the caller's
# updates at returns (Updates: `fsym [u]` with `u : EUpd P Q`) and the fields of a stored struct
# (Fields: `EncField`, whole and field access) and plain accesses of atomic words that keep
# their tag (AtomicPlain) and accesses of a struct whose fields several parts own (Parts) and
# thread steps by the sequential rules with the locality of their command (Threads) and views of
# atoms at stuck steps (Views: atomic words as bytes, a value's encoding, two fees) and a
# thread's run in a protocol (WP: `MemM` segments with inferred posts; WPMutex: the generated
# `Io.Mutex` lock, unlock and lock loop against the lock rules, for every protocol with the
# lock; WPHold: the lock holder's steps by `FLock.Fits.wp_hold` with the holder's next place, the
# protocol's lemmas backwards and forwards) and total stack pushes of a thread with a stack budget
# (Stack: the token rules, a thread, the start, rejected pushes without room). Its large user is
# the FixedBufferAllocator
# (tests/roadmap/alloc-fba/AllocFba/Full.lean). Builds the library modules the examples import
# (scripts/lean-deps.py); runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/sep-auto
python3 -B scripts/lean-deps.py --build "$here"
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-sep-auto.XXXXXX")
trap 'rm -rf "$work"' EXIT
for m in Arith Walk Conc Facts Large Steps Frame Total Plan Region Providers Unify Updates Fields AtomicPlain Parts Threads Views WP WPMutex WPHold Stack Report; do
  { cat "$here/$m.lean"; echo; grep -o '^theorem [^ :({\[]*' "$here/$m.lean" | while read -r _ t; do
      echo "#print axioms SepAuto.$m.$t"; done; } > "$work/$m.lean"
  "${lean_cmd[@]}" "$work/$m.lean" > "$work/$m.txt" 2>&1 || { cat "$work/$m.txt" >&2; exit 1; }
  python3 - "$work/$m.txt" "$(grep -c '^theorem ' "$here/$m.lean")" <<'PY'
import re, sys
text, n = open(sys.argv[1]).read(), int(sys.argv[2])
groups = re.findall(r"depends on axioms: \[([^\]]*)\]|(does not depend on any axioms)", text)
used = {a.strip() for g, _ in groups for a in g.split(",") if a.strip()}
assert ": error" not in text and len(groups) == n, text
assert used <= {"propext", "Classical.choice", "Quot.sound"}, text
PY
done
echo "sep-auto: ok"
