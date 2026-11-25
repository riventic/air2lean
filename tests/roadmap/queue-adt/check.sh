#!/usr/bin/env bash
# P04/P06: the ring-buffer queue of queue.zig (Zig 0.17.1) against the queue contract
# Zig.Full.QueueImpl (ZigLean/Sep/Full/Queue.lean). The retained AIR is its fixture's export
# (exports.lock.json) and the retained translation QueueAdt/Gen.lean is the fresh one, byte for
# byte; the ring proves the contract (QueueAdt/Ring.lean: push, pop, count, each one fsym walk);
# the clients rotate and pushAll are proved for every contract over the generated operations
# (QueueAdt/Clients.lean), pushAll with its exact step count under the capacity premise
# (`pushAll_exact`, `pushAll_steps`, tight by `pushAll_not_within`); QueueAdt/Instances.lean
# instantiates them to the ring. Every theorem of the library depends on the standard axioms
# only. Seeded mutants must fail their proofs (mutants.sh). Every Lean file is a module of the
# fixture's library QueueAdt (tests/roadmap/lakefile.toml), built by Lake with what it imports
# (scripts/fixtures.py; run it under scripts/build-guard.py). Needs a built translator; runs no
# patched compiler. With AIR2LEAN_NATIVE_ZIG (a stock Zig 0.17.1), also builds and runs
# native.zig and compares it with expected.txt.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/queue-adt
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-queue-adt.XXXXXX")
trap 'rm -rf "$work"' EXIT
# The retained AIR is the export of queue.zig that exports.lock.json pins.
python3 -B scripts/fixture-exports.py check queue-adt
# The retained translation is the fresh one, byte for byte (Lake builds the retained file).
"$translator" "$here/air" -o "$work/Gen.lean" --namespace QueueAdt --prefix queue.
cmp "$work/Gen.lean" "$here/QueueAdt/Gen.lean"
python3 -B scripts/fixtures.py build QueueAdt ZigLean.Sep.Full.Queue
# Axioms of every theorem of the library, from the built environment: only the standard ones.
# Named: the theorems, and `ringQueue`, a definition (a `QueueImpl` whose fields are proofs).
named=()
for name in push_spec pop_spec count_spec ringQueue rotate_spec pushAll_exact pushAll_total \
    pushAll_steps pushAll_not_within ring_rotate ring_pushAll_exact ring_pushAll_not_within \
    Shift.push_spec Shift.pop_spec Shift.count_spec shiftQueue rotateShift_spec \
    shift_rotateSteps shift_rotate; do
  named+=(--declaration "QueueAdt.$name")
done
python3 -B scripts/fixtures.py audit --library QueueAdt "${named[@]}"
bash "$here/mutants.sh"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  "$AIR2LEAN_NATIVE_ZIG" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} -OReleaseSafe "$here/native.zig" \
    --cache-dir "$work/cache" --global-cache-dir "$work/cache" -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  diff "$here/expected.txt" "$work/native.txt"
fi
echo "queue-adt: ok"
