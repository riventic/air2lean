#!/usr/bin/env bash
# The translated FixedBufferAllocator against the full-state allocator specification (P4a):
# the retained translation is the fresh one; the entries satisfy FAllocSpec (Full.lean), the
# generated std.mem.Allocator wrappers meet their contracts over it (Wrappers.lean) and the client
# is proved through them (Client.lean, also from the program's start), all walked by the general
# tactic fsym; the client evaluates to the native results; a mutated alloc fails the proof
# (mutant.sh). Every Lean file is a module of the fixture's library AllocFba
# (tests/roadmap/lakefile.toml), built by Lake with what it imports (scripts/fixtures.py; run it
# under scripts/build-guard.py). Needs a built translator; runs no compiler. The AIR is
# exports.json's export, pinned by exports.lock.json (scripts/fixture-exports.py), of Zig 0.16.0
# and 0.17.1. The retained translation is 0.16.0's; over 0.17.1's, in a check tree, the same
# FAllocSpec proof (Full.lean, Creation.lean, CreationDomain.lean) and Eval.lean's `#guard`s are
# built and audited. The wrapper and client contracts are not yet checked over 0.17.1 (README,
# "Zig 0.17.1"). With AIR2LEAN_NATIVE_ZIG (a stock Zig 0.16.0 or 0.17.1), also builds and runs
# native.zig and compares it with expected.txt.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-fba
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-fba.XXXXXX")
trap 'rm -rf "$work"' EXIT
python3 -B scripts/fixture-exports.py check alloc-fba
translate() {  # translate VERSION OUT
  "$translator" "$here/air/$1/client-linux" -o "$2" \
    --namespace AllocFba.Gen --prefix client. --allocator-model translated
}
# The retained translation is the fresh one, byte for byte (Lake builds the retained file).
translate 0.16.0 "$work/Gen.lean"
cmp "$work/Gen.lean" "$here/AllocFba/Gen.lean"
# The library, including creation/domain controls and AllocFba/Eval.lean (`#guard`s).
python3 -B scripts/fixtures.py build AllocFba
# Axioms of every theorem of the proof modules, from the built environment: only the standard ones.
# Named: the theorems, and `FBA.ledger`, a definition (a `ResetLedger` whose fields are proofs).
fba=(FBA.fallocSpec FBA.fthread_alloc FBA.fthread_resize FBA.fthread_remap FBA.fthread_free
  FBA.freset_spec FBA.fown_init FBA.fallocator_init FBA.fallocator_creation FBA.fallocSpec.creation
  FBA.ledger)
declare_all() {  # declare_all NAME...: `--declaration AllocFba.NAME` for each, into `named`
  named=()
  for name in "$@"; do
    named+=(--declaration "AllocFba.$name")
  done
}
declare_all Wrappers.realloc_of Wrappers.allocSentinel_of "${fba[@]}" Client.client_spec \
  Client.client_start
python3 -B scripts/fixtures.py audit AllocFba.Client AllocFba.Full \
  AllocFba.Wrappers AllocFba.Creation AllocFba.CreationDomain "${named[@]}"
# The same FAllocSpec proof text and `#guard`s over the Zig 0.17.1 translation, in a check tree with
# it in place of the retained one (scripts/check-tree.py: the tree clones the root build). The
# allocator's entries (`heap_FixedBufferAllocator_*`) translate to the same code in both versions.
tree=$repo_root/.lake/check-tree/alloc-fba-0.17.1
translate 0.17.1 "$work/Gen-0.17.1.lean"
python3 -B scripts/check-tree.py create "$tree" --replace "$here/AllocFba/Gen.lean=$work/Gen-0.17.1.lean"
declare_all "${fba[@]}"
(cd "$tree" && python3 -B scripts/fixtures.py build AllocFba.Full AllocFba.Creation \
  AllocFba.CreationDomain AllocFba.Eval &&
  python3 -B scripts/fixtures.py audit AllocFba.Full AllocFba.Creation AllocFba.CreationDomain \
  "${named[@]}")
bash "$here/mutant.sh"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  "$AIR2LEAN_NATIVE_ZIG" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} -OReleaseSafe "$here/native.zig" --cache-dir "$work/cache" \
    --global-cache-dir "$work/cache" -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  diff "$here/expected.txt" "$work/native.txt"
fi
echo "alloc-fba: ok"
