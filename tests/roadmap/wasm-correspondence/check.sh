#!/usr/bin/env bash
# T05 contracts of the correspondence kernels. One source (`kernels.zig`) exported by each Zig
# version of exports.json (0.17.1, 0.16.0) for x86_64-linux, aarch64-macos, wasm32-freestanding
# and wasm32-wasi. Per version: re-translate the retained AIR (every kernel translates for every
# target: the checker rejects nothing), compare with the retained
# WasmCorrespondence/<V>/<T>/Gen.lean files byte for byte, check that the proofs of every
# version are the written ones (0.17.1) renamed, build the library WasmCorrespondence
# (tests/roadmap/lakefile.toml: the translations, the contract stated once in
# WasmCorrespondence.Contracts and each version's proof that every target meets it), audit
# its theorems, and check the relation and its claims on the committed records
# (scripts/wasm-correspondence.py check: no compiler).
#
# The AIR is declared in exports.json and pinned by exports.lock.json (this run checks the lock;
# scripts/fixture-exports.py verify|export wasm-correspondence re-exports it).
# Needs `lake build ZigLean Air2Lean air2lean ZigLean.Mem.WidthLemmas`; Lake builds the library
# (scripts/fixtures.py): run it under scripts/build-guard.py.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case_dir=tests/roadmap/wasm-correspondence
[ "$#" -eq 0 ] || { echo 'usage: check.sh' >&2; exit 2; }
# The Zig versions exports.json exports kernels.zig for.
version_list=$(python3 -B -c 'import json, sys
sets = {tuple(e["versions"]) for e in json.load(open(sys.argv[1]))["exports"]}
assert len(sets) == 1, f"the entries differ in their versions: {sets}"
print(*sets.pop())' "$case_dir/exports.json")
read -ra versions <<<"$version_list"
[ "${#versions[@]}" -gt 0 ] || { echo 'exports.json exports kernels.zig for no version' >&2; exit 1; }
pairs=(X64:x86_64-linux A64:aarch64-macos Wasm32:wasm32-freestanding Wasi:wasm32-wasi)
python3 -B scripts/fixture-exports.py check wasm-correspondence
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-wasm-correspondence.XXXXXX")
trap 'rm -rf "$work"' EXIT
modules=(WasmCorrespondence.Contracts)
for v in "${versions[@]}"; do
  V="V${v//./_}"
  for pair in "${pairs[@]}"; do
    ns=${pair%%:*}
    t=${pair#*:}
    # The retained translation is the fresh one, byte for byte (Lake builds the retained file).
    "$translator" "$case_dir/air/$v/$t" -o "$work/$V-$ns.lean" \
      --namespace "WasmCorrespondence.$V.$ns" --prefix kernels.
    cmp "$work/$V-$ns.lean" "$case_dir/WasmCorrespondence/$V/$ns/Gen.lean"
  done
  # One proof file for every version: the written one (0.17.1), the version renamed.
  [ "$V" = V0_17_1 ] || python3 -B scripts/fixtures.py instance \
    "$case_dir/WasmCorrespondence/V0_17_1/Proofs.lean" --subst "V0_17_1=$V"
  modules+=("WasmCorrespondence.$V.Proofs")
done
python3 -B scripts/fixtures.py build WasmCorrespondence
python3 -B scripts/fixtures.py audit "${modules[@]}" \
  --declaration WasmCorrespondence.V0_17_1.Proofs.meets \
  --declaration WasmCorrespondence.Kernels.Meets.exact_agree \
  --declaration WasmCorrespondence.Kernels.Meets.usize_bits_eq_iff
python3 -B "$case_dir/test_correspondence.py"
python3 -B scripts/wasm-correspondence.py check
echo 'wasm-correspondence translation, contract and relation gates passed'
