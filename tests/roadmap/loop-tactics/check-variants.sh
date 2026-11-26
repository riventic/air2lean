#!/usr/bin/env bash
# P09 retranslation (docs/invariant-synthesis.md, "Retranslation"): a retranslation of a program
# with generated loop invariants, for another Zig version or with permuted struct fields, needs a
# regeneration and no hand edit. Each client of air2lean-invgen (the counted loops, the nested
# loop, the linked list of Proofs/Lists) has variants (scripts/invgen.py VARIANTS): the same
# source translated by the other supported Zig versions, and the list with its node's fields
# permuted, each with the module names of the first translation and its own generated Inv.lean.
# For every variant, invgen_variants.py checks that the translation and the invariants are what
# the translator and the generator give for the committed AIR, elaborates the client's one set of
# hand-written specifications and proofs against the variant, unchanged, and checks that the
# client's seeded mutants of the generated invariants still fail there.
# Needs a built translator (lake build air2lean); no Zig compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
# The variants' AIR: exports of this fixture, and for the list's other Zig versions the exports
# of tests/roadmap/interfaces.
python3 -B scripts/fixture-exports.py check loop-tactics interfaces
for client in counted nested lists; do
  python3 -B tests/roadmap/loop-tactics/invgen_variants.py "$client"
done
echo 'retranslated loop-invariant clients: regeneration only, seeded mutants rejected'
