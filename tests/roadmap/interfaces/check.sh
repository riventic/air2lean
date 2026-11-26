#!/usr/bin/env bash
# Open interfaces (docs/interfaces.md): calls through a `std.mem.Allocator`, a `std.Random` or
# E02's `Visitor` callback that the caller passes in. Needs a built translator and `lake build ZigLean ZigLean.Sep.Full.Wrappers
# ZigLean.Sep.Full.Dispatch ZigLean.Sep.Full.Auto ZigLean.Sep.Full.Block ZigLean.Sep.Full.AutoPrim
# ZigLean.Sep.Full.Typed ZigLean.Sep.Full.Try ZigLean.Sep.Full.Region`;
# runs no compiler. Every Zig version's exports translate under the registries and elaborate; the
# 0.17.1 translations are the retained ones byte for byte, and the proofs over them
# (Interfaces/*Spec.lean) check; the list proofs (Proofs/Lists, with M03's Policy) build over the
# 0.17.1, 0.16.0 and 0.15.2 lists translations, and those that take no allocator over the 0.14.1
# one; test_cli.py covers the rejections and the closed default.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 -B scripts/lean-deps.py --build tests/roadmap/interfaces
here=tests/roadmap/interfaces
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(python3 -B scripts/lean-deps.py --lean)  # `lake env lean` with Lake's native fsym
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-interfaces.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/Interfaces"
python3 -B scripts/fixture-exports.py check interfaces
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# E02's callbacks (tests/roadmap/callbacks) with their `Visitor` type open: that fixture's
# exports and per-version registries (the foreign `ext_visit` model) with the `interfaces` entry
# of registry-callbacks-0.17.1.json, whose models are the callbacks fixture's 0.17.1 ones.
cp tests/roadmap/callbacks/CallbackModel.lean "$work/CallbackModel.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/CallbackModel.olean" "$work/CallbackModel.lean"
python3 - "$here/registry-callbacks-0.17.1.json" "$work" <<'PY'
import json, sys
committed, work = json.load(open(sys.argv[1])), sys.argv[2]
for version in ('0.17.1', '0.16.0', '0.15.2', '0.14.1'):
    registry = json.load(open(f'tests/roadmap/callbacks/registry-{version}.json'))
    if version == '0.17.1':
        assert {k: v for k, v in committed.items() if k != 'interfaces'} == registry, \
            'registry-callbacks-0.17.1.json: models differ from tests/roadmap/callbacks'
    registry['interfaces'] = committed['interfaces']
    json.dump(registry, open(f'{work}/registry-callbacks-{version}.json', 'w'))
PY
# program | module | namespace | retained 0.17.1 translation | prefix | exports ({v}: version) |
# registry ({v}) | extra translator options. The lists translation is the program of the
# full-state list proofs (Proofs/Lists), so it is kept there.
programs=(
  "lists|Lists|Lists.Open|Proofs/Lists/Open.lean|lists.|$here/air/{v}/lists|$here/registry-alloc.json|--allocator-model translated"
  "mix|Mix|Interfaces.Mix|$here/Interfaces/Mix.lean|mix.|$here/air/{v}/mix|$here/registry-alloc.json|--allocator-model translated"
  "rnd|Rnd|Interfaces.Rnd|$here/Interfaces/Rnd.lean|rnd.|$here/air/{v}/rnd|$here/registry-random.json|"
  "callbacks|Callbacks|Interfaces.Callbacks|$here/Interfaces/Callbacks.lean|callbacks.|tests/roadmap/callbacks/air/{v}|$work/registry-callbacks-{v}.json|"
  "sentinel|Sentinel|Interfaces.Sentinel|$here/Interfaces/Sentinel.lean|source.|$here/air/{v}/sentinel|$here/registry-alloc.json|--allocator-model translated"
)
translate() {  # translate VERSION ENTRY OUT
  local name module namespace retained prefix air registry extra
  IFS='|' read -r name module namespace retained prefix air registry extra <<< "$2"
  # shellcheck disable=SC2086
  "$translator" "${air//\{v\}/$1}" -o "$3" --namespace "$namespace" --prefix "$prefix" \
    --profile abi64-le-v1 --model-registry "${registry//\{v\}/$1}" $extra
}
for version in 0.16.0 0.15.2 0.14.1 0.17.1; do
  for entry in "${programs[@]}"; do
    module=$(cut -d'|' -f2 <<< "$entry")
    translate "$version" "$entry" "$work/Interfaces/$module.lean"
    "${lean_cmd[@]}" -R "$work" -o "$work/Interfaces/$module.olean" "$work/Interfaces/$module.lean"
    if [ "$module" = Lists ]; then cp "$work/Interfaces/Lists.lean" "$work/lists-$version.lean"; fi
  done
  # The sentinel proofs hold for this version's translation too (0.17.1: the axioms loop below).
  if [ "$version" != 0.17.1 ]; then
    "${lean_cmd[@]}" -R "$work" "$here/Interfaces/SentinelSpec.lean" > "$work/sentinel-$version.txt" 2>&1 || {
      cat "$work/sentinel-$version.txt" >&2; exit 1; }
  fi
done
# The retained translations are the fresh 0.17.1 ones (the last loop round).
for entry in "${programs[@]}"; do
  module=$(cut -d'|' -f2 <<< "$entry")
  cmp "$work/Interfaces/$module.lean" "$(cut -d'|' -f4 <<< "$entry")"
done
# The full-state list proofs hold for every version's lists translation: over the retained 0.17.1
# one in the checkout, over the 0.16.0 and 0.15.2 ones in a check tree (scripts/check-tree.py)
# with that translation in place of Proofs/Lists/Open.lean (the trees clone the checkout's
# build, so only Open and the proofs rebuild there). Lake's own search path only: not this
# check's LEAN_PATH, whose checkout build holds the 0.17.1 Proofs.Lists.Open.
# Proofs.Lists.Policy is M03's `appendEach_spec`: the append loop for every allocator and every
# failure decision.
lists_proofs=(Proofs.Lists.Linked Proofs.Lists.Alloc Proofs.Lists.Append Proofs.Lists.Bounded Proofs.Lists.Policy)
env -u LEAN_PATH lake build "${lists_proofs[@]}"
lists_tree() {  # lists_tree VERSION MODULE...: the modules over VERSION's lists translation
  local version=$1 tree=$repo_root/.lake/check-tree/interfaces-lists-$1
  shift
  python3 scripts/check-tree.py create "$tree" --replace "Proofs/Lists/Open.lean=$work/lists-$version.lean"
  (cd "$tree" && env -u LEAN_PATH lake build "$@")
}
for version in 0.16.0 0.15.2; do lists_tree "$version" "${lists_proofs[@]}"; done
# Zig 0.14.1: the proofs that take no allocator hold over its translation. The proof text of the
# others does not (docs/interfaces.md#the-list-proofs-over-older-zig-versions): 0.14.1's std names
# the list type `ArrayListAlignedUnmanaged`, so the functions that Append and Policy name
# (`array_list_Aligned_u32_null_*`) do not exist in its translation, and its `mem.Allocator`
# computes the alignment by a call of `Alignment.fromByteUnits` at run time, whose walk in Alloc
# passes Lean's default recursion depth. These proofs are not claimed for 0.14.1.
lists_tree 0.14.1 Proofs.Lists.Linked Proofs.Lists.Bounded
grep -q '^def array_list_ArrayListAlignedUnmanaged_u32_null_append ' "$work/lists-0.14.1.lean"
if grep -q '^def array_list_Aligned_u32_null_append ' "$work/lists-0.14.1.lean"; then
  echo 'interfaces: the 0.14.1 lists translation names the list as the proofs do: add it to the versions above' >&2
  exit 1
fi
# The proofs over the 0.17.1 translations (docs/interfaces.md, proof side), kernel-checked with
# only the standard axioms; ClosureCX (after MixSpec, which it imports) is the counterexample to
# using the environment's contract for a vtable of the program.
for spec in MixSpec ClosureCX RndSpec CallbacksSpec SentinelSpec; do
  { cat "$here/Interfaces/$spec.lean"; echo
    grep -o '^theorem [^ :({\[]*' "$here/Interfaces/$spec.lean" | while read -r _ t; do
      echo "#print axioms Interfaces.$spec.$t"; done; } > "$work/Interfaces/$spec.lean"
  "${lean_cmd[@]}" -R "$work" \
    -o "$work/Interfaces/$spec.olean" "$work/Interfaces/$spec.lean" \
    > "$work/$spec.txt" 2>&1 || { cat "$work/$spec.txt" >&2; exit 1; }
  python3 - "$work/$spec.txt" "$(grep -c '^theorem ' "$here/Interfaces/$spec.lean")" <<'PY'
import re, sys
text, n = open(sys.argv[1]).read(), int(sys.argv[2])
groups = re.findall(r"depends on axioms: \[([^\]]*)\]|(does not depend on any axioms)", text)
used = {a.strip() for g, _ in groups for a in g.split(",") if a.strip()}
assert ": error" not in text and len(groups) == n, text
assert used <= {"propext", "Classical.choice", "Quot.sound"}, text
PY
done
# M04: semantic mutants of the translated std allocator sentinel path (the retained 0.17.1
# Interfaces/Sentinel.lean): the unchanged SentinelSpec proofs must reject each one.
python3 -B tests/roadmap/callbacks/mutants.py generate sentinel "$work/mutants" | while IFS=: read -r name module proofs; do
  mroot="$work/mutants/$name"
  "${lean_cmd[@]}" -R "$mroot" -o "$mroot/${module%.lean}.olean" "$mroot/$module"
  cp "$here/$proofs" "$mroot/$proofs"
  status=0
  LEAN_PATH="$mroot:$LEAN_PATH" "${lean_cmd[@]}" -R "$mroot" "$mroot/$proofs" > "$mroot/log" 2>&1 || status=$?
  python3 -B tests/roadmap/callbacks/mutants.py classify "$name" "$status" "$mroot/log" "$mroot/$proofs"
done
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
echo "interfaces: ok"
