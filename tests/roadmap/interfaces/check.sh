#!/usr/bin/env bash
# Open interfaces (docs/interfaces.md): calls through a `std.mem.Allocator`, a `std.Random` or
# E02's `Visitor` callback that the caller passes in. Needs a built translator and `lake build ZigLean ZigLean.Sep.Full.Wrappers
# ZigLean.Sep.Full.Dispatch ZigLean.Sep.Full.Auto ZigLean.Sep.Full.Block ZigLean.Sep.Full.AutoPrim
# ZigLean.Sep.Full.Typed ZigLean.Sep.Full.Try ZigLean.Sep.Full.Region ZigLean.Sep.Full.SentinelBuf
# ZigLean.Sep.Full.RegionEnc`;
# runs no compiler. Every Zig version's exports translate under the registries and elaborate; the
# 0.17.1 translations are the retained ones byte for byte, and the proofs over them
# (Interfaces/*Spec.lean) check; the list proofs (Proofs/Lists, with M03's Policy) build over the
# 0.17.1, 0.16.0 and 0.15.2 lists translations, and those that take no allocator over the 0.14.1
# one; test_cli.py covers the rejections and the closed default. `grow` (growth of a sentinel
# slice itself) has no 0.16.0 export and is proved over 0.17.1 only.
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
  "wide|Wide|Interfaces.Wide|$here/Interfaces/Wide.lean|wide.|$here/air/{v}/wide|$here/registry-alloc.json|--allocator-model translated"
  "kinds|Kinds|Interfaces.Kinds|$here/Interfaces/Kinds.lean|kinds.|$here/air/{v}/kinds|$here/registry-alloc.json|--allocator-model translated"
  "grow|Grow|Interfaces.Grow|$here/Interfaces/Grow.lean|grow.|$here/air/{v}/grow|$here/registry-alloc.json|--allocator-model translated"
  "raw|Raw|Interfaces.Raw|$here/Interfaces/Raw.lean|raw.|$here/air/{v}/raw|$here/registry-alloc.json|--allocator-model translated"
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
    # Zig 0.16.0 rejects `realloc`, `remap` and `resize` of a sentinel slice at compile time:
    # grow.zig has no 0.16.0 export (exports.json).
    if [ "$version:$module" = 0.16.0:Grow ]; then continue; fi
    translate "$version" "$entry" "$work/Interfaces/$module.lean"
    "${lean_cmd[@]}" -R "$work" -o "$work/Interfaces/$module.olean" "$work/Interfaces/$module.lean"
    if [ "$module" = Lists ]; then cp "$work/Interfaces/Lists.lean" "$work/lists-$version.lean"; fi
  done
  # The sentinel proofs (`u8`, the wider item types and the other item kinds) and the proofs of
  # the raw entry points hold for this version's translation too (0.17.1: the axioms loop below).
  if [ "$version" != 0.17.1 ]; then
    for spec in SentinelSpec WideSpec KindsSpec RawSpec; do
      "${lean_cmd[@]}" -R "$work" "$here/Interfaces/$spec.lean" > "$work/$spec-$version.txt" 2>&1 || {
        cat "$work/$spec-$version.txt" >&2; exit 1; }
    done
  fi
  # Growth of the sentinel slice itself is proved over 0.17.1 (the axioms loop below). The std of
  # Zig 0.15.2 and 0.14.1 hands the vtable `len * sz` bytes of the `(len + 1) * sz`-byte grant
  # (`mem.sliceAsBytes`), which is outside `CAllocSpec`: the proofs must stop there, at the
  # contract's length precondition (GrowSpec.lean, "Versions"). A regression pin, so a change of
  # either translation is noticed.
  if [ "$version" = 0.15.2 ] || [ "$version" = 0.14.1 ]; then
    if "${lean_cmd[@]}" -R "$work" "$here/Interfaces/GrowSpec.lean" > "$work/GrowSpec-$version.txt" 2>&1; then
      echo "interfaces: GrowSpec holds over the $version translation: review GrowSpec.lean's versions" >&2
      exit 1
    fi
    # The six theorems that reach `remap` or `resize` (`realloc*_spec`, `move*_grant`,
    # `fit*_grant`) fail, each with that goal; nothing else does.
    [ "$(grep -c 'GrowSpec\.lean:[0-9]*:[0-9]*: error' "$work/GrowSpec-$version.txt")" = 6 ] &&
      [ "$(grep -c '\.len\.toNat = bs\.size$' "$work/GrowSpec-$version.txt")" = 6 ] || {
      cat "$work/GrowSpec-$version.txt" >&2; exit 1; }
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
lists_proofs_no_allocator=(Proofs.Lists.Linked Proofs.Lists.Bounded)
lists_proofs=("${lists_proofs_no_allocator[@]}" Proofs.Lists.Alloc Proofs.Lists.Append Proofs.Lists.Policy)
env -u LEAN_PATH lake build "${lists_proofs[@]}"
lists_tree() {  # lists_tree VERSION MODULE...: the modules over VERSION's lists translation
  local version=$1 tree=$repo_root/.lake/check-tree/interfaces-lists-$1
  shift
  python3 scripts/check-tree.py create "$tree" --replace "Proofs/Lists/Open.lean=$work/lists-$version.lean"
  (cd "$tree" && env -u LEAN_PATH lake build "$@")
}
for version in 0.16.0 0.15.2; do lists_tree "$version" "${lists_proofs[@]}"; done
# Zig 0.14.1: only the proofs that take no allocator; the others are not claimed for it, and why
# their text does not hold there is in docs/interfaces.md#the-list-proofs-over-older-zig-versions.
# One of the two reasons is pinned here, so a translation that changes it is noticed: 0.14.1's std
# names the list type `ArrayListAlignedUnmanaged`, not `Aligned` as Append and Policy do.
if ! grep -q '^def array_list_ArrayListAlignedUnmanaged_u32_null_append ' "$work/lists-0.14.1.lean" ||
    grep -q '^def array_list_Aligned_u32_null_append ' "$work/lists-0.14.1.lean"; then
  echo 'interfaces: the 0.14.1 lists translation no longer names the list ArrayListAlignedUnmanaged:' \
    'review the versions above and docs/interfaces.md' >&2
  exit 1
fi
lists_tree 0.14.1 "${lists_proofs_no_allocator[@]}"
# The proofs over the 0.17.1 translations (docs/interfaces.md, proof side), kernel-checked with
# only the standard axioms; ClosureCX (after MixSpec, which it imports) is the counterexample to
# using the environment's contract for a vtable of the program.
for spec in MixSpec ClosureCX RndSpec CallbacksSpec SentinelSpec WideSpec KindsSpec GrowSpec RawSpec; do
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
# M04: a raw call outside the contract's preconditions has no proof. Interfaces/RawNeg.lean
# states RawSpec's theorems without one precondition each, with RawSpec's proofs: every theorem
# must fail, and where the missing precondition is asked for: the goal the walk leaves (a length
# that may be 0, a length that is not the grant's) or the vtable call it has no rule for (a grant
# at another alignment).
status=0
"${lean_cmd[@]}" -R "$work" "$here/Interfaces/RawNeg.lean" > "$work/RawNeg.txt" 2>&1 || status=$?
python3 - "$here/Interfaces/RawNeg.lean" "$work/RawNeg.txt" "$status" <<'PY'
import re, sys
source, text, status = open(sys.argv[1]).read().splitlines(), open(sys.argv[2]).read(), sys.argv[3]
goal, call = "goal", "call"  # where the expected text is: after the error line, or before it
want = {
    "take_zero": (goal, "⊢ 0 < n.toNat\n"), "fit_zero": (goal, "⊢ 0 < n.toNat\n"),
    "move_zero": (goal, "⊢ 0 < n.toNat\n"), "give_other_length": (goal, "⊢ m.len.toNat = bs.size\n"),
    "give_other_alignment": (call, "fsym: no rule for the command\n  extCall (Ext.call3 fns.free ctx m mem_Alignment.«4» "),
    "fit_other_alignment": (call, "fsym: no rule for the command\n  extCall (Ext.call1 fns.resize ctx m mem_Alignment.«4» "),
}
assert status == "1", f"RawNeg.lean: Lean exit {status}, want 1\n{text}"
assert set(want) == set(re.findall(r"^theorem (\S+)", "\n".join(source), re.M)), "RawNeg.lean: theorems"
errors = [(m.start(), int(m.group(1))) for m in re.finditer(r"RawNeg\.lean:(\d+):\d+: error", text)]
bounds = [0] + [at for at, _ in errors] + [len(text)]
seen = set()
for index, (at, line) in enumerate(errors):
    name = next(m.group(1) for l in reversed(source[:line]) if (m := re.match(r"theorem (\S+)", l)))
    where, expected = want[name]
    block = text[at:bounds[index + 2]] if where == goal else text[bounds[index]:at]
    assert expected in block, f"RawNeg.{name}: does not stop at its precondition:\n{block}"
    # A call's text precedes its error, after the previous theorem's goals: it is this theorem's
    # only if no other theorem prints it.
    assert where == goal or text.count(expected) == 1, f"RawNeg.{name}: {expected!r} is not unique"
    seen.add(name)
assert seen == set(want), f"RawNeg.lean: no error in {sorted(set(want) - seen)}\n{text}"
calls = sum(where == call for where, _ in want.values())
assert text.count("fsym: no rule for the command") == calls, f"RawNeg.lean: want {calls} calls without a rule\n{text}"
print(f"RawNeg: {len(seen)} statements without a precondition have no proof")
PY
# M04: semantic mutants of the translated std allocator sentinel path (the retained 0.17.1
# Interfaces/Sentinel.lean, for item types wider than a byte Interfaces/Wide.lean, and for growth
# of the sentinel slice itself Interfaces/Grow.lean): the unchanged SentinelSpec, WideSpec and
# GrowSpec proofs must reject each one.
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
