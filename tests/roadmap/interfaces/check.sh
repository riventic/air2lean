#!/usr/bin/env bash
# Open interfaces (docs/interfaces.md): calls through a `std.mem.Allocator` or `std.Random` that
# the caller passes in. Needs a built translator and `lake build ZigLean ZigLean.Sep.Full.Wrappers
# ZigLean.Sep.Full.Dispatch ZigLean.Sep.Full.Auto ZigLean.Sep.Full.Block ZigLean.Sep.Full.AutoPrim
# ZigLean.Sep.Full.Typed ZigLean.Sep.Full.Pinned ZigLean.Sep.Full.Try ZigLean.Sep.Full.Region`;
# runs no compiler. Every Zig version's exports translate under the registries and elaborate; the
# 0.17.0 translations are the retained ones byte for byte, and the proofs over them
# (Interfaces/*Spec.lean) check; test_cli.py covers the rejections and the closed default.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/interfaces
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-interfaces.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/Interfaces"
python3 - "$here" <<'PY'
import hashlib, json, pathlib, sys
here = pathlib.Path(sys.argv[1])
root = here.parents[2]
record = json.loads((here / 'provenance.json').read_text())
for name, digest in record['source_sha256'].items():
    path = root / name if '/' in name else here / name
    assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, name
files = {str(p.relative_to(here)): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in sorted((here / 'air').rglob('*.json'))}
assert files == record['air_sha256'], 'AIR fixtures differ from provenance.json'
PY
# program | module | prefix | registry | extra translator options
programs=(
  "lists|Lists|lists.|alloc|--allocator-model translated"
  "mix|Mix|mix.|alloc|--allocator-model translated"
  "rnd|Rnd|rnd.|random|"
)
translate() {  # translate VERSION ENTRY OUT
  local name module prefix registry extra
  IFS='|' read -r name module prefix registry extra <<< "$2"
  # shellcheck disable=SC2086
  "$translator" "$here/air/$1/$name" -o "$3" --namespace "Interfaces.$module" --prefix "$prefix" \
    --profile abi64-le-v1 --model-registry "$here/registry-$registry.json" $extra
}
for version in 0.16.0 0.15.2 0.14.1 0.17.0; do
  for entry in "${programs[@]}"; do
    module=$(cut -d'|' -f2 <<< "$entry")
    translate "$version" "$entry" "$work/Interfaces/$module.lean"
    "${lean_cmd[@]}" -R "$work" -o "$work/Interfaces/$module.olean" "$work/Interfaces/$module.lean"
  done
done
# The retained translations are the fresh 0.17.0 ones (the last loop round).
for entry in "${programs[@]}"; do
  module=$(cut -d'|' -f2 <<< "$entry")
  cmp "$work/Interfaces/$module.lean" "$here/Interfaces/$module.lean"
done
# The proofs over the 0.17.0 translations (docs/interfaces.md, proof side), kernel-checked with
# only the standard axioms; ClosureCX (after MixSpec, which it imports) is the counterexample to
# using the environment's contract for a vtable of the program.
for spec in ListsSpec MixSpec ClosureCX; do
  { cat "$here/Interfaces/$spec.lean"; echo
    grep -o '^theorem [^ :({\[]*' "$here/Interfaces/$spec.lean" | while read -r _ t; do
      echo "#print axioms Interfaces.$spec.$t"; done; } > "$work/Interfaces/$spec.lean"
  LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}" "${lean_cmd[@]}" -R "$work" \
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
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
echo "interfaces: ok"
