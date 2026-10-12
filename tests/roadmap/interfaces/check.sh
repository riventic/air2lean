#!/usr/bin/env bash
# Open interfaces (docs/interfaces.md): calls through a `std.mem.Allocator` or `std.Random` that
# the caller passes in. Needs a built translator and `lake build ZigLean`; runs no compiler. Every
# Zig version's exports translate under the registries and elaborate; the 0.17.0 translations are
# the retained ones byte for byte; test_cli.py covers the rejections and the closed default.
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
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
echo "interfaces: ok"
