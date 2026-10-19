#!/usr/bin/env bash
# Re-export the AIR fixtures of tests/roadmap/interfaces for every Zig version with the patched
# compilers (scripts/zig-air.sh), keep the call closure of each program's roots (closure.py) and
# refresh provenance.json. Run from anywhere; needs the patched compilers.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/interfaces
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-interfaces-export.XXXXXX")
trap 'rm -rf "$work"' EXIT
# program | source | export filter | roots
programs=(
  "lists|examples/lists/lists.zig|lists.,mem.,math.,array_list.,debug.assert,debug.SafetyLock|lists.push,lists.reverse,lists.freeAll,lists.sum,lists.evens"
  "mix|$here/mix.zig|mix.,mem.,math.,heap.FixedBufferAllocator,debug.assert|mix.make,mix.withFba"
  "rnd|$here/rnd.zig|rnd.,Random.|rnd.roll"
  "sentinel|tests/roadmap/sentinel-realloc/source.zig|source.,mem.,math.,debug.assert|source.make,source.append,source.resize,source.release"
)
for version in 0.17.0 0.16.0 0.15.2 0.14.1; do
  zig=$(scripts/zig-air.sh "$version" | tail -1)
  for entry in "${programs[@]}"; do
    IFS='|' read -r name source filter roots <<< "$entry"
    raw="$work/$version-$name"
    mkdir -p "$raw"
    # The exporter also reports the unrelated std types it skips; the closure decides.
    ZIG_AIR_JSON_DIR="$raw" ZIG_AIR_JSON_FILTER="$filter" "$zig" build-obj -fno-emit-bin \
      -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline "$source" \
      --cache-dir "$work/cache" --global-cache-dir "$work/cache" 2> "$work/export.log" || {
        cat "$work/export.log" >&2; exit 1; }
    rm -rf "$here/air/$version/$name"
    python3 -I "$here/closure.py" "$raw" "$here/air/$version/$name" "$roots"
  done
done
python3 - "$here" <<'PY'
import hashlib, json, pathlib, sys
here = pathlib.Path(sys.argv[1])
root = here.parents[2]
sources = ['mix.zig', 'rnd.zig']
record = {
    'source_sha256': {**{s: hashlib.sha256((here / s).read_bytes()).hexdigest() for s in sources},
                      **{s: hashlib.sha256((root / s).read_bytes()).hexdigest()
                         for s in ('examples/lists/lists.zig', 'tests/roadmap/sentinel-realloc/source.zig')}},
    'air': {'exporter': 'zig-patch/air-json/json.zig of this branch (patched compilers from scripts/zig-air.sh)',
            'target': 'x86_64-linux', 'cpu': 'baseline', 'optimization': 'ReleaseSafe',
            'error_tracing': False, 'closure': 'export.sh: closure.py of each program\'s roots'},
    'air_sha256': {str(p.relative_to(here)): hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in sorted((here / 'air').rglob('*.json'))},
}
(here / 'provenance.json').write_text(json.dumps(record, indent=2) + '\n')
PY
