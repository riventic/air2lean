#!/usr/bin/env bash
# Regenerate committed Lean from checked AIR only. Uses an already-built translator;
# does not invoke Zig, Lake, or Lean. Root runs this in its monitored validation queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"
if [ "$#" -gt 1 ]; then echo 'usage: regenerate.sh [TRANSLATOR]' >&2; exit 2; fi
translator=${1:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo "error: build the translator first: $translator" >&2; exit 1; }
case "$translator" in /*) ;; *) translator="$repo_root/$translator" ;; esac
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-regenerate.XXXXXX")
trap 'rm -rf "$work"' EXIT
python3 - "$repo_root" "$work" <<'PY'
import json
import pathlib
import re
import shutil
import sys

root, work = map(pathlib.Path, sys.argv[1:])
tasks = []
for target in sorted((root / 'Proofs').glob('*/Gen.lean')):
    example = target.parent.name.lower()
    versions = root / 'examples' / example / 'zig-versions'
    version = versions.read_text().splitlines()[-1] if versions.exists() else '0.16.0'
    tasks.append((target, example, version, 'linux'))
for target in sorted((root / 'tests/golden').glob('0.*/*/Gen*.lean')):
    example, version = target.parent.name, target.parent.parent.name
    host = target.stem.removeprefix('Gen-') if target.stem.startswith('Gen-') else 'linux'
    tasks.append((target, example, version, host))

with (work / 'manifest.tsv').open('w') as manifest:
    for index, (target, example, version, host) in enumerate(tasks):
        # Later directories replace every instance of a generic function together, matching
        # scripts/check.sh. Copying by filename alone leaves obsolete generic instances.
        selected = {}
        for directory in [root / 'tests/golden' / example / 'air',
                          root / 'tests/golden' / version / example / 'air',
                          root / 'tests/golden' / version / example / ('air-' + host)]:
            groups = {}
            for path in sorted(directory.glob('*.json')):
                name = json.loads(path.read_text())['name']
                group = re.sub(r'__anon_[0-9]+', '__anon_N', name)
                groups.setdefault(group, []).append(path)
            selected.update(groups)
        if not selected:
            raise SystemExit(f'no checked AIR for {example} {version} {host}')
        air = work / str(index)
        air.mkdir()
        sources = [path for group in sorted(selected) for path in selected[group]]
        for source_index, source in enumerate(sources):
            shutil.copyfile(source, air / f'{source_index:05d}-{source.name}')
        namespace = example[:1].upper() + example[1:]
        manifest.write(f'{air}\t{target}\t{namespace}\t{example}\n')
PY
while IFS=$'\t' read -r air target namespace example; do
  args=(--namespace "$namespace" --prefix "$example.")
  if [ -f "examples/$example/translate.args" ]; then
    while IFS= read -r line || [ -n "$line" ]; do
      # translate.args is intentionally a whitespace-separated argv file, not shell code.
      [ -n "${line//[[:space:]]/}" ] || continue
      read -r -a words <<< "$line"
      args+=("${words[@]}")
    done < "examples/$example/translate.args"
  fi
  echo "regenerate: ${target#$repo_root/}" >&2
  "$translator" "$air" -o "$air/Gen.lean" "${args[@]}"
  cp "$air/Gen.lean" "$target"
done < "$work/manifest.tsv"
echo 'checked AIR translations regenerated'
