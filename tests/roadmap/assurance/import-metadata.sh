#!/usr/bin/env bash
# Actual import headers include modules unused by the declaration graph. Also run by check.sh.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
report=${1:-.lake/assurance/regressions/import-metadata.json}
import_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-import-metadata.XXXXXX")
trap 'rm -rf "$import_dir"' EXIT
mkdir -p "$import_dir/src/AssuranceImportFixture" "$import_dir/lib/AssuranceImportFixture"
printf '%s\n' 'module' 'namespace AssuranceImportFixture' 'def unused : Nat := 37' \
  'end AssuranceImportFixture' > "$import_dir/src/AssuranceImportFixture/Leaf.lean"
printf '%s\n' 'module' 'public import AssuranceImportFixture.Leaf' \
  > "$import_dir/src/AssuranceImportFixture/Bridge.lean"
printf '%s\n' 'import AssuranceImportFixture.Bridge' 'namespace AssuranceImportFixture' \
  'theorem header_checked : True := True.intro' 'end AssuranceImportFixture' \
  > "$import_dir/src/AssuranceImportFixture/Root.lean"
for module in Leaf Bridge Root; do
  LEAN_PATH="$import_dir/lib${LEAN_PATH:+:$LEAN_PATH}" lake env lean -R "$import_dir/src" \
    -o "$import_dir/lib/AssuranceImportFixture/$module.olean" \
    "$import_dir/src/AssuranceImportFixture/$module.lean"
done
LEAN_PATH="$import_dir/lib${LEAN_PATH:+:$LEAN_PATH}" scripts/assumptions.sh --no-build \
  --module AssuranceImportFixture.Root --output "$report"
python3 - "$report" <<'PY'
import json, sys
from pathlib import Path
report = json.loads(Path(sys.argv[1]).read_text())
assert report['status'] == 'pass', report.get('violations')
headers = report['module_imports']
assert 'AssuranceImportFixture.Bridge' in headers['AssuranceImportFixture.Root'], headers
assert 'AssuranceImportFixture.Leaf' in headers['AssuranceImportFixture.Bridge'], headers
assert isinstance(headers['AssuranceImportFixture.Leaf'], list), headers
assert not any(node['module'] in {'AssuranceImportFixture.Leaf', 'AssuranceImportFixture.Bridge'}
               for node in report['nodes']), report['nodes']
assert {t['name'] for t in report['theorems']} == {'AssuranceImportFixture.header_checked'}
print('assurance unused transitive import metadata regression passed')
PY
