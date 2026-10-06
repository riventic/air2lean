#!/usr/bin/env bash
# ROOT-only, sequential in prepared 9bc container. No preparation/bootstrap.
set -euo pipefail
cd "${DEADLINE_SOURCE_ROOT:?set extracted frozen source root}"
stock=/opt/toolchains/host-zig-70e49664a74374b48b51e6f3fdfbf437f6395d42509050588bd49abe52ba3d00/zig
patched=/opt/toolchains/zig-air-0.16.0-08aafd77594961a31e69e2a9076f88856dbb6fdd73d080cc96c40aff7b6e023e/bin/zig
out=${DEADLINE_PROBE_OUT:-/artifacts/deadline-futex-probe}
test ! -e "$out"
mkdir -p "$out/air"
export ZIG_GLOBAL_CACHE_DIR=/opt/toolchains/zig-global
sha256sum "$stock" "$patched" tests/roadmap/deadline-futex/*.zig > "$out/source-tool.sha256"
"$stock" version > "$out/stock-version.txt"
"$patched" version > "$out/patched-version.txt"
# Preserve actual pinned API source; Thread.Futex is absent in this version.
cp "$(dirname "$stock")/lib/std/Io.zig" "$out/Io.zig"
cp "$(dirname "$stock")/lib/std/Thread.zig" "$out/Thread.zig"
ZIG_AIR_JSON_DIR="$out/air" ZIG_AIR_JSON_FILTER=probe. \
  "$patched" build-obj tests/roadmap/deadline-futex/probe.zig \
    -OReleaseSafe -target x86_64-linux-musl -mcpu=baseline \
    -fno-error-tracing -fno-emit-bin > "$out/export.log" 2>&1
# Inventory actual tags/callees. No translator/model acceptance is implied.
python3 - "$out/air" > "$out/lowering.json" <<'PY'
import json, sys
from pathlib import Path
result = {}
for p in sorted(Path(sys.argv[1]).glob('*.json')):
    doc = json.loads(p.read_text())
    tags, calls = set(), set()
    def visit(x):
        if isinstance(x, dict):
            if isinstance(x.get('tag'), str): tags.add(x['tag'])
            if isinstance(x.get('func'), str): calls.add(x['func'])
            for value in x.values(): visit(value)
        elif isinstance(x, list):
            for value in x: visit(value)
    visit(doc)
    result[p.name] = dict(name=doc.get('name'), tags=sorted(tags), calls=sorted(calls), profile=doc.get('profile'))
assert len(result) >= 4, 'missing public probe exports'
print(json.dumps(result, sort_keys=True, indent=2))
PY
native_source=${DEADLINE_NATIVE_SOURCE:-tests/roadmap/deadline-futex/native.zig}
"$stock" build-exe -OReleaseSafe -target x86_64-linux-musl -mcpu=baseline -lc \
  --dep probe -Mroot="$native_source" \
  -Mprobe=tests/roadmap/deadline-futex/probe.zig -femit-bin="$out/native" \
  > "$out/native-build.log" 2>&1
timeout 10 "$out/native" > "$out/native.log" 2>&1
sha256sum "$stock" "$patched" tests/roadmap/deadline-futex/*.zig > "$out/source-tool-after.sha256"
cmp "$out/source-tool.sha256" "$out/source-tool-after.sha256"
