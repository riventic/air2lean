#!/usr/bin/env bash
# Architecture audit (models): native-vs-model counterexamples for the allocator and std.Io
# models. Exports AIR of alloc_probe.zig and io_probe.zig with the patched 0.16.0 exporter, translates it in the default
# `--allocator-model std`, runs the generated Lean under several allocation policies, and runs
# the same functions natively with real std allocators and std.Io.Threaded. Exits 0 when the divergence is present
# (the fixture documents it); exits 1 if model and native agree (divergence fixed: update docs).
#
# Env: AIR2LEAN_ZIG_AIR (patched 0.16.0, default /opt/dev/air2lean-build/zig-air-0.16.0/bin/zig)
#      AIR2LEAN_ZIG_NATIVE (stock 0.16.0, default ~/.cache/air2lean/host-0.16.0/zig)
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
patched=${AIR2LEAN_ZIG_AIR:-/opt/dev/air2lean-build/zig-air-0.16.0/bin/zig}
stock=${AIR2LEAN_ZIG_NATIVE:-$HOME/.cache/air2lean/host-0.16.0/zig}
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-audit-models.XXXXXX")
echo "work dir: $work"
cd "$repo"
lake build air2lean ZigLean
mkdir "$work/air"
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER='alloc_probe.' \
  "$patched" build-exe -fno-emit-bin -OReleaseSafe -fno-error-tracing -mcpu=baseline \
  -target x86_64-linux "$here/native.zig" --cache-dir "$work/air-cache" \
  --global-cache-dir "$work/air-gcache"
.lake/build/bin/air2lean "$work/air" -o "$work/Gen.lean" --namespace AuditAlloc \
  --prefix 'alloc_probe.'
cp "$work/Gen.lean" "$work/Runtime.lean"
cat "$here/Runner.lean" >> "$work/Runtime.lean"
lake env lean --run "$work/Runtime.lean" > "$work/model.txt"
"$stock" build-exe -OReleaseSafe -fno-error-tracing -femit-bin="$work/native" \
  "$here/native.zig" --cache-dir "$work/native-cache" --global-cache-dir "$work/native-gcache"
"$work/native" 2> "$work/native.txt"
# std.Io: Group.cancel / cancelable futexWait.
mkdir "$work/io-air"
ZIG_AIR_JSON_DIR="$work/io-air" ZIG_AIR_JSON_FILTER='io_probe.' \
  "$patched" build-exe -fno-emit-bin -OReleaseSafe -fno-error-tracing -mcpu=baseline \
  -target x86_64-linux "$here/io_native.zig" --cache-dir "$work/air-cache" \
  --global-cache-dir "$work/air-gcache"
.lake/build/bin/air2lean "$work/io-air" -o "$work/IoGen.lean" --namespace AuditIo \
  --prefix 'io_probe.'
cp "$work/IoGen.lean" "$work/IoRuntime.lean"
cat "$here/IoRunner.lean" >> "$work/IoRuntime.lean"
lake env lean --run "$work/IoRuntime.lean" >> "$work/model.txt"
"$stock" build-exe -OReleaseSafe -fno-error-tracing -femit-bin="$work/io-native" \
  "$here/io_native.zig" --cache-dir "$work/native-cache" --global-cache-dir "$work/native-gcache"
"$work/io-native" 2>> "$work/native.txt"
status=0; timeout 10 "$work/io-native" single 2>> "$work/native.txt" || status=$?
echo "handoffProbe(single_threaded)=exit:$status" >> "$work/native.txt"
echo "--- model"; cat "$work/model.txt"
echo "--- native"; cat "$work/native.txt"
python3 -I -B - "$work" <<'PY'
import sys
from pathlib import Path
w = Path(sys.argv[1])
model = (w / 'model.txt').read_text().split()
native = (w / 'native.txt').read_text().split()
assert native == ['aliasProbe(FixedBufferAllocator)=42', 'remapProbe(page_allocator)=1',
                  'cancelProbe(Threaded)=1', 'handoffProbe(single_threaded)=exit:124'], native
# The model never yields 42 / 1 under any policy the runner enumerates.
assert all(not x.endswith('=42') for x in model if x.startswith('aliasProbe')), model
assert all(not x.endswith('=1') for x in model if x.startswith('remapProbe')), model
assert [x for x in model if x.startswith('cancelProbe')] == ['cancelProbe=error:Zig.Error.deadlock'], model
handoff = {x for x in model if x.startswith('handoffProbe')}
assert 'handoffProbe=5' in handoff and handoff <= {'handoffProbe=5', 'handoffProbe=no-result'}, model
print('divergences present: model results differ from native std allocators and std.Io (see docs/architecture-audit/models.md)')
PY
