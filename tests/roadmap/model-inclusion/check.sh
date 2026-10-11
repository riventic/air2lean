#!/usr/bin/env bash
# W3 model-inclusion gate (docs/std-models.md §Caller-supplied allocator and Io): each native
# result with a REAL std allocator or std.Io implementation must be one of the model's
# outcomes; known divergences are expected failures (expected.json). See inclusion.py.
#
# Needs stock Zig 0.16.0 (native runs), the patched 0.16.0 exporter (audit probes, exported for
# x86_64-linux as in tests/roadmap/architecture-audit/models/check.sh) and the difftest binary
# that `AIR2LEAN_EXAMPLES="lists sync iogroup" scripts/diff.sh` builds. Run from any directory;
# heavy steps belong under scripts/build-guard.py.
#
# Env: AIR2LEAN_ZIG_NATIVE  stock 0.16.0 (default ~/.cache/air2lean/host-0.16.0/zig)
#      AIR2LEAN_ZIG_AIR     patched 0.16.0 (default /opt/dev/air2lean-build/zig-air-0.16.0/bin/zig)
#      AIR2LEAN_INCLUSION_RUNS      native runs per Io function (default 8, at most 20)
#      AIR2LEAN_INCLUSION_EVIDENCE  evidence output (default: the committed evidence.json)
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd "$here/../../.." && pwd)
stock=${AIR2LEAN_ZIG_NATIVE:-$HOME/.cache/air2lean/host-0.16.0/zig}
patched=${AIR2LEAN_ZIG_AIR:-/opt/dev/air2lean-build/zig-air-0.16.0/bin/zig}
runs=${AIR2LEAN_INCLUSION_RUNS:-8}
evidence=${AIR2LEAN_INCLUSION_EVIDENCE:-$here/evidence.json}
difftest=$repo/tests/diff/.lake/build/bin/difftest
audit=tests/roadmap/architecture-audit/models
[ -x "$difftest" ] || {
  echo "error: build the difftest first: AIR2LEAN_EXAMPLES='lists sync iogroup' scripts/diff.sh" >&2
  exit 2
}
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-model-inclusion.XXXXXX")
trap 'rm -rf "$work"' EXIT
cd "$repo"

native() {
  "$stock" build-exe -OReleaseSafe -mcpu=baseline --cache-dir "$work/cache" \
    --global-cache-dir "$work/gcache" "$@"
}
echo "== building native harnesses ==" >&2
native -femit-bin="$work/lists_native" --dep lists --dep common -Mroot="$here/lists_native.zig" \
  -Mlists=examples/lists/lists.zig -Mcommon=tests/diff/common.zig
native -femit-bin="$work/io_native" --dep sync --dep iogroup --dep io_probe \
  -Mroot="$here/io_native.zig" -Msync=examples/sync/sync.zig -Miogroup=examples/iogroup/iogroup.zig \
  -Mio_probe="$audit/io_probe.zig"
native -femit-bin="$work/probe_native" --dep alloc_probe -Mroot="$here/probe_native.zig" \
  -Malloc_probe="$audit/alloc_probe.zig"

echo "== lists: real allocators, model over allocation policies ==" >&2
for kind in page fixed_buffer arena debug; do
  mkdir -p "$work/native-$kind/tests/diff/lists"
  ln -s "$repo/tests/diff/lists/inputs" "$work/native-$kind/tests/diff/lists/inputs"
  (cd "$work/native-$kind" && "$work/lists_native" "$kind")
done
python3 -B "$here/inclusion.py" policy-inputs tests/diff/lists/inputs \
  "$work/model-lists/tests/diff/lists/inputs"
(cd "$work/model-lists" && AIR2LEAN_EXAMPLES=lists "$difftest")

echo "== std.Io: Threaded and global_single_threaded, model by schedule search ==" >&2
for kind in threaded single_threaded; do
  python3 -B "$here/inclusion.py" io-native "$work/io_native" "$kind" "$work/io-$kind" "$runs" 10
  (cd "$work/io-$kind" && AIR2LEAN_EXAMPLES="sync iogroup" "$difftest")
done

echo "== architecture-audit probes ==" >&2
for kind in page fixed_buffer arena debug; do
  "$work/probe_native" "$kind" 2> "$work/probe-native-$kind.txt"
done
for probe in alloc io; do
  mkdir "$work/$probe-air"
  host=native.zig namespace=AuditAlloc runner=Runner.lean
  if [ "$probe" = io ]; then host=io_native.zig namespace=AuditIo runner=IoRunner.lean; fi
  ZIG_AIR_JSON_DIR="$work/$probe-air" ZIG_AIR_JSON_FILTER="${probe}_probe." \
    "$patched" build-exe -fno-emit-bin -OReleaseSafe -fno-error-tracing -mcpu=baseline \
    -target x86_64-linux "$audit/$host" --cache-dir "$work/air-cache" --global-cache-dir "$work/air-gcache"
  .lake/build/bin/air2lean "$work/$probe-air" -o "$work/$namespace.lean" --namespace "$namespace" \
    --prefix "${probe}_probe."
  cat "$work/$namespace.lean" "$audit/$runner" > "$work/${namespace}Runtime.lean"
  lake env lean --run "$work/${namespace}Runtime.lean" >> "$work/probe-model.txt"
done

python3 -B "$here/inclusion.py" check "$work" --evidence "$evidence"
