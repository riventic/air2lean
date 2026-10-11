#!/usr/bin/env bash
# L-series long tail: export each fixture source (`<stem>.zig`) with the patched compilers of
# every supported Zig version into air/<stem>/<version>, or with --check compare a fresh export
# byte for byte with the committed one.
#
#   export.sh [export|--check] [STEM...]      (default: every stem in provenance.json)
#
# The compilers must be built by zig-patch/build.sh from the zig-patch tree of this checkout;
# provenance.json records the hash of each compiler binary (bin/zig-unlocked behind the AIR-only
# lock wrapper). Point AIR2LEAN_ZIG_AIR at a directory holding zig-air-<version>/bin/zig (default
# /opt/dev/air2lean-build, which may hold older builds). --check refuses a compiler whose hash
# differs from the record. On macOS 0.15.2/0.14.1 also need a failing `xcrun` shim first on PATH
# (zig-patch/README.md). After a re-export, run `python3 tests/roadmap/lang-long-tail/test_provenance.py --refresh`.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
here=tests/roadmap/lang-long-tail
root=${AIR2LEAN_ZIG_AIR:-/opt/dev/air2lean-build}
mode=${1:-export}
case "$mode" in export | --check) shift || true ;; *) mode=export ;; esac
stems=("$@")
if [ "${#stems[@]}" -eq 0 ]; then
  read -r -a stems <<< "$(python3 -c 'import json,sys; print(" ".join(sorted(json.load(open(sys.argv[1]))["sources"])))' "$here/provenance.json")"
fi
versions=(0.17.0 0.16.0 0.15.2 0.14.1)
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-lang-long-tail.XXXXXX")
trap 'rm -rf "$work"' EXIT
sha256() { shasum -a 256 "$1" | cut -d' ' -f1; }
for version in "${versions[@]}"; do
  if [ "$mode" = --check ]; then
    recorded=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["patched_compiler_sha256"][sys.argv[2]])' \
      "$here/provenance.json" "$version")
    actual=$(sha256 "$root/zig-air-$version/bin/zig-unlocked")
    [ "$recorded" = "$actual" ] || {
      echo "error: $root/zig-air-$version is not the recorded compiler ($actual, expected $recorded);" \
        "build one with zig-patch/build.sh and set AIR2LEAN_ZIG_AIR" >&2
      exit 1
    }
  fi
  for stem in "${stems[@]}"; do
    out="$work/$stem/$version"
    mkdir -p "$out"
    # <stem>.filter, if present: more AIR name prefixes (the std functions the fixture calls).
    filter="$stem."
    [ -f "$here/$stem.filter" ] && filter="$filter,$(paste -sd, "$here/$stem.filter")"
    ZIG_AIR_JSON_DIR="$out" ZIG_AIR_JSON_FILTER="$filter" \
      "$root/zig-air-$version/bin/zig" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline "$here/$stem.zig"
    # Keep the call/function-value closure of the fixture's own functions: the filter also
    # matches std instances that only the compiler's panic and debug code reaches, and how many
    # depends on the version.
    python3 - "$out" "$stem." <<'PY'
import json, pathlib, re, sys
out, prefix = pathlib.Path(sys.argv[1]), sys.argv[2]
docs = {p: p.read_text() for p in out.glob("*.json")}
by_name = {}
for p, t in docs.items():
    by_name.setdefault(json.loads(t)["name"], []).append(p)
work = [p for n, ps in by_name.items() if n.startswith(prefix) for p in ps]
keep = set()
while work:
    p = work.pop()
    if p in keep:
        continue
    keep.add(p)
    for ref in set(re.findall(r'"func":\s*"([^"]+)"', docs[p])):
        work.extend(by_name.get(ref, []))
for p in docs:
    if p not in keep:
        p.unlink()
PY
    if [ "$mode" = --check ]; then
      diff -r "$out" "$here/air/$stem/$version"
    else
      rm -rf "$here/air/$stem/$version"
      mkdir -p "$here/air/$stem"
      cp -R "$out" "$here/air/$stem/$version"
    fi
  done
done
echo "lang-long-tail exports ($*): $mode ok"
