#!/usr/bin/env bash
# `--allocator-model translated` (P1): std.heap.page_allocator and FixedBufferAllocator clients
# translated from their real AIR down to `posix.mmap`/`munmap`/`mremap` (ZigLean/Os/Mmap.lean).
# Needs a built translator and `lake build ZigLean ZigLean.Sep.AllocSpec`; runs no compiler. With
# AIR2LEAN_NATIVE_ZIG (a stock Zig 0.16.0), also builds and runs native.zig and compares it with
# expected.txt (aarch64-macos, 16 KiB pages) or expected-linux.txt (x86_64-linux, 4 KiB pages).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-translated
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-translated.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocTranslated"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
python3 - "$here" <<'EOF'
import hashlib, json, pathlib, sys
here = pathlib.Path(sys.argv[1])
record = json.loads((here / 'provenance.json').read_text())
for name, digest in record['source_sha256'].items():
    assert hashlib.sha256((here / name).read_bytes()).hexdigest() == digest, name
files = {str(p.relative_to(here / 'air')): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in sorted((here / 'air').rglob('*.json'))}
assert files == record['air_sha256'], 'AIR fixtures differ from provenance.json'
EOF
for prog in page fba; do
  for os in linux macos; do
    Prog="$(printf '%s' "${prog:0:1}" | tr '[:lower:]' '[:upper:]')${prog:1}"
    Os="$(printf '%s' "${os:0:1}" | tr '[:lower:]' '[:upper:]')${os:1}"
    module="$Prog$Os"
    # The retained translation is the fresh one, byte for byte.
    "$translator" "$here/air/0.16.0/$prog-$os" -o "$work/AllocTranslated/$module.lean" \
      --namespace "AllocTranslated.$module" --prefix "$prog." --allocator-model translated
    cmp "$work/AllocTranslated/$module.lean" "$here/AllocTranslated/$module.lean"
    "${lean_cmd[@]}" -R "$work" -o "$work/AllocTranslated/$module.olean" "$work/AllocTranslated/$module.lean"
  done
done
"${lean_cmd[@]}" "$here/Eval.lean"
# P4b: the translated PageAllocator cannot satisfy AllocSpec (docs/alloc-page.md).
"${lean_cmd[@]}" "$here/PageObstruction.lean"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  "$AIR2LEAN_NATIVE_ZIG" build-exe -OReleaseSafe "$here/native.zig" --cache-dir "$work/cache" \
    --global-cache-dir "$work/cache" -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  expected=$here/expected.txt
  if [ "$(uname -s)" = Linux ]; then expected=$here/expected-linux.txt; fi
  diff "$expected" "$work/native.txt"
fi
echo "alloc-translated: ok"
