#!/usr/bin/env bash
# `--allocator-model translated` (P1): std.heap.page_allocator and FixedBufferAllocator clients
# translated from their real AIR down to `posix.mmap`/`munmap`/`mremap` (ZigLean/Os/Mmap.lean).
# P4b: resize/remap/free proved against the full-state FAllocSpec (PageSpec.lean), the alloc
# obstructions (PageObstruction.lean), a mutant (mutant.sh). Needs a built translator and
# `lake build ZigLean ZigLean.Sep.AllocSpec ZigLean.Sep.Mmap ZigLean.Sep.AllocSpec.Ops
# ZigLean.Sep.AllocSpec.Norm ZigLean.Sep.Full.AllocSpec ZigLean.Sep.Full.Tame`; runs no compiler. With
# AIR2LEAN_NATIVE_ZIG (a stock Zig 0.16.0), also builds and runs native.zig and compares it with
# expected.txt (16 KiB pages, recorded on aarch64-macos) or expected-linux.txt (4 KiB pages,
# recorded on x86_64-linux): the output depends on the page size only, not on the OS.
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
# P4b: resize/remap/free against the full-state FAllocSpec (PageSpec.lean), its axioms, and a
# mutant that frees one page too few (mutant.sh).
"${lean_cmd[@]}" -R "$here" -o "$work/PageSpec.olean" "$here/PageSpec.lean"
cat > "$work/Axioms.lean" <<'AX'
import PageSpec
#print axioms AllocTranslated.PageSpec.free_spec
#print axioms AllocTranslated.PageSpec.resize_spec
#print axioms AllocTranslated.PageSpec.remap_spec
AX
"${lean_cmd[@]}" "$work/Axioms.lean" > "$work/axioms.txt"
if grep -v "\[propext, Classical.choice, Quot.sound\]" "$work/axioms.txt" | grep -q .; then
  cat "$work/axioms.txt" >&2; echo 'alloc-translated: unexpected axioms' >&2; exit 1
fi
bash "$here/mutant.sh"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  "$AIR2LEAN_NATIVE_ZIG" build-exe -OReleaseSafe "$here/native.zig" --cache-dir "$work/cache" \
    --global-cache-dir "$work/cache" -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  page_size=$(getconf PAGESIZE)
  case "$page_size" in
    16384) expected=$here/expected.txt ;;
    4096) expected=$here/expected-linux.txt ;;
    *) echo "alloc-translated: no native expectation for $page_size-byte pages" >&2; exit 1 ;;
  esac
  diff "$expected" "$work/native.txt"
fi
echo "alloc-translated: ok"
