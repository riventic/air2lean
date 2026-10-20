#!/usr/bin/env bash
# `--allocator-model translated` (P1): std.heap.page_allocator and FixedBufferAllocator clients
# translated from their real AIR down to `posix.mmap`/`munmap`/`mremap` (ZigLean/Os/Mmap.lean).
# P4b: resize/remap/free proved against the full-state FAllocSpec (PageSpec.lean,
# PageSpecMacos.lean), the whole vtable with alloc for every alignment (PageAlloc.lean), the
# obstructions (PageObstruction.lean), the O5 regressions (PageAlloc.alloc_high, alloc_top, alloc_edge), a
# mutant (mutant.sh); the four entries as thread triples and CAllocSpec (PageThread.lean); the
# memory-safety tutorial's refuted clients over the page allocator (ListsPage.lean). Every Lean
# file is a module of the fixture's library AllocTranslated (tests/roadmap/lakefile.toml), built
# by Lake with what it imports (scripts/fixtures.py; run it under scripts/build-guard.py). Needs
# a built translator; runs no compiler. With
# AIR2LEAN_NATIVE_ZIG (a stock Zig 0.16.0), also builds and runs native.zig and compares it with
# expected.txt (16 KiB pages, recorded on aarch64-macos) or expected-linux.txt (4 KiB pages,
# recorded on x86_64-linux): the output depends on the page size only, not on the OS.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-translated
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-translated.XXXXXX")
trap 'rm -rf "$work"' EXIT
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
    # The retained translation is the fresh one, byte for byte (Lake builds the retained file).
    "$translator" "$here/air/0.16.0/$prog-$os" -o "$work/$module.lean" \
      --namespace "AllocTranslated.$module" --prefix "$prog." --allocator-model translated
    cmp "$work/$module.lean" "$here/AllocTranslated/$module.lean"
  done
done
# The library: the translations, AllocTranslated/Eval.lean (`#guard`s), P4b's obstruction (the
# translated PageAllocator cannot satisfy AllocSpec, docs/alloc-page.md: PageObstruction.lean),
# resize/remap/free against the full-state FAllocSpec (PageSpec.lean for x86_64-linux,
# PageSpecMacos.lean for aarch64-macos: the invariant PageTok.lean and `fsym`), PageAlloc,
# PageThread, PageCreation, ListsPage and KernelBytes.
python3 -B scripts/fixtures.py build AllocTranslated
# Axioms of every theorem of the proof modules, from the built environment: only the standard
# ones. A mutant whose shrink leaks the cut pages fails PageSpec (mutant.sh).
theorems=()
for name in KernelBytes.start_admissible KernelBytes.push_succeeds ListsPage.controls \
    ListsPage.reuse_happens ListsPage.pushThenFree_returns PageThread.fthread_alloc \
    PageThread.fthread_free PageThread.fthread_resize PageThread.fthread_remap PageThread.cAllocSpec \
    PageAlloc.fallocSpec PageAlloc.fallocSpec.creation PageAlloc.fallocSpec.creation_input_at \
    PageAlloc.fallocSpec.creation_admission PageThread.cAllocSpec.creation \
    PageAlloc.alloc_run PageSpec.free_spec PageSpec.resize_spec PageSpec.remap_spec \
    PageSpecMacos.free_spec PageSpecMacos.resize_spec PageSpecMacos.remap_spec; do
  theorems+=(--declaration "AllocTranslated.$name")
done
python3 -B scripts/fixtures.py audit PageObstruction PageTok PageSpec PageSpecMacos PageAlloc PageThread PageCreation \
  ListsPage KernelBytes "${theorems[@]}"
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
