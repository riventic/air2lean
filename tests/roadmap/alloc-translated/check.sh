#!/usr/bin/env bash
# `--allocator-model translated` (P1): std.heap.page_allocator and FixedBufferAllocator clients
# translated from their real AIR down to `posix.mmap`/`munmap`/`mremap` (ZigLean/Os/Mmap.lean).
# P4b: resize/remap/free proved against the full-state FAllocSpec (PageSpec.lean,
# PageSpecMacos.lean), the whole vtable with alloc for alignments up to a page (PageAlloc.lean for
# x86_64-linux, PageAllocMacos.lean for aarch64-macos, over the hint state of PageTok.lean), the
# obstructions (PageObstruction.lean), the O5 regressions (PageAlloc.alloc_high, alloc_top, alloc_edge), a
# mutant (mutant.sh); the four entries as thread triples and CAllocSpec (PageThread.lean for
# x86_64-linux, PageThreadMacos.lean for aarch64-macos); the memory-safety tutorial's refuted
# clients over the page allocator (ListsPage.lean). Every Lean file is a module of the fixture's library AllocTranslated (tests/roadmap/lakefile.toml), built
# by Lake with what it imports (scripts/fixtures.py; run it under scripts/build-guard.py). Needs
# a built translator; runs no compiler. The AIR of both programs is exports.json's export, pinned
# by exports.lock.json (scripts/fixture-exports.py), of Zig 0.17.1 and 0.16.0: the retained
# translations are 0.17.1's, and the same proofs, audit, `#guard`s and growth lines are checked
# over the 0.16.0 ones in a check tree (scripts/check-tree.py).
# M02: the model's lines of the growths by `remap` and `realloc` (in place, moved, failed, the
# read of a moved block's old address; Eval.lean `growLinux`, `growMacos`), and those of the fixed
# buffer (`fbaGrowLinux`, `fbaGrowMacos`), are compared with the `page_grow` and `fba_grow` lines
# of expected-linux.txt and expected.txt on every host. With
# AIR2LEAN_NATIVE_ZIG (a stock Zig 0.16.0 or 0.17.1), also builds and runs native.zig and compares it with
# expected.txt (16 KiB pages, recorded on aarch64-macos) or expected-linux.txt (4 KiB pages,
# recorded on x86_64-linux): the output depends on the page size only, not on the OS. So the
# model and the native run of one target are compared with the same file.
# M03: with AIR2LEAN_NATIVE_ZIG also the requests above 1 MiB (`page_large`): the model's lines
# come from the compiled runner `alloc-translated-large` (AllocTranslated/Large.lean; Lean's
# interpreter does not run them), which links the float library's archive that the stock Zig
# builds (scripts/diff.sh --build-only). It is built and run in check trees, one per Zig version
# (the checkout gets no archive and no executable), and compared with the same two files.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-translated
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-translated.XXXXXX")
trap 'rm -rf "$work"' EXIT
python3 -B scripts/fixture-exports.py check alloc-translated
module() {  # module PROG OS: the translation's module name, `PageLinux` for `page linux`
  printf '%s%s%s%s' "$(printf '%s' "${1:0:1}" | tr '[:lower:]' '[:upper:]')" "${1:1}" \
    "$(printf '%s' "${2:0:1}" | tr '[:lower:]' '[:upper:]')" "${2:1}"
}
translate() {  # translate VERSION PROG OS OUT: OUT is AllocTranslated.<module> of that AIR
  "$translator" "$here/air/$1/$2-$3" -o "$4" --namespace "AllocTranslated.$(module "$2" "$3")" \
    --prefix "$2." --allocator-model translated
}
# The retained translations are the fresh ones of Zig 0.17.1, byte for byte (Lake builds the
# retained files). The 0.16.0 ones replace them in the check tree (below).
replace=()
for prog in page fba; do
  for os in linux macos; do
    m=$(module "$prog" "$os")
    translate 0.17.1 "$prog" "$os" "$work/$m.lean"
    cmp "$work/$m.lean" "$here/AllocTranslated/$m.lean"
    translate 0.16.0 "$prog" "$os" "$work/$m-0.16.0.lean"
    replace+=(--replace "$here/AllocTranslated/$m.lean=$work/$m-0.16.0.lean")
  done
done
# Axioms of every theorem of the proof modules (below): only the standard ones.
theorems=()
for name in KernelBytes.start_admissible KernelBytes.push_succeeds ListsPage.controls \
    ListsPage.reuse_happens ListsPage.pushThenFree_returns PageThread.fthread_alloc \
    PageThread.fthread_free PageThread.fthread_resize PageThread.fthread_remap PageThread.cAllocSpec \
    PageAlloc.fallocSpec PageAlloc.fallocSpec.creation PageAlloc.fallocSpec.creation_input_at \
    PageAlloc.fallocSpec.creation_admission PageThread.cAllocSpec.creation \
    PageAlloc.alloc_run PageSpec.free_spec PageSpec.resize_spec PageSpec.remap_spec \
    PageSpecMacos.free_spec PageSpecMacos.free_dead_spec PageSpecMacos.resize_spec \
    PageSpecMacos.remap_spec PageAllocMacos.alloc_ct PageAllocMacos.fallocSpec \
    PageAllocMacos.fallocSpec.creation PageAllocMacos.fallocSpec.creation_input_at \
    PageAllocMacos.fallocSpec.creation_admission PageThreadMacos.fthread_alloc \
    PageThreadMacos.fthread_free PageThreadMacos.fthread_resize PageThreadMacos.fthread_remap \
    PageThreadMacos.cAllocSpec PageThreadMacos.cAllocSpec.creation PageTok.hintAligned_iff \
    PageTok.HintKn_linux_eq; do
  theorems+=(--declaration "AllocTranslated.$name")
done
prove() {  # prove LINES: build, audit and run the library of the current tree; LINES: output dir
  # The library: the translations, AllocTranslated/Eval.lean (`#guard`s), P4b's obstruction (the
  # translated PageAllocator cannot satisfy AllocSpec, docs/alloc-page.md: PageObstruction.lean),
  # resize/remap/free against the full-state FAllocSpec (PageSpec.lean for x86_64-linux,
  # PageSpecMacos.lean for aarch64-macos: the invariant PageTok.lean and `fsym`), PageAlloc,
  # PageAllocMacos, PageThread, PageThreadMacos, PageCreation, ListsPage and KernelBytes.
  python3 -B scripts/fixtures.py build AllocTranslated
  # Axioms from the built environment. A mutant whose shrink leaks the cut pages fails PageSpec
  # (mutant.sh).
  python3 -B scripts/fixtures.py audit PageObstruction PageTok PageSpec PageSpecMacos PageAlloc \
    PageAllocMacos PageThread PageThreadMacos PageCreation ListsPage KernelBytes "${theorems[@]}"
  # M02: the model's growth lines against the files the native runs are compared with.
  python3 -B scripts/fixtures.py run "$1" AllocTranslated.Eval:AllocTranslated.Eval.growLinux \
    AllocTranslated.Eval:AllocTranslated.Eval.growMacos \
    AllocTranslated.Eval:AllocTranslated.Eval.fbaGrowLinux \
    AllocTranslated.Eval:AllocTranslated.Eval.fbaGrowMacos
  diff <(grep '^page_grow' "$here/expected-linux.txt") "$1/AllocTranslated.Eval.growLinux.txt"
  diff <(grep '^page_grow' "$here/expected.txt") "$1/AllocTranslated.Eval.growMacos.txt"
  diff <(grep '^fba_grow' "$here/expected-linux.txt") "$1/AllocTranslated.Eval.fbaGrowLinux.txt"
  diff <(grep '^fba_grow' "$here/expected.txt") "$1/AllocTranslated.Eval.fbaGrowMacos.txt"
}
prove "$work/lines"
# The same proof text over the Zig 0.16.0 translations, in a check tree with them in place of the
# retained 0.17.1 ones (scripts/check-tree.py: the tree clones the root build; with
# AIR2LEAN_CAS_DIR, only the translations and what imports them are elaborated again).
tree=$repo_root/.lake/check-tree/alloc-translated-0.16.0
python3 -B scripts/check-tree.py create "$tree" "${replace[@]}"
(cd "$tree" && prove "$work/lines-0.16.0")
bash "$here/mutant.sh"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  source scripts/rosetta.sh
  if air2lean_under_rosetta; then
    # Rosetta maps memory itself and aborts on the 2^47-byte growth ("could not find free space"),
    # where a kernel returns ENOMEM: its result would not be the native one.
    echo 'alloc-translated: the native run needs a Linux kernel, not Rosetta (docs/alloc-page.md)' >&2
    exit 1
  fi
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
  # M03: the model's `page_large` lines. The archive is the one tests/diff's executables link
  # (the harness of one example is built with it and not used).
  AIR2LEAN_ZIG="$AIR2LEAN_NATIVE_ZIG" AIR2LEAN_EXAMPLES=basic bash scripts/diff.sh --build-only "$work/diff-native"
  large() {  # large TREE: the compiled runner over TREE's translations against the expected files
    local runner=$1/tests/roadmap/.lake/build/bin/alloc-translated-large os file
    mkdir -p "$1/tests/diff/out/libm"
    cp "$work/diff-native/air2lean_libm.a" "$1/tests/diff/out/libm/air2lean_libm.a"
    (cd "$1" && python3 -B scripts/fixtures.py build alloc-translated-large)
    for os in linux macos; do
      case "$os" in linux) file=$here/expected-linux.txt ;; macos) file=$here/expected.txt ;; esac
      diff <(grep '^page_large' "$file") <("$runner" "$os")
      # Under the old fixed cap (the differential harness's policy) every request is denied: the
      # line above depends on the default policy having no cap.
      [ "$("$runner" "$os" capped)" = 'page_large ok 0 0' ]
    done
  }
  tree_retained=$repo_root/.lake/check-tree/alloc-translated-0.17.1
  python3 -B scripts/check-tree.py create "$tree_retained"
  large "$tree_retained"
  large "$tree"
fi
echo "alloc-translated: ok"
