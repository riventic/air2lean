#!/usr/bin/env bash
# Allocator milestone 2: std.heap.ArenaAllocator (Zig 0.16.0, lock-free) translated from its AIR with
# its child allocators (FixedBufferAllocator, page_allocator) down to posix.mmap/munmap/mremap
# (`--allocator-model translated`, docs/alloc-arena.md). Checks: the retained translations are the
# fresh ones (the stock arena on both targets, the patched one of upstream/arena-fix.patch on
# x86_64-linux); they elaborate; the one-thread results equal the native ones (AllocArena/Eval.lean;
# the stock arena's O-E run is illegal where native code has undefined behaviour); obstructions
# O-A and O-E are kernel-checked (ArenaObstruction.lean); `free`, `resize` and `remap` are proved
# against FAllocSpec for each module (ArenaSpec*.lean, by fsym with the updates of AllocArena/Core.lean);
# an alloc that reserves nothing is rejected (mutant.sh); the admissions fail closed (test_cli.py).
# Every Lean file is a module of the fixture's library AllocArena (tests/roadmap/lakefile.toml),
# built by Lake with what it imports (scripts/fixtures.py; run it under scripts/build-guard.py).
# Needs a built translator; runs no compiler. With
# AIR2LEAN_NATIVE_ZIG (a stock Zig 0.16.0), also builds and runs native.zig against expected.txt, and
# against expected-fixed.txt over a standard library with upstream/arena-fix.patch (needs `patch`).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-arena
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-arena.XXXXXX")
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
# The stock arena (both targets) and the patched one (upstream/arena-fix.patch, x86_64-linux).
for pair in "arena-linux ArenaLinux" "arena-macos ArenaMacos" "arena-fixed-linux ArenaFixedLinux"; do
  dir=${pair% *}
  module=${pair#* }
  # The retained translation is the fresh one, byte for byte (Lake builds the retained file).
  "$translator" "$here/air/0.16.0/$dir" -o "$work/$module.lean" \
    --namespace "AllocArena.$module" --prefix "arena." --allocator-model translated
  cmp "$work/$module.lean" "$here/AllocArena/$module.lean"
done
# The library: the translations, AllocArena/Eval.lean (`#guard`s), the obstructions, `reset`'s
# retaining modes (HeaderTagCX.lean: a fresh node over a stale atomic location has no `apts`
# header, only a `wpts` one; HeaderMixCX.lean: a `wpts` header word has a thread rule after
# reuse, MM-21), the shared layer of the specification (AllocArena/Core.lean: invariant, lemmas,
# updates; generic over the module), `reset`'s ghost part (AllocArena/Reset.lean) and the specs.
python3 -B scripts/fixtures.py build AllocArena
# Axioms of every theorem of the proof modules, from the built environment: only the standard
# ones. Named: the obstructions; `free`, `resize` and `remap` against FAllocSpec over the
# ghost-epoch invariant, stated for each module and proved by `fsym` over that module's code
# with the shared updates (the stock arena on both targets and the patched one, whose `free` and
# `resize` add a bounds check), `deinit_ct`, `reset_free_all_spec` (`deinit` and
# `reset(.free_all)` walked by `fsym`) and `count_spec` (`countListCapacity`); the
# module-independent fee results of Core (`grant_return`, `own_epTok_empty`,
# `granted_epTok_false`) and of AllocArena/Reset.lean (`reset_release`: `reset`'s ghost part;
# `chain_sizes_le`: a list's node sizes sum to at most 2^63), the M01 statements
# (`granted_in_node`: a slice the arena takes back lies in one of its nodes;
# `reset_free_all_frame`: `reset(.free_all)` keeps every other resource), and `loop78_ct`
# (`reset`'s retaining modes give back every node of a list but the last).
theorems=()
for name in foreign_free_panics oob_free_illegal aligned_index_overflows memTop_unbounded \
    node_buf_low aligned_index_ok not_fallocSpec_arena not_reset_own; do
  theorems+=(--theorem "AllocArena.ArenaObstruction.$name")
done
for name in fresh_node no_apts no_header_apts_triple header_wpts; do
  theorems+=(--theorem "Zig.Full.HeaderTagCX.$name")
done
theorems+=(--theorem Zig.Full.HeaderMixCX.size_load_reads --theorem Zig.Full.HeaderMixCX.size_load_rule)
for name in grant_return own_epTok_empty granted_epTok_false reset_release chain_sizes_le granted_in_node; do
  theorems+=(--theorem "AllocArena.Core.$name")
done
for spec in ArenaSpec ArenaSpecMacos ArenaSpecFixed; do
  for name in free_spec resize_spec remap_spec deinit_ct reset_free_all_spec count_spec; do
    theorems+=(--theorem "AllocArena.$spec.$name")
  done
done
theorems+=(--theorem AllocArena.ArenaSpec.reset_free_all_frame --theorem AllocArena.ArenaSpec.loop78_ct)
modules=()
for module in ArenaObstruction HeaderTagCX HeaderMixCX AllocArena.Core AllocArena.Reset ArenaSpec \
    ArenaSpecMacos ArenaSpecFixed; do
  modules+=(--module "$module")
done
python3 -B scripts/fixtures.py audit "${modules[@]}" "${theorems[@]}"
bash "$here/mutant.sh"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  cp "$here/arena.zig" "$here/native.zig" "$work/"
  "$AIR2LEAN_NATIVE_ZIG" build-exe -OReleaseSafe "$work/native.zig" --cache-dir "$work/cache" \
    --global-cache-dir "$work/cache" -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  diff "$here/expected.txt" "$work/native.txt"
  # The patched arena: the same clients over a standard library with upstream/arena-fix.patch.
  # The lib directory is copied (`std` is patched) except the libc sources, which are linked: Zig's
  # cache check of a linked Zig source (`compiler_rt.zig`) failed with FileNotFound on the CI runner.
  lib_dir=$("$AIR2LEAN_NATIVE_ZIG" env | sed -n 's/^ *\.lib_dir = "\(.*\)",$/\1/p')
  [ -d "$lib_dir/std" ] || { echo "no lib directory from '$AIR2LEAN_NATIVE_ZIG env'" >&2; exit 1; }
  lib_dir=$(cd -- "$lib_dir" && pwd)
  mkdir "$work/lib"
  for entry in "$lib_dir"/*; do
    if [ "$(basename -- "$entry")" = libc ]; then ln -s "$entry" "$work/lib/"
    else cp -R "$entry" "$work/lib/"; fi
  done
  chmod -R u+w "$work/lib/std"
  patch -s -d "$work/lib" -p1 < "$here/upstream/arena-fix.patch"
  "$AIR2LEAN_NATIVE_ZIG" build-exe -OReleaseSafe --zig-lib-dir "$work/lib" "$work/native.zig" \
    --cache-dir "$work/cache" --global-cache-dir "$work/cache" -femit-bin="$work/native-fixed"
  "$work/native-fixed" 2> "$work/native-fixed.txt"
  diff "$here/expected-fixed.txt" "$work/native-fixed.txt"
fi
echo "alloc-arena: ok"
