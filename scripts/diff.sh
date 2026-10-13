#!/usr/bin/env bash
# Differential test: build+run the Zig side (tests/diff/<ex>/harness.zig, tests/diff/common.zig)
# and the Lean side (tests/diff/Diff.lean), then compare their output line by line against the
# same inputs (tests/diff/<ex>/inputs/*.jsonl, from tests/diff/gen_inputs.zig).
#
# scripts/diff-report.py compares the two sides; it is the only classifier. A case matches if both
# sides return the same value (with the same buffers and live allocation count), or both fail with
# matching kinds: the harness's panic-kind name (e.g. "outOfBounds") maps, via
# scripts/panic-policy.tsv, to the `Zig.Error` constructor Diff.lean is expected to throw for the
# same check (docs/generated-code.md §Panics). Anything else — a value mismatch, a kind mismatch, a
# Zig kind with no table entry (including "unknown": the child died without reporting a kind), one
# side ok and the other fail, a model no-result — is a mismatch: printed as "MISMATCH (typed)",
# counted as `mismatch` in the counter lines, and makes the whole run exit 1.
#
# A Lean `Zig.Error.unspecified` or `illegal` (Zig leaves the result open; docs/generated-code.md
# §Panics), or `.unsupportedTimer` (a clock the model lacks), is an exclusion, counted as
# "unspecified", only on an input pinned for it in tests/diff/<ex>/unspecified.txt
# ("<fn> <input_sha256> <count>|<min>-<max> <reason>" lines; a range for an input whose result
# depends on the timing of the compiled threads, a race that the hardware shows on some runs
# only); on any other input it is a mismatch (F3), and a pinned count that differs fails the run.
#
# A concurrent function's Lean line comes from a search over schedules (tests/diff/Diff.lean's
# `searchSchedules`): the schedule that gives Zig's line, if the search finds one. A Lean
# `Zig.Error.capped` (the search stopped at its cap without Zig's line) is an exclusion counted
# as "capped" against tests/diff/<ex>/capped.txt; typed evidence is inconclusive.
#
# The float model follows the translation's target profile (docs/floats.md §Targets): on
# aarch64-macos run that host's translation (scripts/check.sh), whose exclusion pins are
# tests/diff/<ex>/unspecified.<uname -s>-<uname -m>.txt. The compiled Zig can still give other
# bits for some float results (NaN bits, the sign of a zero). tests/diff/<ex>/host.txt lists the
# functions whose results depend on the target, each with the kinds of difference it may show
# ("<fn> <kind>[,<kind>...]": nan_payload, zero_sign, libm_ulp). Only on a host that is not
# x86_64-linux, and only when both sides returned a value and every differing float has a listed
# kind, a disagreement counts as "host"; any other difference is a mismatch (F3). A panic, error
# or exclusion against a value is never a host difference. CI (x86_64-linux) is the reference.
#
# The native side (each example's harness, the libm archive and its self-check, the asm archive)
# is built and the harnesses run in parallel, one job per example (scripts/par.py: AIR2LEAN_JOBS
# workers, output in example order). With AIR2LEAN_CAS_DIR set, every stock-Zig build goes through
# the shared cache (`scripts/cas.py native`, docs/build-cache.md): an unchanged harness is not
# compiled again. `diff.sh --build-only DIR` only builds the native side into DIR; a later run
# with AIR2LEAN_DIFF_PREBUILT=DIR (the same mode, backend, flags and target) runs those binaries.
# scripts/build-mode-docker.sh uses this to cross-compile on the host and run in an emulated
# container.
#
# Usage: diff.sh | diff.sh --build-only DIR
# Env:
#   AIR2LEAN_ZIG        Stock zig to build+run each harness. Default: zig (on PATH). Its version
#                       must be the one whose translations the tree holds (scripts/check-tree.py
#                       check-models); scripts/check.sh with AIR2LEAN_ZIG_VERSION=V needs a Zig V.
#   AIR2LEAN_DIFF_OPTIMIZE  Optimize mode of the native harness: Debug, ReleaseSafe (default),
#                       ReleaseFast or ReleaseSmall (docs/build-modes.md). The shipping build is
#                       `build-exe -OReleaseSafe -mcpu=baseline`. ReleaseFast and ReleaseSmall remove
#                       safety checks, so an input on which the model throws is illegal behavior there:
#                       it is counted as ub_excluded, not compared.
#   AIR2LEAN_DIFF_BACKEND   Native code generator: llvm or stage2_x86_64 (-fno-llvm). Unset: Zig's default.
#   AIR2LEAN_ROSETTA_LINK_FLAGS  Extra build-exe flags for every executable here (`-z norelro`
#                       when the x86_64 binaries run under Rosetta; scripts/rosetta.sh, docs/rosetta.md).
#   AIR2LEAN_DIFF_TARGET  Zig target of the native side (`-target`), e.g. x86_64-linux to
#                       cross-compile for another host. Unset: this host.
#   AIR2LEAN_DIFF_PREBUILT  Native side built by `diff.sh --build-only` (above). Unset: build here.
#   AIR2LEAN_DIFF_ZIG_CACHE  Zig global cache dir for the stock-zig builds of this script (the
#                       harnesses and libm). Unset: Zig's default. CI keeps one per build mode.
#   AIR2LEAN_DIFF_FRESH_INPUTS  The seed of regenerated inputs (scripts/fresh-inputs.sh): the
#                       per-input exclusion pins name the committed inputs, so they are not checked;
#                       a model .illegal/.unspecified result is an exclusion, never a match.
#   AIR2LEAN_EXAMPLES   Space-separated example dirs to test. Default: every dir in examples/
#                       (not `asm` on a host that is not x86_64, and not an example whose
#                       examples/<ex>/zig-versions does not list the zig's version, as in check.sh).
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
build_only=
case "$#:${1:-}" in
  0:) ;;
  2:--build-only) build_only=$(mkdir -p -- "$2" && cd -- "$2" && pwd) ;;
  *) echo "usage: diff.sh [--build-only DIR]" >&2; exit 2 ;;
esac
cd "$repo_root"

# Invalidate old completed evidence before compiler/version/selection setup.
export AIR2LEAN_DIFF_REPORT=${AIR2LEAN_DIFF_REPORT:-tests/diff/out/report.json}
examples=""
build_dir=""
diff_phase=setup
finish_diff() {
  local status=$? evidence_examples=""
  if [ "$diff_phase" != setup ]; then evidence_examples=$examples; fi
  if [ "$status" -ne 0 ] && [ -z "$build_only" ]; then
    if ! python3 scripts/diff-report.py failure --summary "$AIR2LEAN_DIFF_REPORT" \
      --root "$repo_root" --examples "$evidence_examples" --phase "$diff_phase"; then
      echo "error: could not record differential failure evidence" >&2
    fi
  fi
  if [ -n "$build_dir" ]; then rm -rf "$build_dir"; fi
  return "$status"
}
trap finish_diff EXIT
[ -n "$build_only" ] || python3 scripts/diff-report.py init --summary "$AIR2LEAN_DIFF_REPORT" --root "$repo_root"

zig_bin=${AIR2LEAN_ZIG:-zig}
if [ -n "${AIR2LEAN_DIFF_ZIG_CACHE:-}" ]; then export ZIG_GLOBAL_CACHE_DIR=$AIR2LEAN_DIFF_ZIG_CACHE; fi
optimize=${AIR2LEAN_DIFF_OPTIMIZE:-ReleaseSafe}
backend_flag=
case "${AIR2LEAN_DIFF_BACKEND:-}" in
  "") ;;
  llvm) backend_flag=-fllvm ;;
  stage2_x86_64) backend_flag=-fno-llvm ;;
  *) echo "error: invalid AIR2LEAN_DIFF_BACKEND: $AIR2LEAN_DIFF_BACKEND" >&2; exit 1 ;;
esac
case "$optimize" in
  Debug|ReleaseSafe|ReleaseFast|ReleaseSmall) ;;
  *) echo "error: invalid AIR2LEAN_DIFF_OPTIMIZE: $optimize" >&2; exit 1 ;;
esac
zig_version=$("$zig_bin" version)
if [ -n "${AIR2LEAN_EXAMPLES:-}" ]; then
  examples=$AIR2LEAN_EXAMPLES
else
  source "$repo_root/scripts/example-selection.sh"
  examples=$(air2lean_default_examples "$repo_root" "$zig_version" "$(uname -m)")
fi
example_count=0
for ex in $examples; do
  case "$ex" in *[!a-zA-Z0-9_-]* | "")
    echo "error: invalid example: $ex" >&2; exit 1 ;;
  esac
  [ -f "tests/diff/$ex/harness.zig" ] || { echo "error: unknown example: $ex" >&2; exit 1; }
  example_count=$((example_count + 1))
done
[ "$example_count" -gt 0 ] || { echo "error: no examples selected" >&2; exit 1; }

# Clear this selection's old sidecars only after setup has validated it.
[ -n "$build_only" ] ||
  python3 scripts/diff-report.py init --summary "$AIR2LEAN_DIFF_REPORT" --root "$repo_root" --examples "$examples"
diff_phase=build_native

# A stock-Zig build, from the shared cache when AIR2LEAN_CAS_DIR is set (docs/build-cache.md).
stock_zig() {
  if [ -n "${AIR2LEAN_CAS_DIR:-}" ]; then
    python3 -B "$repo_root/scripts/cas.py" native -- "$zig_bin" "$@"
  else
    "$zig_bin" "$@"
  fi
}
# A fixed CPU: float results can depend on CPU features (FMA, native f16; docs/floats.md).
target_flags="-mcpu=baseline${AIR2LEAN_DIFF_TARGET:+ -target $AIR2LEAN_DIFF_TARGET}"
build_harness() {
  # shellcheck disable=SC2086  # $backend_flag is empty or one flag, $target_flags are flags
  stock_zig build-exe -O"$optimize" $target_flags $backend_flag ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} -femit-bin="$native_dir/$1" \
    --dep "$1" --dep common -Mroot="tests/diff/$1/harness.zig" \
    -M"$1"="examples/$1/$1.zig" -Mcommon=tests/diff/common.zig
}
export -f stock_zig build_harness
export repo_root zig_bin optimize backend_flag target_flags

native_dir=${build_only:-${AIR2LEAN_DIFF_PREBUILT:-}}
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-diff.XXXXXX")
if [ -z "$native_dir" ]; then native_dir=$build_dir; fi
export native_dir
if [ -z "${AIR2LEAN_DIFF_PREBUILT:-}" ]; then
  echo "== building zig harnesses ==" >&2
  # shellcheck disable=SC2086  # $examples is a space-separated list
  python3 scripts/par.py --mem-mib 1024 -- "$BASH" -c 'set -euo pipefail; build_harness "$1"' build_harness {} \
    ::: $examples

  diff_phase=build_libm
  echo "== building libm ==" >&2
# tests/diff/libm/libm.zig re-exports 8 compiler_rt transcendental functions per float width
# (see its doc comment for the ABI). It calls compiler_rt by Zig name through a `crt` module we
# generate here: a copy of the stock zig's own compiler_rt/ (needed for its internal cross-file
# imports, e.g. sin.zig's rem_pio2.zig) plus one re-export file naming the 8 top-level ops. 0.16.0
# also needs a top-level compiler_rt.zig: its compiler_rt/<op>.zig files import it as
# "../compiler_rt.zig" for `symbol`/`want_ppc_abi`/`want_float_exceptions` (0.15.2's op files
# don't need it at all). The real lib/compiler_rt.zig is NOT an option here: its own top-level
# `comptime` block unconditionally imports and @exports all of compiler_rt (incl. memset/memcpy/
# memmove), which the Lean difftest link then pulls in whole — that bloats the archive and once
# hung the Lean binary for over an hour inside its allocator init. A stub with just the 3 names
# the 8 op files (and everything they transitively import: trig.zig, rem_pio2*.zig,
# long_double.zig) use — checked by grep — avoids that. Values taken from the real file for this
# build's conditions (not a test build, not wasm, not C object format, static linkage). `symbol`
# itself is a no-op here, not the real @export: -fcompiler-rt below already bundles Zig's own
# compiler_rt.o, which @exports these same 8 ops' C names for the (non-Zig, clang-linked) Lean
# side. If our copy exported them too, both would be duplicate weak defs; 0.16.0's linker rejects
# that (0.15.2's happens not to). We only ever call these files' Zig-level decls (libm.zig's
# `crt.sin.sinh` etc.), never their C names, so dropping our own export side effect is safe.
# Both versions' compiler_rt.zig import their sibling files as literal "compiler_rt/<name>.zig",
# so the copied dir must be named exactly "compiler_rt" on disk. A module's imports must stay
# inside its root file's directory tree, so the re-export file (the module root) lives at
# $crt_root, one level above compiler_rt/, with the stub compiler_rt.zig alongside it — putting
# both "../compiler_rt.zig" and "compiler_rt/*.zig" in path. The stub is inert for 0.15.2: its
# op files never import the top-level compiler_rt.zig at all.
  # `zig env` is ZON from 0.15.0 (`.lib_dir = "..."`), JSON before (`"lib_dir": "..."`).
  lib_dir=$("$zig_bin" env | sed -n -e 's/^ *\.lib_dir = "\([^"]*\)".*/\1/p' -e 's/^ *"lib_dir": "\([^"]*\)".*/\1/p')
  crt_root="$build_dir/crt"
  mkdir "$crt_root"
  cp -R "$lib_dir/compiler_rt" "$crt_root/compiler_rt"
cat >"$crt_root/compiler_rt.zig" <<'EOF'
const builtin = @import("builtin");
pub const want_ppc_abi = builtin.cpu.arch.isPowerPC();
pub const want_float_exceptions = !builtin.cpu.arch.isWasm();
pub inline fn symbol(comptime func: *const anyopaque, comptime name: []const u8) void {
    _ = func;
    _ = name;
}
// 0.17.0's op files declare their (unexported, see `symbol`) C wrappers with these ABI types.
// Bytes, not the float: f80 is not a C-ABI parameter type on every host (aarch64).
fn BytesAbi(comptime T: type) type {
    return struct {
        pub const Abi = extern struct { bytes: [@sizeOf(T)]u8 };
        pub inline fn toAbi(x: T) Abi {
            return .{ .bytes = @import("std").mem.toBytes(x) };
        }
        pub inline fn fromAbi(a: Abi) T {
            return @import("std").mem.bytesToValue(T, &a.bytes);
        }
    };
}
pub const @"f16" = BytesAbi(f16);
pub const @"f32" = BytesAbi(f32);
pub const @"f64" = BytesAbi(f64);
pub const @"f80" = BytesAbi(f80);
pub const @"f128" = BytesAbi(f128);
EOF
cat >"$crt_root/air2lean_root.zig" <<'EOF'
pub const sin = @import("compiler_rt/sin.zig");
pub const cos = @import("compiler_rt/cos.zig");
pub const tan = @import("compiler_rt/tan.zig");
pub const exp = @import("compiler_rt/exp.zig");
pub const exp2 = @import("compiler_rt/exp2.zig");
pub const log = @import("compiler_rt/log.zig");
pub const log2 = @import("compiler_rt/log2.zig");
pub const log10 = @import("compiler_rt/log10.zig");
EOF
# -fcompiler-rt: the Lean-side link is a plain clang/lld link, not a zig one, so it doesn't get
# Zig's own implicit compiler-rt support the way a zig-compiled consumer (e.g. selfcheck) does.
# sin.zig's f80/f128 wide paths need helpers like __extendxftf2 that only compiler_rt.o provides;
# without this flag that link fails with "undefined symbol: __extendxftf2" (seen on 0.15.2 too,
# not just 0.16.0). Our own crt module's `symbol` is a no-op (see above) so it doesn't also
# @export the 8 ops we import, which would otherwise duplicate compiler_rt.o's own exports.
# -OReleaseFast, like Zig builds compiler_rt for a ReleaseSafe program
# (Compilation.compilerRtOptMode): with safety checks, 0.16.0's f80 `cosx` panics ("integer
# overflow" in rem_pio2_large) on inputs where the real `@cos` returns a value. A per-module -O
# for the crt module alone does not change its code (the archive stays the same). libm.zig itself
# only uses @bitCast and @truncate, which have no safety checks.
  # shellcheck disable=SC2086  # $target_flags are flags
  stock_zig build-lib -static -fcompiler-rt -fPIC -OReleaseFast $target_flags --name air2lean_libm \
    -femit-bin="$native_dir/air2lean_libm.a" \
    --dep crt -Mroot=tests/diff/libm/libm.zig -Mcrt="$crt_root/air2lean_root.zig"
  # Compares the archive against Zig's own @sin/@cos/... builtins in the same binary
  # (tests/diff/libm/selfcheck.zig's doc comment): fatal on Linux, informational elsewhere.
  # shellcheck disable=SC2086  # $target_flags are flags
  stock_zig build-exe -OReleaseSafe -mcpu=baseline ${AIR2LEAN_DIFF_TARGET:+-target "$AIR2LEAN_DIFF_TARGET"} ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} \
    -femit-bin="$native_dir/libm_selfcheck" tests/diff/libm/selfcheck.zig "$native_dir/air2lean_libm.a"

  echo "== building asm archive ==" >&2
# tests/diff/asm/asm.zig re-implements examples/asm/asm.zig's ops with ordinary Zig builtins
# (@byteSwap/@popCount/@clz, `/` and `%`) instead of inline asm, so it builds on any host, unlike the example
# itself (x86_64 only). No compiler_rt dependency (unlike libm): these are plain integer ops.
  # shellcheck disable=SC2086  # $target_flags are flags
  stock_zig build-lib -static -fPIC -OReleaseFast $target_flags --name air2lean_asm \
    -femit-bin="$native_dir/air2lean_asm.a" -Mroot=tests/diff/asm/asm.zig
fi
[ -z "$build_only" ] || exit 0

diff_phase=build_native
echo "== running zig harnesses ==" >&2
# A harness writes only tests/diff/out/zig/<ex>/; each case keeps its own deadline and memory
# limit (tests/diff/common.zig `forkCall`).
# shellcheck disable=SC2086  # $examples is a space-separated list
python3 scripts/par.py --mem-mib 512 -- "$native_dir/{}" ::: $examples
diff_phase=build_libm
mkdir -p tests/diff/out/libm tests/diff/out/asm
cp "$native_dir/air2lean_libm.a" tests/diff/out/libm/air2lean_libm.a
cp "$native_dir/air2lean_asm.a" tests/diff/out/asm/air2lean_asm.a
echo "== libm self-check ==" >&2
"$native_dir/libm_selfcheck"

diff_phase=run_model
echo "== building + running lean side ==" >&2
# The archives are traced inputs of difftest (tests/diff/lakefile.toml `moreLinkObjs`): a changed
# archive relinks it, and Lake's artifact cache never restores one linked against another archive.
(cd tests/diff && lake build difftest)
(cd tests/diff && lake env lean --run ScheduleSearchTest.lean)
# Fail closed: the Lean side must be the translation for the stock Zig's version on this host
# (scripts/check-tree.py check-models). Checked only before the comparison, so that a
# cache-warming run (.github/workflows/ci-cache.yml) still builds the harnesses and tests/diff.
diff_phase=check_models
# shellcheck disable=SC2086  # $examples is a space-separated list
python3 scripts/check-tree.py check-models "$zig_version" $examples
diff_phase=run_model
# Diff.lean runs only the examples this script compares.
AIR2LEAN_EXAMPLES="$examples" tests/diff/.lake/build/bin/difftest

# Compare: scripts/diff-report.py is the one classifier. It types every case, prints a "MISMATCH
# (typed)" line per mismatch, the per-function, per-example and "TOTAL:" counter lines (every typed
# mismatch counts as `mismatch`, never as `host`), checks the exclusion pins and exits non-zero on
# any mismatch, pin violation or setup failure.
echo "== comparing ==" >&2
diff_phase=compare
python3 "$repo_root/scripts/diff-report.py" compare --summary "$AIR2LEAN_DIFF_REPORT" \
  --root "$repo_root" --examples "$examples" --version "$zig_version" \
  --host "$(uname -s)-$(uname -m)" \
  ${AIR2LEAN_DIFF_OPTIMIZE:+--optimize "$AIR2LEAN_DIFF_OPTIMIZE" --backend "${AIR2LEAN_DIFF_BACKEND:-llvm}"} \
  --schedule-receipts "${AIR2LEAN_SCHEDULE_RECEIPTS:-}" \
  ${AIR2LEAN_DIFF_FRESH_INPUTS:+--fresh-inputs "$AIR2LEAN_DIFF_FRESH_INPUTS"}
