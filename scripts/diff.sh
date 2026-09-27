#!/usr/bin/env bash
# Differential test: build+run the Zig side (tests/diff/<ex>/harness.zig, tests/diff/common.zig)
# and the Lean side (tests/diff/Diff.lean), then compare their output line by line against the
# same inputs (tests/diff/<ex>/inputs/*.jsonl, from tests/diff/gen_inputs.zig).
#
# A line counts as a match if both sides say "ok" with the same value, or both say "fail" with
# matching kinds: the harness's panic-kind name (e.g. "outOfBounds") maps, via the fixed table in
# expected_ctor_for_zig_kind() below, to the `Zig.Error` constructor Diff.lean is expected to
# throw for the same check (e.g. "outOfBounds"; docs/generated-code.md §Panics). "ok" values
# follow docs/generated-code.md's diff protocol: a plain int (bare or quoted decimal), an
# optional (`null` or the inner value), or an error union (`{"err":"<Name>"}` or the inner
# value) — classify_line() below folds all three into one comparable $val, so the match check
# itself doesn't need to know which shape it's looking at. Anything else — a value mismatch, a
# kind mismatch, a Zig kind with no table entry (including "unknown" — the child died without
# reporting a kind), one side ok and the other fail, or a Lean "diverge" (none of basic's or
# recursion's functions should ever not terminate) — is a mismatch: printed immediately, and
# makes the whole run exit 1.
#
# A Lean `Zig.Error.unspecified` (Zig leaves the result open; docs/generated-code.md §Panics)
# matches any Zig line and is counted as "unspecified". The count per function must equal the
# one in tests/diff/<ex>/unspecified.txt ("<fn> <count>" lines; a function that is not listed
# expects 0), so a model that throws `unspecified` too often fails the test.
#
# Usage: diff.sh
# Env:
#   AIR2LEAN_ZIG        Stock zig to build+run each harness. Default: zig (on PATH).
#   AIR2LEAN_EXAMPLES   Space-separated example dirs to test. Default: every dir in examples/.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

zig_bin=${AIR2LEAN_ZIG:-zig}
examples=${AIR2LEAN_EXAMPLES:-$(cd examples && for d in */; do printf '%s ' "${d%/}"; done)}

# The names of an example's functions are the names of its input files (layout convention).
functions_of() {
  (cd "tests/diff/$1/inputs" && for f in *.jsonl; do printf '%s ' "${f%.jsonl}"; done)
}

echo "== building zig harnesses ==" >&2
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-diff.XXXXXX")
trap 'rm -rf "$build_dir"' EXIT
for ex in $examples; do
  # A fixed CPU: float results can depend on CPU features (FMA, native f16; docs/floats.md).
  "$zig_bin" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$build_dir/$ex" \
    --dep "$ex" --dep common -Mroot="tests/diff/$ex/harness.zig" \
    -M"$ex"="examples/$ex/$ex.zig" -Mcommon=tests/diff/common.zig
  "$build_dir/$ex"
done

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
# $build_dir, one level above compiler_rt/, with the stub compiler_rt.zig alongside it — putting
# both "../compiler_rt.zig" and "compiler_rt/*.zig" in path. The stub is inert for 0.15.2: its
# op files never import the top-level compiler_rt.zig at all.
lib_dir=$("$zig_bin" env | sed -n 's/^ *\.lib_dir = "\([^"]*\)".*/\1/p')
crt_dir="$build_dir/compiler_rt"
cp -R "$lib_dir/compiler_rt" "$crt_dir"
cat >"$build_dir/compiler_rt.zig" <<'EOF'
const builtin = @import("builtin");
pub const want_ppc_abi = builtin.cpu.arch.isPowerPC();
pub const want_float_exceptions = !builtin.cpu.arch.isWasm();
pub inline fn symbol(comptime func: *const anyopaque, comptime name: []const u8) void {
    _ = func;
    _ = name;
}
EOF
cat >"$build_dir/air2lean_root.zig" <<'EOF'
pub const sin = @import("compiler_rt/sin.zig");
pub const cos = @import("compiler_rt/cos.zig");
pub const tan = @import("compiler_rt/tan.zig");
pub const exp = @import("compiler_rt/exp.zig");
pub const exp2 = @import("compiler_rt/exp2.zig");
pub const log = @import("compiler_rt/log.zig");
pub const log2 = @import("compiler_rt/log2.zig");
pub const log10 = @import("compiler_rt/log10.zig");
EOF
mkdir -p tests/diff/out/libm
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
"$zig_bin" build-lib -static -fcompiler-rt -fPIC -OReleaseFast -mcpu=baseline --name air2lean_libm \
  -femit-bin=tests/diff/out/libm/air2lean_libm.a \
  --dep crt -Mroot=tests/diff/libm/libm.zig -Mcrt="$build_dir/air2lean_root.zig"

echo "== libm self-check ==" >&2
# Compares the archive against Zig's own @sin/@cos/... builtins in the same binary
# (tests/diff/libm/selfcheck.zig's doc comment): fatal on Linux, informational elsewhere.
"$zig_bin" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$build_dir/libm_selfcheck" \
  tests/diff/libm/selfcheck.zig tests/diff/out/libm/air2lean_libm.a
"$build_dir/libm_selfcheck"

echo "== building + running lean side ==" >&2
# Lake does not track tests/diff/out/libm/air2lean_libm.a (linked in via lakefile.toml's
# moreLinkArgs) as a build input, so a changed archive alone would not trigger a relink.
rm -f tests/diff/.lake/build/bin/difftest
(cd tests/diff && lake build difftest)
# Diff.lean runs only the examples this script compares.
AIR2LEAN_EXAMPLES="$examples" tests/diff/.lake/build/bin/difftest

# Classifies one JSONL output line into $kind (ok|fail|diverge) and $val. For ok: `null` as the
# literal string "null"; an error union's `{"err":"Name"}` as "err:Name"; otherwise the decimal
# string (quotes stripped, if any) — docs/generated-code.md's diff protocol. For fail: the raw
# kind string — the harness's panic-name (e.g. "outOfBounds") or Diff.lean's fully-qualified
# constructor (e.g. "Zig.Error.overflow"), still with its "Zig.Error." prefix at this point. Both
# sides only ever emit these shapes (common.zig / Diff.lean). Order matters: the more specific
# "ok" patterns (null, err-object) must be checked before the generic bare-value one, since a
# `case` glob like '{"ok":'*'}' also matches them.
classify_line() {
  local line=$1
  case "$line" in
    '{"ok":null}')
      kind=ok
      val=null
      ;;
    '{"ok":{"err":"'*'"}}')
      kind=ok
      val=${line#'{"ok":{"err":"'}
      val="err:${val%'"}}'}"
      ;;
    '{"ok":"'*'"}')
      kind=ok
      val=${line#'{"ok":"'}
      val=${val%'"}'}
      ;;
    '{"ok":'*'}')
      kind=ok
      val=${line#'{"ok":'}
      val=${val%'}'}
      ;;
    '{"fail":"'*'"}')
      kind=fail
      val=${line#'{"fail":"'}
      val=${val%'"}'}
      ;;
    '{"diverge":true}')
      kind=diverge
      ;;
    *)
      echo "error: unrecognized output line: $line" >&2
      exit 1
      ;;
  esac
}

# Maps a Zig panic kind (a member name of common.zig's `panic`) to the `Zig.Error` constructor
# (bare name, no "Zig.Error." prefix) the Lean side is expected to throw for the same check.
# Echoes nothing for a kind with no expected constructor — including "unknown" — which the
# caller then treats as a mismatch: v0's scope (README.md) never reaches an unlisted kind, so
# seeing one at all is itself a bug. bash 3.2 has no associative arrays, hence the `case`.
expected_ctor_for_zig_kind() {
  case "$1" in
    integerOverflow | shlOverflow | shrOverflow | integerOutOfBounds | integerPartOutOfBounds)
      echo overflow ;;
    outOfBounds) echo outOfBounds ;;
    divideByZero) echo divByZero ;;
    reachedUnreachable) echo unreachable ;;
    exactDivisionRemainder | unwrapNull | unwrapError | forLenMismatch | invalidEnumValue \
      | inactiveUnionField | corruptSwitch | panic) echo panic ;;
    *) echo "" ;;
  esac
}

echo "== comparing ==" >&2
total_ok=0
total_fail_match=0
total_unspecified=0
total_mismatch=0
mismatch_found=0

for ex in $examples; do
  ex_ok=0
  ex_fail_match=0
  ex_unspecified=0
  ex_mismatch=0

  for fn in $(functions_of "$ex"); do
    in_file="tests/diff/$ex/inputs/${fn}.jsonl"
    zig_file="tests/diff/out/zig/$ex/${fn}.jsonl"
    lean_file="tests/diff/out/lean/$ex/${fn}.jsonl"

    # Line counts first, then one tab-joined line per input (JSON lines have no raw tabs).
    # No `readarray`: it needs bash 4, and macOS ships bash 3.2.
    n=$(wc -l <"$in_file" | tr -d ' ')
    [ "$n" -gt 0 ] || { echo "error: $in_file has no inputs" >&2; exit 1; }
    for f in "$zig_file" "$lean_file"; do
      m=$(wc -l <"$f" | tr -d ' ')
      [ "$m" -eq "$n" ] || { echo "error: $f has $m lines, expected $n" >&2; exit 1; }
    done

    fn_ok=0
    fn_fail_match=0
    fn_unspecified=0
    fn_mismatch=0
    i=0
    while IFS=$'\t' read -r in_line zig_line lean_line; do
      i=$((i + 1))
      classify_line "$zig_line"
      zkind=$kind
      zval=${val:-}
      classify_line "$lean_line"
      lkind=$kind
      lval=${val:-}

      if [ "$zkind" = ok ] && [ "$lkind" = ok ] && [ "$zval" = "$lval" ]; then
        fn_ok=$((fn_ok + 1))
      elif [ "$lkind" = fail ] && [ "$lval" = Zig.Error.unspecified ]; then
        fn_unspecified=$((fn_unspecified + 1))
      elif [ "$zkind" = fail ] && [ "$lkind" = fail ] &&
        [ -n "$(expected_ctor_for_zig_kind "$zval")" ] &&
        [ "$(expected_ctor_for_zig_kind "$zval")" = "${lval#'Zig.Error.'}" ]; then
        fn_fail_match=$((fn_fail_match + 1))
      else
        fn_mismatch=$((fn_mismatch + 1))
        mismatch_found=1
        echo "MISMATCH $ex.$fn input#$i: $in_line" >&2
        echo "  zig:  $zig_line" >&2
        echo "  lean: $lean_line" >&2
      fi
    done < <(paste "$in_file" "$zig_file" "$lean_file")

    want_unspecified=0
    if [ -f "tests/diff/$ex/unspecified.txt" ]; then
      want_unspecified=$(awk -v f="$fn" '$1 == f { print $2 }' "tests/diff/$ex/unspecified.txt")
      want_unspecified=${want_unspecified:-0}
    fi
    if [ "$fn_unspecified" -ne "$want_unspecified" ]; then
      mismatch_found=1
      echo "UNSPECIFIED COUNT $ex.$fn: $fn_unspecified, expected $want_unspecified" \
        "(tests/diff/$ex/unspecified.txt)" >&2
    fi

    echo "$ex.$fn: ok=$fn_ok fail_match=$fn_fail_match unspecified=$fn_unspecified" \
      "mismatch=$fn_mismatch (of $n)"
    ex_ok=$((ex_ok + fn_ok))
    ex_fail_match=$((ex_fail_match + fn_fail_match))
    ex_unspecified=$((ex_unspecified + fn_unspecified))
    ex_mismatch=$((ex_mismatch + fn_mismatch))
  done

  echo "TOTAL $ex: ok=$ex_ok fail_match=$ex_fail_match unspecified=$ex_unspecified" \
    "mismatch=$ex_mismatch"
  total_ok=$((total_ok + ex_ok))
  total_fail_match=$((total_fail_match + ex_fail_match))
  total_unspecified=$((total_unspecified + ex_unspecified))
  total_mismatch=$((total_mismatch + ex_mismatch))
done

echo "TOTAL: ok=$total_ok fail_match=$total_fail_match unspecified=$total_unspecified" \
  "mismatch=$total_mismatch"
[ "$mismatch_found" -eq 0 ]
