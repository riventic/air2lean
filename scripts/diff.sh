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
# reporting a kind), one side ok and the other fail, or the legacy Lean "diverge" wire shape (a model no-result; bounded scheduler
# evaluation does not establish divergence) — is a mismatch: printed immediately, and
# makes the whole run exit 1.
#
# A Lean `Zig.Error.unspecified` (Zig leaves the result open; docs/generated-code.md §Panics)
# is projected into the legacy "unspecified" counter, distinct from an exact match in the typed report. The count per function must equal the
# one in tests/diff/<ex>/unspecified.txt ("<fn> <count>" lines; a function that is not listed
# expects 0), so a model that throws `unspecified` too often fails the test. "<fn> <min>-<max>"
# pins a range: for a function whose count depends on the timing of the compiled threads (a race
# that the hardware shows on some runs only).
#
# A concurrent function's Lean line comes from a search over schedules (tests/diff/Diff.lean's
# `searchSchedules`): the schedule that gives Zig's line, if the search finds one. A Lean
# `Zig.Error.capped` (the search stopped at its cap without Zig's line) is the same kind of
# legacy exclusion, counted separately against tests/diff/<ex>/capped.txt; typed evidence is inconclusive.
#
# The float model follows x86_64-linux (docs/floats.md). On another host the compiled Zig gives
# other bits for some float results (NaN bits, f80, the sign of a zero). tests/diff/<ex>/host.txt
# lists the functions whose results depend on the target, one per line. Only on a host that is
# not x86_64-linux, a mismatch of such a function counts as "host", prints no MISMATCH line and
# does not fail the run: CI (x86_64-linux) is the reference.
#
# Usage: diff.sh
# Env:
#   AIR2LEAN_ZIG        Stock zig to build+run each harness. Default: zig (on PATH).
#   AIR2LEAN_DIFF_OPTIMIZE  Optimize mode of the native harness: Debug, ReleaseSafe (default),
#                       ReleaseFast or ReleaseSmall (docs/build-modes.md). The shipping build is
#                       `build-exe -OReleaseSafe -mcpu=baseline`. ReleaseFast and ReleaseSmall remove
#                       safety checks, so an input on which the model throws is illegal behavior there:
#                       it is counted as ub_excluded, not compared.
#   AIR2LEAN_DIFF_BACKEND   Native code generator: llvm or stage2_x86_64 (-fno-llvm). Unset: Zig's default.
#   AIR2LEAN_DIFF_LINK_FLAGS  Extra build-exe flags for the harness (the emulated x86_64 runs pass
#                       `-z norelro`: Rosetta rejects the empty RELRO segment of release builds).
#   AIR2LEAN_EXAMPLES   Space-separated example dirs to test. Default: every dir in examples/
#                       (not `asm` on a host that is not x86_64, and not an example whose
#                       examples/<ex>/zig-versions does not list the zig's version, as in check.sh).
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

# Invalidate old completed evidence before compiler/version/selection setup.
export AIR2LEAN_DIFF_REPORT=${AIR2LEAN_DIFF_REPORT:-tests/diff/out/report.json}
examples=""
build_dir=""
diff_phase=setup
finish_diff() {
  local status=$? evidence_examples=""
  if [ "$diff_phase" != setup ]; then evidence_examples=$examples; fi
  if [ "$status" -ne 0 ]; then
    if ! python3 scripts/diff-report.py failure --summary "$AIR2LEAN_DIFF_REPORT" \
      --root "$repo_root" --examples "$evidence_examples" --phase "$diff_phase"; then
      echo "error: could not record differential failure evidence" >&2
    fi
  fi
  if [ -n "$build_dir" ]; then rm -rf "$build_dir"; fi
  return "$status"
}
trap finish_diff EXIT
python3 scripts/diff-report.py init --summary "$AIR2LEAN_DIFF_REPORT" --root "$repo_root"

zig_bin=${AIR2LEAN_ZIG:-zig}
optimize=${AIR2LEAN_DIFF_OPTIMIZE:-ReleaseSafe}
backend_flag=
case "${AIR2LEAN_DIFF_BACKEND:-}" in
  "") ;;
  llvm) backend_flag=-fllvm ;;
  stage2_x86_64) backend_flag=-fno-llvm ;;
  *) echo "error: invalid AIR2LEAN_DIFF_BACKEND: $AIR2LEAN_DIFF_BACKEND" >&2; exit 1 ;;
esac
case "$optimize" in
  Debug|ReleaseSafe) exclude_ub=0 ;;
  ReleaseFast|ReleaseSmall) exclude_ub=1 ;;
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
python3 scripts/diff-report.py init --summary "$AIR2LEAN_DIFF_REPORT" --root "$repo_root" --examples "$examples"
diff_phase=build_native

# The names of an example's functions are the names of its input files (layout convention).
functions_of() {
  (cd "tests/diff/$1/inputs" && for f in *.jsonl; do printf '%s ' "${f%.jsonl}"; done)
}

echo "== building zig harnesses ==" >&2
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-diff.XXXXXX")
for ex in $examples; do
  # A fixed CPU: float results can depend on CPU features (FMA, native f16; docs/floats.md).
  # shellcheck disable=SC2086  # $backend_flag is empty or one flag
  "$zig_bin" build-exe -O"$optimize" -mcpu=baseline $backend_flag ${AIR2LEAN_DIFF_LINK_FLAGS:-} -femit-bin="$build_dir/$ex" \
    --dep "$ex" --dep common -Mroot="tests/diff/$ex/harness.zig" \
    -M"$ex"="examples/$ex/$ex.zig" -Mcommon=tests/diff/common.zig
  "$build_dir/$ex"
done

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

echo "== building asm archive ==" >&2
# tests/diff/asm/asm.zig re-implements examples/asm/asm.zig's ops with ordinary Zig builtins
# (@byteSwap/@popCount/@clz, `/` and `%`) instead of inline asm, so it builds on any host, unlike the example
# itself (x86_64 only). No compiler_rt dependency (unlike libm): these are plain integer ops.
mkdir -p tests/diff/out/asm
"$zig_bin" build-lib -static -fPIC -OReleaseFast -mcpu=baseline --name air2lean_asm \
  -femit-bin=tests/diff/out/asm/air2lean_asm.a -Mroot=tests/diff/asm/asm.zig

diff_phase=run_model
echo "== building + running lean side ==" >&2
# Lake does not track tests/diff/out/libm/air2lean_libm.a (linked in via lakefile.toml's
# moreLinkArgs) as a build input, so a changed archive alone would not trigger a relink.
rm -f tests/diff/.lake/build/bin/difftest
(cd tests/diff && lake build difftest)
(cd tests/diff && lake env lean --run ScheduleSearchTest.lean)
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
  # A function that takes an allocator also writes the number of live allocations after the
  # call: split it off.
  live=
  case "$line" in
    '{"ok":'*',"live":'*'}')
      live=${line##*,\"live\":}
      live=${live%\}}
      line="${line%,\"live\":*}}"
      ;;
  esac
  # A function that uses memory also writes the input buffers after the call: split them off.
  bufs=
  case "$line" in
    '{"ok":'*',"bufs":['*']}')
      bufs=${line##*,\"bufs\":}
      bufs=${bufs%\}}
      line="${line%,\"bufs\":*}}"
      ;;
  esac
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

# Load the shared native-panic/model-constructor policy once. Bash 3.2 indexed
# arrays avoid associative-array dependencies; each lookup uses only shell builtins.
panic_kinds=()
panic_ctors=()
while IFS=$'\t' read -r panic_kind panic_ctor; do
  [ -n "$panic_kind" ] || continue
  panic_kinds+=("$panic_kind")
  panic_ctors+=("$panic_ctor")
done <"$repo_root/scripts/panic-policy.tsv"
expected_ctor_for_zig_kind() {
  local i
  expected_ctor=""
  for ((i=0; i<${#panic_kinds[@]}; i++)); do
    if [ "${panic_kinds[$i]}" = "$1" ]; then
      expected_ctor=${panic_ctors[$i]}
      return 0
    fi
  done
}

# The pin of function `$1` in the pin file `$2`: "<count>" or "<min>-<max>"; not listed: 0.
pin_of() {
  local spec=0
  [ -f "$2" ] && spec=$(awk -v f="$1" '$1 == f { print $2 }' "$2")
  echo "${spec:-0}"
}

# The pin of function `$1` in the pin file `$2` allows the count `$3`.
pin_ok() {
  local spec lo hi
  spec=$(pin_of "$1" "$2")
  lo=${spec%-*}; hi=${spec#*-}
  [ "$3" -ge "$lo" ] && [ "$3" -le "$hi" ]
}

# The buffers after the call: a Lean `??` (an undefined byte, docs/generated-code.md §Memory)
# matches any two Zig hex digits. `[` and `]` are glob characters, so both sides replace them.
bufs_match() {
  local z=${1//[\[\]]/_} l=${2//[\[\]]/_}
  [[ $z == $l ]]
}

# The reference host of the float model (docs/floats.md).
reference_host=0
if [ "$(uname -s)" = Linux ] && [ "$(uname -m)" = x86_64 ]; then reference_host=1; fi

echo "== comparing ==" >&2
total_ok=0
total_fail_match=0
total_unspecified=0
total_capped=0
total_mismatch=0
total_host=0
total_ub=0
mismatch_found=0

for ex in $examples; do
  ex_ok=0
  ex_fail_match=0
  ex_unspecified=0
  ex_capped=0
  ex_mismatch=0
  ex_host=0
  ex_ub=0

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
    fn_ub=0
    fn_fail_match=0
    fn_unspecified=0
    fn_capped=0
    fn_mismatch=0
    fn_host=0
    host_dependent=0
    if [ "$reference_host" -eq 0 ] && [ -f "tests/diff/$ex/host.txt" ] &&
      grep -qx "$fn" "tests/diff/$ex/host.txt"; then
      host_dependent=1
    fi
    # A process substitution hides the producer's exit status from set -e/pipefail.
    # Materialize the joined rows first so a failed or truncated paste cannot pass.
    joined_file="$build_dir/compare.tsv"
    paste "$in_file" "$zig_file" "$lean_file" >"$joined_file"
    i=0
    while IFS=$'\t' read -r in_line zig_line lean_line; do
      i=$((i + 1))
      classify_line "$zig_line"
      zkind=$kind
      zval=${val:-}
      zbufs=$bufs
      zlive=$live
      classify_line "$lean_line"
      lkind=$kind
      lval=${val:-}
      lbufs=$bufs
      llive=$live

      if [ "$zkind" = ok ] && [ "$lkind" = ok ] && [ "$zval" = "$lval" ] &&
        bufs_match "$zbufs" "$lbufs" && [ "$zlive" = "$llive" ]; then
        fn_ok=$((fn_ok + 1))
      elif [ "$exclude_ub" -eq 1 ] && [ "$lkind" = fail ] &&
        [ "$lval" != Zig.Error.unspecified ] && [ "$lval" != Zig.Error.illegal ] &&
        [ "$lval" != Zig.Error.capped ] && [ "$lval" != Zig.Error.deadlock ]; then
        # The model throws: illegal behavior in a build without safety checks.
        fn_ub=$((fn_ub + 1))
      elif [ "$lkind" = fail ] && { [ "$lval" = Zig.Error.unspecified ] || [ "$lval" = Zig.Error.illegal ]; }; then
        fn_unspecified=$((fn_unspecified + 1))
      elif [ "$lkind" = fail ] && [ "$lval" = Zig.Error.capped ]; then
        fn_capped=$((fn_capped + 1))
      elif [ "$zkind" = fail ] && [ "$lkind" = fail ] &&
        expected_ctor_for_zig_kind "$zval" &&
        [ -n "$expected_ctor" ] &&
        [ "$expected_ctor" = "${lval#'Zig.Error.'}" ]; then
        fn_fail_match=$((fn_fail_match + 1))
      elif [ "$host_dependent" -eq 1 ]; then
        fn_host=$((fn_host + 1))
      else
        fn_mismatch=$((fn_mismatch + 1))
        mismatch_found=1
        echo "MISMATCH $ex.$fn input#$i: $in_line" >&2
        echo "  zig:  $zig_line" >&2
        echo "  lean: $lean_line" >&2
      fi
    done <"$joined_file"
    [ "$i" -eq "$n" ] || {
      echo "error: compared $i rows of $in_file, expected $n" >&2
      exit 1
    }

    if ! pin_ok "$fn" "tests/diff/$ex/unspecified.txt" "$fn_unspecified"; then
      mismatch_found=1
      echo "UNSPECIFIED COUNT $ex.$fn: $fn_unspecified, expected" \
        "$(pin_of "$fn" "tests/diff/$ex/unspecified.txt") (tests/diff/$ex/unspecified.txt)" >&2
    fi

    if ! pin_ok "$fn" "tests/diff/$ex/capped.txt" "$fn_capped"; then
      mismatch_found=1
      echo "CAPPED COUNT $ex.$fn: $fn_capped, expected" \
        "$(pin_of "$fn" "tests/diff/$ex/capped.txt") (tests/diff/$ex/capped.txt)" >&2
    fi

    host_str=""
    if [ "$fn_host" -gt 0 ]; then host_str=" host=$fn_host"; fi
    if [ "$fn_ub" -gt 0 ]; then host_str="$host_str ub_excluded=$fn_ub"; fi
    echo "$ex.$fn: ok=$fn_ok fail_match=$fn_fail_match unspecified=$fn_unspecified" \
      "capped=$fn_capped mismatch=$fn_mismatch$host_str (of $n)"
    ex_ok=$((ex_ok + fn_ok))
    ex_fail_match=$((ex_fail_match + fn_fail_match))
    ex_unspecified=$((ex_unspecified + fn_unspecified))
    ex_capped=$((ex_capped + fn_capped))
    ex_mismatch=$((ex_mismatch + fn_mismatch))
    ex_host=$((ex_host + fn_host))
    ex_ub=$((ex_ub + fn_ub))
  done

  host_str=""
  if [ "$ex_host" -gt 0 ]; then host_str=" host=$ex_host"; fi
  if [ "$ex_ub" -gt 0 ]; then host_str="$host_str ub_excluded=$ex_ub"; fi
  echo "TOTAL $ex: ok=$ex_ok fail_match=$ex_fail_match unspecified=$ex_unspecified" \
    "capped=$ex_capped mismatch=$ex_mismatch$host_str"
  total_ok=$((total_ok + ex_ok))
  total_fail_match=$((total_fail_match + ex_fail_match))
  total_unspecified=$((total_unspecified + ex_unspecified))
  total_capped=$((total_capped + ex_capped))
  total_mismatch=$((total_mismatch + ex_mismatch))
  total_host=$((total_host + ex_host))
  total_ub=$((total_ub + ex_ub))
done

host_str=""
if [ "$total_host" -gt 0 ]; then host_str=" host=$total_host"; fi
if [ "$total_ub" -gt 0 ]; then host_str="$host_str ub_excluded=$total_ub"; fi
echo "TOTAL: ok=$total_ok fail_match=$total_fail_match unspecified=$total_unspecified" \
  "capped=$total_capped mismatch=$total_mismatch$host_str"
if [ "$total_host" -gt 0 ]; then
  echo "note: $total_host host-dependent float results differ from the x86_64-linux model" \
    "(tests/diff/<ex>/host.txt); CI checks them" >&2
fi
if [ -n "${AIR2LEAN_DIFF_REPORT:-}" ]; then
  diff_phase=compare
  python3 "$repo_root/scripts/diff-report.py" compare --summary "$AIR2LEAN_DIFF_REPORT" \
    --root "$repo_root" --examples "$examples" --version "$zig_version" \
    --host "$(uname -s)-$(uname -m)" \
    ${AIR2LEAN_DIFF_OPTIMIZE:+--optimize "$AIR2LEAN_DIFF_OPTIMIZE" --backend "${AIR2LEAN_DIFF_BACKEND:-llvm}"} \
    --schedule-receipts "${AIR2LEAN_SCHEDULE_RECEIPTS:-}" || mismatch_found=1
fi
[ "$mismatch_found" -eq 0 ]
