#!/usr/bin/env bash
# Full air2lean pipeline for each examples/<ex>/<ex>.zig:
#   1. dump AIR-JSON and validate/translate its real profiles (`lake exe air2lean`)
#   2. compare AIR and generated semantics with goldens, retaining profile provenance
#   3. build the generated Lean
#   4. differential-test it against the real Zig behaviour (scripts/diff.sh)
#
# It never writes a tracked file. Steps 3-4 run in the checkout when every committed
# Proofs/<Ex>/Gen.lean already holds the new translation (identical after the first-line profile
# record), else in a check tree (scripts/check-tree.py): a copy of the checkout with the new
# translations in place of the committed ones. Its path is written to
# $AIR2LEAN_CHECK_REPORT_DIR/build-tree; later steps that build this version's proofs run there.
#
# Usage: check.sh
# Env:
#   AIR2LEAN_ZIG_VERSION  Zig version: selects the per-version goldens and the default patched zig.
#                         Default: 0.16.0
#   AIR2LEAN_ZIG_AIR      Patched zig (zig-patch/build.sh output). Default: zig-air-$AIR2LEAN_ZIG_VERSION/bin/zig
#   AIR2LEAN_CI           If 1: fail when the committed translation differs from the new translator
#                         output: tests/golden/<version>/<ex>/Gen.lean if it exists, else
#                         Proofs/<Ex>/Gen.lean; and when Proofs/ differs from HEAD at all.
#   AIR2LEAN_EXAMPLES     Space-separated example dirs to check. Default: every dir in examples/
#                         (not `asm` on a host that is not x86_64).
#                         Also forwarded (via the environment) to scripts/diff.sh at the end.
#   AIR2LEAN_OUT_DIR      If set: copy each example's dumped AIR-JSON to $AIR2LEAN_OUT_DIR/<ex>/,
#                         before the golden check. CI uploads it when a job fails: the golden
#                         files of another host OS (tests/golden/<version>/<ex>/air-<os>/) come
#                         from there, and the translator makes that OS's Gen.lean from them.
#   AIR2LEAN_CHECK_REPORT_DIR  Profile/input/generated-hash receipts. Default:
#                         .lake/check-reports/<zig-version>/; actual generated sources are retained.
#   AIR2LEAN_CHECK_TREE   The check tree, when one is needed. Default: .lake/check-tree/<zig-version>.
#   AIR2LEAN_STAGE_TIMEOUT  Seconds per AIR dump/translation stage (default 3600; 0 disables).
#                         A timed-out or interrupted stage's process group is stopped.
#   AIR2LEAN_DIFF         If 0: skip step 4. For a Zig version whose std cannot build the diff
#                         harness; the stale-Gen.lean check (AIR2LEAN_CI=1) then shows that the
#                         translation equals the one that the diff test checks.
#
# examples/<ex>/translate.args, if present: one line of extra `lake exe air2lean` arguments for
# that example (e.g. `--float-semantics compiler-rt`; docs/generated-code.md). Opt-in per
# example, since most examples never need a non-default flag.
#
# Generated Gen.lean files and check reports are staged, fsynced and atomically renamed
# into place (docs/safe-output.md): an interrupted, failed or timed-out run leaves each
# previous file intact, never a prefix of a new one.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"
. "$repo_root/scripts/workflow-common.sh"
workflow_stage_timeout=${AIR2LEAN_STAGE_TIMEOUT:-3600}
case "$workflow_stage_timeout" in
  '' | *[!0-9]*) echo "error: AIR2LEAN_STAGE_TIMEOUT must be whole seconds (0 disables)" >&2; exit 2 ;;
esac
air_dir='' cmp_dir=''
cleanup() {
  [ -z "$air_dir" ] || rm -rf -- "$air_dir"
  [ -z "$cmp_dir" ] || rm -rf -- "$cmp_dir"
}
trap cleanup EXIT
trap 'workflow_interrupt 129' HUP
trap 'workflow_interrupt 130' INT
trap 'workflow_interrupt 143' TERM

zig_version=${AIR2LEAN_ZIG_VERSION:-0.16.0}
zig_air=${AIR2LEAN_ZIG_AIR:-zig-air-$zig_version/bin/zig}
[ -x "$zig_air" ] || {
  echo "error: patched zig not found/executable at $zig_air" >&2
  echo "hint: build one with zig-patch/build.sh $zig_version (see zig-patch/README.md)" >&2
  exit 1
}

# The default list skips `asm` on a host that is not x86_64: its asm is x86_64 only
# (examples/asm/asm.zig). It also skips an example whose `examples/<ex>/zig-versions` file (one
# version per line) does not list this Zig version (`sync`: std code that only 0.16.0 has).
if [ -n "${AIR2LEAN_EXAMPLES:-}" ]; then
  examples=$AIR2LEAN_EXAMPLES
else
  source "$repo_root/scripts/example-selection.sh"
  examples=$(air2lean_default_examples "$repo_root" "$zig_version" "$(uname -m)")
fi
gen_targets=()
replacements=()
report_dir=${AIR2LEAN_CHECK_REPORT_DIR:-.lake/check-reports/$zig_version}
rm -f "$report_dir/build-tree"  # Written only once this run has selected its modules.
if [ "${AIR2LEAN_CI:-0}" = 1 ]; then
  # The checkout's modules are compared with HEAD's and may be built: they must be HEAD's.
  python3 scripts/normalize-generated.py proof-status
fi

for ex in $examples; do
  # <Ex>: the namespace/dir form of <ex> (layout convention) — first letter uppercased. No
  # `${ex^}`: that's a bash-4 operator, and macOS ships bash 3.2.
  Ex="$(printf '%s' "${ex:0:1}" | tr '[:lower:]' '[:upper:]')${ex:1}"
  gen_targets+=("Proofs.$Ex.Gen")
  # One golden set for every Zig version (tests/golden/<ex>/air/). A file in
  # tests/golden/<version>/<ex>/air/ replaces the shared file of the same name for that version
  # only (PLAN.md §Zig version support). A file in tests/golden/<version>/<ex>/air-<os>/ (os:
  # `uname -s` in lower case) replaces it on that host OS only: std code that the compiler picks
  # by OS (`std.Thread`'s implementation) is in the type table. The translation does not change
  # (the translator emits only the types that the code uses).
  golden_dir="tests/golden/$ex/air"
  version_dir="tests/golden/$zig_version/$ex/air"
  os_dir="tests/golden/$zig_version/$ex/air-$(uname -s | tr '[:upper:]' '[:lower:]')"
  air_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-check.XXXXXX")
  cmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-check.XXXXXX")

  # examples/<ex>/filter, if present: more name prefixes to translate, one per line: the std
  # functions that the example calls and that have no model (docs/std-models.md).
  filter="$ex."
  if [ -f "examples/$ex/filter" ]; then
    filter="$filter,$(paste -sd, "examples/$ex/filter")"
  fi
  echo "== $ex: dumping AIR ==" >&2
  workflow_run_stage env ZIG_AIR_JSON_DIR="$air_dir" ZIG_AIR_JSON_FILTER="$filter" "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "examples/$ex/$ex.zig"

  if ! ls "$air_dir"/*.json >/dev/null 2>&1; then
    echo "error: the AIR dump of $ex wrote no files (ZIG_AIR_JSON_FILTER=$filter)" >&2
    exit 1
  fi
  if [ -n "${AIR2LEAN_OUT_DIR:-}" ]; then
    mkdir -p "$AIR2LEAN_OUT_DIR/$ex"
    cp "$air_dir"/*.json "$AIR2LEAN_OUT_DIR/$ex/"
  fi

  # Profile checks run on the actual, complete program before any metadata-insensitive
  # comparison. Keep generation temporary until every golden/CI check passes.
  echo "== $ex: validating profiles and translating to Lean ==" >&2
  translate_args=""
  if [ -f "examples/$ex/translate.args" ]; then
    translate_args=$(cat "examples/$ex/translate.args")
  fi
  generated="$cmp_dir/Gen.lean"
  workflow_run_stage lake exe air2lean "$air_dir" -o "$generated" --namespace "$Ex" --prefix "$ex." $translate_args
  mkdir -p "$report_dir"
  report="$report_dir/$ex.json"
  python3 scripts/normalize-generated.py report "$generated" "$air_dir" "$cmp_dir/report.json"
  workflow_publish --overwrite "$cmp_dir/report.json" "$report"
  workflow_publish --overwrite "$generated" "$report_dir/$ex.Gen.lean"
  if [ -n "${AIR2LEAN_OUT_DIR:-}" ]; then
    mkdir -p "$AIR2LEAN_OUT_DIR/check-reports/$zig_version"
    workflow_publish --overwrite "$cmp_dir/report.json" "$AIR2LEAN_OUT_DIR/check-reports/$zig_version/$ex.json"
    workflow_publish --overwrite "$generated" "$AIR2LEAN_OUT_DIR/check-reports/$zig_version/$ex.Gen.lean"
  fi

  echo "== $ex: checking against golden ($golden_dir, then $version_dir, then $os_dir) ==" >&2
  # A validated receipt permits the known schema-12 profile/schema-11 transition.
  # Target/profile failures are already fatal; observable AIR data remains compared.
  # The number of a generic std instance (`mem.Allocator.dupeZ__anon_16959`) or of a std type without a name
  # (`Thread.Completion__enum_1614`, `c.pthread_t__opaque_339`, `Io.Operation.Result__union_2204`,
  # a `__struct_N`) depends on how much std code the
  # compiler analyses, which differs by run and host OS in 0.16.0; the translator gives the first
  # a stable number (`Air2Lean/Air/Anon.lean`) and does not emit the others (`usedTys`; a
  # `Thread` handle is `Ty.thread`). Normalize only compiler identities, preserving observable
  # field/error names and string/asm data. Normalize function file names too (a golden file
  # is `<name>__anon_N.json`).
  #
  # Two instances of one generic function (`math.sub` for `u64` and for `i64`) have the same
  # normalized name: each gets its content hash in the name (`math.sub__anon_N.<hash>.json`), so
  # the comparison matches them by content. A later directory (version, OS) replaces every file of
  # a name in the earlier ones, all instances together.
  mkdir "$cmp_dir/golden" "$cmp_dir/new"
  # One process per directory loads/indexes the receipt once. Later overlays remove
  # every earlier normalized basename variant; collision hashes retain the old format.
  add_dir() {
    [ -d "$1" ] || return 0
    if [ "$3" = actual ]; then
      python3 scripts/normalize-air.py "$1" --output-dir "$2" --check-report "$report" --actual
    else
      python3 scripts/normalize-air.py "$1" --output-dir "$2" --check-report "$report"
    fi
  }
  add_dir "$golden_dir" "$cmp_dir/golden" golden
  add_dir "$version_dir" "$cmp_dir/golden" golden
  add_dir "$os_dir" "$cmp_dir/golden" golden
  add_dir "$air_dir" "$cmp_dir/new" actual
  # diff exits 1 on a difference and 2 on an error (e.g. a missing golden dir): both fail.
  if ! diff_output=$(diff -r "$cmp_dir/golden" "$cmp_dir/new" 2>&1); then
    echo "error: AIR output for $ex does not match its golden files" >&2
    echo "$diff_output" >&2
    echo "hint: if only the golden files are stale (a deliberate exporter change), regenerate: cp $air_dir/* $golden_dir/ (then rename each <name>__anon_<n>.json to <name>__anon_N.json)" >&2
    echo "hint: if only Zig $zig_version differs, copy just the differing files to $version_dir/" >&2
    echo "hint: if only this host OS differs, copy just the differing files to $os_dir/" >&2
    exit 1
  fi

  # The committed Proofs/<Ex>/Gen.lean is the translation for every Zig version on Linux (the
  # reference host), except a version with its own tests/golden/<version>/<ex>/Gen.lean, and a
  # host OS with its own tests/golden/<version>/<ex>/Gen-<os>.lean (std code that differs per
  # OS, e.g. 0.15.2's `std.Thread.Mutex`; os: `uname -s` in lower case, as for air-<os>/).
  gen_golden="tests/golden/$zig_version/$ex/Gen-$(uname -s | tr '[:upper:]' '[:lower:]').lean"
  [ -f "$gen_golden" ] || gen_golden="tests/golden/$zig_version/$ex/Gen.lean"
  [ -f "$gen_golden" ] || gen_golden="Proofs/$Ex/Gen.lean"
  # Generated comparisons skip only the first-line profile record (host-specific: the target
  # triple names the kernel and libc versions); the committed files are canonical bodies.
  if ! python3 scripts/normalize-generated.py compare "$gen_golden" "$generated" "$report"; then
    if [ "${AIR2LEAN_CI:-0}" = 1 ]; then
      diff -u "$gen_golden" "$generated" >&2 || true
      echo "error: committed $gen_golden differs from the translator output; commit the new file" >&2
      exit 1
    fi
    echo "note: $gen_golden is not this translation; to commit it: cp $report_dir/$ex.Gen.lean $gen_golden" >&2
  fi
  # Build and test the new translation: the checkout's module only when it is the same one.
  if ! python3 scripts/normalize-generated.py compare "Proofs/$Ex/Gen.lean" "$generated" "$report" 2>/dev/null; then
    replacements+=(--replace "Proofs/$Ex/Gen.lean=$report_dir/$ex.Gen.lean")
  fi

  rm -rf "$air_dir" "$cmp_dir"
  air_dir='' cmp_dir=''
done

[ "${#gen_targets[@]}" -gt 0 ] || { echo "error: no examples selected" >&2; exit 1; }
tree=$repo_root
if [ "${#replacements[@]}" -gt 0 ]; then
  tree=${AIR2LEAN_CHECK_TREE:-$repo_root/.lake/check-tree/$zig_version}
  echo "== check tree $tree: this translation in place of committed modules (${replacements[*]}) ==" >&2
  python3 "$repo_root/scripts/check-tree.py" create "$tree" "${replacements[@]}"
  tree=$(cd -- "$tree" && pwd)
fi
printf '%s\n' "$tree" > "$report_dir/build-tree"
cd "$tree"
echo "== building Lean ==" >&2
lake build "${gen_targets[@]}"

if [ "${AIR2LEAN_DIFF:-1}" = 0 ]; then
  echo "== differential testing: skipped (AIR2LEAN_DIFF=0) ==" >&2
  exit 0
fi

echo "== differential testing ==" >&2
exec scripts/diff.sh
