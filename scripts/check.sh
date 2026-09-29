#!/usr/bin/env bash
# Full air2lean pipeline for each examples/<ex>/<ex>.zig:
#   1. dump AIR-JSON with the patched compiler (zig-patch/) and check it against the golden files
#   2. translate that AIR to Lean (`lake exe air2lean`)
#   3. build the generated Lean
#   4. differential-test it against the real Zig behaviour (scripts/diff.sh)
#
# Usage: check.sh
# Env:
#   AIR2LEAN_ZIG_VERSION  Zig version: selects the per-version goldens and the default patched zig.
#                         Default: 0.16.0
#   AIR2LEAN_ZIG_AIR      Patched zig (zig-patch/build.sh output). Default: zig-air-$AIR2LEAN_ZIG_VERSION/bin/zig
#   AIR2LEAN_CI           If 1: fail when the committed translation differs from the new translator
#                         output: tests/golden/<version>/<ex>/Gen.lean if it exists, else
#                         Proofs/<Ex>/Gen.lean.
#   AIR2LEAN_EXAMPLES     Space-separated example dirs to check. Default: every dir in examples/
#                         (not `asm` on a host that is not x86_64).
#                         Also forwarded (via the environment) to scripts/diff.sh at the end.
#   AIR2LEAN_DIFF         If 0: skip step 4. For a Zig version whose std cannot build the diff
#                         harness; the stale-Gen.lean check (AIR2LEAN_CI=1) then shows that the
#                         translation equals the one that the diff test checks.
#
# examples/<ex>/translate.args, if present: one line of extra `lake exe air2lean` arguments for
# that example (e.g. `--float-semantics compiler-rt`; docs/generated-code.md). Opt-in per
# example, since most examples never need a non-default flag.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

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
examples=${AIR2LEAN_EXAMPLES:-$(cd examples && for d in */; do
  if [ "${d%/}" = asm ] && [ "$(uname -m)" != x86_64 ]; then continue; fi
  if [ -f "${d}zig-versions" ] && ! grep -qx "$zig_version" "${d}zig-versions"; then continue; fi
  printf '%s ' "${d%/}"
done)}
restore_gen=""

for ex in $examples; do
  # <Ex>: the namespace/dir form of <ex> (layout convention) — first letter uppercased. No
  # `${ex^}`: that's a bash-4 operator, and macOS ships bash 3.2.
  Ex="$(printf '%s' "${ex:0:1}" | tr '[:lower:]' '[:upper:]')${ex:1}"
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
  trap 'rm -rf "$air_dir" "$cmp_dir"' EXIT

  # examples/<ex>/filter, if present: more name prefixes to translate, one per line: the std
  # functions that the example calls and that have no model (docs/std-models.md).
  filter="$ex."
  if [ -f "examples/$ex/filter" ]; then
    filter="$filter,$(paste -sd, "examples/$ex/filter")"
  fi
  echo "== $ex: dumping AIR ==" >&2
  ZIG_AIR_JSON_DIR="$air_dir" ZIG_AIR_JSON_FILTER="$filter" "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "examples/$ex/$ex.zig"

  if ! ls "$air_dir"/*.json >/dev/null 2>&1; then
    echo "error: the AIR dump of $ex wrote no files (ZIG_AIR_JSON_FILTER=$filter)" >&2
    exit 1
  fi

  echo "== $ex: checking against golden ($golden_dir, then $version_dir, then $os_dir) ==" >&2
  # Each file names the Zig version that wrote it; compare everything else. The number of a
  # generic std instance (`mem.Allocator.dupeZ__anon_16959`) or of a std type without a name
  # (`Thread.Completion__enum_1614`, `c.pthread_t__opaque_339`, `Io.Operation.Result__union_2204`,
  # a `__struct_N`) depends on how much std code the
  # compiler analyses, which differs by run and host OS in 0.16.0; the translator gives the first
  # a stable number (`Air2Lean/Air/Anon.lean`) and does not emit the others (`usedTys`; a
  # `Thread` handle is `Ty.thread`), so the comparison ignores them, also in the file names (a
  # golden file is `<name>__anon_N.json`).
  mkdir "$cmp_dir/golden" "$cmp_dir/new"
  norm_name() { printf '%s' "${1##*/}" | sed 's/__anon_[0-9][0-9]*/__anon_N/g'; }
  for f in "$golden_dir"/*.json "$version_dir"/*.json "$os_dir"/*.json; do
    if [ -f "$f" ]; then grep -v '"zig_version"' "$f" | sed -E 's/__(anon|enum|opaque|union|struct)_[0-9]+/__\1_N/g' >"$cmp_dir/golden/$(norm_name "$f")"; fi
  done
  for f in "$air_dir"/*.json; do
    n=$(norm_name "$f")
    if [ -f "$cmp_dir/new/$n" ]; then
      echo "error: $ex has two instances of the generic function in $n; the golden check cannot tell them apart" >&2
      exit 1
    fi
    grep -v '"zig_version"' "$f" | sed -E 's/__(anon|enum|opaque|union|struct)_[0-9]+/__\1_N/g' >"$cmp_dir/new/$n"
  done
  # diff exits 1 on a difference and 2 on an error (e.g. a missing golden dir): both fail.
  if ! diff_output=$(diff -r "$cmp_dir/golden" "$cmp_dir/new" 2>&1); then
    echo "error: AIR output for $ex does not match its golden files" >&2
    echo "$diff_output" >&2
    echo "hint: if only the golden files are stale (a deliberate exporter change), regenerate: cp $air_dir/* $golden_dir/ (then rename each <name>__anon_<n>.json to <name>__anon_N.json)" >&2
    echo "hint: if only Zig $zig_version differs, copy just the differing files to $version_dir/" >&2
    echo "hint: if only this host OS differs, copy just the differing files to $os_dir/" >&2
    exit 1
  fi

  echo "== $ex: translating to Lean ==" >&2
  translate_args=""
  if [ -f "examples/$ex/translate.args" ]; then
    translate_args=$(cat "examples/$ex/translate.args")
  fi
  lake exe air2lean "$air_dir" -o "Proofs/$Ex/Gen.lean" --namespace "$Ex" --prefix "$ex." $translate_args

  # The committed Proofs/<Ex>/Gen.lean is the translation for every Zig version, except a
  # version with its own tests/golden/<version>/<ex>/Gen.lean (its translation differs).
  gen_golden="tests/golden/$zig_version/$ex/Gen.lean"
  if [ -f "$gen_golden" ]; then
    # The committed Proofs/<Ex>/Gen.lean is overwritten in either mode: always say so (below).
    restore_gen="$restore_gen Proofs/$Ex/Gen.lean"
  fi
  if [ "${AIR2LEAN_CI:-0}" = 1 ] && [ -f "$gen_golden" ]; then
    if ! cmp -s "$gen_golden" "Proofs/$Ex/Gen.lean"; then
      diff -u "$gen_golden" "Proofs/$Ex/Gen.lean" >&2 || true
      echo "error: $gen_golden differs from the translator output; commit the new file" >&2
      exit 1
    fi
  # `git status` against HEAD: also catches a Gen.lean that is only staged or never added.
  elif [ "${AIR2LEAN_CI:-0}" = 1 ] && [ -n "$(git status --porcelain -- "Proofs/$Ex/Gen.lean")" ]; then
    git status --short -- "Proofs/$Ex/Gen.lean" >&2
    git diff HEAD -- "Proofs/$Ex/Gen.lean" >&2 || true
    echo "error: committed Proofs/$Ex/Gen.lean differs from the translator output; commit the new file" >&2
    exit 1
  fi

  rm -rf "$air_dir" "$cmp_dir"
  trap - EXIT
done

if [ -n "$restore_gen" ]; then
  echo "note: these files hold the Zig $zig_version translation:$restore_gen. Restore the committed ones with: git checkout --$restore_gen" >&2
fi

echo "== building Lean ==" >&2
lake build

if [ "${AIR2LEAN_DIFF:-1}" = 0 ]; then
  echo "== differential testing: skipped (AIR2LEAN_DIFF=0) ==" >&2
  exit 0
fi

echo "== differential testing ==" >&2
exec scripts/diff.sh
