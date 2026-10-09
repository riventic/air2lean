#!/usr/bin/env bash
# Q01 generated-program and parser fuzzing (docs/fuzzing.md).
#   --light [SEEDS]                 generator/shrinker unit tests + typed generator invariants; no tools
#   --air BINARY [SEEDS] [SAVE_DIR]  committed regressions + seeded malformed AIR JSON against a built translator
#   --heavy OUT_DIR [START] [COUNT]  generated Zig: native test, AIR export + translation, Lean evaluation
#   --reproduces CASE_DIR STAGE      exit 1 iff STAGE (native|translate|lean) is the first failing stage
# --heavy needs AIR2LEAN_ZIG_NATIVE (stock Zig) and AIR2LEAN_ZIG_AIR (patched Zig). It runs
# compilers and Lean sequentially; wrap the whole invocation in one scripts/build-guard.py.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/fuzz
export PYTHONDONTWRITEBYTECODE=1

stages=(native translate lean)

# Run the stages of one emitted case directory; print the first failing stage, if any.
first_failure() {
  local dir=$1 zig module namespace
  zig=$(find "$dir" -maxdepth 1 -name 'fuzz_s*.zig' -print -quit)
  module=$(basename "$zig" .zig)
  namespace="Fuzz${module#fuzz_}"
  if ! "$AIR2LEAN_ZIG_NATIVE" test "$zig" -OReleaseSafe >"$dir/native.log" 2>&1; then
    echo native; return
  fi
  if ! scripts/translate.sh "$zig" -o "$dir/Gen.lean" --namespace "$namespace" \
      --zig-air "$AIR2LEAN_ZIG_AIR" --overwrite >"$dir/translate.log" 2>&1; then
    echo translate; return
  fi
  if ! python3 "$here/zig_gen.py" lean-checks "$dir/expected.json" "$dir/Gen.lean" "$namespace" \
      "$dir/Check.lean" >"$dir/lean.log" 2>&1 || ! lake env lean "$dir/Check.lean" >>"$dir/lean.log" 2>&1; then
    echo lean; return
  fi
}

# A failure's normalized first error (paths, function names and numbers removed), so shrinking
# keeps the same failure rather than any failure at the same stage.
signature() {
  local dir=$1 stage=$2
  # translate.sh ends with its own "error: ..." line; the cause is the line before it.
  { case "$stage" in
      native) grep -E -m1 'error:' "$dir/native.log" ;;
      translate) grep -E -m1 'Gen\.lean:[0-9]+:[0-9]+: error' "$dir/translate.log" \
                   || grep -E -B1 -m1 '^error: ' "$dir/translate.log" | head -1 ;;
      *) grep -E -m1 'error' "$dir/lean.log" ;;
    esac || true; } \
    | sed -E 's#^.*\.(json|zig|lean)(:[0-9]+)*: ##; s#fuzz_s[0-9]+\.[A-Za-z0-9_]+: ##; s#fuzz_s[0-9]+#S#g; s#[0-9]+#N#g'
}

case "${1:-}" in
  --light)
    python3 -m unittest discover -s "$here" -p 'test_*.py' -v
    python3 "$here/zig_gen.py" light --seeds "${2:-300}"
    ;;
  --air)
    [ "$#" -ge 2 ] || { echo 'usage: check.sh --air BINARY [SEEDS] [SAVE_DIR]' >&2; exit 2; }
    python3 "$here/air_fuzz.py" replay "$2"
    save=()
    if [ -n "${4:-}" ]; then save=(--save "$4" --report "$4/report.json"); mkdir -p "$4"; fi
    python3 "$here/air_fuzz.py" run "$2" --seeds "${3:-200}" ${save[@]+"${save[@]}"}
    ;;
  --reproduces)
    [ "$#" -ge 3 ] || { echo 'usage: check.sh --reproduces CASE_DIR STAGE [SIG]' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig}" "${AIR2LEAN_ZIG_AIR:?set the patched Zig}"
    [ "$(first_failure "$2")" = "$3" ] || exit 0
    [ -z "${4:-}" ] || [ "$(signature "$2" "$3")" = "$4" ] || exit 0
    exit 1
    ;;
  --heavy)
    [ "$#" -ge 2 ] || { echo 'usage: check.sh --heavy OUT_DIR [START] [COUNT]' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig}" "${AIR2LEAN_ZIG_AIR:?set the patched Zig}"
    out=$2 start=${3:-0} count=${4:-5} failed=0
    # Each seed costs minutes (AIR export, translation, Lean); a range is capped unless overridden.
    max=${AIR2LEAN_FUZZ_HEAVY_MAX:-50}
    case "$start$count" in *[!0-9]*) echo 'START and COUNT must be whole numbers' >&2; exit 2 ;; esac
    [ "$count" -le "$max" ] || { echo "COUNT $count exceeds the cap $max (AIR2LEAN_FUZZ_HEAVY_MAX)" >&2; exit 2; }
    mkdir -p "$out"
    out=$(cd -- "$out" && pwd)
    for ((seed = start; seed < start + count; seed++)); do
      case_dir="$out/seed-$seed"
      rm -rf "$case_dir"
      python3 "$here/zig_gen.py" emit "$seed" "$case_dir" >/dev/null
      stage=$(first_failure "$case_dir")
      if [ -z "$stage" ]; then echo "seed $seed: ok"; continue; fi
      failed=1
      sig=$(signature "$case_dir" "$stage")
      echo "seed $seed: $stage failed [$sig]; shrinking (logs in $case_dir)"
      # A failure that does not reproduce (flaky) is reported, not fatal to the remaining seeds.
      # Every probe is a full pipeline run, so shrinking is capped (probes, not seconds).
      if python3 "$here/zig_gen.py" shrink "$case_dir/program.json" --budget "${AIR2LEAN_FUZZ_SHRINK_BUDGET:-150}" \
          --command "bash $here/check.sh --reproduces {dir} $stage ${sig:+$(printf '%q' "$sig")}" "$out/shrunk-$seed"; then
        first_failure "$out/shrunk-$seed" >/dev/null || true
      else
        echo "seed $seed: $stage failure did not reproduce for shrinking"
      fi
    done
    exit "$failed"
    ;;
  *)
    echo 'usage: check.sh --light [SEEDS]|--air BINARY [SEEDS] [SAVE_DIR]|--heavy OUT_DIR [START] [COUNT]|--reproduces CASE_DIR STAGE' >&2
    exit 2
    ;;
esac
