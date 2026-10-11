#!/usr/bin/env bash
# Export fresh AIR, translate and elaborate, then publish the checked Lean file.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
caller_dir=$PWD
. "$repo_root/scripts/workflow-common.sh"
usage() {
  cat <<'HELP'
Usage: scripts/translate.sh INPUT.zig -o OUTPUT.lean --namespace NAME [OPTIONS]

Export AIR, translate it and check the generated Lean. Publish OUTPUT only on success.
Run from any directory; input, output and --zig-air paths are relative to that directory.

Options:
  --zig-version VERSION     0.16.0 (default), 0.15.2, 0.14.1 (Linux only) or 0.17.0 (in qualification)
  --zig-air PATH            Existing patched compiler (default: repo/zig-air-VERSION/bin/zig)
  --prefix PREFIX           Strip this prefix from Lean names (default: input basename + '.')
  --filter PREFIXES         Comma-separated AIR name prefixes (default: --prefix)
  --float-semantics MODE    ieee (default) or compiler-rt; forwarded to air2lean
  --assume-no-lb            Accept relaxed load-then-store code (premise ORD-02); forwarded
  --overwrite               Replace an existing OUTPUT after a successful check (default)
  --no-clobber              Refuse to replace an existing OUTPUT, even one created concurrently
  --timeout SECONDS         Per-stage limit (default 3600; 0 disables); the stage's process
                            group is stopped and OUTPUT is left unchanged
  --help, -h                Show this help
  --                        Treat the next argument as the input, even if it starts with '-'

Environment: AIR2LEAN_ZIG_VERSION, AIR2LEAN_ZIG_AIR, AIR2LEAN_STAGE_TIMEOUT.
OUTPUT is written by fsync + atomic rename: an interrupted, failed or timed-out run leaves
the previous OUTPUT intact; see docs/safe-output.md.
Needs the installed Lean toolchain in lean-toolchain and an existing patched Zig.
No downloads or compiler bootstrap; Lean uses one worker per process and stages run sequentially.
Target: x86_64-linux -mcpu=baseline, ReleaseSafe, no error tracing or binary emission.
Functions must be exported or referenced (for example comptime { _ = &f; }).
Add unmodeled dependencies to --filter; see docs/std-models.md. This checks generated
Lean definitions; write and check property proofs separately.
HELP
}
zig_version=${AIR2LEAN_ZIG_VERSION:-0.16.0}
zig_air=${AIR2LEAN_ZIG_AIR:-}
input='' output='' namespace='' prefix='' filter='' float_semantics=ieee
overwrite=--overwrite workflow_stage_timeout=${AIR2LEAN_STAGE_TIMEOUT:-3600}
prefix_set=0 filter_set=0 positional_only=0 assume_no_lb=()
while [ "$#" -gt 0 ]; do
  if [ "$positional_only" = 1 ]; then
    [ -z "$input" ] || { workflow_error "unexpected argument: $1"; exit 2; }
    input=$1; shift; continue
  fi
  case "$1" in
    --help | -h) usage; exit 0 ;;
    --) positional_only=1; shift ;;
    --overwrite | --no-clobber) overwrite=$1; shift ;;
    --assume-no-lb) assume_no_lb=(--assume-no-lb); shift ;;
    -o | --namespace | --zig-version | --zig-air | --prefix | --filter | --float-semantics | --timeout)
      [ "$#" -ge 2 ] || { workflow_error "missing value for $1"; exit 2; }
      case "$1" in
        -o) output=$2 ;; --namespace) namespace=$2 ;; --zig-version) zig_version=$2 ;;
        --zig-air) zig_air=$2 ;; --prefix) prefix=$2; prefix_set=1 ;;
        --filter) filter=$2; filter_set=1 ;; --float-semantics) float_semantics=$2 ;;
        --timeout) workflow_stage_timeout=$2 ;;
      esac
      shift 2 ;;
    -*) workflow_error "unknown option: $1"; usage >&2; exit 2 ;;
    *) [ -z "$input" ] || { workflow_error "unexpected argument: $1"; exit 2; }; input=$1; shift ;;
  esac
done
[ -n "$input" ] && [ -n "$output" ] && [ -n "$namespace" ] || {
  workflow_error 'INPUT.zig, -o OUTPUT.lean and --namespace NAME are required'; usage >&2; exit 2;
}
case "$float_semantics" in
  ieee | compiler-rt) ;;
  *) workflow_error "invalid --float-semantics '$float_semantics'; choose ieee or compiler-rt"; exit 2 ;;
esac
case "$workflow_stage_timeout" in
  '' | *[!0-9]*) workflow_error "invalid --timeout '$workflow_stage_timeout'; give whole seconds (0 disables)"; exit 2 ;;
esac
command -v python3 >/dev/null 2>&1 || { workflow_error 'python3 is required for bounded stages and atomic publication'; exit 1; }
case "$input" in /*) ;; *) input="$caller_dir/$input" ;; esac
case "$output" in /*) ;; *) output="$caller_dir/$output" ;; esac
[ -f "$input" ] || { workflow_error "input file not found: $input"; exit 1; }
case "$output" in *.lean) ;; *) workflow_error '-o output must end in .lean'; exit 2 ;; esac
output_parent=$(dirname -- "$output")
[ -d "$output_parent" ] || { workflow_error "output directory does not exist: $output_parent; create it first"; exit 1; }
if { [ -e "$output" ] && [ ! -f "$output" ]; } || [ -L "$output" ] || [ "$input" -ef "$output" ]; then
  workflow_error 'output must be a regular file path distinct from the input (no symlinks or directories)'; exit 1
fi
if [ "$overwrite" = --no-clobber ] && [ -e "$output" ]; then
  workflow_error "output exists and --no-clobber was given: $output"; exit 1
fi
if [ "$prefix_set" = 0 ]; then source_name=${input##*/}; prefix="${source_name%.zig}."; fi
if [ "$filter_set" = 0 ]; then filter=$prefix; fi
workflow_version
workflow_lean
workflow_patched_zig
work='' stage='' lock=''
cleanup() {
  [ -z "$work" ] || rm -rf -- "$work"
  [ -z "$stage" ] || rm -rf -- "$stage"
  [ -z "$lock" ] || rmdir -- "$lock"
}
trap cleanup EXIT
trap 'workflow_interrupt 129' HUP
trap 'workflow_interrupt 130' INT
trap 'workflow_interrupt 143' TERM
# One pipeline per worktree. Do not steal a lock after an interrupted run: the
# user must first establish that no other translate.sh is still using this build.
mkdir -p "$repo_root/.lake"
if mkdir "$repo_root/.lake/air2lean-translate.lock" 2>/dev/null; then
  lock="$repo_root/.lake/air2lean-translate.lock"
else
  workflow_error "another translation owns $repo_root/.lake/air2lean-translate.lock"
  printf 'hint: wait for it to finish; after an interrupted run, verify no translation is running before removing this empty lock directory\n' >&2
  exit 1
fi
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-translate.XXXXXX")
work=$(cd -- "$work" && pwd)
stage=$(mktemp -d "$output_parent/.air2lean-output.XXXXXX")
mkdir "$work/air"
cd "$repo_root"
printf '1/4 Building runtime and translator\n' >&2
if ! workflow_lake build ZigLean air2lean; then
  workflow_error 'Lean build failed; output was not changed'; exit 1
fi
printf '2/4 Exporting fresh AIR (x86_64-linux, baseline CPU)\n' >&2
if ! workflow_run_stage env ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER="$filter" "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline "$input" \
    2>"$work/export.stderr"; then
  cat "$work/export.stderr" >&2
  workflow_error 'AIR export failed; check the Zig source and patched compiler; output was not changed'; exit 1
fi
cat "$work/export.stderr" >&2
if grep -Eq 'air2lean: (cannot open|name too long for a file|no JSON for|incomplete JSON for)' "$work/export.stderr"; then
  workflow_error 'AIR export was incomplete; resolve the exporter warning above; output was not changed'
  exit 1
fi
jsons=("$work/air"/*.json)
if [ ! -f "${jsons[0]}" ]; then
  workflow_error "no fresh AIR files were exported (filter: '$filter')"
  printf 'hint: use the patched compiler; export fn or reference functions in comptime { _ = &f; }; check --filter\n' >&2
  exit 1
fi
printf '3/4 Translating AIR to Lean\n' >&2
if ! workflow_run_stage "$repo_root/.lake/build/bin/air2lean" "$work/air" -o "$stage/Gen.lean" \
    --namespace "$namespace" --prefix "$prefix" --float-semantics "$float_semantics" \
    ${assume_no_lb[@]+"${assume_no_lb[@]}"}; then
  workflow_error 'translation failed; check the reported subset/model limitation; output was not changed'; exit 1
fi
[ -f "$stage/Gen.lean" ] || { workflow_error 'translator did not write fresh Lean output'; exit 1; }
printf '4/4 Checking generated Lean\n' >&2
if ! workflow_lake env lean "$stage/Gen.lean"; then
  workflow_error 'generated Lean did not elaborate; output was not changed'; exit 1
fi
if { [ -e "$output" ] && [ ! -f "$output" ]; } || [ -L "$output" ] || [ "$input" -ef "$output" ]; then
  workflow_error 'output path changed while translating; refusing to publish'; exit 1
fi
# fsync + atomic rename (or no-clobber link) beside OUTPUT; a failure leaves OUTPUT unchanged.
workflow_publish "$overwrite" "$stage/Gen.lean" "$output" || exit 1
printf 'Generated and checked: %s\nWrite property proofs separately; see docs/proofs.md.\n' "$output"
