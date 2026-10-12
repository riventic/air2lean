#!/usr/bin/env bash
# The `run:` shell of a traced CI job (`defaults: run: shell: bash scripts/ci-trace.sh {0}`,
# docs/ci.md#enforcement). Without AIR2LEAN_TRACE_DIR it is GitHub's own bash invocation. With it,
# the step runs under `strace -f` and scripts/ci-reuse.py reduces every file-system observation of
# every process to <dir>/<n>.json; <n>.started marks a step whose reduction must exist. The step
# runs without the run-specific GITHUB_* variables (their values differ per run, the job text does
# not) and without the reuse decision's own variables. AIR2LEAN_UNTRACED=1 runs a step plain: only
# the coverage check and the record step after every gate may set it (ci-reuse.py check-workflow).
set -u
script=$1
if [ -z "${AIR2LEAN_TRACE_DIR:-}" ] || [ "${AIR2LEAN_UNTRACED:-}" = 1 ]; then
  exec bash --noprofile --norc -eo pipefail "$script"
fi
dir=$AIR2LEAN_TRACE_DIR tool=$AIR2LEAN_REUSE_TOOL
step=$(printf '%04d' "$(find "$dir" -maxdepth 1 -name '*.started' | wc -l)")
: > "$dir/$step.started"
keep='^(GITHUB_(WORKSPACE|ENV|PATH|OUTPUT|STEP_SUMMARY|STATE|ACTIONS|REPOSITORY|SERVER_URL|API_URL)|RUNNER_(TEMP|OS|ARCH|TOOL_CACHE|WORKSPACE|ENVIRONMENT))$'
for name in $(compgen -e); do
  case "$name" in
    GITHUB_*|ACTIONS_*|RUNNER_*|AIR2LEAN_REUSE*|AIR2LEAN_TRACE_DIR|AIR2LEAN_SELF_CHECK|AIR2LEAN_RECORD|AIR2LEAN_PART)
      [[ $name =~ $keep ]] || unset "$name" ;;
  esac
done
# -q, not -qq: the reducer needs the exit lines (a later process can reuse a pid). The step's own
# status; strace exits with it (128+n for a signal). The reducer's pipe is closed and waited for
# before strace exits, so <step>.json is complete when this returns.
strace -f --seccomp-bpf -y -q -s 65536 \
  -e trace=%file,getdents64,getdents,chdir,fchdir,clone,clone3,fork,vfork \
  -o "|python3 -I $tool reduce --workspace $GITHUB_WORKSPACE --out $dir/$step.json" \
  bash --noprofile --norc -eo pipefail "$script"
