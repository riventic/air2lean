#!/usr/bin/env bash
# Shared setup for doctor.sh, translate.sh and check.sh; source after computing repo_root.
# The callers supply zig_version, zig_air and caller_dir.
# shellcheck disable=SC2154
workflow_error() { printf 'error: %s\n' "$*" >&2; }
workflow_version() {
  case "$zig_version" in
    0.16.0 | 0.15.2 | 0.14.1) ;;
    *) workflow_error "unsupported Zig version '$zig_version'; choose 0.16.0, 0.15.2 or 0.14.1"; return 1 ;;
  esac
  if [ "$zig_version" = 0.14.1 ] && [ "$(uname -s)" != Linux ]; then
    workflow_error 'Zig 0.14.1 is supported on Linux only; choose 0.16.0 or 0.15.2 on this host'
    return 1
  fi
  zig_air=${zig_air:-"$repo_root/zig-air-$zig_version/bin/zig"}
  case "$zig_air" in /*) ;; *) zig_air="$caller_dir/$zig_air" ;; esac
  if [ "${zig_air##*/}" = zig-unlocked ]; then
    workflow_error 'use bin/zig, which preserves the AIR-only safety lock, instead of zig-unlocked'
    return 1
  fi
}
workflow_lean() {
  toolchain=$(cat "$repo_root/lean-toolchain")
  if ! command -v elan >/dev/null 2>&1; then
    workflow_error "elan is missing; install elan, then run: elan toolchain install $toolchain"
    return 1
  fi
  local installed
  if ! installed=$(elan toolchain list); then
    workflow_error 'could not list installed elan toolchains'
    return 1
  fi
  if ! printf '%s\n' "$installed" | awk '{print $1}' | grep -Fxq "$toolchain"; then
    workflow_error "pinned Lean toolchain is not installed; run: elan toolchain install $toolchain"
    return 1
  fi
}
workflow_lake() {
  # elan run installs a missing toolchain only when --install is explicitly supplied.
  workflow_run_stage env LEAN_NUM_THREADS=1 elan run "$toolchain" lake "$@"
}
workflow_patched_zig() {
  if [ ! -x "$zig_air" ] || [ -d "$zig_air" ]; then
    workflow_error "patched Zig is missing or not executable: $zig_air"
    printf 'hint: from the repository, run zig-patch/build.sh %s with stock Zig %s on PATH; see zig-patch/README.md\n' "$zig_version" "$zig_version" >&2
    return 1
  fi
  local actual
  if ! actual=$("$zig_air" version); then
    workflow_error "could not query patched Zig: $zig_air"
    return 1
  fi
  if [ "$actual" != "$zig_version" ]; then
    workflow_error "patched Zig reports '$actual', expected '$zig_version'; select the matching --zig-version and --zig-air"
    return 1
  fi
}
# Bounded stages (docs/safe-output.md): each command runs in its own process group under
# scripts/safe-output.py. A timeout, a leftover child process or a trapped signal stops the
# whole group before the caller cleans up, so no stage keeps writing a staged artifact.
# Callers set workflow_stage_timeout (seconds; 0 disables) and install
#   trap 'workflow_interrupt 130' INT   (likewise 129 for HUP, 143 for TERM).
workflow_stage_pid=''
workflow_run_stage() {
  # Run in the background and wait, so a trapped signal interrupts the wait at once.
  python3 "$repo_root/scripts/safe-output.py" run --timeout "${workflow_stage_timeout:-0}" -- "$@" &
  workflow_stage_pid=$!
  local status=0
  wait "$workflow_stage_pid" || status=$?
  workflow_stage_pid=''
  return "$status"
}
workflow_interrupt() {
  if [ -n "$workflow_stage_pid" ]; then
    kill -TERM "$workflow_stage_pid" 2>/dev/null || true
    wait "$workflow_stage_pid" 2>/dev/null || true
    workflow_stage_pid=''
  fi
  exit "$1"
}
workflow_publish() {
  # workflow_publish --overwrite|--no-clobber STAGED DESTINATION: fsync, then atomic rename/link.
  python3 "$repo_root/scripts/safe-output.py" publish "$@"
}
