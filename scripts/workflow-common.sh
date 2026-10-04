#!/usr/bin/env bash
# Shared setup for doctor.sh and translate.sh; source after computing repo_root.
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
  LEAN_NUM_THREADS=1 elan run "$toolchain" lake "$@"
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
