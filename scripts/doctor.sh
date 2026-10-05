#!/usr/bin/env bash
# Diagnose first-use prerequisites without downloads, builds or AIR export.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
caller_dir=$PWD
. "$repo_root/scripts/workflow-common.sh"
usage() {
  cat <<'HELP'
Usage: scripts/doctor.sh [--zig-version VERSION] [--zig-air PATH]

Check the pinned installed Lean toolchain, stock Zig and an existing patched Zig.
No downloads or builds. Defaults: Zig 0.16.0, zig-air-VERSION/bin/zig.
Environment: AIR2LEAN_ZIG_VERSION, AIR2LEAN_ZIG_AIR, AIR2LEAN_ZIG (stock Zig).
A version check cannot prove an arbitrary Zig binary includes the AIR exporter;
translate.sh checks that it actually writes fresh AIR.
HELP
}
zig_version=${AIR2LEAN_ZIG_VERSION:-0.16.0}
zig_air=${AIR2LEAN_ZIG_AIR:-}
while [ "$#" -gt 0 ]; do
  case "$1" in
    --help | -h) usage; exit 0 ;;
    --zig-version | --zig-air)
      [ "$#" -ge 2 ] && [ -n "$2" ] || { workflow_error "missing value for $1"; exit 2; }
      case "$1" in --zig-version) zig_version=$2 ;; --zig-air) zig_air=$2 ;; esac
      shift 2 ;;
    *) workflow_error "unknown argument: $1"; usage >&2; exit 2 ;;
  esac
done
workflow_version
failed=0
if workflow_lean; then
  printf 'OK: pinned Lean %s is installed\n' "$toolchain"
  printf 'Ready for committed proofs: lake build Proofs.Basic.Proofs\n'
else failed=1; fi
stock_zig=${AIR2LEAN_ZIG:-zig}
if ! command -v "$stock_zig" >/dev/null 2>&1; then
  printf 'note: stock Zig is missing (%s); only rebuilding the exporter needs Zig %s on PATH\n' "$stock_zig" "$zig_version"
elif ! stock_version=$("$stock_zig" version); then
  printf 'note: could not query stock Zig (%s); only rebuilding the exporter needs it\n' "$stock_zig"
else
  case "$stock_version" in
    0.16.0 | 0.15.2 | 0.14.1)
      printf 'OK: stock Zig %s (%s)\n' "$stock_version" "$stock_zig"
      if [ "$stock_version" != "$zig_version" ]; then
        printf 'note: rebuilding the Zig %s exporter needs stock Zig %s on PATH\n' "$zig_version" "$zig_version"
      fi ;;
    *) printf 'note: stock Zig %s is unsupported; rebuilding the exporter needs Zig %s on PATH\n' "$stock_version" "$zig_version" ;;
  esac
fi
if workflow_patched_zig; then printf 'OK: patched Zig %s (%s; exporter verified during translation)\n' "$zig_version" "$zig_air"; else failed=1; fi
if [ -x "$repo_root/.lake/build/bin/air2lean" ]; then
  printf 'OK: translator build exists; translate.sh refreshes it before use\n'
else
  printf 'note: translator is not built yet; translate.sh builds it before exporting AIR\n'
fi
printf 'Model: x86_64-linux, baseline CPU, little-endian 64-bit pointers; ReleaseSafe AIR.\n'
if [ "$failed" -ne 0 ]; then exit 1; fi
printf 'Ready: scripts/translate.sh INPUT.zig -o OUTPUT.lean --namespace My\n'
