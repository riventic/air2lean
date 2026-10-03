#!/usr/bin/env bash
# Lock a patched zig that has no LLVM (build.sh's default): put a wrapper in front of it that
# allows only what air2lean uses — an AIR dump (`build-obj`/`build-exe`/`build-lib`/`test` with
# `-fno-emit-bin`), `version`, `env`, `targets` — and refuses everything else with an error.
#
# Why: without LLVM, the compiler makes machine code for the host with Zig's own backends. On
# aarch64-macos that backend crashes at once (SIGBUS), also for a hello world, and each crash
# made macOS's crash reporter use tens of GB of memory. Build and run programs with a stock zig
# (or a patched zig built with AIR2LEAN_LLVM=1, which needs no lock).
#
# Usage: lock.sh <prefix>   (the prefix of build.sh; moves bin/zig to bin/zig-unlocked)
set -euo pipefail

prefix=${1:?"usage: lock.sh <prefix>"}
bin="$prefix/bin"
[ -x "$bin/zig" ] || { echo "error: no $bin/zig" >&2; exit 1; }
# Idempotent: bin/zig is the wrapper after a run. A new build installs a new compiler as
# bin/zig: it replaces the old bin/zig-unlocked.
if ! grep -q 'air2lean-lock' "$bin/zig" 2>/dev/null; then
  mv -f "$bin/zig" "$bin/zig-unlocked"
fi

cat >"$bin/zig" <<'EOF'
#!/usr/bin/env bash
# air2lean-lock: a patched zig without LLVM. It only writes AIR (zig-patch/lock.sh).
real="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/zig-unlocked"
case "${1:-}" in
  version | env | targets | help | -h | --help) exec "$real" "$@" ;;
  build-obj | build-exe | build-lib | test)
    # Response files can hide emission overrides, and a flag-looking token can be another
    # option's value. Reject hidden overrides and inject a flag at a guaranteed option position.
    no_bin=0
    for a in "$@"; do
      case "$a" in
        -fno-emit-bin) no_bin=1 ;;
        -femit-bin*) no_bin=0; break ;;
        @*) no_bin=0; break ;;
      esac
    done
    if [ "$no_bin" = 1 ]; then exec "$real" "$1" -fno-emit-bin "${@:2}"; fi ;;
esac
echo "error: this patched zig has no LLVM and only writes AIR (build-obj -fno-emit-bin)." >&2
echo "Build and run programs with a stock zig, or rebuild this one with AIR2LEAN_LLVM=1" >&2
echo "(zig-patch/README.md). Without LLVM, native code for this host can crash the compiler." >&2
exit 2
EOF
chmod +x "$bin/zig"
echo "locked: $bin/zig (the compiler is $bin/zig-unlocked)" >&2
