#!/usr/bin/env bash
# T03 concurrency and allocator models at both byte orders (`concurrency.zig`, README.md
# §Concurrency). Exports for s390x-linux and mips64-linux (big endian) and x86_64-linux (little
# endian) with Zig 0.17.0, and 0.15.2 (which also has `std.Thread.Futex`).
#
#   concurrency.sh [--check]          translate air/<version>/concurrency/<target>, compare with
#                                     conc-gen/<version>-<target>.lean, build, run ConcDiff.lean and ConcFutex.lean
#                                     (24 scheduler oracles per case) and compare with
#                                     observed/concurrency-<version>-<target>.txt
#   concurrency.sh --native VERSION   build concurrency_native.zig with a stock Zig VERSION
#                                     (AIR2LEAN_ZIG_NATIVE) for each target, run it and compare
#                                     with the retained observation: s390x in Docker
#                                     linux/s390x, mips64 and x86_64 in Docker linux/amd64 (mips64
#                                     through the Docker VM's qemu-mips64 binfmt handler, which
#                                     matches ELF ABI version 0: the copy that runs has
#                                     EI_ABIVERSION cleared, the code is unchanged)
#   concurrency.sh --export VERSION DIR   fresh AIR (AIR2LEAN_ZIG_AIR)
# Run in the serialized build queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/big-endian
versions=(0.15.2 0.17.0)
targets=(s390x-linux mips64-linux x86_64-linux)
case "${1:---check}" in
  --export)
    [ "$#" -eq 3 ] || { echo 'usage: concurrency.sh --export VERSION DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a patched Zig with the repository exporter}"
    for t in "${targets[@]}"; do
      out="$3/$t"
      mkdir -p "$out"
      [ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo "$out must be empty" >&2; exit 1; }
      cpu=()
      [ "$t" = x86_64-linux ] && cpu=(-mcpu=baseline)
      ZIG_AIR_JSON_DIR="$(cd -- "$out" && pwd)" ZIG_AIR_JSON_FILTER=concurrency.,atomic.Value \
        "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
        -target "$t" "${cpu[@]}" "$dir/concurrency.zig"
    done
    exit ;;
  --native)
    [ "$#" -eq 2 ] || { echo 'usage: concurrency.sh --native VERSION' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig of that version}"
    work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-be-conc.XXXXXX")
    trap 'rm -rf "$work"' EXIT
    for t in "${targets[@]}"; do
      arch=${t%-linux}
      abi=musl
      [ "$arch" = mips64 ] && abi=muslabi64
      "$AIR2LEAN_ZIG_NATIVE" build-exe -OReleaseSafe -target "$t-$abi" -femit-bin="$work/$arch" \
        "$dir/concurrency_native.zig"
      platform=linux/amd64
      [ "$arch" = s390x ] && platform=linux/s390x
      [ "$arch" = mips64 ] && python3 "$dir/elf-abiversion.py" "$work/$arch"
      docker run --rm --platform "$platform" -v "$work:/w:ro" alpine:3 sh -c "/w/$arch 2>&1" \
        > "$work/$arch.txt"
      diff -u "$dir/observed/concurrency-$2-$t.txt" "$work/$arch.txt"
      echo "native $t ($2) matches the retained observation"
    done
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: concurrency.sh [--check]' >&2; exit 2; } ;;
  *) echo 'usage: concurrency.sh [--check|--native VERSION|--export VERSION DIR]' >&2; exit 2 ;;
esac
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-be-conc.XXXXXX")
trap 'rm -rf "$work"' EXIT
for v in "${versions[@]}"; do
  for t in "${targets[@]}"; do
    w="$work/$v-$t"
    mkdir -p "$w/Conc"
    "$translator" "$dir/air/$v/concurrency/$t" -o "$w/Conc/Gen.lean" --namespace Conc \
      --prefix concurrency.
    cmp "$w/Conc/Gen.lean" "$dir/conc-gen/$v-$t.lean"
    LEAN_PATH="$w:$repo_root/.lake/build/lib/lean" \
      "${lean_cmd[@]}" -R "$w" -o "$w/Conc/Gen.olean" "$w/Conc/Gen.lean"
    cp "$dir/ConcRun.lean" "$dir/ConcDiff.lean" "$dir/ConcFutex.lean" "$w/"
    export LEAN_PATH="$w:$repo_root/.lake/build/lib/lean"
    "${lean_cmd[@]}" -R "$w" -o "$w/ConcRun.olean" "$w/ConcRun.lean"
    "${lean_cmd[@]}" -R "$w" --run "$w/ConcDiff.lean" > "$w/lines.txt" \
      || { cat "$w/lines.txt" >&2; exit 1; }
    if [ "$v" = 0.15.2 ]; then
      "${lean_cmd[@]}" -R "$w" --run "$w/ConcFutex.lean" >> "$w/lines.txt" \
        || { cat "$w/lines.txt" >&2; exit 1; }
    fi
    diff -u "$dir/observed/concurrency-$v-$t.txt" "$w/lines.txt"
    echo "$v $t: the model's $(wc -l < "$w/lines.txt" | tr -d ' ') lines match the native observation"
  done
done
# The big-endian lines differ from the little-endian ones where the bytes are observed, and the
# two big-endian targets agree.
for v in "${versions[@]}"; do
  differ=$(paste -d'\n' "$dir/observed/concurrency-$v-s390x-linux.txt" \
    "$dir/observed/concurrency-$v-x86_64-linux.txt" | paste - - | awk -F'\t' '$1 != $2' | wc -l)
  [ "$differ" -ge 5 ] || { echo "$v: only $differ lines depend on the byte order" >&2; exit 1; }
  cmp "$dir/observed/concurrency-$v-s390x-linux.txt" "$dir/observed/concurrency-$v-mips64-linux.txt"
done
echo 'big-endian concurrency translation, schedule and observation gates passed'
