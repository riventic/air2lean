#!/usr/bin/env bash
# T03 byte-order fixtures. One source (`big_endian.zig`) exported for s390x-linux (big endian)
# and x86_64-linux (little endian); the two AIR exports differ only in their profile.
#
#   check.sh [--check]       re-translate the retained AIR, compare with the retained Gen.lean
#                            files byte for byte, build them, check the proofs, compare the
#                            model's lines with the retained native observations, and check the
#                            big-endian rejections (test_cli.py)
#   check.sh --native        also build native.zig with a stock Zig 0.16.0 (AIR2LEAN_ZIG_NATIVE)
#                            for s390x-linux-musl and x86_64-linux-musl, run both, and compare
#                            their output with the model and the retained observations
#   check.sh --export DIR    write fresh AIR with a patched Zig 0.16.0 (AIR2LEAN_ZIG_AIR)
#
# Runners for --native: AIR2LEAN_S390X_RUN / AIR2LEAN_X86_64_RUN name a command prefix that runs
# a static Linux binary (`qemu-s390x-static`, or empty for the host); `docker` (the default for
# a target that is not the host) runs it in `alpine:3` with `--platform linux/<arch>`.
# Needs `lake build ZigLean Air2Lean air2lean ZigLean.EndianLemmas`. All tool invocations must
# run in the repository's serialized build queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case_dir=tests/roadmap/big-endian
src=$case_dir/big_endian.zig
pairs=(S390x:s390x-linux:s390x X64:x86_64-linux:x86_64)
mode=${1:---check}
case "$mode" in
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a patched Zig 0.16.0 with the repository exporter}"
    for pair in "${pairs[@]}"; do
      t=$(cut -d: -f2 <<<"$pair")
      out="$2/$t"
      mkdir -p "$out"
      [ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo "$out must be empty" >&2; exit 1; }
      cpu=()
      [ "$t" = x86_64-linux ] && cpu=(-mcpu=baseline)
      ZIG_AIR_JSON_DIR="$(cd -- "$out" && pwd)" ZIG_AIR_JSON_FILTER=big_endian. \
        "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
        -target "$t" "${cpu[@]}" "$src"
    done
    out="$2/s390x-reject"
    mkdir -p "$out"
    [ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo "$out must be empty" >&2; exit 1; }
    ZIG_AIR_JSON_DIR="$(cd -- "$out" && pwd)" ZIG_AIR_JSON_FILTER=reject. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target s390x-linux "$case_dir/reject.zig"
    exit ;;
  --check|--native) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check|--native]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check|--native|--export OUTPUT_DIR]' >&2; exit 2 ;;
esac
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-big-endian.XXXXXX")
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
for pair in "${pairs[@]}"; do
  ns=$(cut -d: -f1 <<<"$pair")
  t=$(cut -d: -f2 <<<"$pair")
  mkdir -p "$work/BigEndian/$ns"
  "$translator" "$case_dir/air/0.16.0/$t" -o "$work/BigEndian/$ns/Gen.lean" \
    --namespace "BigEndian.$ns" --prefix big_endian.
  cmp "$work/BigEndian/$ns/Gen.lean" "$case_dir/BigEndian/$ns/Gen.lean"
  "${lean_cmd[@]}" -R "$work" -o "$work/BigEndian/$ns/Gen.olean" "$work/BigEndian/$ns/Gen.lean"
done
# The two translations differ only in the profile header, the namespace, the opened
# big-endian instances and the byte order of the two bit-pointer accesses.
diff "$case_dir/BigEndian/S390x/Gen.lean" "$case_dir/BigEndian/X64/Gen.lean" \
  | grep '^[<>]' | sed -E 's/^([<>]) .*air2lean-profile.*/\1 PROFILE/' > "$work/gen.diff" || true
cmp "$work/gen.diff" "$case_dir/expected-gen.diff"
"${lean_cmd[@]}" -R "$case_dir" "$case_dir/BigEndian/Proofs.lean"
for pair in "${pairs[@]}"; do
  arch=$(cut -d: -f3 <<<"$pair")
  "${lean_cmd[@]}" --run "$case_dir/Diff.lean" "$arch" > "$work/model-$arch.txt"
  diff -u "$case_dir/observed/$arch-linux-musl-ReleaseSafe.txt" "$work/model-$arch.txt"
done
# The fixtures observe byte order: the two profiles disagree on most lines.
differ=$(paste -d'\n' "$work/model-s390x.txt" "$work/model-x86_64.txt" | paste - - \
  | awk -F'\t' '$1 != $2' | wc -l)
[ "$differ" -ge 60 ] || { echo "only $differ lines depend on the byte order" >&2; exit 1; }
python3 "$case_dir/test_cli.py" "$translator"
if [ "$mode" = --native ]; then
  : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig 0.16.0}"
  host_arch=$(uname -m)
  [ "$host_arch" = arm64 ] && host_arch=aarch64
  for pair in "${pairs[@]}"; do
    arch=$(cut -d: -f3 <<<"$pair")
    bin="$work/native-$arch"
    "$AIR2LEAN_ZIG_NATIVE" build-exe -OReleaseSafe -target "$arch-linux-musl" \
      -femit-bin="$bin" "$case_dir/native.zig"
    var=AIR2LEAN_$(tr a-z A-Z <<<"$arch")_RUN
    if [ -n "${!var+set}" ]; then runner=${!var}
    elif [ "$host_arch" = "$arch" ] && [ "$(uname -s)" = Linux ]; then runner=
    else runner=docker; fi
    if [ "$runner" = docker ]; then
      docker run --rm --platform "linux/$([ "$arch" = x86_64 ] && echo amd64 || echo "$arch")" \
        -v "$work:/w:ro" alpine:3 sh -c "/w/native-$arch 2>&1" > "$work/native-$arch.txt"
    else
      # shellcheck disable=SC2086
      $runner "$bin" 2> "$work/native-$arch.txt"
    fi
    diff -u "$work/model-$arch.txt" "$work/native-$arch.txt"
    cmp "$work/native-$arch.txt" "$case_dir/observed/$arch-linux-musl-ReleaseSafe.txt"
    echo "native $arch-linux-musl matches the model ($(wc -l < "$work/native-$arch.txt" | tr -d " ") lines)"
  done
fi
echo 'big-endian translation, proof, observation and rejection gates passed'
