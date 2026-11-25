#!/usr/bin/env bash
# T03 byte-order fixtures. One source (`big_endian.zig`) exported by each Zig version of
# exports.json (0.17.1, 0.16.0) for s390x-linux and mips64-linux (big endian) and x86_64-linux
# (little endian); the exports of one version differ only in their profile.
#
#   check.sh [--check]        per version: re-translate the retained AIR, compare with the
#                             retained BigEndian/<V>/<T>/Gen.lean files byte for byte, check that
#                             every Diff module is the written one (0.17.1 x86_64-linux) renamed,
#                             build the library BigEndian (tests/roadmap/lakefile.toml: the
#                             translations, their Diff modules and BigEndian.Proofs), compare the
#                             model's lines with the retained native observations
#                             (observed/<version>-<arch>-linux-musl-ReleaseSafe.txt), and check
#                             the big-endian rejections of every version (test_cli.py)
#   check.sh --native VERSION build native.zig with a stock Zig VERSION (AIR2LEAN_ZIG_NATIVE) for
#                             s390x-linux-musl, mips64-linux-muslabi64 and x86_64-linux-musl, run
#                             each, and compare its output with the retained observation (which
#                             the default run compares with the model)
#
# The AIR is declared in exports.json and pinned by exports.lock.json (the default run checks the
# lock; scripts/fixture-exports.py verify|export big-endian re-exports it).
# Runners for --native: AIR2LEAN_S390X_RUN / AIR2LEAN_MIPS64_RUN / AIR2LEAN_X86_64_RUN name a
# command prefix that runs a static Linux binary (`qemu-s390x-static`, or empty for the host);
# `docker` (the default for a target that is not the host) runs it in `alpine:3` with
# `--platform linux/<arch>`.
# Needs `lake build ZigLean Air2Lean air2lean ZigLean.EndianLemmas`; Lake builds the library
# (scripts/fixtures.py): run it under scripts/build-guard.py.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case_dir=tests/roadmap/big-endian
# The Zig versions exports.json exports big_endian.zig for.
version_list=$(python3 -B -c 'import json, sys
sets = {tuple(e["versions"]) for e in json.load(open(sys.argv[1]))["exports"] if e["source"] == "big_endian.zig"}
assert len(sets) == 1, f"big_endian.zig entries differ in their versions: {sets}"
print(*sets.pop())' "$case_dir/exports.json")
read -ra versions <<<"$version_list"
[ "${#versions[@]}" -gt 0 ] || { echo 'exports.json exports big_endian.zig for no version' >&2; exit 1; }
pairs=(S390x:s390x-linux:s390x Mips64:mips64-linux:mips64 X64:x86_64-linux:x86_64)
case "${1:---check}" in
  --native)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --native VERSION' >&2; exit 2; }
    version=$2
    [ -f "$case_dir/observed/$version-x86_64-linux-musl-ReleaseSafe.txt" ] ||
      { echo "no retained observation for Zig $version" >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig of that version}"
    [ "$("$AIR2LEAN_ZIG_NATIVE" version)" = "$version" ] ||
      { echo "AIR2LEAN_ZIG_NATIVE is not Zig $version" >&2; exit 1; }
    work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-big-endian.XXXXXX")
    trap 'rm -rf "$work"' EXIT
    host_arch=$(uname -m)
    [ "$host_arch" = arm64 ] && host_arch=aarch64
    # run ARCH NAME: run the static binary $work/NAME on ARCH, its stderr to stdout.
    run() {
      local var runner
      var=AIR2LEAN_$(tr a-z A-Z <<<"$1")_RUN
      if [ -n "${!var+set}" ]; then runner=${!var}
      elif [ "$host_arch" = "$1" ] && [ "$(uname -s)" = Linux ]; then runner=
      else runner=docker; fi
      if [ "$runner" = docker ]; then
        docker run --rm --platform "linux/$([ "$1" = s390x ] && echo s390x || echo amd64)" \
          -v "$work:/w:ro" alpine:3 sh -c "/w/$2 2>&1"
      else
        # shellcheck disable=SC2086
        $runner "$work/$2" 2>&1
      fi
    }
    for pair in "${pairs[@]}"; do
      arch=$(cut -d: -f3 <<<"$pair")
      abi=musl
      [ "$arch" = mips64 ] && abi=muslabi64
      "$AIR2LEAN_ZIG_NATIVE" build-exe -OReleaseSafe -target "$arch-linux-$abi" \
        -femit-bin="$work/native-$arch" "$case_dir/native.zig"
      # names.zig's endian-aware test (`@tagName`, `@errorName`, a stored name's length bytes).
      "$AIR2LEAN_ZIG_NATIVE" test -OReleaseSafe -target "$arch-linux-$abi" --test-no-exec \
        -femit-bin="$work/names-$arch" "$case_dir/names.zig"
      # mips64 runs through the Docker VM's qemu-mips64 binfmt handler (concurrency.sh).
      if [ "$arch" = mips64 ]; then
        python3 "$case_dir/elf-abiversion.py" "$work/native-$arch"
        python3 "$case_dir/elf-abiversion.py" "$work/names-$arch"
      fi
      run "$arch" "native-$arch" > "$work/native-$arch.txt"
      diff -u "$case_dir/observed/$version-$arch-linux-musl-ReleaseSafe.txt" "$work/native-$arch.txt"
      echo "native $arch-linux-$abi ($version) matches the retained observation ($(wc -l < "$work/native-$arch.txt" | tr -d " ") lines)"
      run "$arch" "names-$arch"
    done
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check|--native VERSION]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check|--native VERSION]' >&2; exit 2 ;;
esac
python3 -B scripts/fixture-exports.py check big-endian
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-big-endian.XXXXXX")
trap 'rm -rf "$work"' EXIT
# A retained translation with its version as a namespace component: `BigEndian.<V>.` dropped.
unversioned() { sed -E 's/BigEndian\.V[0-9_]+\./BigEndian./' "$1"; }
mains=()
for v in "${versions[@]}"; do
  V="V${v//./_}"
  gen="$case_dir/BigEndian/$V"
  for pair in "${pairs[@]}"; do
    ns=$(cut -d: -f1 <<<"$pair")
    t=$(cut -d: -f2 <<<"$pair")
    # The retained translation is the fresh one, byte for byte (Lake builds the retained file).
    "$translator" "$case_dir/air/$v/$t" -o "$work/$V-$ns.lean" \
      --namespace "BigEndian.$V.$ns" --prefix big_endian.
    cmp "$work/$V-$ns.lean" "$gen/$ns/Gen.lean"
    # One model for every version and target: the written one, the version and target renamed.
    [ "$V/$ns" = V0_17_1/X64 ] || python3 -B scripts/fixtures.py instance \
      "$case_dir/BigEndian/V0_17_1/X64/Diff.lean" --subst "V0_17_1=$V" --subst "X64=$ns"
    mains+=("BigEndian.$V.$ns.Diff:BigEndian.$V.$ns.Diff.main")
  done
  # The two big-endian translations differ only in the profile header and the namespace.
  body_diff=$(diff "$gen/S390x/Gen.lean" "$gen/Mips64/Gen.lean" | grep '^[<>]' \
    | grep -v -e 'air2lean-profile' -e "BigEndian\.$V\.\(S390x\|Mips64\)$" || true)
  [ -z "$body_diff" ] || { echo "$v: the s390x and mips64 translations differ: $body_diff" >&2; exit 1; }
  # The big- and little-endian translations differ only in the profile header, the namespace, the
  # opened big-endian instances and the byte order of the two bit-pointer accesses.
  diff <(unversioned "$gen/S390x/Gen.lean") <(unversioned "$gen/X64/Gen.lean") \
    | grep '^[<>]' | sed -E 's/^([<>]) .*air2lean-profile.*/\1 PROFILE/' > "$work/gen-$v.diff" || true
  cmp "$work/gen-$v.diff" "$case_dir/expected-gen.diff"
  # names.zig (`@tagName`, `@errorName`): the retained translations are the fresh ones, and the
  # version's proofs (BigEndian.Names.<V>.Proofs, built with the library) are the written 0.17.1
  # ones renamed.
  for pair in "${pairs[@]}"; do
    ns=$(cut -d: -f1 <<<"$pair")
    t=$(cut -d: -f2 <<<"$pair")
    "$translator" "$case_dir/air/$v/names/$t" -o "$work/names-$V-$ns.lean" \
      --namespace "BigEndian.Names.$V.$ns" --prefix names.
    cmp "$work/names-$V-$ns.lean" "$case_dir/BigEndian/Names/$V/$ns/Gen.lean"
  done
  [ "$V" = V0_17_1 ] || python3 -B scripts/fixtures.py instance \
    "$case_dir/BigEndian/Names/V0_17_1/Proofs.lean" --subst "V0_17_1=$V"
done
python3 -B scripts/fixtures.py build BigEndian
python3 -B scripts/fixtures.py run "$work/out" "${mains[@]}"
for v in "${versions[@]}"; do
  V="V${v//./_}"
  for pair in "${pairs[@]}"; do
    ns=$(cut -d: -f1 <<<"$pair")
    arch=$(cut -d: -f3 <<<"$pair")
    lines="$work/out/BigEndian.$V.$ns.Diff.main.txt"
    diff -u "$case_dir/observed/$v-$arch-linux-musl-ReleaseSafe.txt" "$lines"
    echo "$v $arch: the model's $(wc -l < "$lines" | tr -d ' ') lines match the native observation"
  done
  # The fixtures observe byte order: the two profiles disagree on most lines. Up to 0.16 every
  # `@bitCast` to or from bytes does too; from 0.17 on it is logical, and only the memory views
  # do (docs/bitcast-semantics.md).
  floor=50
  [ "$v" = 0.16.0 ] && floor=60
  differ=$(paste -d'\n' "$case_dir/observed/$v-s390x-linux-musl-ReleaseSafe.txt" \
    "$case_dir/observed/$v-x86_64-linux-musl-ReleaseSafe.txt" | paste - - | awk -F'\t' '$1 != $2' | wc -l)
  [ "$differ" -ge "$floor" ] || { echo "$v: only $differ lines depend on the byte order" >&2; exit 1; }
  cmp "$case_dir/observed/$v-s390x-linux-musl-ReleaseSafe.txt" "$case_dir/observed/$v-mips64-linux-musl-ReleaseSafe.txt"
done
# Byte-order mutants of the retained 0.17.1 s390x translation (mutations.py): the translation
# builds, the byte-order theorems of BigEndian.Proofs fail on it.
python3 -B "$case_dir/mutations.py" --self-test
python3 -B "$case_dir/mutations.py" generate "$work/mutants" | while read -r name; do
  python3 -B scripts/fixtures.py mutant "big-endian-$name" --src "$work/mutants/$name" --fails BigEndian.Proofs
  python3 -B "$case_dir/mutations.py" kill "$name"
done
python3 "$case_dir/test_cli.py" "$translator"
echo 'big-endian translation, proof, observation and rejection gates passed'
