#!/usr/bin/env bash
# L04 pointer-try lifetimes and native runs (README.md). Lake builds the library TryLifetimes
# (tests/roadmap/lakefile.toml; scripts/fixtures.py, run it under scripts/build-guard.py).
#   check.sh [--check]          translate air/<version>/ and air-payloads/<version>/ (0.14.1,
#                               0.15.2, 0.16.0, 0.17.1), compare with TryLifetimes/<version>/
#                               Gen.lean and PayloadsGen.lean, check that each version's
#                               Lifetimes.lean and Payloads.lean are the 0.17.1 ones with the
#                               version renamed, build the library, audit the axioms and run each
#                               version's `main`s (kernel-checked sequential theorems, 32 scheduler
#                               oracles; the payload-shape runtime cases)
#   check.sh --native VERSION   with a stock Zig VERSION (AIR2LEAN_ZIG_NATIVE): the tests of
#                               try_pointers.zig, try_aliases.zig, try_lifetimes.zig and
#                               try_payloads.zig for
#                               x86_64-linux-musl, ReleaseSafe and Debug, in Docker linux/amd64
#                               (AIR2LEAN_X86_64_RUN overrides the runner; empty: the host)
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/try-pointers/lifetimes
versions=(0.14.1 0.15.2 0.16.0 0.17.1)
case "${1:---check}" in
  --native)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --native VERSION' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig of that version}"
    work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-try-native.XXXXXX")
    trap 'rm -rf "$work"' EXIT
    for src in tests/roadmap/try-pointers/try_pointers.zig tests/roadmap/try-pointers/try_aliases.zig \
        "$dir/try_lifetimes.zig" "$dir/try_payloads.zig"; do
      for mode in ReleaseSafe Debug; do
        bin="$work/$(basename "$src" .zig)-$mode"
        "$AIR2LEAN_ZIG_NATIVE" test "$src" "-O$mode" -target x86_64-linux-musl --test-no-exec \
          -femit-bin="$bin"
        if [ -n "${AIR2LEAN_X86_64_RUN+set}" ]; then
          # shellcheck disable=SC2086
          ${AIR2LEAN_X86_64_RUN} "$bin"
        else
          docker run --rm --platform linux/amd64 -v "$work:/w:ro" alpine:3 "/w/$(basename "$bin")"
        fi
        echo "$2 x86_64-linux-musl $mode: $(basename "$src") tests pass"
      done
    done
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check|--native VERSION]' >&2; exit 2 ;;
esac
# air/<version>: try-pointers/exports.json, pinned by its exports.lock.json.
python3 -B scripts/fixture-exports.py check try-pointers
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-try-lifetimes.XXXXXX")
trap 'rm -rf "$work"' EXIT
modules=() mains=() theorems=()
for v in "${versions[@]}"; do
  t="V${v//./_}"
  # The retained translations are the fresh ones, byte for byte (Lake builds the retained files).
  "$translator" "$dir/air/$v" -o "$work/$t.lean" --namespace "TryLifetimes.$t" \
    --prefix try_lifetimes.
  cmp "$work/$t.lean" "$dir/TryLifetimes/$t/Gen.lean"
  "$translator" "$dir/air-payloads/$v" -o "$work/$t.payloads.lean" \
    --namespace "TryLifetimes.$t.Payloads" --prefix try_payloads.
  cmp "$work/$t.payloads.lean" "$dir/TryLifetimes/$t/PayloadsGen.lean"
  # Every version's modules state the same theorems: the 0.17.1 ones, the version renamed.
  for primary in Lifetimes Payloads; do
    [ "$t" = V0_17_1 ] || python3 -B scripts/fixtures.py instance \
      "$dir/TryLifetimes/V0_17_1/$primary.lean" --subst "V0_17_1=$t"
  done
  modules+=("TryLifetimes.$t.Lifetimes" "TryLifetimes.$t.Payloads")
  mains+=("TryLifetimes.$t.Lifetimes:TryLifetimes.$t.Lifetimes.main"
    "TryLifetimes.$t.Payloads:TryLifetimes.$t.PayloadRules.main")
  theorems+=(--declaration "TryLifetimes.$t.Lifetimes.readDangling_illegal"
    --declaration "TryLifetimes.$t.PayloadRules.cleanup64_owned"
    --declaration "TryLifetimes.$t.PayloadRules.resetOnErrorPair_owned")
done
python3 -B scripts/fixtures.py build TryLifetimes
# Compiled and audited (axioms, sorry, kernel replay), not only run: they are indexed (F2).
python3 -B scripts/fixtures.py audit "${modules[@]}" "${theorems[@]}"
python3 -B scripts/fixtures.py run "$work/out" "${mains[@]}"
for v in "${versions[@]}"; do
  t="V${v//./_}"
  echo "$v: $(cat "$work/out/TryLifetimes.$t.Lifetimes.main.txt")"
  echo "$v: $(cat "$work/out/TryLifetimes.$t.PayloadRules.main.txt")"
done
