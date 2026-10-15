#!/usr/bin/env bash
# Translator cases of the soundness audit 2026-10-14 (S2, S3, F1). Each case re-translates its committed
# real export (air/) with the built translator, compiles the result and elaborates the witness
# next to it. `vulnerable`: the input is still accepted and the witness (a model fact that native
# code refutes) holds. A fix rejects the input or refutes the witness: `fixed`.
#   unsafe-panic  S3: unchecked IB is `.panic`, not `.illegal` (native: returns a value); fixed
#                 also needs `Fixed.lean` (every unchecked op is `.illegal`) to hold
#   shr-unsafe    S3b: `@shrExact` with safety off is `.overflow`, not `.illegal`; fixed also
#                 needs `Fixed.lean` (unchecked `.illegal`, checked still `.overflow`)
#   posix-spoof   S2: a user `posix.zig` binds `Zig.Os.mmap` (`--allocator-model translated`)
#   libdir-spoof  F1: a modified std lib (`--zig-lib-dir`) still binds the reviewed std model;
#                 the export is from that lib (allocator-create.patch), so only the translation
#                 side is re-run here.
# Usage: check.sh [CASE...] (default: every case).
set -uo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$here/../../../../.." && pwd)
cd "$repo_root"
translator=${AIR2LEAN_AUDIT_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-audit-1014.XXXXXX")
trap 'rm -rf "$work"' EXIT
open=0

# elaborate DIR FILE: FILE (copied into DIR) elaborates against DIR's compiled Gen.
elaborate() {
  cp "$here/$1/$2" "$work/$1/" &&
    LEAN_PATH="$work/$1:$(lake env printenv LEAN_PATH)" lake env lean -R "$work/$1" "$work/$1/$2" \
      >"$work/$1/$2.log" 2>&1
}

# case_run NAME NS PREFIX WITNESS EXPECT FIXED ARGS...: EXPECT is a fixed string the rejection must
# contain to count as the fix (empty: any rejection; another rejection is an error). FIXED is a
# witness of the fixed model that must hold once WITNESS no longer does (empty: none).
case_run() {
  local name=$1 ns=$2 prefix=$3 witness=$4 expect=$5 fixed=$6; shift 6
  local w="$work/$name"
  mkdir -p "$w"
  if ! "$translator" "$here/$name/air" -o "$w/Gen.lean" --namespace "$ns" --prefix "$prefix" "$@" \
      >"$w/tr.log" 2>&1; then
    if [ -n "$expect" ] && ! grep -Fq -- "$expect" "$w/tr.log"; then
      echo "$name: ERROR -- rejected without '$expect': $(head -c 300 "$w/tr.log")"
      open=1
    else
      echo "$name: fixed -- rejected: $(head -c 300 "$w/tr.log")"
    fi
    return
  fi
  if ! lake env lean -R "$w" -o "$w/Gen.olean" "$w/Gen.lean" >"$w/gen.log" 2>&1; then
    echo "$name: ERROR -- the translation does not compile: $(head -c 300 "$w/gen.log")"
    open=1
  elif elaborate "$name" "$witness"; then
    echo "$name: vulnerable -- accepted, $witness holds"
    open=1
  elif [ -n "$fixed" ] && ! elaborate "$name" "$fixed"; then
    echo "$name: ERROR -- $witness no longer holds, but $fixed does not either: $(head -c 300 "$w/$fixed.log")"
    open=1
  else
    echo "$name: fixed -- $witness no longer holds${fixed:+, $fixed holds}"
  fi
}

cases=("$@")
[ "${#cases[@]}" = 0 ] && cases=(unsafe-panic shr-unsafe posix-spoof libdir-spoof)
for name in "${cases[@]}"; do
  case $name in
    unsafe-panic) case_run unsafe-panic Up up. UnsafePanic.lean '' Fixed.lean ;;
    shr-unsafe) case_run shr-unsafe Shr shr. ShrUnsafe.lean '' Fixed.lean ;;
    posix-spoof) case_run posix-spoof Spoof spoof. PosixSpoof.lean "'root:posix.mmap' has no AIR file" '' \
      --allocator-model translated ;;
    libdir-spoof) case_run libdir-spoof H h. LibSpoof.lean '' '' ;;
    *) echo "unknown case $name" >&2; exit 2 ;;
  esac
done
exit "$open"
