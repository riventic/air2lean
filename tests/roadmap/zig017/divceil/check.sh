#!/usr/bin/env bash
# Zig 0.17.0 `@divCeil` gate (`support:tags:div_ceil`, qualification/0.17.0.json).
#   check.sh --export DIR   dump divceil.zig's AIR with a patched 0.17.0 compiler (AIR2LEAN_ZIG_AIR),
#                           ReleaseSafe, x86_64-linux baseline: the committed air/0.17.0
#   check.sh [--check]      translate the committed AIR, compare with the committed DivCeil/Gen.lean,
#                           run it on inputs.txt and compare every line with the stock Zig 0.17.0
#                           build (AIR2LEAN_ZIG_NATIVE) of native.zig; for the inputs that reach a
#                           safety check, run the native call alone and require Zig's panic message
#                           (division by zero / integer overflow) where Lean throws that error.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/zig017/divceil
case "${1:---check}" in
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a patched Zig 0.17.0 with the AIR exporter}"
    mkdir -p "$2"
    out=$(cd -- "$2" && pwd)
    ZIG_AIR_JSON_DIR="$out" ZIG_AIR_JSON_FILTER=divceil. "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin \
      -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline "$dir/divceil.zig"
    exit ;;
  --check) ;;
  *) echo 'usage: check.sh [--check|--export OUTPUT_DIR]' >&2; exit 2 ;;
esac
: "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig 0.17.0}"
[ "$("$AIR2LEAN_ZIG_NATIVE" version)" = 0.17.0 ] || { echo 'AIR2LEAN_ZIG_NATIVE is not Zig 0.17.0' >&2; exit 1; }
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-divceil.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/DivCeil"
"$translator" "$dir/air/0.17.0" -o "$work/DivCeil/Gen.lean" --namespace DivCeil --prefix divceil.
# The committed file has no profile header (it names the exporting host).
tail -n +2 "$work/DivCeil/Gen.lean" | cmp - "$dir/DivCeil/Gen.lean"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -R "$work" -o "$work/DivCeil/Gen.olean" "$work/DivCeil/Gen.lean"
lake env lean -R "$dir" --run "$dir/DivCeil/Runtime.lean" "$dir/inputs.txt" > "$work/lean.txt"
"$AIR2LEAN_ZIG_NATIVE" build-exe -OReleaseSafe --dep divceil -Mroot="$dir/native.zig" \
  -Mdivceil="$dir/divceil.zig" -femit-bin="$work/native" --cache-dir "$work/zig-cache"
"$work/native" > "$work/native.txt"
python3 - "$work" <<'PY'
import subprocess, sys
work = sys.argv[1]
lean = open(f'{work}/lean.txt').read().splitlines()
native = open(f'{work}/native.txt').read().splitlines()
assert len(lean) == len(native) > 0, (len(lean), len(native))
messages = {'panic:divByZero': 'division by zero', 'panic:overflow': 'integer overflow'}
values = panics = 0
for l, n in zip(lean, native):
    lf, nf = l.split(' '), n.split(' ')
    assert lf[:3] == nf[:3], (l, n)
    if nf[3] != 'panic':
        assert l == n, f'value differs: lean {l!r}, native {n!r}'
        values += 1
        continue
    assert lf[3] in messages, f'native panics, lean does not: {l!r}'
    run = subprocess.run([f'{work}/native', '--one', *nf[:3]], capture_output=True, text=True)
    assert run.returncode != 0 and messages[lf[3]] in run.stderr, (l, run.returncode, run.stderr[-300:])
    panics += 1
print(f'divCeil differential: {values} values equal, {panics} safety panics agree ({len(lean)} inputs)')
PY
