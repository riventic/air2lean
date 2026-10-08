#!/usr/bin/env bash
# L13 device-effect gate (docs/volatile-effects.md §Device contract, §Inline asm). Run serialized
# (it calls Lean, and with --export the patched compiler).
#   check-device.sh               committed AIR: provenance, translation pins, default rejection,
#                                 device-mode rejections, proofs, semantic mutants
#   check-device.sh --export OUT  fresh exports with $AIR2LEAN_ZIG_AIR into the empty OUT; each
#                                 translation must equal the committed Gen.lean except for the
#                                 profile header line (device_asm.zig needs Zig 0.15.2 or later)
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/volatile-effects
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first' >&2; exit 1; }
translate_uart() {
  "$translator" "$1" -o "$2" --namespace DeviceEffects --prefix device_effects. \
    --device-contract "$dir/uart.json"
}
# Only `elapsed` of device_asm.zig is a declared device event; the others stay rejected.
translate_tsc() {
  local only
  only=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-tsc.XXXXXX")
  cp "$1/device_asm.elapsed.json" "$only/"
  "$translator" "$only" -o "$2" --namespace DeviceAsm --prefix device_asm. \
    --device-contract "$dir/tsc.json"
  rm -rf "$only"
}
export_fixture() {  # source, filter, output directory
  ZIG_AIR_JSON_DIR="$3" ZIG_AIR_JSON_FILTER="$2" \
    "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
    -target x86_64-linux -mcpu=baseline "$1" --cache-dir "$3.cache"
}
same_but_header() {  # fresh, committed
  cmp <(tail -n +2 "$1") <(tail -n +2 "$2")
  head -n 1 "$1" | grep -q '^-- air2lean-profile: '
}

if [ "${1:-}" = --export ]; then
  [ "$#" -eq 2 ] || { echo 'usage: check-device.sh --export OUTPUT_DIR' >&2; exit 2; }
  : "${AIR2LEAN_ZIG_AIR:?set a patched AIR compiler}"
  mkdir -p "$2"
  [ -z "$(find "$2" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo 'output must be empty' >&2; exit 1; }
  out=$(cd -- "$2" && pwd)
  version=$("$AIR2LEAN_ZIG_AIR" version)
  mkdir "$out/air"
  export_fixture "$dir/device_effects.zig" "$(paste -sd, "$dir/device-filter")" "$out/air"
  [ "$(find "$out/air" -name '*.json' | wc -l)" -eq "$(wc -l < "$dir/device-filter")" ] ||
    { echo 'fresh export does not have one file per filtered function' >&2; exit 1; }
  translate_uart "$out/air" "$out/Gen.lean"
  same_but_header "$out/Gen.lean" "$dir/DeviceEffects/Gen.lean"
  if [ "$version" = 0.14.1 ]; then
    echo "fresh $version export: device_effects only (device_asm.zig uses 0.15 clobber syntax)"
    exit
  fi
  mkdir "$out/air-asm"
  export_fixture "$dir/device_asm.zig" device_asm. "$out/air-asm"
  [ "$(find "$out/air-asm" -name '*.json' | wc -l)" -eq 5 ] ||
    { echo 'fresh device_asm export does not have five functions' >&2; exit 1; }
  translate_tsc "$out/air-asm" "$out/AsmGen.lean"
  same_but_header "$out/AsmGen.lean" "$dir/DeviceAsm/Gen.lean"
  echo "fresh $version exports translate to the committed device-effect Gen.lean files"
  exit
fi
[ "$#" -eq 0 ] || { echo 'usage: check-device.sh [--export OUTPUT_DIR]' >&2; exit 2; }

python3 -B "$dir/device-mutants.py" --self-test
# The committed AIR is the recorded export of the current sources.
python3 - "$dir" <<'PY'
import hashlib, json, sys
from pathlib import Path
d = Path(sys.argv[1])
h = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for root, source in (("air", "device_effects.zig"), ("air-asm", "device_asm.zig")):
    record = json.loads((d / root / "provenance.json").read_text())
    assert record["source_sha256"] == h(d / source), f"{source} changed: re-export"
    files = {p.name: h(p) for p in sorted((d / root / "0.16.0").glob("*.json"))}
    assert files == record["air_sha256"], f"committed {root} AIR differs from its provenance.json"
PY
if grep -nE '\b(sorry|admit|native_decide|axiom)\b' "$dir/DeviceEffects/Proofs.lean" "$dir/DeviceAsm/Proofs.lean"; then
  echo 'device proofs contain an untrusted declaration' >&2; exit 1
fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-device.XXXXXX")
trap 'rm -rf "$work"' EXIT

# The committed translations are exactly what the translator writes for the committed AIR.
mkdir -p "$work/base/DeviceEffects" "$work/base/DeviceAsm"
translate_uart "$dir/air/0.16.0" "$work/base/DeviceEffects/Gen.lean"
cmp "$work/base/DeviceEffects/Gen.lean" "$dir/DeviceEffects/Gen.lean"
translate_tsc "$dir/air-asm/0.16.0" "$work/base/DeviceAsm/Gen.lean"
cmp "$work/base/DeviceAsm/Gen.lean" "$dir/DeviceAsm/Gen.lean"

# Without a contract the default rejects every device access and every off-allowlist asm, and
# ordinary translation writes nothing.
for air in air air-asm; do
  status=0
  "$translator" --diagnostics-json "$dir/$air/0.16.0" > "$work/default-$air.json" || status=$?
  [ "$status" -eq 1 ]
  printf 'KEEP\n' > "$work/default.lean"
  status=0
  "$translator" "$dir/$air/0.16.0" -o "$work/default.lean" --namespace Default 2> /dev/null || status=$?
  [ "$status" -eq 1 ] && [ "$(cat "$work/default.lean")" = KEEP ]
done
status=0
"$translator" --diagnostics-json "$dir/air-asm/0.16.0" --device-contract "$dir/tsc.json" \
  > "$work/device-air-asm.json" || status=$?
[ "$status" -eq 1 ]
python3 - "$work" <<'PY'
import collections, json, sys
from pathlib import Path
work = Path(sys.argv[1])
def codes(name):
    report = json.loads((work / name).read_text())
    return collections.Counter((d["function"], d["code"]) for d in report["diagnostics"])
uart = codes("default-air.json")
for name in ("putc", "statusTwice", "clearStatus", "sendThenStatus"):
    assert uart[(f"device_effects.{name}", "VOLATILE_ACCESS")], (name, uart)
assert uart[("device_effects.writeAll", "CALLEE_BLOCKED")], uart
# rdtsc twice, rdrand, output-less asm, a memory clobber and non-volatile rdtsc.
asm = codes("default-air-asm.json")
expected = {"elapsed": 2, "random": 1, "fence": 1, "barrier": 1, "ticksPlain": 1}
assert asm == collections.Counter({(f"device_asm.{n}", "ASM_VOLATILE_EFFECT"): k
                                   for n, k in expected.items()}), asm
# The contract declares only the volatile rdtsc: the rest stays rejected.
device = codes("device-air-asm.json")
assert device == collections.Counter({(f"device_asm.{n}", "ASM_VOLATILE_EFFECT"): 1
                                      for n in ("random", "fence", "barrier", "ticksPlain")}), device
PY

lake build ZigLean ZigLean.Mem.Lemmas
lean_path="$(lake env printenv LEAN_PATH)"
for module in DeviceEffects DeviceAsm; do
  lake env lean -R "$work/base" -o "$work/base/$module/Gen.olean" "$work/base/$module/Gen.lean"
  LEAN_PATH="$work/base:$lean_path" lake env lean -R "$dir" "$dir/$module/Proofs.lean"
done

python3 -B "$dir/device-mutants.py" generate "$work/mutants" > "$work/names"
while IFS=: read -r name module; do
  m="$work/mutants/$name"
  lake env lean -R "$m" -o "$m/$module/Gen.olean" "$m/$module/Gen.lean"
  status=0
  LEAN_PATH="$m:$lean_path" lake env lean -R "$dir" "$dir/$module/Proofs.lean" > "$m/proofs.log" 2>&1 || status=$?
  python3 -B "$dir/device-mutants.py" classify "$name" "$status" "$m/proofs.log" "$dir/$module/Proofs.lean"
done < "$work/names"
echo 'device-effect provenance, translation pins, rejections, proofs and mutants passed'
