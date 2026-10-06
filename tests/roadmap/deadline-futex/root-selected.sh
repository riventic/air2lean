#!/usr/bin/env bash
# ROOT-only sequential interpreter-candidate checks in prepared Linux environment.
# No Zig bootstrap, native build, or OS-clock/public-source conformance claim.
set -euo pipefail
root=${DEADLINE_SOURCE_ROOT:?set frozen source snapshot root}
air=${DEADLINE_RETAINED_AIR:?set actual retained four-function AIR directory}
out=${DEADLINE_SELECTED_OUT:?set fresh absolute output directory}
[[ $root = /* && $air = /* && $out = /* ]]
test ! -e "$out"
cd "$root"
mkdir -p "$out/DeadlineActual"

# Bind the full local Lean import closure plus scripts and retained producer input.
python3 - "$root" "$air" "$out/before.json" <<'PY'
import hashlib, json, pathlib, re, sys
root, air, output = map(pathlib.Path, sys.argv[1:])
paths = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
         'tests/roadmap/deadline-futex/root-selected.sh',
         'tests/roadmap/deadline-futex/probe.zig'}
pending = ['ZigLean.lean', 'ZigLean/Conc/TimedBody.lean',
           'Air2Lean/Main.lean', 'Air2Lean/TimedEmit.lean',
           'tests/roadmap/deadline-futex/Guard.lean',
           'tests/roadmap/deadline-futex/Adapter.lean',
           'tests/roadmap/deadline-futex/Client.lean',
           'tests/roadmap/deadline-futex/Translate.lean',
           'tests/roadmap/deadline-futex/Generated.lean']
while pending:
    path = pending.pop()
    if path in paths:
        continue
    paths.add(path)
    text = (root / path).read_text()
    for line in text.splitlines():
        if line.startswith('import '):
            for module in line[7:].split():
                child = module.replace('.', '/') + '.lean'
                if (root / child).is_file():
                    pending.append(child)
                elif module.startswith(('Air2Lean.', 'ZigLean.')) or module == 'ZigLean':
                    raise RuntimeError('missing local import ' + module)
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
files = sorted(air.glob('*.json'))
assert {p.name for p in files} == {'probe.observe.json', 'probe.waitZero.json',
    'probe.waitDeadline.json', 'probe.boundaryClient.json'}, 'wrong retained AIR inventory'
output.write_text(json.dumps({'source': {p: digest(root / p) for p in sorted(paths)},
    'air': {p.name: digest(p) for p in files}}, sort_keys=True, indent=2) + '\n')
PY

bound=${DEADLINE_SELECTED_STEP_SECONDS:-300}
timeout --kill-after=10 "$bound" lake build ZigLean Air2Lean.Main Air2Lean.TimedEmit \
  ZigLean.Conc.TimedBody ZigLean.Conc.TimedClient ZigLean.Conc.TimedCompare \
  > "$out/build.log" 2>&1
timeout --kill-after=10 "$bound" lake env lean -R "$root" \
  tests/roadmap/deadline-futex/Guard.lean > "$out/Guard.log" 2>&1
for fixture in Adapter Client; do
  timeout --kill-after=10 "$bound" lake env lean -R "$root" --run \
    "tests/roadmap/deadline-futex/$fixture.lean" > "$out/$fixture.log" 2>&1
done
timeout --kill-after=10 "$bound" lake env lean -R "$root" --run \
  tests/roadmap/deadline-futex/Translate.lean "$air" "$out/DeadlineActual/Gen.lean" \
  > "$out/translate.log" 2>&1
timeout --kill-after=10 "$bound" lake env lean -R "$out" \
  -o "$out/DeadlineActual/Gen.olean" "$out/DeadlineActual/Gen.lean" \
  > "$out/generated-build.log" 2>&1
export DEADLINE_GENERATED_ROOT="$out"
timeout --kill-after=10 "$bound" lake env bash -c \
  'export LEAN_PATH="$DEADLINE_GENERATED_ROOT:$LEAN_PATH"; exec lean -R "$DEADLINE_SOURCE_ROOT" --run tests/roadmap/deadline-futex/Generated.lean' \
  > "$out/generated.log" 2>&1
set +e
timeout --kill-after=10 "$bound" lake env lean -R "$root" --run Air2Lean/Main.lean \
  --diagnostics-json "$air" > "$out/default-diagnostics.json" 2> "$out/default-diagnostics.log"
default_status=$?
set -e
test "$default_status" -eq 1
python3 - "$out" "$root" "$air" <<'PY'
import hashlib, json, pathlib, sys
out, root, air = map(pathlib.Path, sys.argv[1:])
report = json.loads((out / 'default-diagnostics.json').read_text())
codes = {d['code'] for d in report['diagnostics']}
assert not report['complete'] and {'CALLEE_MISSING', 'MODEL_FAILURE'} <= codes
before = json.loads((out / 'before.json').read_text())
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
after = {'source': {p: digest(root / p) for p in before['source']},
         'air': {p.name: digest(p) for p in sorted(air.glob('*.json'))}}
assert before == after, 'source or retained AIR changed during candidate checks'
(out / 'after.json').write_text(json.dumps(after, sort_keys=True, indent=2) + '\n')
(out / 'generated.sha256').write_text(digest(out / 'DeadlineActual/Gen.lean') + '\n')
(out / 'interpreter-candidate.passed').write_text(
    'acyclic-unqualified; source atomic coherence and OS conformance remain open\n')
PY
