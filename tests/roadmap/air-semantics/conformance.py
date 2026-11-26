#!/usr/bin/env python3
"""Conformance of the AIR interpreter on the differential corpus (V01 stage 7,
docs/air-semantics.md §Conformance).

    python3 -B tests/roadmap/air-semantics/conformance.py [--zig-version V] [--examples "a b"]
        [--air-dir DIR] [--diff-out DIR] [--diff-report FILE] [--coverage-only] [--update]
        [--report FILE]

For every function of the differential corpus (`tests/diff/<ex>/inputs/<fn>.jsonl`) of the
selected examples, the compiled `Conformance.lean` runs the interpreter (`Sem.run`) on the
function's exported AIR with every corpus input, or records why the function is outside the
interpreter's coverage. The AIR is the patched compiler's export for Zig version V on this host:
`--air-dir` (the AIR2LEAN_OUT_DIR of a scripts/check.sh run, which also compares it with the
goldens), else exported here by check.sh's command. Then each outcome is compared three ways,
with the native outcome and with the generated Lean model's outcome, both as `scripts/diff.sh`
left them (`--diff-out`, default tests/diff/out; its summary must be a complete run of the same
Zig version on this host):

- the interpreter and the model must give the same outcome (the same value, buffers and returned
  error, or the same `Zig.Error`);
- the interpreter's outcome must match the native one as the model's does: by
  scripts/diff-report.py's classifier, a value, returned-error, panic or trap match, or the
  model's own pinned exclusion (`unspecified.txt`: both Lean sides give that `.illegal` or
  `.unspecified`).

Anything else is a disagreement: it is printed with the function, the input line number and the
three outcomes, and fails the run. A run of a function inside the coverage that is stuck fails
the run too (the classifier of `Conformance.lean` missed a reason).

Nothing is skipped silently. Each function outside the coverage is counted under each of its
reasons (an instruction kind without an arm, a value kind without a value, a call out of the
program), and the table of reasons is printed: it is the work list of stages 4 to 6.
`conformance/<V>.json` pins the functions that run; `--update` rewrites it. `--coverage-only`
stops after that check and needs no native side.

The whole corpus (the heavy run; under scripts/build-guard.py on a shared machine):

    AIR2LEAN_ZIG_VERSION=V AIR2LEAN_OUT_DIR=OUT scripts/check.sh
    python3 -B tests/roadmap/air-semantics/conformance.py --zig-version V --air-dir OUT \\
        --diff-out "$(cat .lake/check-reports/V/build-tree)/tests/diff/out" \\
        --diff-report tests/diff/out/report.json

A bounded run: `AIR2LEAN_EXAMPLES="basic recursion" scripts/diff.sh`, then this script with
`--examples "basic recursion"`. The runner is built here with scripts/fixtures.py (Lake).
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
# The compiled Conformance.lean (tests/roadmap/lakefile.toml).
RUNNER = 'air-semantics-conformance'


def load_script(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'scripts' / f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def export_air(example, version, zig_air, dest):
    """Export the example's AIR with the patched compiler, as scripts/check.sh step 1 does (the
    same command, filter and CPU; through the shared cache when AIR2LEAN_CAS_DIR is set)."""
    prefixes = [f'{example}.']
    for name in ('filter', f'filter-{version}'):
        path = ROOT / 'examples' / example / name
        if path.is_file():
            prefixes += path.read_text().split()
    command = [zig_air, 'build-obj', '-fno-emit-bin', '-OReleaseSafe', '-fno-error-tracing']
    if (platform.system(), platform.machine()) == ('Linux', 'aarch64'):
        command.append('-mcpu=baseline')
    command.append(f'examples/{example}/{example}.zig')
    if os.environ.get('AIR2LEAN_CAS_DIR'):
        command = [sys.executable, '-B', str(ROOT / 'scripts/cas.py'), 'air', '--'] + command
    dest.mkdir(parents=True)
    env = dict(os.environ, ZIG_AIR_JSON_DIR=str(dest), ZIG_AIR_JSON_FILTER=','.join(prefixes))
    run = subprocess.run(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if run.returncode != 0 or not list(dest.glob('*.json')):
        sys.exit(f'conformance: the AIR export of {example} failed:\n{run.stdout}')


def examples_of(version, host, requested):
    """The requested examples (default: every example with corpus inputs) that scripts/diff.sh
    runs for this Zig version on this host: (selected, {example: why it is not run})."""
    names = requested or sorted(p.parent.name for p in (ROOT / 'tests/diff').glob('*/inputs'))
    selected, excluded = [], {}
    for name in names:
        if not (ROOT / 'tests/diff' / name / 'inputs').is_dir():
            sys.exit(f'conformance: no corpus inputs for example {name}')
        versions = ROOT / 'examples' / name / 'zig-versions'
        if versions.is_file() and version not in versions.read_text().splitlines():
            excluded[name] = f'the example is not built with Zig {version} (examples/{name}/zig-versions)'
        elif name == 'asm' and not host.endswith('-x86_64'):
            excluded[name] = 'inline x86_64 assembly: only on an x86_64 host'
        else:
            selected.append(name)
    return selected, excluded


def interpret(version, examples, air_dir, execute, log):
    """Run Conformance.lean on each example's exported AIR (`air_dir/<ex>/*.json`, the
    AIR2LEAN_OUT_DIR of scripts/check.sh; None: exported here): {(example, fn): record}.
    `execute`: run the functions inside the coverage on their inputs (else only classify them).
    AIR of another Zig version is never interpreted as this version's."""
    records = {}
    with tempfile.TemporaryDirectory(prefix='air2lean-conformance.') as tmp:
        if air_dir is None:
            zig_air = os.environ.get('AIR2LEAN_ZIG_AIR') or subprocess.run(
                [str(ROOT / 'scripts/zig-air.sh'), version], check=True, text=True,
                stdout=subprocess.PIPE).stdout.strip()
            air_dir = Path(tmp) / 'air'
            for example in examples:
                export_air(example, version, zig_air, air_dir / example)
        manifest = []
        for example in examples:
            files = sorted((air_dir / example).glob('*.json'))
            other = sorted({str(json.loads(p.read_text()).get('zig_version')) for p in files} - {version})
            if not files or other:
                sys.exit(f'conformance: {air_dir / example} is not an AIR export of {example} by Zig {version}'
                         + (f' (found {", ".join(other)})' if other else ''))
            functions = sorted(p.stem for p in (ROOT / 'tests/diff' / example / 'inputs').glob('*.jsonl'))
            manifest.append({'name': example, 'air': [str(p) for p in files],
                             'functions': functions, 'inputs': f'tests/diff/{example}/inputs'})
        out = Path(tmp) / 'out.jsonl'
        (Path(tmp) / 'manifest.json').write_text(
            json.dumps({'out': str(out), 'execute': execute, 'examples': manifest}))
        for command in ([sys.executable, '-B', str(ROOT / 'scripts/fixtures.py'), 'build', RUNNER],
                        [str(ROOT / 'tests/roadmap/.lake/build/bin' / RUNNER), str(Path(tmp) / 'manifest.json')]):
            run = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if run.returncode != 0:
                print(run.stdout, file=log)
                sys.exit(f'conformance: {" ".join(command[:4])} failed')
        for line in out.read_text().splitlines():
            record = json.loads(line)
            records[record['example'], record['fn']] = record
    for entry in manifest:
        for fn in entry['functions']:
            if (entry['name'], fn) not in records:
                sys.exit(f'conformance: no record for {entry["name"]}.{fn}')
    return records


def reason_table(records):
    """reason -> [corpus functions it keeps out, those it alone keeps out, instructions]. An
    instruction of a shared callee counts once."""
    table = defaultdict(lambda: [0, 0, 0])
    seen = set()
    for (example, fn), record in sorted(records.items()):
        if record['status'] != 'skip':
            continue
        own = {r['reason'] for r in record['reasons']}
        for reason in own:
            table[reason][0] += 1
            table[reason][1] += len(own) == 1
        for r in record['reasons']:
            key = (example, r['where'], r['reason'])
            if key not in seen:
                seen.add(key)
                table[r['reason']][2] += r['insts']
    return table


def stage_of(reason):
    found = re.search(r'(stage [0-9]+|not staged)\)$', reason)
    return found[1] if found else 'harness' if reason.startswith('harness:') else 'not staged'


def print_coverage(records, excluded, log):
    run = sorted(k for k, r in records.items() if r['status'] == 'run')
    skip = sorted(k for k, r in records.items() if r['status'] == 'skip')
    print(f'coverage: {len(run)} of {len(records)} corpus functions run in the interpreter, '
          f'{len(skip)} are outside its coverage', file=log)
    for example, why in sorted(excluded.items()):
        print(f'coverage: example {example} not selected: {why}', file=log)
    table = reason_table(records)
    stages = Counter()
    for (example, fn) in skip:
        for stage in {stage_of(r['reason']) for r in records[example, fn]['reasons']}:
            stages[stage] += 1
    print('coverage: functions outside, by stage of a reason (a function counts once per stage): '
          + ', '.join(f'{stage} {count}' for stage, count in sorted(stages.items())), file=log)
    print('reason | functions | only this reason | instructions', file=log)
    for reason, (functions, alone, insts) in sorted(table.items(), key=lambda kv: (-kv[1][0], kv[0])):
        print(f'{reason} | {functions} | {alone} | {insts}', file=log)
    return run, skip, table


def check_pin(version, run, update, log):
    """The functions that run are the pinned ones (the same on every host: `asm`, which only an
    x86_64 host selects, is outside the coverage)."""
    path = HERE / 'conformance' / f'{version}.json'
    current = {'zig_version': version, 'run': [f'{ex}.{fn}' for ex, fn in run]}
    if update:
        path.parent.mkdir(exist_ok=True)
        path.write_text(json.dumps(current, indent=1) + '\n')
        return True
    if not path.is_file():
        print(f'conformance: no pinned coverage {path.relative_to(ROOT)} (--update writes it)', file=log)
        return False
    pinned = json.loads(path.read_text())
    if pinned == current:
        return True
    gone = sorted(set(pinned['run']) - set(current['run']))
    new = sorted(set(current['run']) - set(pinned['run']))
    print(f'conformance: coverage differs from {path.relative_to(ROOT)}: no longer run {gone}, newly run {new} '
          '(--update after review)', file=log)
    return False


def same_outcome(dr, model, mkind, sem, skind):
    """The two Lean sides agree exactly: no defined-bit matching, no panic table."""
    if mkind.value != skind:
        return False
    if 'ok' not in model or 'ok' not in sem:
        return dr.json_equal(model, sem)
    return (dr.json_equal(dr.normalized(model['ok']), dr.normalized(sem['ok']))
            and model.get('bufs') == sem.get('bufs') and model.get('live') == sem.get('live'))


def compare(dr, version, records, run, diff_out, summary, host, log):
    """Three-way comparison of every run function: (agreement counts, disagreements, stuck)."""
    if not summary.is_file():
        sys.exit(f'conformance: no differential summary {summary}: run scripts/diff.sh first')
    report = dr.read_summary(summary)
    profile = report.get('profile') or {}
    if not report.get('complete') or profile != {'host': host, 'zig_version': version}:
        sys.exit(f'conformance: {summary} is not a complete differential run of Zig {version} on {host} '
                 f'(complete={report.get("complete")}, profile={profile})')
    agreed, disagreements, stuck = Counter(), [], Counter()
    agree_statuses = set(dr.MATCHES) | {dr.Status.ILLEGAL, dr.Status.UNSPECIFIED}
    for example, fn in run:
        pinned = dr.pins(dr.pin_file(ROOT / 'tests/diff' / example, 'unspecified', host)).get(fn, {})
        inputs = list(dr.lines(ROOT / 'tests/diff' / example / 'inputs' / f'{fn}.jsonl'))
        sides = []
        for side in ('zig', 'lean'):
            path = diff_out / side / example / f'{fn}.jsonl'
            if not path.is_file():
                sys.exit(f'conformance: {path} is missing: run scripts/diff.sh for example {example} first')
            sides.append((list(dr.lines(path)), list(dr.lines(Path(str(path) + '.outcomes')))))
        outcomes = records[example, fn]['outcomes']
        if not all(len(rows) == len(inputs) for pair in sides for rows in pair) or len(outcomes) != len(inputs):
            sys.exit(f'conformance: {example}.{fn}: the outcome counts differ from the input count')
        for index, raw in enumerate(inputs):
            native = dr.wire(sides[0][0][index])
            model = dr.wire(sides[1][0][index])
            nkind, _ = dr.observation(sides[0][1][index], native, 'native')
            mkind, search = dr.observation(sides[1][1][index], model, 'model')
            sem = json.loads(outcomes[index]['line'])
            skind = outcomes[index]['kind']
            if skind == 'stuck':
                stuck[example, fn] += 1
                continue
            is_pinned = hashlib.sha256(raw.encode()).hexdigest() in pinned
            model_status = dr.classify(native, model, nkind, mkind, search, pinned=is_pinned)
            sem_status = dr.classify(native, dr.wire(sem), nkind, dr.Kind(skind), None, pinned=is_pinned)
            lean_agree = same_outcome(dr, model, mkind, sem, skind)
            if lean_agree and sem_status == model_status and sem_status in agree_statuses:
                agreed[sem_status.value] += 1
            else:
                disagreements.append({
                    'function': f'{example}.{fn}', 'input_line': index + 1, 'input': raw.strip(),
                    'native': sides[0][0][index].strip(), 'model': sides[1][0][index].strip(),
                    'interpreter': outcomes[index]['line'],
                    'interpreter_vs_model': 'same' if lean_agree else 'differs',
                    'interpreter_vs_native': sem_status.value, 'model_vs_native': model_status.value})
    for d in disagreements:
        print(f'DISAGREE {d["function"]} input line {d["input_line"]}: interpreter {d["interpreter"]} '
              f'(vs native: {d["interpreter_vs_native"]}; vs model: {d["interpreter_vs_model"]}), '
              f'model {d["model"]} (vs native: {d["model_vs_native"]}), native {d["native"]}, '
              f'input {d["input"][:200]}', file=log)
    for (example, fn), count in sorted(stuck.items()):
        print(f'STUCK {example}.{fn}: {count} input(s) stuck inside the coverage '
              '(a reason is missing in Conformance.lean)', file=log)
    return agreed, disagreements, stuck


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--zig-version', default=None, help="default: compatibility.json's zig.default")
    ap.add_argument('--examples', default='', help='space-separated examples (default: every example with inputs)')
    ap.add_argument('--air-dir', help="the examples' exported AIR, <ex>/*.json (scripts/check.sh's "
                    'AIR2LEAN_OUT_DIR); default: exported here with the patched compiler')
    ap.add_argument('--diff-out', default=str(ROOT / 'tests/diff/out'),
                    help="scripts/diff.sh's output directory (in the check tree, when check.sh used one)")
    ap.add_argument('--diff-report', help="scripts/diff.sh's summary (default: DIR/report.json)")
    ap.add_argument('--coverage-only', action='store_true', help='check the coverage only (no native side needed)')
    ap.add_argument('--update', action='store_true', help='rewrite the pinned coverage (all examples only)')
    ap.add_argument('--report', help='write the coverage table, the counts and the disagreements as JSON')
    args = ap.parse_args()
    version = args.zig_version or json.loads((ROOT / 'compatibility.json').read_text())['zig']['default']
    requested = args.examples.split()
    host = f'{platform.system()}-{platform.machine()}'
    log = sys.stdout
    examples, excluded = examples_of(version, host, requested)
    records = interpret(version, examples, Path(args.air_dir).resolve() if args.air_dir else None,
                        not args.coverage_only, log)
    run, skip, table = print_coverage(records, excluded, log)
    ok = True
    if requested:
        if args.update:
            sys.exit('conformance: --update pins every example; drop --examples')
    else:
        ok = check_pin(version, run, args.update, log)
    result = {'zig_version': version, 'host': host, 'examples': examples, 'excluded': excluded,
              'run': [f'{ex}.{fn}' for ex, fn in run],
              'outside': {f'{ex}.{fn}': records[ex, fn]['reasons'] for ex, fn in skip},
              'reasons': {reason: dict(zip(('functions', 'only', 'instructions'), row)) for reason, row in table.items()}}
    if not args.coverage_only:
        dr = load_script('diff-report')
        diff_out = Path(args.diff_out).resolve()
        summary = Path(args.diff_report).resolve() if args.diff_report else diff_out / 'report.json'
        agreed, disagreements, stuck = compare(dr, version, records, run, diff_out, summary, host, log)
        cases = sum(agreed.values()) + len(disagreements) + sum(stuck.values())
        print(f'conformance: Zig {version}: {len(run)} functions, {cases} cases: '
              + ' '.join(f'{k}={v}' for k, v in sorted(agreed.items()))
              + f' disagree={len(disagreements)} stuck={sum(stuck.values())}', file=log)
        result.update(agreed=dict(agreed), disagreements=disagreements,
                      stuck={f'{ex}.{fn}': n for (ex, fn), n in stuck.items()})
        ok = ok and not disagreements and not stuck
    if args.report:
        Path(args.report).write_text(json.dumps(result, indent=1, sort_keys=True) + '\n')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
