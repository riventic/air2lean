#!/usr/bin/env python3
"""W3 gate: every native result with a REAL std allocator or `std.Io` is a model outcome.

The differential test compares each model run with a hand-written mirror of the model
(`common.TestAllocator`), so it cannot show that the model includes what the real std code
does. This gate runs the allocator and `std.Io` examples natively with real implementations
and requires outcome-set inclusion (native result in the model's outcomes), not equality:

* `lists` (each input line) with `page_allocator`, `FixedBufferAllocator`, `ArenaAllocator`
  and `DebugAllocator`; the model's outcomes are its results over the allocation policies of
  `policy-inputs` (no failure, and a failure at each of the first `FAIL_PREFIX` attempts, all
  with the harness's 1 MiB request cap). A subset of the policies under-approximates the
  model's outcome set, so an inclusion found here is real; a miss is a divergence or a policy
  to add. The model without a cap (its default) is too slow for the inputs above the cap
  (a 1 MiB block of model bytes takes minutes): a native result of such an input that is not
  in the capped outcomes is reported as `unevaluated`, never as included.
* `sync` and `iogroup` with `Io.Threaded` and `Io.Threaded.global_single_threaded`; the
  model's outcomes are found by the differential schedule search, with a native hang
  searched as the model's `Zig.Error.deadlock` (every thread blocked).
* The architecture-audit probes (`tests/roadmap/architecture-audit/models`), whose model
  outcomes come from the audit runners.

A row that fails inclusion must be a known divergence of `expected.json` (an expected
failure with reason and link); any other failure fails the gate, and so does a known
divergence that no longer fails (the model or std changed: update the docs). Commands:

  policy-inputs SRC DST         write the model's policy variants of the lists inputs
  io-native BIN KIND OUT RUNS T run io_native RUNS times per function (timeout T s)
  check WORK [--evidence PATH]  compare; write the per-row evidence JSON
  validate                      check expected.json and the committed evidence (no toolchain)
"""
from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
EXPECTED = HERE / 'expected.json'
EVIDENCE = HERE / 'evidence.json'
AUDIT = 'docs/architecture-audit/models.md#divergences-native-vs-model'
ALLOCATORS = ('page', 'fixed_buffer', 'arena', 'debug')
IOS = ('threaded', 'single_threaded')
LISTS = ('sumRange', 'dupe', 'dupeZLen', 'evens', 'listSum')
IO_FUNCTIONS = {'sync': ('mutexCounter', 'handoff', 'semaphoreCounter', 'rwLockRead', 'rwLockSnapshotPair'),
                'iogroup': ('groupCounter', 'groupConcurrent')}
IO_PROBES = ('cancelProbe', 'handoffProbe')
ALLOC_PROBES = ('aliasProbe', 'remapProbe')
FAIL_PREFIX = 4
OUT_OF_MEMORY = {'err': 'OutOfMemory'}
HANG = 'hang'
DEADLOCK = '{"fail":"Zig.Error.deadlock"}'
ILLEGAL = '{"fail":"Zig.Error.illegal"}'
CAPPED = '{"fail":"Zig.Error.capped"}'


def lines(path: Path) -> list[str]:
    return [line for line in path.read_text().splitlines() if line]


# ----------------------------------------------------------------------------- model inputs

def policies() -> list[int | None]:
    """The difftest's legacy policy argument: no failure, or the allocation that fails."""
    return [None, *range(FAIL_PREFIX)]


def policy_inputs(src: Path, dst: Path) -> None:
    """Each lists input once per policy, in order: line i, variant v is line i * len + v."""
    dst.mkdir(parents=True, exist_ok=True)
    for name in LISTS:
        out = []
        for line in lines(src / f'{name}.jsonl'):
            record = json.loads(line)
            for policy in policies():
                record['args'][0] = policy
                out.append(json.dumps(record, separators=(',', ':')))
        (dst / f'{name}.jsonl').write_text('\n'.join(out) + '\n')


# ----------------------------------------------------------------------------- native Io

def io_native(binary: Path, kind: str, out: Path, runs: int, timeout: float) -> None:
    """Run each Io function `runs` times; write the observed lines (a hang searched as a model
    deadlock) as the difftest's Zig side, plus `native.json` with the raw outcomes."""
    raw = {}
    for ex, names in [*IO_FUNCTIONS.items(), ('io_probe', IO_PROBES)]:
        for name in names:
            seen = []
            for _ in range(runs):
                try:
                    done = subprocess.run([str(binary), kind, f'{ex}.{name}'], capture_output=True,
                                          text=True, timeout=timeout)
                    text = done.stderr.strip()
                    seen.append(text if done.returncode == 0 and text.startswith('{') else
                                f'crash:{done.returncode}')
                except subprocess.TimeoutExpired:
                    seen.append(HANG)
            raw[f'{ex}.{name}'] = seen
            if ex in IO_FUNCTIONS:
                # The difftest's layout: one input line per run, the native line as its target.
                inputs = lines(ROOT / f'tests/diff/{ex}/inputs/{name}.jsonl')
                if len(inputs) < runs:
                    raise ValueError(f'{ex}.{name}: {runs} runs need as many input lines')
                for target, text in [(out / f'tests/diff/{ex}/inputs', inputs[:runs]),
                                     (out / f'tests/diff/out/zig/{ex}', [DEADLOCK if s == HANG else s for s in seen])]:
                    target.mkdir(parents=True, exist_ok=True)
                    (target / f'{name}.jsonl').write_text('\n'.join(text) + '\n')
    (out / 'native.json').write_text(json.dumps(raw, indent=2) + '\n')


# ----------------------------------------------------------------------------- comparison

def panic_ctors() -> dict[str, str]:
    table = {}
    for line in lines(ROOT / 'scripts/panic-policy.tsv'):
        kind, ctor = line.split('\t')[:2]
        table[kind] = ctor
    return table


def canonical(line: str, ctors: dict[str, str]) -> str:
    """A result line without the model-only live count; a native panic kind as the model's
    `Zig.Error` constructor (scripts/panic-policy.tsv, as scripts/diff.sh maps it)."""
    record = json.loads(line)
    record.pop('live', None)
    # A wide integer may be quoted on one side only (scripts/diff.sh strips the quotes too).
    if isinstance(record.get('ok'), str) and record['ok'].lstrip('-').isdigit():
        record['ok'] = int(record['ok'])
    if 'fail' in record and not record['fail'].startswith('Zig.Error.'):
        record['fail'] = 'Zig.Error.' + ctors.get(record['fail'], 'unmapped:' + record['fail'])
    return json.dumps(record, sort_keys=True, separators=(',', ':'))


def row(row_id: str, native: list[str], included: list[bool | None], note: str = '') -> dict:
    """`included[i]`: native result i is a model outcome (True), is not (False), or was not
    evaluated (None, see `lists_rows`)."""
    counts = collections.Counter(native)
    missed = sorted({n for n, ok in zip(native, included) if ok is False})
    unevaluated = sum(ok is None for ok in included)
    # Per-input results (lists) are summarized; a few distinct results are kept whole.
    shown = {'native': dict(sorted(counts.items()))} if len(counts) <= 8 else {'native_distinct': len(counts)}
    return {'id': row_id, 'runs': len(native), 'included': sum(ok is True for ok in included),
            **({'unevaluated': unevaluated} if unevaluated else {}), **shown, 'outside_model': missed[:3],
            'status': 'fail' if missed else 'pass', **({'note': note} if note else {})}


def lists_rows(work: Path) -> list[dict]:
    ctors, rows, width = panic_ctors(), [], len(policies())
    for name in LISTS:
        model = [canonical(line, ctors) for line in lines(work / f'model-lists/tests/diff/out/lean/lists/{name}.jsonl')]
        groups = [model[i:i + width] for i in range(0, len(model), width)]
        for kind in ALLOCATORS:
            native = [canonical(line, ctors) for line in
                      lines(work / f'native-{kind}/tests/diff/out/zig/lists/{name}.jsonl')]
            if len(native) != len(groups):
                raise ValueError(f'lists.{name}: {len(native)} native lines for {len(groups)} model inputs')
            # A failure-free model run that is out of memory was stopped by the request cap.
            included = [True if n in group else
                        None if json.loads(group[0]).get('ok') == OUT_OF_MEMORY else False
                        for n, group in zip(native, groups)]
            rows.append(row(f'lists/{kind}/{name}', native, included,
                            'unevaluated: a request above the 1 MiB harness cap' if None in included else ''))
    return rows


def io_rows(work: Path) -> list[dict]:
    rows = []
    for kind in IOS:
        base = work / f'io-{kind}'
        raw = json.loads((base / 'native.json').read_text())
        for ex, names in IO_FUNCTIONS.items():
            for name in names:
                native = raw[f'{ex}.{name}']
                model = lines(base / f'tests/diff/out/lean/{ex}/{name}.jsonl')
                # The schedule search reports the native line when a schedule gives it; a data
                # race makes the program undefined (any result); a capped search is no evidence.
                targets = [DEADLOCK if n == HANG else n for n in native]
                included = [m == t or (m == ILLEGAL and t != DEADLOCK) for m, t in zip(model, targets)]
                if len(model) != len(native):
                    raise ValueError(f'{ex}.{name} ({kind}): {len(model)} model lines for {len(native)} runs')
                note = 'capped schedule search' if CAPPED in model else ''
                rows.append(row(f'{ex}/{kind}/{name}', native, included, note))
    return rows


def probe_outcomes(path: Path) -> dict[str, set[str]]:
    """`name[policy]=value` / `name=value` lines of the audit runners, by probe name."""
    found = collections.defaultdict(set)
    for line in lines(path):
        key, _, value = line.partition('=')
        found[key.split('[')[0]].add(value)
    return found


def probe_rows(work: Path) -> list[dict]:
    model = probe_outcomes(work / 'probe-model.txt')
    rows = []
    for kind in ALLOCATORS:
        native = probe_outcomes(work / f'probe-native-{kind}.txt')
        for name in ALLOC_PROBES:
            values = sorted(native[name])
            rows.append(row(f'alloc_probe/{kind}/{name}', values, [v in model[name] for v in values]))
    for kind in IOS:
        raw = json.loads((work / f'io-{kind}/native.json').read_text())
        for name in IO_PROBES:
            native = raw[f'io_probe.{name}']
            values = ['error:Zig.Error.deadlock' if n == HANG else
                      str(json.loads(n)['ok']) if n.startswith('{') else n for n in native]
            rows.append(row(f'io_probe/{kind}/{name}', native, [v in model[name] for v in values]))
    return rows


def load_expected(path: Path = EXPECTED) -> dict[str, dict]:
    data = json.loads(path.read_text())
    if data.get('schema') != 'air2lean-model-inclusion-expected/1' or not isinstance(data.get('known_divergences'), dict):
        raise ValueError('invalid expected.json')
    for row_id, entry in data['known_divergences'].items():
        if set(entry) != {'divergence', 'reason', 'link'} or not all(isinstance(v, str) and v for v in entry.values()):
            raise ValueError(f'{row_id}: a known divergence needs divergence, reason and link')
        link = entry['link'].split('#')[0]
        if not (ROOT / link).is_file():
            raise ValueError(f'{row_id}: link {entry["link"]} names no file')
    return data['known_divergences']


def judge(rows: list[dict], expected: dict[str, dict]) -> list[str]:
    """Mark known divergences; return the failures: new divergences and stale expectations."""
    problems = []
    ids = {r['id'] for r in rows}
    for row_id in sorted(set(expected) - ids):
        problems.append(f'{row_id}: known divergence names no checked row')
    for r in rows:
        known = expected.get(r['id'])
        if known is None:
            if r['status'] == 'fail':
                problems.append(f'{r["id"]}: NEW divergence: native {r["outside_model"]} is not a model outcome')
        elif r['status'] == 'pass':
            problems.append(f'{r["id"]}: known divergence {known["divergence"]} no longer diverges; update expected.json and docs')
        else:
            r.update(status='xfail', divergence=known['divergence'], reason=known['reason'], link=known['link'])
    return problems


def check(work: Path, evidence: Path | None) -> int:
    rows = lists_rows(work) + io_rows(work) + probe_rows(work)
    problems = judge(rows, load_expected())
    summary = collections.Counter(r['status'] for r in rows)
    report = {'schema': 'air2lean-model-inclusion-evidence/1', 'status': 'fail' if problems else 'pass',
              'summary': dict(sorted(summary.items())), 'failures': problems, 'rows': rows,
              'scope': 'Native results of the listed std implementations on these inputs, each checked '
                       'against the model outcomes of the listed policies or schedules. Not a proof '
                       'that the model includes every behavior of these implementations.'}
    if evidence is not None:
        evidence.write_text(json.dumps(report, indent=2) + '\n')
    for problem in problems:
        print(f'  {problem}', file=sys.stderr)
    print(f'model inclusion {report["status"]}: {dict(summary)}', file=sys.stderr)
    return 1 if problems else 0


def validate() -> int:
    expected = load_expected()
    report = json.loads(EVIDENCE.read_text())
    problems = []
    if report.get('schema') != 'air2lean-model-inclusion-evidence/1' or report.get('status') != 'pass':
        problems.append('committed evidence is not a passing schema-1 record')
    rows = {r['id']: r for r in report.get('rows', [])}
    for row_id, entry in expected.items():
        r = rows.get(row_id)
        if r is None or r.get('status') != 'xfail' or r.get('divergence') != entry['divergence']:
            problems.append(f'{row_id}: evidence does not record the known divergence')
    for row_id, r in rows.items():
        if r.get('status') not in ('pass', 'xfail') or (r['status'] == 'xfail') != (row_id in expected):
            problems.append(f'{row_id}: evidence status {r.get("status")} disagrees with expected.json')
    for problem in problems:
        print(f'  {problem}', file=sys.stderr)
    return 1 if problems else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('policy-inputs')
    p.add_argument('src', type=Path)
    p.add_argument('dst', type=Path)
    p = sub.add_parser('io-native')
    p.add_argument('binary', type=Path)
    p.add_argument('kind', choices=IOS)
    p.add_argument('out', type=Path)
    p.add_argument('runs', type=int)
    p.add_argument('timeout', type=float)
    p = sub.add_parser('check')
    p.add_argument('work', type=Path)
    p.add_argument('--evidence', type=Path)
    sub.add_parser('validate')
    args = parser.parse_args(argv)
    try:
        if args.command == 'policy-inputs':
            policy_inputs(args.src, args.dst)
        elif args.command == 'io-native':
            io_native(args.binary, args.kind, args.out, args.runs, args.timeout)
        elif args.command == 'check':
            return check(args.work, args.evidence)
        else:
            return validate()
    except (OSError, ValueError, KeyError) as error:
        print(f'model inclusion error: {error}', file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
