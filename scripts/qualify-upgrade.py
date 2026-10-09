#!/usr/bin/env python3
"""Q07 upgrade qualification: turn a coverage change-impact report into explicit obligations.

Subcommands (docs/coverage.md, Upgrade qualification):
  plan      run `scripts/coverage.py diff BEFORE AFTER` and write a qualification record
            whose obligations are probes, affected example translations, affected proof
            dependency audits and reviews (support expansion, std models, compiler sources)
  commands  print the shell commands of the executable obligations (nothing runs)
  run       execute pending command obligations and record exit status and log hashes
  record    record a review decision or externally produced evidence for one obligation
  check     fail unless every obligation has a passing result, support expansion and
            model changes carry an accepted review with evidence, and the plan is intact

`plan` and `check` never start a compiler, Lake or Lean. `run` does (check.sh, floatprobe.sh,
abi-probe.py and assumptions.py); it is a heavy release step.
"""
import argparse
from collections import Counter
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 'air2lean-upgrade-qualification/1'
# Support rank per inventory disposition. A higher rank in the new inventory is a support
# expansion; a disposition outside the vocabulary (new or renamed) is treated as one too.
# The vocabulary is coverage.py's DISPOSITIONS plus any `dispositions` table embedded in the
# compared inventories; a name ranks 0 (no support) when it is a rejection, unreachable or
# the unclassified placeholder, otherwise 1. LEGACY_RANKS covers pre-disposition inventories.
LEGACY_RANKS = {
    'tags': {'normalizer-rejected-compiler-state-or-effect': 0, 'normalizer-rejected-fast-math': 0,
             'normalizer-unclassified-or-unknown': 0, 'conditional-pipeline-review-required': 1,
             'source-pipeline-candidate-unqualified': 2},
    'types': {'exporter-fallback-unclassified': 0, 'exporter-arm-conditional-checker-review': 1},
    'constants': {'unclassified-review-writeRef-and-Check': 1},
    'pointer_bases': {'exporter-fallback-unsupported-marker-review': 0,
                      'exporter-explicit-arm-conditional-review': 1},
}
NO_SUPPORT = ('unreachable-at-export',)
ROW_KEYS = {'tags': 'tag', 'types': 'name', 'constants': 'name', 'pointer_bases': 'name'}
REVIEW_DECISIONS = ('accepted', 'rejected')
# A translation/proof obligation of an example whose `examples/<ex>/zig-versions` omits the target
# version may be recorded as not applicable (a reviewed exclusion, never a pass).
NOT_APPLICABLE = 'not-applicable'
STATIC_FIELDS = ('id', 'kind', 'reason', 'scope', 'command', 'env', 'requires_evidence')
PLACEHOLDER = re.compile(r'\{(zig|out)\}')


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def digest(value):
    return sha256_bytes(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())


def impact_report(before, after, coverage=ROOT / 'scripts/coverage.py'):
    """Consume coverage.py's own diff output; the inventory comparison is not reimplemented."""
    proc = subprocess.run([sys.executable, str(coverage), 'diff', str(before), str(after)],
                          capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        raise ValueError(f'coverage.py diff failed: {proc.stderr.strip()}')
    return json.loads(proc.stdout)


def coverage_vocabulary(coverage=ROOT / 'scripts/coverage.py'):
    """coverage.py's disposition vocabulary per category and its unclassified placeholder."""
    spec = importlib.util.spec_from_file_location('air2lean_coverage', coverage)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return {c: set(names) for c, names in module.DISPOSITIONS.items()}, module.FORBIDDEN


def vocabulary(*inventories, coverage=ROOT / 'scripts/coverage.py'):
    known, forbidden = coverage_vocabulary(coverage)
    for inventory in inventories:
        for category, names in (inventory.get('dispositions') or {}).items():
            if isinstance(names, dict):
                known.setdefault(category, set()).update(names)
    return known, forbidden


def rank(category, disposition, known, forbidden):
    legacy = LEGACY_RANKS.get(category, {})
    if disposition in legacy:
        return legacy[disposition]
    if disposition is None or disposition not in known.get(category, ()):
        return None
    if (disposition == forbidden or disposition in NO_SUPPORT or disposition.startswith('rejected-')
            or disposition.endswith('-rejected')):
        return 0
    return 1


def support_expansions(before, after):
    """Rows whose disposition is new or ranks higher; unknown dispositions count as expansion."""
    found = []
    known, forbidden = vocabulary(before, after)
    def first(rows, key):  # coverage.py diff also keys duplicate rows by their first occurrence
        result = {}
        for row in rows:
            result.setdefault(row[key], row['disposition'])
        return result

    for category, key in ROW_KEYS.items():
        old = first(before.get(category, []), key)
        for name, new in first(after.get(category, []), key).items():
            if name in old and old[name] == new:
                continue
            old_rank, new_rank = (rank(category, d, known, forbidden) for d in (old.get(name), new))
            if new_rank is None or new_rank > 0 and (old_rank is None or new_rank > old_rank):
                found.append({'category': category, 'name': name, 'from': old.get(name), 'to': new})
    return found


def model_changes(before, after):
    old = {row['name']: row for row in before.get('models', [])}
    new = {row['name']: row for row in after.get('models', [])}
    return [{'name': name, 'from': old.get(name), 'to': new.get(name)}
            for name in sorted(set(old) | set(new)) if old.get(name) != new.get(name)]


def golden_examples(inventory, tags):
    found = set()
    for row in inventory.get('tags', []):
        if row['tag'] in tags:
            for path in row.get('tests', {}).get('paths', []):
                parts = Path(path).parts
                if len(parts) > 3 and parts[:2] == ('tests', 'golden'):
                    found.add(parts[3])
    return found


def proof_modules(root, example):
    dirs = [d for d in subdirs(root / 'Proofs') if d.name.lower() == example.lower()]
    return ['.'.join(p.relative_to(root).with_suffix('').parts) for d in dirs for p in sorted(d.rglob('*.lean'))]


def subdirs(path):
    return sorted(d for d in path.iterdir() if d.is_dir()) if path.is_dir() else []


def build_obligations(before, after, impact, root=ROOT):
    obligations = []

    def add(id_, kind, reason, scope=None, command=None, env=None, requires_evidence=False):
        obligations.append({'id': id_, 'kind': kind, 'reason': reason, 'scope': scope or {},
                            'command': command, 'env': env or {}, 'requires_evidence': requires_evidence})

    sources = impact['source_changes']
    universes = {k: v for k, v in impact['universes'].items() if v['added'] or v['removed']}
    expansions = support_expansions(before, after)
    models = model_changes(before, after)
    changed_tags = set(impact['tag_dispositions_changed'])
    tag_universe = universes.get('air_tags', {'added': [], 'removed': []})
    changed_tags |= set(tag_universe['added']) | set(tag_universe['removed'])
    upgrade = impact['from'] != impact['to'] or impact['compiler_sources_changed']
    golden_os_changed = impact['golden_selection']['from_os'] != impact['golden_selection']['to_os']
    anything = (upgrade or universes or expansions or models or changed_tags or impact['model_boundary_changed']
                or any(sources.values()) or golden_os_changed)
    if not anything:
        return obligations

    # Support expansion and model changes need an explicit accepted review with evidence.
    for row in expansions:
        add(f"support:{row['category']}:{row['name']}", 'review',
            f"support expansion: {row['category']} {row['name']} {row['from']} -> {row['to']}; requires a "
            'compiler fixture, rejection/differential tests and a checked contract before acceptance',
            scope=row, requires_evidence=True)
    for row in models:
        add(f"model:{row['name']}", 'review', 'std model recognition changed; review docs/std-models.md contract',
            scope=row, requires_evidence=True)
    if impact['model_boundary_changed']:
        std = [p for p in impact['compiler_source_changes'] if p.startswith('lib/std/')]
        add('model-boundary', 'review',
            'std model boundary sources changed; review allocator/Thread/Io/time contracts and Memory.lean recognizers',
            scope={'model_recognition_changed': impact['model_recognition_changed'], 'compiler_std_sources': std,
                   'project_sources': sources.get('model-boundaries', [])}, requires_evidence=True)
    for category, change in sorted(universes.items()):
        add(f'universe:{category}', 'review',
            'compiler universe changed; renames appear as removal plus addition and need explicit dispositions',
            scope={'added': change['added'], 'removed': change['removed']})
    if impact['tag_dispositions_changed']:
        add('evidence:tags', 'review', 'AIR tag inventory rows changed; review exporter/normalizer/checker evidence',
            scope={'tags': impact['tag_dispositions_changed']})
    if impact['compiler_source_changes']:
        add('compiler-sources', 'review',
            'selected compiler fingerprints changed; release diff review of lowering and other compiler/std files',
            scope={'paths': impact['compiler_source_changes']})

    # Probes rerun for every upgrade or probe-source change.
    if upgrade or sources.get('qualification-probes'):
        add('probe:float', 'probe', 'rerun the float target probe on the reference target',
            command=['scripts/floatprobe.sh'], env={'AIR2LEAN_ZIG': '{zig}'})
        profiles = sorted((root / 'tests/roadmap/abi-probes').glob('*.json'))
        for profile in profiles:
            rel = profile.relative_to(root).as_posix()
            add(f'probe:layout:{profile.stem}', 'probe', 'rerun the layout/ABI probe for a qualified profile',
                command=['python3', 'scripts/abi-probe.py', 'observe', '--zig', '{zig}',
                         '--profile', rel, '--output', f'{{out}}/abi/{profile.stem}.json'])

    # Affected example translations (check.sh also runs the differential test).
    examples = [d.name for d in subdirs(root / 'examples')]
    all_examples = (upgrade or golden_os_changed or impact['model_boundary_changed'] or any(
        sources.get(scope) for scope in ('translation', 'runtime-models', 'inventory-tool')))
    affected = set(examples) if all_examples else (golden_examples(before, changed_tags)
                                                    | golden_examples(after, changed_tags)) & set(examples)
    for example in sorted(affected):
        add(f'translation:{example}', 'translation',
            'regenerate and compare the translation, then rerun its differential test',
            scope={'example': example, 'zig_version': impact['to']}, command=['scripts/check.sh'],
            env={'AIR2LEAN_CI': '1', 'AIR2LEAN_ZIG_VERSION': impact['to'], 'AIR2LEAN_EXAMPLES': example})

    # Affected theorems: rebuild and record the kernel dependency audit.
    proof_dirs = set(affected)
    if sources.get('runtime-models') or upgrade:
        proof_dirs |= {d.name.lower() for d in subdirs(root / 'Proofs')}
    for path in sources.get('proof-sources', []):
        parts = Path(path).parts
        if len(parts) > 2 and parts[0] == 'Proofs':
            proof_dirs.add(parts[1].lower())
    for name in sorted(proof_dirs):
        modules = proof_modules(root, name)
        if not modules:
            continue
        command = ['python3', 'scripts/assumptions.py', '--output', f'{{out}}/assumptions/{name}.json']
        for module in modules:
            command += ['--module', module]
        add(f'proofs:{name}', 'proofs',
            'rebuild affected proofs and record the kernel dependency audit; compare it with the previous release audit',
            scope={'modules': modules}, command=command)
    return obligations


def plan_digest(record):
    return digest({'from': record['from'], 'to': record['to'], 'inputs': record['inputs'],
                   'impact_sha256': record['impact_sha256'],
                   'obligations': [{k: o[k] for k in STATIC_FIELDS} for o in record['obligations']]})


def make_plan(before_path, after_path, root=ROOT, coverage=ROOT / 'scripts/coverage.py'):
    before, after = json.loads(before_path.read_text()), json.loads(after_path.read_text())
    impact = impact_report(before_path, after_path, coverage)
    record = {'schema': SCHEMA, 'from': impact['from'], 'to': impact['to'],
              'inputs': {'before_sha256': sha256_bytes(before_path.read_bytes()),
                         'after_sha256': sha256_bytes(after_path.read_bytes())},
              'impact_sha256': digest(impact), 'impact': impact,
              'obligations': build_obligations(before, after, impact, root), 'results': {}}
    record['plan_sha256'] = plan_digest(record)
    return record


def write_record(path, record):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile('w', dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        try:
            json.dump(record, handle, indent=2)
            handle.write('\n')
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    os.replace(temporary, path)


def load_record(path):
    record = json.loads(path.read_text())
    if record.get('schema') != SCHEMA:
        raise ValueError(f'{path}: not a {SCHEMA} record')
    return record


def logs_dir(path):
    return path.parent / (path.stem + '.d')


def now():
    return datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat()


def git_head(root=ROOT):
    proc = subprocess.run(['git', '-C', str(root), 'rev-parse', 'HEAD'], capture_output=True, text=True, check=False)
    return proc.stdout.strip() or None


def expand(value, zig, out):
    return PLACEHOLDER.sub(lambda m: {'zig': zig, 'out': str(out)}[m.group(1)], value)


def shell_line(obligation, zig, out):
    env = ' '.join(f'{k}={expand(v, zig, out)}' for k, v in sorted(obligation['env'].items()))
    return ' '.join(filter(None, [env, ' '.join(expand(a, zig, out) for a in obligation['command'])]))


def subprocess_executor(argv, env, log, cwd):
    with log.open('wb') as handle:
        return subprocess.run(argv, env=dict(os.environ, **env), cwd=cwd, stdout=handle,
                              stderr=subprocess.STDOUT, check=False).returncode


def run_obligations(path, zig, only=(), rerun=False, executor=subprocess_executor, root=ROOT):
    record = load_record(path)
    unknown = set(only) - {o['id'] for o in record['obligations'] if o['command'] is not None}
    if unknown:
        raise ValueError(f'--only names no command obligation: {", ".join(sorted(unknown))}')
    out = logs_dir(path).resolve()
    for sub in ('logs', 'abi', 'assumptions'):
        (out / sub).mkdir(parents=True, exist_ok=True)
    failures = 0
    for obligation in record['obligations']:
        oid = obligation['id']
        if obligation['command'] is None or (only and oid not in only):
            continue
        previous = record['results'].get(oid)
        if previous and previous['status'] == NOT_APPLICABLE:
            continue
        if previous and previous['status'] == 'pass' and not rerun:
            continue
        argv = [expand(a, zig, out) for a in obligation['command']]
        env = {k: expand(v, zig, out) for k, v in obligation['env'].items()}
        log = out / 'logs' / (re.sub(r'[^A-Za-z0-9._-]', '_', oid) + '.log')
        print(f'qualify-upgrade: {oid}: {shell_line(obligation, zig, out)}', file=sys.stderr)
        code = executor(argv, env, log, root)
        status = 'pass' if code == 0 else 'fail'
        failures += status != 'pass'
        record['results'][oid] = {'status': status, 'source': 'run', 'exit_code': code, 'argv': argv, 'env': env,
                                  'log': os.path.relpath(log, path.parent), 'log_sha256': sha256_bytes(log.read_bytes()),
                                  'recorded_at': now(), 'git_head': git_head(root)}
        write_record(path, record)  # Progress survives an interrupted release run.
    return failures


def excluded_example(record, obligation, root=ROOT):
    """The example of a translation/proof obligation, if its `zig-versions` omits the target."""
    kind, _, example = obligation['id'].partition(':')
    if obligation['kind'] not in ('translation', 'proofs') or kind != obligation['kind']:
        raise ValueError(f"{obligation['id']}: only translation and proof obligations can be not applicable")
    versions = root / 'examples' / example / 'zig-versions'
    if not versions.is_file() or record['to'] in versions.read_text().split():
        raise ValueError(f"{obligation['id']}: examples/{example}/zig-versions must exist and omit {record['to']}")
    return example


def record_result(path, oid, status=None, reviewer=None, decision=None, evidence=(), note=None, root=ROOT):
    record = load_record(path)
    obligation = next((o for o in record['obligations'] if o['id'] == oid), None)
    if obligation is None:
        raise ValueError(f'unknown obligation {oid}')
    if status == NOT_APPLICABLE:
        excluded_example(record, obligation, root)
        if not reviewer or not note or not evidence:
            raise ValueError(f'{oid}: a not-applicable result needs --reviewer, --note and --evidence')
    elif obligation['kind'] == 'review':
        if decision not in REVIEW_DECISIONS or not reviewer:
            raise ValueError(f'{oid}: a review needs --reviewer and --decision accepted|rejected')
        status = 'pass' if decision == 'accepted' else 'fail'
    elif status not in ('pass', 'fail') or not evidence:
        raise ValueError(f'{oid}: an externally run obligation needs --status pass|fail and --evidence')
    record['results'][oid] = {'status': status, 'source': 'record', 'reviewer': reviewer, 'decision': decision,
                              'evidence': list(evidence), 'note': note, 'recorded_at': now(), 'git_head': git_head(root)}
    write_record(path, record)


def check_record(path, before=None, after=None, root=ROOT, coverage=ROOT / 'scripts/coverage.py'):
    record = load_record(path)
    problems = []
    if record.get('plan_sha256') != plan_digest(record):
        problems.append('plan digest mismatch: obligations, inputs or impact were edited after `plan`')
    if before and after:
        fresh = make_plan(before, after, root, coverage)
        if fresh['plan_sha256'] != record['plan_sha256']:
            problems.append('plan is stale for the given inventories; rerun `plan`')
    ids = {o['id'] for o in record['obligations']}
    for oid in sorted(set(record['results']) - ids):
        problems.append(f'{oid}: result for an unknown obligation')
    for obligation in record['obligations']:
        oid, result = obligation['id'], record['results'].get(obligation['id'])
        if result is None:
            problems.append(f'{oid}: no result recorded')
            continue
        if result.get('status') == NOT_APPLICABLE:
            try:
                excluded_example(record, obligation, root)
            except ValueError as error:
                problems.append(str(error))
            if not (result.get('reviewer') and result.get('note') and result.get('evidence')):
                problems.append(f'{oid}: not-applicable result needs a reviewer, a note and evidence')
            continue
        if result.get('status') != 'pass':
            problems.append(f'{oid}: result is {result.get("status")}')
        if obligation['kind'] == 'review':
            if result.get('decision') != 'accepted' or not result.get('reviewer'):
                problems.append(f'{oid}: needs an accepted review with a named reviewer')
            if obligation['requires_evidence'] and not result.get('evidence'):
                problems.append(f'{oid}: support expansion or model change needs review evidence')
        elif result.get('source') == 'run':
            log = path.parent / result.get('log', '')
            if result.get('exit_code') != 0:
                problems.append(f'{oid}: exit code {result.get("exit_code")}')
            if not log.is_file() or sha256_bytes(log.read_bytes()) != result.get('log_sha256'):
                problems.append(f'{oid}: log missing or changed: {log}')
        elif not result.get('evidence'):
            problems.append(f'{oid}: recorded result has no evidence')
    return problems


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('plan')
    p.add_argument('before', type=Path)
    p.add_argument('after', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--force', action='store_true', help='replace an existing record (drops recorded results)')
    p = sub.add_parser('commands')
    p.add_argument('record', type=Path)
    p.add_argument('--zig', default='$AIR2LEAN_ZIG')
    p = sub.add_parser('run')
    p.add_argument('record', type=Path)
    p.add_argument('--zig', default=os.environ.get('AIR2LEAN_ZIG', 'zig'), help='stock zig for the probes')
    p.add_argument('--only', action='append', default=[])
    p.add_argument('--rerun', action='store_true', help='rerun obligations that already passed')
    p = sub.add_parser('record')
    p.add_argument('record', type=Path)
    p.add_argument('obligation')
    p.add_argument('--status', choices=('pass', 'fail', NOT_APPLICABLE))
    p.add_argument('--reviewer')
    p.add_argument('--decision', choices=REVIEW_DECISIONS)
    p.add_argument('--evidence', action='append', default=[])
    p.add_argument('--note')
    p = sub.add_parser('check')
    p.add_argument('record', type=Path)
    p.add_argument('--before', type=Path)
    p.add_argument('--after', type=Path)
    args = parser.parse_args(argv)
    if args.command == 'plan':
        if args.output.exists() and not args.force:
            raise ValueError(f'{args.output} exists; pass --force to discard its results')
        record = make_plan(args.before, args.after)
        write_record(args.output, record)
        kinds = dict(Counter(o['kind'] for o in record['obligations']))
        print(f"{record['from']} -> {record['to']}: {len(record['obligations'])} obligations {kinds}")
        return 0
    if args.command == 'commands':
        record = load_record(args.record)
        for o in record['obligations']:
            if o['command'] is not None:
                print(f"# {o['id']}\n{shell_line(o, args.zig, logs_dir(args.record))}")
        return 0
    if args.command == 'run':
        return 1 if run_obligations(args.record, args.zig, set(args.only), args.rerun) else 0
    if args.command == 'record':
        record_result(args.record, args.obligation, args.status, args.reviewer, args.decision, args.evidence, args.note)
        return 0
    if bool(args.before) != bool(args.after):
        raise ValueError('--before and --after go together')
    problems = check_record(args.record, args.before, args.after)
    for problem in problems:
        print(f'qualify-upgrade: {problem}', file=sys.stderr)
    if problems:
        return 1
    record = load_record(args.record)
    excluded = sorted(oid for oid, r in record['results'].items() if r.get('status') == NOT_APPLICABLE)
    print(f'{args.record}: all upgrade obligations have passing results' +
          (f' ({len(excluded)} not applicable: {", ".join(excluded)})' if excluded else ''))
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(f'qualify-upgrade: {error}', file=sys.stderr)
        sys.exit(2)
