#!/usr/bin/env python3
"""Per-version/target differential accounting (Q04).

`publish` reads complete scripts/diff-report.py summaries (one per Zig version and host target)
and writes one table whose columns partition every observed case: exact matches, host
differences, illegal, unspecified and unsupported-timer exclusions, capped searches, bounded no-result runs,
mismatches and setup failures. Skipped examples/functions and proof exclusions are reported
beside the partition; they are not cases. The headline `successful_comparisons` is the exact
match total only.

`check` verifies a published table: every row partitions its cases, totals are column sums, the
headline equals the exact-match total, and the table equals one regenerated from its summaries.

`claims` checks the README support claims (supported versions, full/restricted CI rows, example
lists, the restricted-row sentence and the headline report arithmetic) against the CI matrix
and against the selection actually recorded in the given summaries.

Exit 1 on a problem, 2 on an unreadable input. Starts no compiler, Lake or Lean process.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 1


def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(rel))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


REPORT = load('air2lean_diff_report', 'diff-report.py')
MATRIX = load('air2lean_support_matrix', 'support-matrix.py')
S = REPORT.Status
# Each comparison status lands in exactly one column; `skipped` rows are selections, not cases.
COLUMN = {status: 'exact_matches' for status in REPORT.MATCHES} | {
    S.HOST: 'host_differences', S.ILLEGAL: 'illegal',
    S.UNSPECIFIED: 'unspecified', S.UNSPECIFIED_TIMER: 'unspecified_timer', S.SEARCH_CAP: 'capped_searches',
    S.BOUNDED_NO_RESULT: 'bounded_no_result', S.MISMATCH: 'mismatches',
    S.INPUT_FAILURE: 'setup_failures', S.NATIVE_HARNESS_FAILURE: 'setup_failures',
}
PARTITION = ['exact_matches', 'host_differences', 'illegal', 'unspecified', 'unspecified_timer', 'capped_searches',
             'bounded_no_result', 'mismatches', 'setup_failures']
OUTSIDE = ['skipped_examples', 'skipped_functions', 'proof_exclusions']
NUMERIC = ['cases'] + PARTITION + OUTSIDE
HEADLINE = 'successful_comparisons'
DEFINITION = ('exact matches only (value_match, error_return_match, panic_match); host '
              'differences, illegal/unspecified/unsupported-timer exclusions, capped searches, bounded no-result '
              'runs, mismatches, setup failures, skipped functions and proof exclusions are excluded')
PROOF_UNEVALUATED = 'not_evaluated_by_differential_runner'


class Problem(Exception):
    pass


def count(value, what):
    if type(value) is not int or value < 0:
        raise Problem(f'{what} is not a non-negative integer: {value!r}')
    return value


def summary_row(path):
    """One validated accounting row from a complete diff-report summary."""
    raw = Path(path).read_bytes()
    try:
        data = json.loads(raw)
    except ValueError as error:
        raise Problem(f'{path}: not JSON ({error})')
    where = str(path)
    if not isinstance(data, dict) or data.get('schema') != SCHEMA:
        raise Problem(f'{where}: unsupported summary schema')
    if data.get('complete') is not True:
        raise Problem(f'{where}: incomplete run ({data.get("phase")}: {data.get("reason")}) '
                      'cannot be published as comparisons')
    if data.get('qualified') is not False:
        raise Problem(f'{where}: summary must record qualified=false')
    profile = data.get('profile')
    if not isinstance(profile, dict) or not all(isinstance(profile.get(k), str) and profile[k]
                                                for k in ('zig_version', 'host')):
        raise Problem(f'{where}: profile lacks zig_version/host')
    counts = data.get('counts')
    if not isinstance(counts, dict):
        raise Problem(f'{where}: counts missing')
    row = {'version': profile['zig_version'], 'target': profile['host'],
           'summary_sha256': hashlib.sha256(raw).hexdigest()}
    row.update({column: 0 for column in PARTITION})
    known = {status.value: status for status in COLUMN}
    for status, n in counts.items():
        if status not in known:
            raise Problem(f'{where}: unknown comparison status {status!r}')
        row[COLUMN[known[status]]] += count(n, f'{where}: counts[{status}]')
    row['cases'] = count(data.get('case_count'), f'{where}: case_count')
    observed = sum(row[c] for c in PARTITION)
    if observed != row['cases']:
        raise Problem(f'{where}: status counts sum to {observed}, '
                      f'case_count is {row["cases"]}')
    # The producer's own headline must not absorb any excluded status.
    if count(data.get('exact_matches'), f'{where}: exact_matches') != row['exact_matches']:
        raise Problem(f'{where}: exact_matches {data["exact_matches"]} is not the exact-match '
                      f'status total {row["exact_matches"]}')
    if count(data.get('setup_failures'), f'{where}: setup_failures') != row['setup_failures']:
        raise Problem(f'{where}: setup_failures disagrees with its status counts')
    row['skipped_examples'] = count(data.get('skipped_examples'), f'{where}: skipped_examples')
    row['skipped_functions'] = count(data.get('skipped_functions'), f'{where}: skipped_functions')
    if data.get('proof_applicability') != PROOF_UNEVALUATED:
        raise Problem(f'{where}: unsupported proof_applicability {data.get("proof_applicability")!r}')
    exclusions = data.get('proof_exclusions')
    if not isinstance(exclusions, list) or not all(
            isinstance(e, dict) and isinstance(e.get('example'), str)
            and e.get('reason') == 'proof_applicability_not_evaluated' for e in exclusions):
        raise Problem(f'{where}: malformed proof_exclusions')
    selected = [e['example'] for e in exclusions]
    if not selected or len(set(selected)) != len(selected):
        raise Problem(f'{where}: proof_exclusions must name each selected example once')
    row['proof_exclusions'] = len(selected)
    row['selected_examples'] = sorted(selected)
    row['proof_applicability'] = PROOF_UNEVALUATED
    return row


def publish(paths):
    rows = sorted((summary_row(p) for p in paths), key=lambda r: (r['version'], r['target']))
    if not rows:
        raise Problem('no summaries given')
    for a, b in zip(rows, rows[1:]):
        if (a['version'], a['target']) == (b['version'], b['target']):
            raise Problem(f'two summaries for Zig {a["version"]} on {a["target"]}; '
                          'publish one per version/target')
    totals = {c: sum(r[c] for r in rows) for c in NUMERIC}
    return {'schema': SCHEMA, 'qualified': False, 'columns': NUMERIC,
            'partition': PARTITION, 'outside_partition': OUTSIDE,
            'headline': {HEADLINE: totals['exact_matches'], 'definition': DEFINITION},
            'rows': rows, 'totals': totals}


def markdown(table):
    head = ['Zig', 'Target'] + table['columns']
    lines = [f'Successful comparisons (exact matches only): **{table["headline"][HEADLINE]}**.', '',
             '| ' + ' | '.join(head) + ' |', '|' + '---|' * 2 + '---:|' * len(table['columns'])]
    for row in table['rows'] + [dict(table['totals'], version='total', target='')]:
        lines.append('| ' + ' | '.join([row['version'], row['target']]
                                       + [str(row[c]) for c in table['columns']]) + ' |')
    return '\n'.join(lines) + '\n'


def invariants(table):
    """Problems in a published table, independent of its summaries."""
    problems = []
    if table.get('qualified') is not False:
        problems.append('published table must record qualified=false')
    if (table.get('columns'), table.get('partition'), table.get('outside_partition')) != (NUMERIC, PARTITION, OUTSIDE):
        problems.append('published columns differ from the accounting columns')
    rows = table.get('rows') if isinstance(table.get('rows'), list) else []
    if not rows:
        problems.append('published table has no rows')
    for row in rows:
        label = f'Zig {row.get("version")} on {row.get("target")}'
        try:
            values = {c: count(row.get(c), f'{label}: {c}') for c in NUMERIC}
        except Problem as error:
            problems.append(str(error)); continue
        if sum(values[c] for c in PARTITION) != values['cases']:
            problems.append(f'{label}: columns do not partition its {values["cases"]} cases')
    totals = table.get('totals') if isinstance(table.get('totals'), dict) else {}
    for c in NUMERIC:
        if totals.get(c) != sum(r.get(c, 0) if type(r.get(c)) is int else 0 for r in rows):
            problems.append(f'total {c} is not the sum of its rows')
    if type(totals.get('cases')) is int and sum(totals.get(c, 0) for c in PARTITION) != totals['cases']:
        problems.append('total columns do not partition the total cases')
    headline = (table.get('headline') or {}).get(HEADLINE)
    if headline != totals.get('exact_matches'):
        problems.append(f'headline {HEADLINE}={headline} is not the exact-match total '
                        f'{totals.get("exact_matches")}; excluded cases are not successful comparisons')
    return problems


# ---- README claims ---------------------------------------------------------------------------

def readme_claims(root):
    text = (root/'README.md').read_text(encoding='utf-8')
    start, end = MATRIX.begin('zig-versions'), MATRIX.end('zig-versions')
    if start not in text or end not in text:
        raise MATRIX.Stale('README.md: zig-versions region not found')
    region = text.split(start, 1)[1].split(end, 1)[0]
    supported = re.search(r'^Supported: Zig (.*?)\. ', region, re.M)
    if not supported:
        raise MATRIX.Stale('README.md: supported-version sentence not found')
    rows = {}
    for m in re.finditer(r'^\| (\d+\.\d+\.\d+)(?: \(default\))? \| ([^|]+) \| ([^|]+) \|', region, re.M):
        rows[m.group(1)] = {'ci': m.group(2).strip(), 'examples': sorted(re.findall(r'`([^`]+)`', m.group(3)))}
    return text, re.findall(r'\*\*(\d+\.\d+\.\d+)\*\*', supported.group(1)), rows


def claims(root, table):
    problems = []
    text, supported, rows = readme_claims(root)
    ci_versions = sorted({r['zig'] for r in MATRIX.ci_matrix(root)})
    if sorted(supported) != ci_versions:
        problems.append(f'README supports Zig {supported}; CI matrix runs {ci_versions}')
    if sorted(rows) != sorted(supported):
        problems.append(f'README version table rows {sorted(rows)} differ from supported {supported}')
    full_claims = set()
    for version, claim in rows.items():
        full, restricted, _ = MATRIX.ci_jobs(root, version)
        if claim['ci'].startswith('full job') and 'diff test' in claim['ci']:
            full_claims.add(version)
            if not full:
                problems.append(f'README claims a full Zig {version} job with a diff test; CI has none')
        elif claim['ci'].startswith('restricted job') and 'no diff harness' in claim['ci']:
            if full or not restricted:
                problems.append(f'README claims a restricted Zig {version} job; CI has '
                                f'{len(full)} full and {len(restricted)} restricted rows')
            for job in restricted:
                listed = sorted(job.get('examples', '').split())
                if listed != claim['examples']:
                    problems.append(f'README Zig {version} restricted examples {claim["examples"]} '
                                    f'differ from CI examples {listed}')
        else:
            problems.append(f'README Zig {version} CI claim {claim["ci"]!r} is not recognized')
    for version in re.findall(r"The (\d+\.\d+\.\d+) row uses CI's restricted examples and skips\s+the\s+differential harness", text):
        if version in full_claims or version not in rows:
            problems.append(f'README prose says Zig {version} skips the differential harness; '
                            'its version row disagrees')
    m = re.search(r'records ([\d,]+) cases: ([\d,]+) exact matches, ([\d,]+) illegal cases and '
                  r'([\d,]+) unspecified cases', text)
    if not m:
        problems.append('README headline report sentence not found')
    else:
        cases, exact, illegal, unspecified = (int(g.replace(',', '')) for g in m.groups())
        if exact + illegal + unspecified != cases:
            problems.append(f'README headline: {exact} exact matches + {illegal} illegal + '
                            f'{unspecified} unspecified != {cases} cases; exact matches must '
                            'exclude every excluded case')
    every = MATRIX.examples(root)
    for row in (table or {}).get('rows', []):
        label = f'Zig {row["version"]} on {row["target"]}'
        claim = rows.get(row['version'])
        if claim is None:
            problems.append(f'{label}: version is not a README-supported version'); continue
        if row['version'] not in full_claims:
            problems.append(f'{label}: README claims no diff harness for this version, '
                            'yet a differential summary exists')
            continue
        expected = [e for e in claim['examples'] if e != 'asm' or row['target'].endswith('-x86_64')]
        if row['selected_examples'] != expected:
            problems.append(f'{label}: ran examples {row["selected_examples"]}, README claims {expected}')
        if row['skipped_examples'] != len(every) - len(row['selected_examples']):
            problems.append(f'{label}: skipped_examples {row["skipped_examples"]} does not account '
                            f'for the {len(every) - len(row["selected_examples"])} unselected examples')
    return problems, full_claims


def write(path, text):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(text, encoding='utf-8')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('mode', choices=['publish', 'check', 'claims'])
    parser.add_argument('--summary', action='append', default=[], type=Path,
                        help='a diff-report summary; repeat once per version/target')
    parser.add_argument('--json', type=Path, help='publish: output; check: published table')
    parser.add_argument('--markdown', type=Path, help='publish: also write a markdown table')
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--require-full-versions', action='store_true',
                        help='claims: every README full-diff version needs a summary')
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        if args.mode == 'publish':
            if not args.json: parser.error('publish needs --json')
            table = publish(args.summary)
            problems = invariants(table)
            if not problems:
                write(args.json, json.dumps(table, indent=2, sort_keys=True) + '\n')
                if args.markdown: write(args.markdown, markdown(table))
                print(markdown(table), end='')
        elif args.mode == 'check':
            if not args.json: parser.error('check needs --json')
            published = json.loads(args.json.read_text(encoding='utf-8'))
            problems = invariants(published)
            if args.summary and publish(args.summary) != published:
                problems.append(f'{args.json} differs from the table regenerated from its summaries')
            if not args.summary:
                problems.append('check needs the --summary files the table was published from')
        else:
            table = publish(args.summary) if args.summary else None
            problems, full_claims = claims(root, table)
            if args.require_full_versions:
                have = {r['version'] for r in (table or {}).get('rows', [])}
                problems += [f'no differential summary for README full-diff Zig {v}'
                             for v in sorted(full_claims - have)]
    except Problem as error:
        problems = [str(error)]
    except (OSError, ValueError, KeyError, TypeError, AttributeError, MATRIX.Stale) as error:
        print(f'accounting: {error}', file=sys.stderr)
        return 2
    for problem in problems:
        print(f'accounting: {problem}', file=sys.stderr)
    if problems: return 1
    if args.mode != 'publish': print(f'accounting {args.mode}: ok')
    return 0


if __name__ == '__main__':
    sys.exit(main())
