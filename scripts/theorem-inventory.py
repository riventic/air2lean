#!/usr/bin/env python3
"""Theorem inventory: each headline theorem, its scope and domain, and its current check result.

assurance/theorem-inventory.json lists each theorem (Lean name, module, example, scope class,
domain) and the guarded `lake build` runs that checked it. A theorem must be checked against
the translation of every Zig version/target that its example supports (`translations`):
`tests/golden/<v>/<ex>/Gen-<os>.lean`, else `tests/golden/<v>/<ex>/Gen.lean`, else the
committed `Proofs/<Ex>/Gen.lean` (the rule of scripts/check.sh). A run result is current only
while the translation file and every `Proofs` source the module imports have the hashes the
run recorded.

`check` (default) fails when a listed theorem is missing from its module, has no current
successful run for a required translation, has an all-schedules scope without a statement
over every fuel and oracle, when a document or Lean doc comment says "every schedule" of a
theorem whose scope is narrower, when a theorem of a proved-examples table is not listed,
or when docs/theorem-inventory.md is stale. `write` regenerates that document's table.
`swap-build` builds modules against other translation files and restores the committed
ones. `record` adds a build-guard report of such a build to the inventory, after
scripts/gen-integrity.py attests that each translation file it records is a fresh translation
of its committed AIR. See
docs/theorem-inventory.md.
"""
from __future__ import annotations

import argparse
import functools
import hashlib
import json
from pathlib import Path
import re
import signal
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = Path('assurance/theorem-inventory.json')
DOC = Path('docs/theorem-inventory.md')
BEGIN, END = '<!-- BEGIN theorem-inventory -->', '<!-- END theorem-inventory -->'
SCOPES = ('single-step', 'single-schedule', 'bounded-schedules', 'all-schedules', 'sequential')
TARGETS = ('linux', 'darwin')
# Documents whose claims are checked against the scopes. Lean doc comments of listed theorems
# are checked too.
CLAIM_DOCS = ('README.md', 'PLAN.md', 'docs/proofs.md', 'docs/vector-proofs.md',
              'docs/rwlock-contracts.md', 'docs/std-models.md')
ALL_SCHEDULES_RE = re.compile(
    r'(?i)\b(?:every|all|any|no)\s+(?:schedules?|oracles?)\b|all-schedules|over all schedules')
# Proved-example tables: (document, heading, module of a row that names no file). Every theorem
# a row names must be listed.
LISTINGS = (('docs/proofs.md', '## Proved examples', None),
            ('docs/vector-proofs.md', '# Checked vector addition proofs', 'Proofs.Vectors.Proofs'))
TICK_RE = re.compile(r'`([^`]+)`')
DECL_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*'
                     r'theorem\s+([^\s(:{\[]+)')
IMPORT_RE = re.compile(r'^import\s+(Proofs\.[\w.]+)\s*$', re.M)
SWAP_PREFIX = 'theorem-inventory swap: '


class Error(Exception):
    pass


@functools.lru_cache(maxsize=None)
def _sha256(path: Path, mtime_ns: int, size: int) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256(path: Path) -> str:
    info = path.stat()
    return _sha256(path, info.st_mtime_ns, info.st_size)


def module_path(module: str) -> Path:
    return Path(*module.split('.')).with_suffix('.lean')


def gen_module(example: str) -> str:
    return f'Proofs.{example.capitalize()}.Gen'


# ----------------------------------------------------------------------------- Lean sources

def declarations(text: str) -> dict[str, dict]:
    """Theorem full name -> statement (up to `:=`) and the doc comment right before it."""
    stack: list[tuple[str, str | None]] = []
    lines = text.splitlines()
    found: dict[str, dict] = {}
    for i, line in enumerate(lines):
        if m := re.match(r'^namespace\s+([\w.]+)\s*$', line):
            stack.append(('namespace', m.group(1)))
        elif m := re.match(r'^section(?:\s+([\w.]+))?\s*$', line):
            stack.append(('section', m.group(1)))
        elif m := re.match(r'^end(?:\s+([\w.]+))?\s*$', line):
            if stack:
                stack.pop()
        elif m := DECL_RE.match(line):
            ns = [name for kind, name in stack if kind == 'namespace']
            full = '.'.join([*ns, m.group(1)])
            statement = []
            for rest in lines[i:]:
                statement.append(rest.split(':=')[0])
                if ':=' in rest:
                    break
            doc = []
            j = i - 1
            while j >= 0 and lines[j].startswith('@['):
                j -= 1
            if j >= 0 and lines[j].rstrip().endswith('-/'):
                while j >= 0:
                    doc.insert(0, lines[j])
                    if lines[j].lstrip().startswith('/-'):
                        break
                    j -= 1
                if not doc[0].lstrip().startswith('/--'):
                    doc = []  # a module or section comment, not this theorem's
            found[full] = {'statement': '\n'.join(statement), 'doc': '\n'.join(doc), 'line': i + 1}
    return found


def all_schedules_statement(statement: str) -> bool:
    """`Sched.run dispatch fuel o …` with `fuel` and `o` bound by the statement itself."""
    for m in re.finditer(r'Sched\.run\s+\S+\s+(\w+)\s+(\w+)', statement):
        fuel, oracle = m.groups()
        if (re.search(r'[({]\s*' + fuel + r'\b[^:]*:\s*Nat\s*[)}]', statement) and
                re.search(r'[({][^:]*\b' + oracle + r'\b[^:]*:\s*Nat\s*→\s*Nat\s*[)}]', statement)):
            return True
    return False


def closure(root: Path, modules: list[str]) -> list[str]:
    """`Proofs` modules imported (transitively) by `modules`, the modules included."""
    seen: set[str] = set()
    todo = list(modules)
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = root / module_path(mod)
        if not path.is_file():
            raise Error(f'{mod}: no source file {module_path(mod)}')
        todo.extend(IMPORT_RE.findall(path.read_text()))
    return sorted(seen)


def library_modules(root: Path) -> list[str]:
    return sorted('.'.join(p.relative_to(root).with_suffix('').parts)
                  for p in (root / 'Proofs').rglob('*.lean'))


# ----------------------------------------------------------------------------- translations

def versions(root: Path) -> list[str]:
    data = json.loads((root / 'compatibility.json').read_text())
    return [v['version'] for v in data['zig']['versions']]


def translations(root: Path, example: str) -> list[dict]:
    """The (version, target, translation file) of every translation of `example`."""
    listed = root / 'examples' / example / 'zig-versions'
    supported = listed.read_text().split() if listed.is_file() else versions(root)
    result = []
    for version in versions(root):
        if version not in supported:
            continue
        base = Path('tests/golden') / version / example
        default = base / 'Gen.lean'
        if not (root / default).is_file():
            default = Path('Proofs') / example.capitalize() / 'Gen.lean'
        result.append({'zig': version, 'target': 'linux', 'gen': str(default)})
        for target in TARGETS[1:]:
            os_gen = base / f'Gen-{target}.lean'
            if (root / os_gen).is_file():
                result.append({'zig': version, 'target': target, 'gen': str(os_gen)})
    return result


# ----------------------------------------------------------------------------- check

def load(root: Path) -> dict:
    return json.loads((root / INVENTORY).read_text())


def current_result(root: Path, inv: dict, thm: dict, tr: dict, decl_closure: list[str]):
    """The id of a successful run whose recorded hashes match the current files, or None."""
    gen_sha = sha256(root / tr['gen'])
    for run_id, run in sorted(inv.get('runs', {}).items()):
        if run.get('outcome') != 'success' or run.get('exit_code') != 0:
            continue
        if thm['module'] not in run.get('modules', []):
            continue
        gen = run.get('gens', {}).get(thm['example'])
        if not gen or gen.get('path') != tr['gen'] or gen.get('sha256') != gen_sha:
            continue
        sources, gens = run.get('sources', {}), run.get('gens', {})

        def unchanged(mod: str) -> bool:
            if not mod.endswith('.Gen'):
                return sources.get(mod) == sha256(root / module_path(mod))
            # Another example's translation that the module imports counts like a source.
            recorded = gens.get(mod.split('.')[1].lower(), {})
            return recorded.get('sha256') == sha256(root / recorded.get('path', module_path(mod)))
        if all(unchanged(mod) for mod in decl_closure):
            return run_id
    return None


def results(root: Path, inv: dict) -> tuple[list[dict], list[str]]:
    """Per theorem: its required translations with the current run (or the exclusion)."""
    errors: list[str] = []
    rows = []
    names = set()
    decl_cache: dict[str, dict] = {}
    for thm in inv.get('theorems', []):
        name = thm.get('name', '?')
        missing = [k for k in ('name', 'module', 'example', 'scope', 'domain') if not thm.get(k)]
        if missing:
            errors.append(f'{name}: missing {", ".join(missing)}')
            continue
        key = (name, thm['module'])
        if key in names:
            errors.append(f'{name}: listed twice')
        names.add(key)
        if thm['scope'] not in SCOPES:
            errors.append(f'{name}: unknown scope {thm["scope"]!r} (one of {", ".join(SCOPES)})')
        path = root / module_path(thm['module'])
        if not path.is_file():
            errors.append(f'{name}: no module {thm["module"]}')
            continue
        decls = decl_cache.setdefault(thm['module'], declarations(path.read_text()))
        decl = decls.get(name)
        if decl is None:
            errors.append(f'{name}: no `theorem` of this name in {module_path(thm["module"])}')
            continue
        if thm['scope'] == 'all-schedules' and not all_schedules_statement(decl['statement']):
            errors.append(f'{name}: scope all-schedules, but its statement does not quantify '
                          f'`Sched.run` over every fuel and oracle')
        if thm['scope'] != 'all-schedules' and ALL_SCHEDULES_RE.search(decl['doc']):
            errors.append(f'{name}: its doc comment claims every schedule, scope is {thm["scope"]}')
        try:
            mods = closure(root, [thm['module']])
        except Error as error:
            errors.append(str(error))
            continue
        if gen_module(thm['example']) not in mods:
            errors.append(f'{name}: {thm["module"]} does not import {gen_module(thm["example"])}')
        excluded = {(e['zig'], e['target']): e['reason'] for e in thm.get('excluded', [])}
        checks = []
        for tr in translations(root, thm['example']):
            label = f'{tr["zig"]}/{tr["target"]}'
            if (tr['zig'], tr['target']) in excluded:
                checks.append({**tr, 'excluded': excluded.pop((tr['zig'], tr['target']))})
                continue
            run = current_result(root, inv, thm, tr, mods)
            if run is None:
                errors.append(f'{name}: no current check result for {label} ({tr["gen"]})')
            checks.append({**tr, 'run': run})
        for zig, target in excluded:
            errors.append(f'{name}: excludes {zig}/{target}, which is not a translation of '
                          f'{thm["example"]}')
        rows.append({**thm, 'checks': checks})
    return rows, errors


def segments(line: str) -> list[str]:
    """The clauses of a line (split at `;` and sentence ends). In a table row each clause is
    split again at every mention, since a cell gives each theorem's claim after its name."""
    clauses = re.split(r';\s+|(?<=\.)\s+(?=[A-Z`(])', line)
    if not line.lstrip().startswith('|'):
        return clauses
    parts = []
    for clause in (c for cell in clauses for c in cell.split('|')):
        starts = [m.start() for m in TICK_RE.finditer(clause)]
        bounds = [0, *starts[1:], len(clause)]
        parts.extend(clause[a:b] for a, b in zip(bounds, bounds[1:]))
    return parts


def claim_errors(root: Path, inv: dict) -> list[str]:
    """A document that says "every schedule" of a theorem whose scope is narrower."""
    by_name: dict[str, set[str]] = {}
    for thm in inv.get('theorems', []):
        for alias in (thm['name'], thm['name'].rsplit('.', 1)[-1]):
            by_name.setdefault(alias, set()).add(thm['scope'])
    errors = []
    for doc in CLAIM_DOCS:
        path = root / doc
        if not path.is_file():
            continue
        for number, line in enumerate(path.read_text().splitlines(), 1):
            for part in segments(line):
                if not ALL_SCHEDULES_RE.search(part):
                    continue
                for token in TICK_RE.findall(part):
                    narrower = by_name.get(token, set()) - {'all-schedules'}
                    if narrower:
                        errors.append(f'{doc}:{number}: says every schedule of `{token}`, whose '
                                      f'scope is {", ".join(sorted(narrower))}')
    return errors


def listing_errors(root: Path, inv: dict) -> list[str]:
    """Every theorem of a proved-examples table is in the inventory."""
    listed = {(t['name'].rsplit('.', 1)[-1], t['module']) for t in inv.get('theorems', [])}
    errors = []
    for doc, heading, default in LISTINGS:
        text = (root / doc).read_text()
        if heading not in text:
            errors.append(f'{doc}: heading {heading!r} not found')
            continue
        section = text.split(heading, 1)[1]
        section = re.split(r'^#{1,2} ', section, maxsplit=1, flags=re.M)[0]
        for line in section.splitlines():
            if not line.startswith('|') or line.startswith('|---'):
                continue
            ticks = TICK_RE.findall(line)
            files = ['.'.join(Path(t).with_suffix('').parts) for t in ticks if t.endswith('.lean')]
            modules = files or ([default] if default else [])
            shorts = {m: {n.rsplit('.', 1)[-1] for n in declarations(source.read_text())}
                      for m in modules if (source := root / module_path(m)).is_file()}
            for token in ticks:
                short = token.rsplit('.', 1)[-1]
                for module, declared in shorts.items():
                    if short in declared and (short, module) not in listed:
                        errors.append(f'{doc}: `{token}` ({module}) is not in {INVENTORY}')
    return errors


# ----------------------------------------------------------------------------- document

def render(rows: list[dict], inv: dict) -> str:
    def cell(text: str) -> str:
        return ' '.join(text.split()).replace('|', '\\|')

    out = ['| Theorem | Module | Scope | Domain | Check results |', '|---|---|---|---|---|']
    for row in rows:
        checks = []
        for c in row['checks']:
            label = f'{c["zig"]}/{c["target"]}'
            if 'excluded' in c:
                checks.append(f'{label}: excluded ({cell(c["excluded"])})')
            else:
                checks.append(f'{label}: {"pass, run `" + c["run"] + "`" if c["run"] else "none"}')
        out.append(f'| `{row["name"]}` | `{row["module"]}` | {row["scope"]} | {cell(row["domain"])} '
                   f'| {"<br>".join(checks)} |')
    out += ['', '| Run | Translation | Build | Result | Revision | Started (UTC) | Log SHA-256 |',
            '|---|---|---|---|---|---|---|']
    for run_id, run in sorted(inv.get('runs', {}).items()):
        swapped = ', '.join(f'`{g["path"]}`' for g in run['gens'].values()
                            if not g['path'].startswith('Proofs/'))
        translation = (f'{run["zig"]}/{run["target"]}: {swapped}' if swapped else
                       'committed `Proofs/*/Gen.lean` (Linux, every version without a golden)')
        revision = run.get('revision', {})
        rev = revision.get('head', 'unknown')[:12] + (' (dirty)' if revision.get('tracked_dirty') else '')
        out.append(f'| `{run_id}` | {translation} | `{" ".join(run["command"])}` | '
                   f'{run["outcome"]} (exit {run["exit_code"]}) | `{rev}` | '
                   f'{run.get("started_utc", "")[:19]} | `{run.get("log_sha256", "")[:16]}` |')
    return '\n'.join(out) + '\n'


def document(root: Path, rows: list[dict], inv: dict) -> tuple[str, str]:
    text = (root / DOC).read_text()
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise Error(f'{DOC}: needs one {BEGIN} and one {END}')
    head, rest = text.split(BEGIN)
    _, tail = rest.split(END)
    return text, f'{head}{BEGIN}\n{render(rows, inv)}{END}{tail}'


def check(root: Path = ROOT, write: bool = False) -> list[str]:
    inv = load(root)
    rows, errors = results(root, inv)
    errors += claim_errors(root, inv) + listing_errors(root, inv)
    try:
        old, new = document(root, rows, inv)
        if write:
            (root / DOC).write_text(new)
        elif old != new:
            errors.append(f'{DOC} is stale: run python3 scripts/theorem-inventory.py write')
    except Error as error:
        errors.append(str(error))
    return errors


# ----------------------------------------------------------------------------- build and record

def swap_build(root: Path, swaps: list[str], modules: list[str]) -> int:
    """`lake build modules` with `Proofs/<Ex>/Gen.lean` replaced; the originals are restored."""
    pairs = []
    for spec in swaps:
        example, _, src = spec.partition('=')
        target = root / 'Proofs' / example.capitalize() / 'Gen.lean'
        if not src or not (root / src).is_file() or not target.is_file():
            raise Error(f'bad --swap {spec!r}: want <example>=<translation file>')
        pairs.append((example, Path(src), target))
    saved = {target: target.read_bytes() for _, _, target in pairs}

    def stop(signum, _frame):
        raise SystemExit(128 + signum)
    previous = {s: signal.signal(s, stop) for s in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP)}
    try:
        for example, src, target in pairs:
            target.write_bytes((root / src).read_bytes())
            print(f'{SWAP_PREFIX}{example} {src} {sha256(root / src)}', flush=True)
        return subprocess.run(['lake', 'build', *modules], cwd=root).returncode
    finally:
        for target, data in saved.items():
            target.write_bytes(data)
        for s, handler in previous.items():
            signal.signal(s, handler)


def portable(root: Path, arg: str) -> str:
    """An absolute path in the repository relative to it; another absolute path by its name."""
    path = Path(arg)
    if not path.is_absolute():
        return arg
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError:
        return path.name


def attest_generated(root: Path, paths: list[str]) -> None:
    """Refuse a result over a translation file that is not a fresh translation of its committed
    AIR (scripts/gen-integrity.py attest; the translator must be built)."""
    result = subprocess.run([sys.executable, str(root / 'scripts/gen-integrity.py'), 'attest', *paths],
                            cwd=root, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if result.returncode != 0:
        raise Error('translation files are not fresh translations of their committed AIR:\n'
                    + result.stderr.strip())


def record(root: Path, zig: str, target: str, report_path: Path, log_path: Path) -> dict:
    report = json.loads(report_path.read_text())
    log = log_path.read_bytes()
    if hashlib.sha256(log).hexdigest() != report.get('log_sha256'):
        raise Error(f'{log_path}: does not match the log_sha256 of {report_path}')
    if report.get('log_truncated'):
        raise Error(f'{log_path}: truncated; rerun with a larger --log-bytes')
    if Path(report.get('cwd', '')).resolve() != root.resolve():
        raise Error(f'{report_path}: ran in {report.get("cwd")}, not {root}')
    command = report.get('command') or []
    names = [Path(c).name for c in command]
    if 'lake' in names and 'build' in command:
        modules = command[command.index('build') + 1:]
    elif '--' in command:
        modules = command[command.index('--') + 1:]
    else:
        raise Error(f'{report_path}: not a lake build or swap-build command: {command}')
    built = library_modules(root) if 'Proofs' in modules else closure(root, modules)
    swaps = {}
    for line in log.decode(errors='replace').splitlines():
        if line.startswith(SWAP_PREFIX):
            example, src, digest = line[len(SWAP_PREFIX):].split()
            if sha256(root / src) != digest:
                raise Error(f'{src}: changed since the run (recorded {digest[:12]})')
            swaps[example] = {'path': src, 'sha256': digest}
    gens, sources = {}, {}
    for mod in built:
        parts = mod.split('.')
        if parts[-1] == 'Gen':
            example = parts[1].lower()
            gens[example] = swaps.get(example) or {
                'path': str(module_path(mod)), 'sha256': sha256(root / module_path(mod))}
        else:
            sources[mod] = sha256(root / module_path(mod))
    attest_generated(root, sorted({gen['path'] for gen in gens.values()}))
    toolchain = [p for p in report.get('pins', []) if p.get('path', '').endswith('lean-toolchain')]
    return {
        'zig': zig, 'target': target, 'command': [portable(root, c) for c in command],
        'outcome': report.get('outcome'), 'exit_code': report.get('exit_code'),
        'revision': report.get('revision', {}), 'started_utc': report.get('started_utc'),
        'elapsed_seconds': report.get('elapsed_seconds'), 'host': report.get('host'),
        'log_sha256': report.get('log_sha256'),
        'lean_toolchain_sha256': toolchain[0]['sha256'] if toolchain else None,
        'modules': sorted(m for m in built if not m.endswith('.Gen')),
        'gens': dict(sorted(gens.items())), 'sources': dict(sorted(sources.items())),
    }


def write_inventory(root: Path, inv: dict) -> None:
    (root / INVENTORY).write_text(json.dumps(inv, indent=2, ensure_ascii=False) + '\n')


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    p.add_argument('--root', type=Path, default=ROOT)
    sub = p.add_subparsers(dest='cmd')
    sub.add_parser('check')
    sub.add_parser('write')
    sb = sub.add_parser('swap-build')
    sb.add_argument('--swap', action='append', default=[], metavar='EXAMPLE=GEN')
    sb.add_argument('modules', nargs='+')
    rc = sub.add_parser('record')
    rc.add_argument('--run', required=True)
    rc.add_argument('--zig', required=True)
    rc.add_argument('--target', choices=TARGETS, default='linux')
    rc.add_argument('--guard-report', type=Path, required=True)
    rc.add_argument('--guard-log', type=Path, required=True)
    a = p.parse_args(argv)
    root = a.root.resolve()
    try:
        if a.cmd == 'swap-build':
            return swap_build(root, a.swap, [m for m in a.modules if m != '--'])
        if a.cmd == 'record':
            inv = load(root)
            inv.setdefault('runs', {})[a.run] = record(root, a.zig, a.target,
                                                       a.guard_report, a.guard_log)
            write_inventory(root, inv)
            print(f'recorded run {a.run}: {inv["runs"][a.run]["outcome"]}')
            return 0
        errors = check(root, write=a.cmd == 'write')
    except (Error, OSError, KeyError, ValueError) as error:
        print(f'error: {error}', file=sys.stderr)
        return 1
    for error in errors:
        print(f'error: {error}', file=sys.stderr)
    if errors:
        return 1
    print('theorem inventory: every listed theorem has a current check result and scope')
    return 0


if __name__ == '__main__':
    sys.exit(main())
