#!/usr/bin/env python3
"""Theorem inventory: each headline theorem, its scope and domain, and its current check result.

assurance/theorem-inventory.json lists each theorem (Lean name, module, example, scope class,
domain) and the guarded `lake build` runs that checked it. A theorem must be checked against
the translation of every Zig version/target that its example supports (`translations`):
`tests/golden/<v>/<ex>/Gen-<os>.lean`, else `tests/golden/<v>/<ex>/Gen.lean`, else the
committed `Proofs/<Ex>/Gen.lean` (the rule of scripts/check.sh); a theorem whose entry names
`gen` only against that retained translation (`retained`). A run result is current only
while the translation file and every `Proofs` source the module imports have the hashes the
run recorded.

`check` (default) fails when a listed theorem is missing from its module, has no current
successful run for a required translation, has an all-schedules scope without a statement
over every fuel and oracle, names a `completes` witness that does not show a completed run of
the same program, when a document or Lean doc comment says "every schedule" of a
theorem whose scope is narrower, when a theorem of a proved-examples table is not listed,
or when docs/theorem-inventory.md is stale. `write` regenerates that document's table.
`swap-build` builds modules against other translation files in a check tree, never
replacing the committed ones. `record` adds a build-guard report of such a build to the inventory, after
scripts/gen-integrity.py attests that each translation file it records is a fresh translation
of its committed AIR. See
docs/theorem-inventory.md.
"""
from __future__ import annotations

import argparse
import functools
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = Path('assurance/theorem-inventory.json')
DOC = Path('docs/theorem-inventory.md')
BEGIN, END = '<!-- BEGIN theorem-inventory -->', '<!-- END theorem-inventory -->'
SCOPES = ('single-step', 'single-schedule', 'bounded-schedules', 'all-schedules', 'sequential')
# Host keys of the translation files (`Gen-<target>.lean`, as scripts/check.sh selects them).
TARGETS = ('linux', 'darwin', 'linux-aarch64')
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
SWAP_PREFIX = 'theorem-inventory swap: '
PROFILE_PREFIX = '-- air2lean-profile: '
DEPS_SPEC = importlib.util.spec_from_file_location('inventory_lean_deps', Path(__file__).resolve().with_name('lean-deps.py'))
DEPS = importlib.util.module_from_spec(DEPS_SPEC)
DEPS_SPEC.loader.exec_module(DEPS)


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


def canonical_example(module: str) -> str | None:
    """Only an example's exact canonical translation owns its short inventory key."""
    return module.split('.')[1].lower() if canonical_gen(module) else None


def swap_identity(example: str, source: str) -> tuple[str, str]:
    """Canonical example key and repository-relative source spelling for a swap."""
    if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', example):
        raise Error(f'bad swap example {example!r}: expected one ASCII identifier')
    path = Path(source)
    if (not source or '\0' in source or any(char.isspace() for char in source)
            or path.is_absolute() or '..' in path.parts):
        raise Error(f'bad swap {example}={source!r}: use an example and a repository-relative path '
                    'without whitespace, NUL or ..')
    return example.lower(), str(path)


class CommandParser(argparse.ArgumentParser):
    def error(self, message):
        raise Error(message)


def argument_parser(root: Path = ROOT, *, add_help: bool = True):
    """One definition of the executable inventory CLI and recorded swap-build grammar."""
    p = CommandParser(description=__doc__.split('\n\n')[0], add_help=add_help)
    p.add_argument('--root', type=Path, default=root)
    sub = p.add_subparsers(dest='cmd')
    sub.add_parser('check', add_help=add_help)
    sub.add_parser('write', add_help=add_help)
    sb = sub.add_parser('swap-build', add_help=add_help)
    sb.add_argument('--lake', type=Path, help='physical selected toolchain Lake (required for recording)')
    sb.add_argument('--swap', action='append', default=[], metavar='EXAMPLE=GEN')
    sb.add_argument('modules', nargs='+')
    rc = sub.add_parser('record', add_help=add_help)
    rc.add_argument('--run', required=True)
    rc.add_argument('--zig', required=True)
    rc.add_argument('--target', choices=TARGETS, default='linux')
    rc.add_argument('--guard-report', type=Path, required=True)
    rc.add_argument('--guard-log', type=Path, required=True)
    return p


class BuildCommand:
    def __init__(self, kind, lake, modules, swaps, lake_args=(), python=()):
        self.kind, self.lake = kind, lake
        self.modules, self.swaps = modules, swaps
        self.lake_args, self.python = lake_args, python

    def invocation(self, lake: Path, python: str | None = None) -> list[str]:
        """Reconstruct supported semantics with an explicitly selected local producer."""
        if self.kind == 'lake':
            return [str(lake), *self.lake_args]
        command = [*([python] if python is not None else self.python),
                   'scripts/theorem-inventory.py', 'swap-build', '--lake', str(lake)]
        for example, source in self.swaps.items():
            command += ['--swap', f'{example}={source}']
        return [*command, '--', *self.modules]

    def renewal(self, lake: Path, python: str) -> list[str]:
        """Fresh renewal permits rebuilding; historical recording keeps captured policy."""
        command = self.invocation(lake, python)
        return [arg for arg in command if arg != '--no-build'] if self.kind == 'lake' else command


def parse_build_command(root: Path, command: list[str], *, lake: str | None = None) -> BuildCommand:
    """Supported build targets and last normalized swaps, under the trusted local runtime.

    Command spelling identifies the supported producer position, not the authenticity of
    a historical executable. Lake's root-preserving subset follows the pinned Lake CLI;
    workspace/configuration changes, unknown options and implicit default targets fail closed.
    """
    if not isinstance(command, list) or not command or any(not isinstance(arg, str) for arg in command):
        raise Error('malformed recorded build command')
    swaps = {}
    lake_args, python = [], []
    if command[0] == 'lake' or (lake is not None and command[0] == lake):
        kind, lake, lake_args = 'lake', command[0], command[1:]
        # These alter hashing, reporting, failure thresholds or cache/build policy, never
        # the selected workspace/configuration. Lake processes options among targets too.
        flags = {'--rehash', '-H', '--quiet', '-q', '--verbose', '-v', '--text', '--json', '-J',
                 '--ansi', '--no-ansi', '--wfail', '--iofail', '--no-build', '--no-cache',
                 '--try-cache', '--offline'}
        levels = {'trace', 'info', 'information', 'warn', 'warning', 'error'}
        modules, build, index = [], False, 1
        while index < len(command):
            arg = command[index]
            if arg in flags:
                index += 1
                continue
            option, equals, value = arg.partition('=')
            if option in ('--log-level', '--fail-level'):
                if not equals:
                    index += 1
                    value = command[index] if index < len(command) else ''
                if value.lower() not in levels:
                    raise Error(f'bad Lake log level {value!r}')
            elif arg.startswith('-'):
                raise Error(f'unsupported Lake option {arg!r}: expected a root-preserving build')
            elif not build:
                if arg != 'build':
                    raise Error('unsupported Lake command: expected build with explicit modules')
                build = True
            else:
                modules.append(arg)
            index += 1
        if not build:
            raise Error('unsupported Lake command: expected build with explicit modules')
    elif re.fullmatch(r'(?:python(?:3(?:\.[0-9]+)?)?|Python)', Path(command[0]).name):
        kind = 'swap'
        index = 1
        while index < len(command) and command[index] in ('-B', '-u'):
            index += 1
        if index == len(command) or (root / command[index]).resolve() != (root / 'scripts/theorem-inventory.py').resolve():
            raise Error('unsupported build producer: expected the root inventory script at Python script position')
        args = argument_parser(root, add_help=False).parse_args(command[index + 1:])
        if args.cmd != 'swap-build' or (root / args.root).resolve() != root.resolve():
            raise Error('unsupported inventory command: expected swap-build in the same root')
        modules = args.modules
        lake = str(args.lake) if args.lake is not None else None
        python = command[:index]
        for spec in args.swap:
            example, sep, source = spec.partition('=')
            if not sep:
                raise Error(f'bad --swap {spec!r}: expected EXAMPLE=SOURCE')
            example, source = swap_identity(example, source)
            swaps[example] = source
    else:
        raise Error('unsupported build producer: expected direct Lake or Python inventory swap-build')
    if not modules or any(not isinstance(m, str) or not DEPS.MODULE_NAME.fullmatch(m) for m in modules):
        raise Error('build requires explicit Lean module or library names')
    return BuildCommand(kind, lake, modules, swaps, lake_args, python)


def selected_lake(root: Path) -> Path:
    """The physical pinned toolchain, using CI's Elan lookup without invoking Lean/Lake."""
    pin = (root / 'lean-toolchain').read_text().strip()
    if not pin:
        raise Error('lean-toolchain is empty')
    try:
        result = subprocess.run(['elan', 'which', 'lake'], cwd=root,
                                env={**os.environ, 'ELAN_TOOLCHAIN': pin}, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode:
            raise Error('cannot locate pinned Lean toolchain: ' + result.stderr.strip())
        entry = Path(result.stdout.strip())
        if not entry.is_absolute() or not entry.is_file():
            raise Error('Elan did not name an installed absolute Lake entry')
        lake = entry.resolve(strict=True)
        if not lake.is_file() or not os.access(lake, os.X_OK):
            raise Error('selected toolchain Lake is not executable: ' + str(lake))
        return lake
    except OSError as error:
        raise Error('cannot locate pinned Lean toolchain: ' + str(error)) from error


def producer_path(run: dict) -> str | None:
    """A structurally valid historical identity, without inspecting its file or release pin."""
    row = run.get('producer')
    if not isinstance(row, dict) or set(row) != {'path', 'sha256', 'bytes'}:
        return None
    path, digest, size = row['path'], row['sha256'], row['bytes']
    valid = (isinstance(path, str) and Path(path).is_absolute() and str(Path(path)) == path
            and '..' not in Path(path).parts and '\0' not in path
            and isinstance(digest, str) and re.fullmatch(r'[0-9a-f]{64}', digest) is not None
            and type(size) is int and size > 0)
    return path if valid else None


def producer_matches(root: Path, run: dict, build: BuildCommand) -> bool:
    """Historical identity only: never open another host's captured producer path."""
    path = producer_path(run)
    return (path is not None and build.lake == path
            and run.get('lean_toolchain_sha256') == sha256(root / 'lean-toolchain'))


def captured_producer(root: Path, report: dict, build: BuildCommand, lake: Path) -> dict:
    """Validate live selected bytes against the guard's actual producer capture at record time."""
    expected = {'path': str(lake), 'sha256': hashlib.sha256(lake.read_bytes()).hexdigest(),
                'bytes': lake.stat().st_size}
    if build.lake != str(lake):
        raise Error('build command must name the selected physical Lake explicitly')
    if report.get('schema') != 1 or report.get('requested_command') != report.get('command'):
        raise Error('guard command capture is missing or inconsistent')
    tools = report.get('tools')
    if not isinstance(tools, list):
        raise Error('guard producer capture is missing')
    candidates = tools[:1] if build.kind == 'lake' else tools[3:]
    if expected not in candidates:
        raise Error('guard producer capture differs from selected Lake (swap-build needs --tool LAKE)')
    pin = root / 'lean-toolchain'
    pin_row = {'path': str(pin.resolve()), 'sha256': sha256(pin), 'bytes': pin.stat().st_size}
    if pin_row not in report.get('pins', []):
        raise Error('guard toolchain pin is missing or stale')
    return expected


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
    """`Sched.run env dispatch fuel o …` with `fuel` and `o` bound by the statement itself (the
    environment `env` is explicit: a bound variable or a literal)."""
    for m in re.finditer(r'Sched\.run\b', statement):
        args = _sched_args(statement, m.end(), 4)
        if len(args) < 4 or not re.fullmatch(r'\w+', args[2]) or not re.fullmatch(r'\w+', args[3]):
            continue
        fuel, oracle = args[2], args[3]
        if (re.search(r'[({]\s*' + fuel + r'\b[^:]*:\s*Nat\s*[)}]', statement) and
                re.search(r'[({][^:]*\b' + oracle + r'\b[^:]*:\s*Nat\s*→\s*Nat\s*[)}]', statement)):
            return True
    return False


def _sched_args(text: str, start: int, count: int) -> list[str]:
    """The next `count` whitespace-separated arguments after `start`, keeping brackets balanced."""
    args, depth, current = [], 0, ''
    for ch in text[start:]:
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            if depth == 0:
                break
            depth -= 1
        if ch.isspace() and depth == 0:
            if current:
                args.append(current)
                current = ''
                if len(args) == count:
                    break
            continue
        current += ch
    if current and len(args) < count:
        args.append(current)
    return args


def sched_programs(statement: str) -> set[str]:
    """Head identifiers of the programs run by `Sched.run env dispatch fuel o program mem`."""
    programs = set()
    for m in re.finditer(r'Sched\.run\b', statement):
        args = _sched_args(statement, m.end(), 5)
        if len(args) == 5 and (head := re.match(r'[(\s]*([\w.]+)', args[4])):
            programs.add(head.group(1))
    return programs


def completion_errors(thm: dict, decl: dict, listed: dict, decls: dict) -> list[str]:
    """An all-schedules theorem says nothing about runs that never complete (out of fuel is
    allowed). Its `completes` companion, if named, is a listed single- or bounded-schedule
    theorem of the same example whose statement shows a `Sched.run` of the same program with a
    successful result (`= some ...`): at least one schedule completes within its fuel."""
    name, companion = thm['name'], thm.get('completes')
    if companion is None:
        return []
    if thm['scope'] != 'all-schedules':
        return [f'{name}: `completes` is only for all-schedules theorems']
    other = listed.get(companion)
    if other is None or other['scope'] not in ('single-schedule', 'bounded-schedules') \
            or other['example'] != thm['example']:
        return [f'{name}: completion witness {companion} is not a listed single- or bounded-schedule '
                f'theorem of {thm["example"]}']
    statement = (decls.get(other['module']) or {}).get(companion, {}).get('statement', '')
    if not (sched_programs(statement) & sched_programs(decl['statement'])) or not re.search(r'=\s*some\b', statement):
        return [f'{name}: completion witness {companion} does not show a completed `Sched.run` of the same program']
    return []


def scope_label(row: dict) -> str:
    """The rendered scope: an all-schedules theorem without a completion witness is labelled so."""
    if row['scope'] == 'all-schedules' and not row.get('completes'):
        return 'all-schedules (no run shown to complete)'
    return row['scope']


def closure(root: Path, modules: list[str], swaps: dict[str, str] | None = None) -> list[str]:
    """`Proofs` imports of the actual selected sources, preserving module identities."""
    swaps = {} if swaps is None else swaps
    seen: set[str] = set()
    todo = list(modules)
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = root / swaps.get(canonical_example(mod), module_path(mod))
        if not path.is_file():
            raise Error(f'{mod}: no source file {module_path(mod)}')
        try:
            todo.extend(m for m in DEPS.imports(path) if m.startswith('Proofs.'))
        except ValueError as error:
            raise Error(str(error)) from error
    return sorted(seen)


def library_modules(root: Path) -> list[str]:
    return sorted('.'.join(p.relative_to(root).with_suffix('').parts)
                  for p in (root / 'Proofs').rglob('*.lean'))


def discover_modules(root: Path, modules: list[str], swaps: dict[str, str], cache=None) -> list[str]:
    """Share source discovery only within an invocation, including its swap overlay."""
    whole_library = 'Proofs' in modules
    key = ((root.resolve(), 'library') if whole_library else
           (root.resolve(), tuple(sorted(set(modules))), tuple(sorted(swaps.items()))))
    cache = {} if cache is None else cache
    if key not in cache:
        cache[key] = library_modules(root) if whole_library else closure(root, modules, swaps)
    return cache[key]


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


@functools.lru_cache(maxsize=None)
def _is_translation(path: Path, mtime_ns: int, size: int) -> bool:
    with path.open('rb') as f:
        return f.readline().startswith(PROFILE_PREFIX.encode())


def is_translation(path: Path) -> bool:
    """A profile-bearing module, cached with the existing source-hash metadata key."""
    info = path.stat()
    return _is_translation(path, info.st_mtime_ns, info.st_size)


def retained(root: Path, gen: str) -> dict:
    """A theorem's own retained translation (`gen` in its entry: a generated module of `Proofs`
    other than its example's `Gen.lean`, such as a translation with an open interface), with the
    Zig version and target of its profile record."""
    first = (root / gen).read_text().split('\n', 1)[0]
    if not first.startswith(PROFILE_PREFIX):
        raise Error(f'{gen}: no `{PROFILE_PREFIX.strip()}` record on its first line')
    profile = json.loads(first[len(PROFILE_PREFIX):])['profile']
    triple = profile['target_triple']
    target = ('darwin' if 'macos' in triple else
              'linux-aarch64' if triple.startswith('aarch64') else 'linux')
    return {'zig': profile['zig_version'], 'target': target, 'gen': gen}


def theorem_translations(root: Path, thm: dict) -> list[dict]:
    """The translations a theorem must hold for: its retained one, else its example's."""
    return [retained(root, thm['gen'])] if thm.get('gen') else translations(root, thm['example'])


def gen_key(thm: dict) -> str:
    """The key of a theorem's translation in a run's `gens`: the module of a retained
    translation, else the example."""
    return '.'.join(Path(thm['gen']).with_suffix('').parts) if thm.get('gen') else thm['example']


def canonical_gen(mod: str) -> bool:
    parts = mod.split('.')
    return len(parts) == 3 and parts[0] == 'Proofs' and parts[-1] == 'Gen'


def module_evidence_matches(root: Path, run: dict, module: str, swaps: dict[str, str]) -> bool:
    """A built module has its own current evidence, including the declared canonical swap."""
    path = module_path(module)
    source = root / path
    if not source.is_file():
        return False
    example = canonical_example(module)
    info = None
    if example is not None:
        expected = swaps.get(example, str(path))
        recorded = run.get('gens', {}).get(example, {})
    else:
        info = source.stat()
        if not module.endswith('.Gen') and not _is_translation(source, info.st_mtime_ns, info.st_size):
            return run.get('sources', {}).get(module) == _sha256(source, info.st_mtime_ns, info.st_size)
        expected = str(path)
        recorded = run.get('gens', {}).get(module, {})
    expected_source = root / expected
    if recorded.get('path') != expected:
        return False
    if expected_source == source:
        if info is None:
            info = source.stat()
        return recorded.get('sha256') == _sha256(source, info.st_mtime_ns, info.st_size)
    return expected_source.is_file() and recorded.get('sha256') == sha256(expected_source)


# ----------------------------------------------------------------------------- check

def load(root: Path) -> dict:
    return json.loads((root / INVENTORY).read_text())


def prepare_run(root: Path, run: dict, discovered=None):
    """Parse and discover one candidate run; source evidence remains checked by each caller."""
    try:
        build = parse_build_command(root, run.get('command'), lake=producer_path(run))
        if not producer_matches(root, run, build):
            return None
        built = discover_modules(root, build.modules, build.swaps, discovered)
        if sorted(m for m in built if not m.endswith('.Gen')) != run.get('modules'):
            return None
        return build, built
    except Error:
        return None


def current_result(root: Path, inv: dict, thm: dict, tr: dict, decl_closure: list[str], prepared=None, discovered=None):
    """The id of a successful run whose recorded hashes match the current files, or None."""
    gen_sha = sha256(root / tr['gen'])
    prepared = {} if prepared is None else prepared
    discovered = {} if discovered is None else discovered
    for run_id, run in sorted(inv.get('runs', {}).items()):
        if run.get('outcome') != 'success' or run.get('exit_code') != 0:
            continue
        if thm['module'] not in run.get('modules', []):
            continue
        gen = run.get('gens', {}).get(gen_key(thm))
        if not gen or gen.get('path') != tr['gen'] or gen.get('sha256') != gen_sha:
            continue
        if run_id not in prepared:
            prepared[run_id] = prepare_run(root, run, discovered)
        if prepared[run_id] is None:
            continue
        build, _ = prepared[run_id]
        try:
            modules = (discover_modules(root, [thm['module']], build.swaps, discovered)
                       if build.swaps else decl_closure)
        except Error:
            continue
        if all(module_evidence_matches(root, run, mod, build.swaps) for mod in modules):
            return run_id
    return None


def results(root: Path, inv: dict) -> tuple[list[dict], list[str]]:
    """Per theorem: its required translations with the current run (or the exclusion)."""
    errors: list[str] = []
    rows = []
    names = set()
    decl_cache: dict[str, dict] = {}
    prepared = {}  # Invocation-local: never persist parsing or module discovery.
    discovered = {}
    listed = {t['name']: t for t in inv.get('theorems', []) if all(t.get(k) for k in ('name', 'module', 'example', 'scope'))}
    for thm in listed.values():
        path = root / module_path(thm['module'])
        if thm['module'] not in decl_cache and path.is_file():
            decl_cache[thm['module']] = declarations(path.read_text())
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
        errors += completion_errors(thm, decl, listed, decl_cache)
        try:
            mods = discover_modules(root, [thm['module']], {}, discovered)
        except Error as error:
            errors.append(str(error))
            continue
        imported = gen_key(thm) if thm.get('gen') else gen_module(thm['example'])
        if imported not in mods:
            errors.append(f'{name}: {thm["module"]} does not import {imported}')
        excluded = {(e['zig'], e['target']): e['reason'] for e in thm.get('excluded', [])}
        checks = []
        try:
            required = theorem_translations(root, thm)
        except (Error, OSError, KeyError, ValueError) as error:
            errors.append(f'{name}: {error}')
            continue
        for tr in required:
            label = f'{tr["zig"]}/{tr["target"]}'
            if (tr['zig'], tr['target']) in excluded:
                checks.append({**tr, 'excluded': excluded.pop((tr['zig'], tr['target']))})
                continue
            run = current_result(root, inv, thm, tr, mods, prepared, discovered)
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
        out.append(f'| `{row["name"]}` | `{row["module"]}` | {scope_label(row)} | {cell(row["domain"])} '
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

def swap_build(root: Path, swaps: dict[str, str], modules: list[str], lake: Path) -> int:
    """`lake build modules` with `Proofs/<Ex>/Gen.lean` replaced, in a check tree
    (scripts/check-tree.py): the checkout's files are never written."""
    replacements = []
    for example, src in swaps.items():
        target = root / 'Proofs' / example.capitalize() / 'Gen.lean'
        source = root / src
        if not source.is_file() or not target.is_file():
            raise Error(f'bad --swap {example}={src}: want <example>=<translation file>')
        replacements.append(f'{target.relative_to(root)}={source}')
        print(f'{SWAP_PREFIX}{example} {src} {sha256(source)}', flush=True)
    spec = importlib.util.spec_from_file_location('check_tree', Path(__file__).resolve().with_name('check-tree.py'))
    check_tree = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(check_tree)
    try:
        tree = check_tree.create(root / '.lake/check-tree/theorem-inventory', replacements, root)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise Error(f'check tree: {error}')
    return subprocess.run([str(lake), 'build', *modules], cwd=tree).returncode


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
    lake = selected_lake(root)
    build = parse_build_command(root, command, lake=str(lake))
    producer = captured_producer(root, report, build, lake)
    built = discover_modules(root, build.modules, build.swaps)
    swaps = {}
    for line in log.decode(errors='replace').splitlines():
        if line.startswith(SWAP_PREFIX):
            fields = line[len(SWAP_PREFIX):].split()
            if len(fields) != 3:
                raise Error('bad swap log: expected one ASCII identifier, relative path and digest')
            example, src, digest = fields
            example, src = swap_identity(example, src)
            if sha256(root / src) != digest:
                raise Error(f'{src}: changed since the run (recorded {digest[:12]})')
            swaps[example] = {'path': src, 'sha256': digest}
    if {example: entry['path'] for example, entry in swaps.items()} != build.swaps:
        raise Error('swap log identities differ from the recorded build command')
    gens, sources = {}, {}
    for mod in built:
        path = module_path(mod)
        source = root / path
        # Only the canonical example translation owns the short key. Deeper Gen modules
        # are retained translations, each recorded under its full module below.
        example = canonical_example(mod)
        if example is not None:
            gens[example] = swaps.get(example) or {
                'path': str(path), 'sha256': sha256(source)}
        elif mod.endswith('.Gen') or is_translation(source):
            gens[mod] = {'path': str(path), 'sha256': sha256(source)}
        else:
            sources[mod] = sha256(source)
    if gens:
        attest_generated(root, sorted({gen['path'] for gen in gens.values()}))
    return {
        'zig': zig, 'target': target, 'command': build.invocation(Path(producer['path'])),
        'producer': producer,
        'outcome': report.get('outcome'), 'exit_code': report.get('exit_code'),
        'revision': report.get('revision', {}), 'started_utc': report.get('started_utc'),
        'elapsed_seconds': report.get('elapsed_seconds'), 'host': report.get('host'),
        'log_sha256': report.get('log_sha256'),
        'lean_toolchain_sha256': sha256(root / 'lean-toolchain'),
        'modules': sorted(m for m in built if not m.endswith('.Gen')),
        'gens': dict(sorted(gens.items())), 'sources': dict(sorted(sources.items())),
    }


def write_inventory(root: Path, inv: dict) -> None:
    (root / INVENTORY).write_text(json.dumps(inv, indent=2, ensure_ascii=False) + '\n')


def main(argv: list[str] | None = None) -> int:
    try:
        a = argument_parser().parse_args(argv)
        root = a.root.resolve()
        if a.cmd == 'swap-build':
            command = [sys.executable, str(root / 'scripts/theorem-inventory.py'), 'swap-build']
            if a.lake is not None:
                command += ['--lake', str(a.lake)]
            for spec in a.swap:
                command += ['--swap', spec]
            build = parse_build_command(root, [*command, '--', *a.modules])
            lake = selected_lake(root)
            if build.lake is not None and build.lake != str(lake):
                raise Error('swap-build --lake must name the selected physical Lake')
            return swap_build(root, build.swaps, build.modules, lake)
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
