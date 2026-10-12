#!/usr/bin/env python3
"""T05 native/WASM correspondence: observe paired fixtures and check the stated relation.

One source (tests/roadmap/wasm-correspondence/kernels.zig) is compiled for a native target and
for wasm32-freestanding with the same stock compiler and optimize mode. Every export maps `u64`
words to a `u64` word; an observation is that word or `trap` (a safety panic). The relation in
`relation.json` gives each export one class (docs/research/T05.md):

  exact            the native and the wasm32 observation are equal, word or trap;
  tolerated        floats: both NaN of the format (sign and payload may differ), or at most
                   `ulp` units in the last place apart (0: bit-equal); a trap pairs with a trap;
  target-specific  the targets are not compared with each other: each target's observation
                   equals `expect` evaluated with that target's `bits` (pointer width), the
                   per-profile model of the effect.

`record` builds and runs one target and writes its observations, bound to the compiler, the
source bytes and the generated cases. `check` fails closed: an export without a relation entry
(or an entry without an export), a missing record of the declared matrix, a stale record, an
unknown class, an unrelated pair, and a claim that cites a theorem about another target's
generated module (a native theorem is never relabeled as a wasm32 theorem) all fail.

  scripts/wasm-correspondence.py record --zig ZIG --target native|wasm32   (writes records/)
  scripts/wasm-correspondence.py record --zig ZIG --target ... --verify     (rerun = record)
  scripts/wasm-correspondence.py check
"""
from __future__ import annotations

import argparse
import ast
import ctypes
import hashlib
import json
import operator
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CASE_DIR = ROOT / 'tests/roadmap/wasm-correspondence'
RELATION = CASE_DIR / 'relation.json'
RECORDS = CASE_DIR / 'records'
WASM = 'wasm32-freestanding'
CLASSES = ('exact', 'tolerated', 'target-specific')
TRAP = 'trap'
MASK64 = (1 << 64) - 1
EXPORT_RE = re.compile(r'^export fn (\w+)\(([^)]*)\) u64 \{$', re.M)
FORMATS = {'f32': (32, 8), 'f64': (64, 11)}  # width, exponent bits


# ------------------------------------------------------------------------------ relation

def load_relation(path: Path = RELATION) -> dict:
    data = json.loads(path.read_text())
    if not isinstance(data, dict) or data.get('schema') != 1:
        raise ValueError(f'{path}: unsupported relation schema')
    for key in ('source', 'modules', 'optimize', 'targets', 'matrix', 'domains', 'kernels', 'claims'):
        if key not in data:
            raise ValueError(f'{path}: missing {key}')
    return data


def exports(source: str) -> dict[str, int]:
    """Export name -> parameter count; every parameter must be a `u64`."""
    found = {}
    for name, params in EXPORT_RE.findall(source):
        parts = [p.strip() for p in params.split(',') if p.strip()]
        if any(not re.fullmatch(r'\w+: u64', p) for p in parts):
            raise ValueError(f'export {name}: every parameter must be u64')
        found[name] = len(parts)
    if source.count('export fn ') != len(found):
        raise ValueError('an export does not have the form `export fn name(a: u64, ...) u64 {`')
    return found


# A small closed expression language for `expect`: integers, `a`/`b`/`c` (the arguments),
# `bits`, `NONE` (maxInt(u64)), `TRAP`, arithmetic, comparisons, `and`/`or`/`not`, `x if c else y`.
_BIN = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul, ast.FloorDiv: operator.floordiv,
        ast.Mod: operator.mod, ast.Pow: operator.pow, ast.LShift: operator.lshift, ast.RShift: operator.rshift,
        ast.BitAnd: operator.and_, ast.BitOr: operator.or_, ast.BitXor: operator.xor}
_CMP = {ast.Lt: operator.lt, ast.LtE: operator.le, ast.Gt: operator.gt, ast.GtE: operator.ge,
        ast.Eq: operator.eq, ast.NotEq: operator.ne}


def evaluate(expr: str, env: dict):
    def go(node):
        if isinstance(node, ast.Expression):
            return go(node.body)
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return node.value
        if isinstance(node, ast.Name) and node.id in env:
            return env[node.id]
        if isinstance(node, ast.BinOp) and type(node.op) in _BIN:
            return _BIN[type(node.op)](go(node.left), go(node.right))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return not go(node.operand)
        if isinstance(node, ast.BoolOp):
            values = [go(v) for v in node.values]
            return all(values) if isinstance(node.op, ast.And) else any(values)
        if isinstance(node, ast.Compare) and len(node.ops) == 1 and type(node.ops[0]) in _CMP:
            return _CMP[type(node.ops[0])](go(node.left), go(node.comparators[0]))
        if isinstance(node, ast.IfExp):
            return go(node.body) if go(node.test) else go(node.orelse)
        raise ValueError(f'unsupported expect expression element {ast.dump(node)[:60]}')
    return go(ast.parse(expr, mode='eval'))


def validate(relation: dict, root: Path = ROOT) -> list[str]:
    errors = []
    source = (root / relation['source']).read_text()
    found = exports(source)
    kernels = relation['kernels']
    for name in sorted(set(found) - set(kernels)):
        errors.append(f'export {name} has no relation entry (every observation needs a class)')
    for name in sorted(set(kernels) - set(found)):
        errors.append(f'relation entry {name} has no export in {relation["source"]}')
    for name, entry in kernels.items():
        cls = entry.get('class')
        if cls not in CLASSES:
            errors.append(f'{name}: unknown class {cls!r}')
            continue
        domains = entry.get('domains')
        if not isinstance(domains, list) or any(d not in relation['domains'] for d in domains):
            errors.append(f'{name}: domains must name entries of `domains`')
        elif name in found and len(domains) != found[name]:
            errors.append(f'{name}: {len(domains)} domains for {found[name]} parameters')
        if cls == 'tolerated' and (entry.get('format') not in FORMATS or type(entry.get('ulp')) is not int
                                   or entry['ulp'] < 0):
            errors.append(f'{name}: a tolerated class needs a float format and an ulp bound >= 0')
        if 'illegal' in entry:
            try:
                evaluate(entry['illegal'], expect_env([0] * len(domains or []), 0))
            except (ValueError, SyntaxError, KeyError) as error:
                errors.append(f'{name}: illegal: {error}')
        if cls == 'target-specific':
            if not isinstance(entry.get('expect'), str):
                errors.append(f'{name}: a target-specific class needs an expect expression')
            else:
                try:
                    evaluate(entry['expect'], expect_env([0] * len(domains or []), 32))
                except (ValueError, SyntaxError, KeyError) as error:
                    errors.append(f'{name}: expect: {error}')
        if not isinstance(entry.get('why'), str) or not entry['why']:
            errors.append(f'{name}: state why the class holds (`why`)')
    for version, targets in relation['matrix'].items():
        if WASM not in targets or not set(targets) <= set(relation['targets']):
            errors.append(f'matrix {version}: needs {WASM} and declared targets only')
    for target, facts in relation['targets'].items():
        if facts.get('pointer_bits') not in (32, 64):
            errors.append(f'target {target}: pointer_bits must be 32 or 64')
    return errors


# ------------------------------------------------------------------------------ cases

def splitmix(seed: int):
    state = seed & MASK64
    while True:
        state = (state + 0x9E3779B97F4A7C15) & MASK64
        z = state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
        yield z ^ (z >> 31)


def cases(relation: dict) -> dict[str, list[list[int]]]:
    """Per kernel: the product of its domains' edge values (capped), then seeded random draws."""
    out = {}
    for name, entry in sorted(relation['kernels'].items()):
        domains = [relation['domains'][d] for d in entry['domains']]
        rows: list[list[int]] = [[]]
        for domain in domains:
            rows = [r + [int(v, 0)] for r in rows for v in domain['edges']]
        rows = rows[:entry.get('edge_cap', 400)]
        rng = splitmix(int.from_bytes(hashlib.sha256(name.encode()).digest()[:8], 'little'))
        for _ in range(entry.get('random', 64) if domains else 0):
            row = []
            for domain in domains:
                r = next(rng)
                row.append(r % domain['random_mod'] if 'random_mod' in domain else r)
            rows.append(row)
        out[name] = rows
    return out


def digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources(relation: dict, root: Path = ROOT) -> dict[str, str]:
    paths = [relation['source'], *relation['modules'].values()]
    return {p: file_sha256(root / p) for p in paths}


# ------------------------------------------------------------------------------ observation

def native_target() -> str:
    arch = {'x86_64': 'x86_64', 'AMD64': 'x86_64', 'arm64': 'aarch64', 'aarch64': 'aarch64'}[platform.machine()]
    return f'{arch}-{ {"Darwin": "macos", "Linux": "linux"}[platform.system()]}'


def build(zig: str, relation: dict, target: str, out: Path) -> Path:
    modules = []
    for name in relation['modules']:
        modules += ['--dep', name]
    modules.append(f'-Mroot={ROOT / relation["source"]}')
    modules += [f'-M{name}={ROOT / path}' for name, path in relation['modules'].items()]
    common = [f'-O{relation["optimize"]}', '--cache-dir', str(out / 'cache'), '--global-cache-dir', str(out / 'gcache')]
    if target == WASM:
        binary = out / 'kernels.wasm'
        command = [zig, 'build-exe', *common, '-target', WASM, '-fno-entry', '-rdynamic', *modules]
    else:
        binary = out / ('libkernels.dylib' if target.endswith('macos') else 'libkernels.so')
        # macOS dylibs must link libSystem; the Linux library links no libc.
        command = [zig, 'build-lib', '-dynamic', *common, *(['-lc'] if target.endswith('macos') else []), *modules]
    subprocess.run([*command, f'-femit-bin={binary}'], check=True, cwd=out)
    return binary


def observe_wasm(binary: Path, calls: dict) -> dict:
    run = subprocess.run(['node', '--no-warnings', str(CASE_DIR / 'run-wasm.mjs'), str(binary)],
                         input=json.dumps({k: [[str(a) for a in row] for row in v] for k, v in calls.items()}),
                         capture_output=True, text=True, check=True)
    return {k: [r if r == TRAP else int(r) for r in v] for k, v in json.loads(run.stdout).items()}


def observe_native(binary: Path, calls: dict) -> dict:
    """Run each kernel's cases in a forked child; a child that dies on a signal trapped on the
    case after its last reported result, and a new child resumes after it."""
    lib = ctypes.CDLL(str(binary))
    out = {}
    for name, rows in calls.items():
        fn = getattr(lib, name)
        fn.restype = ctypes.c_uint64
        fn.argtypes = [ctypes.c_uint64] * (len(rows[0]) if rows else 0)
        results: list = []
        while len(results) < len(rows):
            read, write = os.pipe()
            pid = os.fork()
            if pid == 0:
                os.close(read)
                # A panic's report is not part of the observation.
                os.dup2(os.open(os.devnull, os.O_WRONLY), 2)
                with os.fdopen(write, 'w') as pipe:
                    for row in rows[len(results):]:
                        pipe.write(f'{fn(*row)}\n')
                        pipe.flush()
                os._exit(0)
            os.close(write)
            with os.fdopen(read) as pipe:
                results += [int(line) for line in pipe]
            _, status = os.waitpid(pid, 0)
            if os.WIFSIGNALED(status):
                results.append(TRAP)
            elif os.WEXITSTATUS(status) != 0 or len(results) < len(rows):
                raise RuntimeError(f'{name}: native child exited with status {os.WEXITSTATUS(status)}')
        out[name] = results
    return out


def dump_record(data: dict) -> str:
    """The record as JSON with one line per kernel's results."""
    head = {k: v for k, v in data.items() if k != 'results'}
    rows = ',\n'.join(f'  {json.dumps(k)}: {json.dumps(v, separators=(",", ":"))}'
                      for k, v in sorted(data['results'].items()))
    return json.dumps(head, indent=1, sort_keys=True)[:-2] + ',\n "results": {\n' + rows + '\n }\n}\n'


def zig_version(zig: str) -> str:
    return subprocess.run([zig, 'version'], capture_output=True, text=True, check=True).stdout.strip()


def record(zig: str, which: str, relation: dict) -> tuple[Path, dict]:
    target = WASM if which == 'wasm32' else native_target()
    version = zig_version(zig)
    if target not in relation['matrix'].get(version, []):
        raise ValueError(f'{target} is not declared for Zig {version} in the relation matrix')
    calls = cases(relation)
    with tempfile.TemporaryDirectory(prefix='air2lean-wasm-corr-') as tmp:
        binary = build(zig, relation, target, Path(tmp))
        results = observe_wasm(binary, calls) if target == WASM else observe_native(binary, calls)
    data = {'schema': 1, 'zig_version': version, 'target': target, 'optimize': relation['optimize'],
            'compiler_sha256': file_sha256(Path(zig).resolve()), 'sources_sha256': sources(relation),
            'cases_sha256': digest(calls), 'results': results}
    return RECORDS / version / f'{target}.json', data


# ------------------------------------------------------------------------------ the relation

def is_nan(bits: int, fmt: str) -> bool:
    width, exp = FORMATS[fmt]
    frac = width - 1 - exp
    return (bits >> frac) & ((1 << exp) - 1) == (1 << exp) - 1 and bits & ((1 << frac) - 1) != 0


def ordered(bits: int, fmt: str) -> int:
    """The float's position on the integer line, for ulp distances: -0 is one below +0."""
    width = FORMATS[fmt][0]
    sign = 1 << (width - 1)
    bits &= (1 << width) - 1
    return -(bits & (sign - 1)) - 1 if bits & sign else bits


def expect_env(args: list[int], bits: int, zig: int = 17) -> dict:
    """`zig` is the minor version (0.17.0: 17)."""
    env = {'bits': bits, 'zig': zig, 'NONE': MASK64, 'TRAP': TRAP}
    env.update(zip('abc', args))
    return env


def minor(version: str) -> int:
    return int(version.split('.')[1])


def illegal(entry: dict, args: list[int], zig: int) -> bool:
    """The case is illegal behaviour that the version's safe mode does not check (the model's
    `.illegal`): any observation is allowed, and the pair is not compared."""
    return 'illegal' in entry and bool(evaluate(entry['illegal'], expect_env(args, 0, zig)))


def relate(entry: dict, args: list[int], native, wasm, bits: dict) -> str | None:
    """None if the pair is related, else the reason."""
    cls = entry['class']
    if cls == 'exact':
        return None if native == wasm else f'exact: native {native} != wasm32 {wasm}'
    if cls == 'tolerated':
        if TRAP in (native, wasm):
            return None if native == wasm else f'tolerated: a trap pairs with {native if wasm == TRAP else wasm}'
        fmt = entry['format']
        if is_nan(native, fmt) and is_nan(wasm, fmt):
            return None
        if is_nan(native, fmt) or is_nan(wasm, fmt):
            return f'tolerated: only one side is NaN ({native:#x}, {wasm:#x})'
        distance = abs(ordered(native, fmt) - ordered(wasm, fmt))
        return None if distance <= entry['ulp'] else f'tolerated: {distance} ulp > {entry["ulp"]} ({native:#x}, {wasm:#x})'
    for side, value in (('native', native), ('wasm32', wasm)):
        want = evaluate(entry['expect'], expect_env(args, bits[side]))
        want = want if want == TRAP else want & MASK64
        if value != want:
            return f'target-specific: {side} (bits {bits[side]}) observed {value}, the profile model gives {want}'
    return None


def load_record(path: Path, relation: dict, calls: dict, root: Path = ROOT) -> dict:
    data = json.loads(path.read_text())
    if data.get('schema') != 1 or data.get('optimize') != relation['optimize']:
        raise ValueError(f'{path}: unsupported record or optimize mode')
    if data.get('sources_sha256') != sources(relation, root):
        raise ValueError(f'{path}: stale record: the kernel sources changed; re-record it')
    if data.get('cases_sha256') != digest(calls):
        raise ValueError(f'{path}: stale record: the generated cases changed; re-record it')
    results = data.get('results')
    if not isinstance(results, dict) or set(results) != set(calls) or any(
            not isinstance(results[k], list) or len(results[k]) != len(calls[k]) or
            any(r != TRAP and (type(r) is not int or not 0 <= r <= MASK64) for r in results[k]) for k in calls):
        raise ValueError(f'{path}: results do not match the cases (one word or "trap" per case)')
    return data


# ------------------------------------------------------------------------------ claims

PROFILE_RE = re.compile(r'^-- air2lean-profile: (\{.*\})$', re.M)


def theorem_text(text: str, name: str) -> str | None:
    """The statement of `theorem name` (up to its `:=`)."""
    short = name.rsplit('.', 1)[-1]
    match = re.search(rf'^theorem {re.escape(short)}\b(.*?):=', text, re.M | re.S)
    return match.group(1) if match else None


def generated_targets(proof: Path, root: Path) -> dict[str, str]:
    """Namespace -> recorded `arch-os` of each generated module the proof file imports."""
    found = {}
    for module in re.findall(r'^import (\S+\.Gen)$', proof.read_text(), re.M):
        path = proof.parent.parent / Path(*module.split('.')).with_suffix('.lean')
        if not path.is_file():
            continue
        text = path.read_text()
        header = PROFILE_RE.search(text)
        namespace = re.search(r'^namespace (\S+)$', text, re.M)
        if header and namespace:
            triple = json.loads(header.group(1))['profile']['target_triple']
            arch, os_ = triple.split('-')[:2]
            found[namespace.group(1)] = f'{arch}-{os_.split(".")[0]}'
    return found


def check_claims(relation: dict, root: Path = ROOT) -> list[str]:
    """Each claim binds one kernel on one target to a theorem whose statement is about a
    generated module recorded for that target (arch and OS). A theorem about another target's
    module is refused: proofs are per profile, never relabeled."""
    errors = []
    for claim in relation['claims']:
        where = f'claim {claim.get("kernel")} on {claim.get("target")}'
        if claim.get('kernel') not in relation['kernels'] or claim.get('target') not in relation['targets']:
            errors.append(f'{where}: unknown kernel or target')
            continue
        proof = root / claim['file']
        statement = theorem_text(proof.read_text(), claim['theorem']) if proof.is_file() else None
        if statement is None:
            errors.append(f'{where}: theorem {claim["theorem"]} not found in {claim["file"]}')
            continue
        targets = generated_targets(proof, root)
        enclosing = re.findall(r'^namespace (\S+)$', proof.read_text(), re.M)
        cited = set()
        for token in re.findall(r'[A-Za-z_][\w.]*', statement):
            for namespace, target in targets.items():
                names = [token] + [f'{e}.{token}' for e in enclosing] + \
                        [f'{e.rsplit(".", 1)[0]}.{token}' for e in enclosing if '.' in e]
                if any(n.startswith(namespace + '.') for n in names):
                    cited.add(target)
        want = relation['targets'][claim['target']]['model_target']
        if not cited:
            errors.append(f'{where}: {claim["theorem"]} states nothing about a generated module')
        elif cited != {want}:
            errors.append(f'{where}: {claim["theorem"]} is about {", ".join(sorted(cited))}, not {want}; '
                          'a theorem is never relabeled to another target')
    return errors


# ------------------------------------------------------------------------------ check

def check(relation: dict, root: Path = ROOT, records: Path = RECORDS) -> tuple[list[str], dict]:
    errors = validate(relation, root) + check_claims(relation, root)
    if errors:
        return errors, {}
    calls = cases(relation)
    summary = {}
    for version, targets in sorted(relation['matrix'].items()):
        loaded = {}
        for target in targets:
            path = records / version / f'{target}.json'
            if not path.is_file():
                errors.append(f'missing record {version}/{target}.json (declared in the matrix)')
                continue
            try:
                loaded[target] = load_record(path, relation, calls, root)
            except ValueError as error:
                errors.append(str(error))
                continue
            if loaded[target]['zig_version'] != version or loaded[target]['target'] != target:
                errors.append(f'{path}: records Zig {loaded[target]["zig_version"]} on {loaded[target]["target"]}')
        if WASM not in loaded:
            continue
        for target in sorted(set(loaded) - {WASM}):
            bits = {'native': relation['targets'][target]['pointer_bits'],
                    'wasm32': relation['targets'][WASM]['pointer_bits']}
            counts = {cls: 0 for cls in (*CLASSES, 'illegal')}
            for name, rows in calls.items():
                entry = relation['kernels'][name]
                for i, args in enumerate(rows):
                    if illegal(entry, args, minor(version)):
                        counts['illegal'] += 1
                        continue
                    reason = relate(entry, args, loaded[target]['results'][name][i],
                                    loaded[WASM]['results'][name][i], bits)
                    if reason:
                        errors.append(f'{version} {target}/{WASM} {name}{tuple(args)}: {reason}')
                    else:
                        counts[entry['class']] += 1
            summary[f'{version} {target}/{WASM}'] = counts
    return errors, summary


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    rec = sub.add_parser('record', help='build and observe one target')
    rec.add_argument('--zig', required=True)
    rec.add_argument('--target', choices=('native', 'wasm32'), required=True)
    rec.add_argument('--verify', action='store_true', help='compare with the committed record instead of writing')
    sub.add_parser('check', help='check the relation on every committed record pair')
    args = parser.parse_args(argv)
    relation = load_relation()
    if args.command == 'record':
        errors = validate(relation)
        if errors:
            print('\n'.join(errors), file=sys.stderr)
            return 1
        path, data = record(args.zig, args.target, relation)
        if args.verify:
            committed = json.loads(path.read_text()) if path.is_file() else None
            same = committed is not None and {k: v for k, v in committed.items() if k != 'compiler_sha256'} == \
                {k: v for k, v in data.items() if k != 'compiler_sha256'}
            print(f'{path.relative_to(ROOT)}: {"matches" if same else "DIFFERS from"} the fresh observation')
            return 0 if same else 1
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(dump_record(data))
        print(f'wrote {path.relative_to(ROOT)}')
        return 0
    errors, summary = check(relation)
    for pair, counts in summary.items():
        print(f'{pair}: ' + ', '.join(f'{n} {cls}' for cls, n in counts.items()))
    if errors:
        print('\n'.join(errors[:50]), file=sys.stderr)
        if len(errors) > 50:
            print(f'... and {len(errors) - 50} more', file=sys.stderr)
        return 1
    print('native/wasm32 correspondence relation holds on every recorded pair')
    return 0


if __name__ == '__main__':
    sys.exit(main())
