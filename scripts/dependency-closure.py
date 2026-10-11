#!/usr/bin/env python3
"""Dependency closure over exported AIR (I02): classify every required dependency.

Starting from root functions, follow direct calls, comptime function arguments of
non-exported generic instances (spawn workers), function values, qualified indirect
targets (address-taken functions whose function type matches an indirect callee, as
`Air2Lean/Memory.lean` `fnRefs`) and referenced globals. Each target is one of:

* ``exported``: its AIR is in the supplied set (globals: embedded in the referencing AIR);
* ``modelled``: a model boundary (built-in std model qualified for the Zig version, a
  project model-registry binding, a recognized panic handler, an extern global's
  initial-state parameter);
* ``missing``: a function the translator needs whose AIR was not exported; the exact
  fully qualified name and the ``ZIG_AIR_JSON_FILTER`` prefix that would include it;
* ``unresolvable``: a boundary no re-export can close (runtime function pointer with
  no qualified target, rejected std model, unmodelled noreturn callee, thread-local
  or unresolved global), with the exact function, instruction and reason.

The tool reads AIR only; it never runs Zig, Lean or the translator. Std model rows are
read from the single table in ``Air2Lean/StdModels.lean``.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import shlex
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 1
KIND = 'air2lean-dependency-closure'
VERSIONS = ('0.14.1', '0.15.2', '0.16.0')
# `Air2Lean/StdModels.lean`: a row qualifies for exactly the Zig versions of its reviewed std
# sources (`StdReview`): a `review "file" [(version, sha256), ...]` helper, `allocatorZig`
# (optionally restricted to a version list) or `only [versions] helper`.
OSES = ('linux', 'darwin')
IDENTITY_MARKER = re.compile(r'__(anon|enum|opaque|union|struct)_[0-9]+')
# A compiler identity number, raw or normalized (`__anon_N`): not stable across exports.
PREFIX_STOP = re.compile(r'__(?:anon|enum|opaque|union|struct)_(?:[0-9]+|N)')
# Air2Lean/Air/Op.lean `panicErrorFor?`: the handlers the emitter maps to a typed error.
PANIC_PREFIX = "debug.FullPanic((function 'defaultPanic'))."
PANIC_HANDLERS = frozenset(
    'integerOverflow integerOutOfBounds integerPartOutOfBounds shlOverflow shrOverflow outOfBounds '
    'divideByZero reachedUnreachable exactDivisionRemainder unwrapNull unwrapError forLenMismatch '
    'invalidEnumValue inactiveUnionField corruptSwitch call sentinelMismatch copyLenMismatch '
    'memcpyAlias castToNull incorrectAlignment startGreaterThanEnd'.split())
MODEL_ROW = re.compile(r'^  (allocModel|threadModel) "([^"\n]+)" \.\w+ #\[[^\]]*\]( [^\n]*?)?,?$', re.M)
ZIG_VERSION = re.compile(r'\.v(\d+)_(\d+)_(\d+)\b')
REVIEW_HELPER = re.compile(r'^private def (\w+)(?: \([^)]*\))? : Array StdReview :=\s*review "[^"]+"\s*(?:<\|\s*)?\[(.*?)\]',
                           re.M | re.S)
# Zig 0.17.0 names a generic instance `<fn>__func_<n>` (`Air2Lean/Air/Anon.lean` `funcInstances017`).
FUNC_017 = re.compile(r'__func_([0-9])')
REJECTED_ROW = re.compile(r'symbol := "([^"\n]+)",\s*kind := \.rejected "([^"\n]*)"')
# `Air2Lean/StdModels.lean`'s `asyncReason symbol reason` (C08 futures).
ASYNC_REJECTED_ROW = re.compile(
    r'symbol := "([^"\n]+)",\s*kind := \.rejected \(asyncReason "([^"\n]+)" "([^"\n]*)"\)')


class Invalid(ValueError):
    pass


def instance_base(name):
    """`Air2Lean/StdModels.lean` `stdModelBase`: an instance `<fn>__anon_<n>` names `<fn>`, and a
    method of an instantiated generic type (`Io.Future(u32).await`) names its generic method."""
    base = name.split('__anon_')[0]
    for generic in ('Io.Future', 'Io.Select'):
        parts = base.split(').')
        if base.startswith(generic + '(') and len(parts) >= 2:
            return f'{generic}.{parts[-1]}'
    return base


def filter_prefix(name):
    """Export filter prefix for `name`: everything before its first compiler identity number."""
    match = PREFIX_STOP.search(name)
    return name[:match.start()] if match else name


def normalized(name):
    return IDENTITY_MARKER.sub(r'__\1_N', name)


def zig_versions(text):
    """The `ZigVersion` constructors (`.v0_16_0`) in `text`, spelled as versions (`0.16.0`)."""
    return tuple('.'.join(v) for v in ZIG_VERSION.findall(text))


def std_models(text=None):
    """Rows of `stdModels`: symbol -> (status, zig versions, rejection reason)."""
    if text is None:
        text = (ROOT / 'Air2Lean/StdModels.lean').read_text(encoding='utf-8')
    start = text.index('def stdModels')
    end = text.find('\n\n', start)
    table = text[start:] if end < 0 else text[start:end]
    helpers = {name: zig_versions(body) for name, body in REVIEW_HELPER.findall(text)}

    def reviewed(kind, expr):
        expr = (expr or '').strip()
        if expr.startswith('(') and expr.endswith(')'):
            expr = expr[1:-1].strip()
        if not expr:
            if kind != 'allocModel':
                raise Invalid('Air2Lean/StdModels.lean: a thread model row without reviewed sources')
            return helpers['allocatorZig']
        m = re.fullmatch(r'(?:only (\[[^\]]*\]) )?(\w+)(?: (\[[^\]]*\]))?', expr)
        if not m or m.group(2) not in helpers:
            raise Invalid('Air2Lean/StdModels.lean: unreadable reviewed sources ' + expr)
        versions = helpers[m.group(2)]
        for restrict in (m.group(1), m.group(3)):
            if restrict:
                keep = zig_versions(restrict)
                versions = tuple(v for v in versions if v in keep)
        return versions
    models = {}
    for kind, symbol, expr in MODEL_ROW.findall(table):
        models[symbol] = ('modelled', reviewed(kind, expr), None)
    for symbol, reason in REJECTED_ROW.findall(table):
        models[symbol] = ('rejected', (), reason)
    for symbol, named, reason in ASYNC_REJECTED_ROW.findall(table):
        models[symbol] = ('rejected', (), f'{named} is not a qualified async API: {reason} (docs/futures.md)')
    rows = len(re.findall(r'^  (?:allocModel|threadModel)\b', table, re.M)) + table.count('kind := .rejected')
    if not models or rows != len(models):
        raise Invalid('Air2Lean/StdModels.lean table has rows this reader cannot parse')
    return models


def panic_handler(name):
    if name == 'debug.defaultPanic':
        return True
    if not name.startswith(PANIC_PREFIX):
        return False
    return instance_base(name.rsplit('.', 1)[-1]) in PANIC_HANDLERS


def fn_type(types, ty):
    """The function type name of a pointer-to-function type id, else None (`calleeFnTy?`)."""
    entry = types[ty] if isinstance(ty, int) and 0 <= ty < len(types) else None
    if not isinstance(entry, dict) or entry.get('k') != 'ptr':
        return None
    child = entry.get('child')
    child = types[child] if isinstance(child, int) and 0 <= child < len(types) else None
    if isinstance(child, dict) and child.get('k') == 'other' and str(child.get('name', '')).startswith('fn ('):
        return child['name']
    return None


def scan(air):
    """References of one AIR function: calls, function values, indirect calls, globals."""
    if not isinstance(air, dict) or not isinstance(air.get('name'), str) or not isinstance(air.get('body'), list):
        raise Invalid('AIR must be an object with a function name and body')
    if air.get('zig_version') == '0.17.0':
        air = json.loads(FUNC_017.sub(r'__anon_\1', json.dumps(air)))
    types = air.get('types') if isinstance(air.get('types'), list) else []
    insts, calls, values, indirect = {}, [], [], []

    def refs(node, inst, out):
        stack = [node]
        while stack:
            item = stack.pop()
            if isinstance(item, list):
                stack.extend(reversed(item))
            elif isinstance(item, dict):
                if isinstance(item.get('func'), str):
                    out.append((item['func'], inst))
                stack.extend(reversed(list(item.values())))

    stack = [air['body']]
    while stack:
        item = stack.pop()
        if isinstance(item, list):
            stack.extend(reversed(item))
            continue
        if not isinstance(item, dict) or 'tag' not in item:
            continue
        iid = item.get('id')
        insts[iid] = item.get('ty')
        callee = item.get('callee') if str(item['tag']).startswith('call') else None
        if isinstance(callee, dict) and isinstance(callee.get('func'), str):
            calls.append({'target': callee['func'], 'instruction': iid, 'noreturn': callee.get('noreturn') is True,
                          'comptime_fn': callee.get('comptime_fn')})
        elif isinstance(callee, dict) and 'inst' in callee:
            indirect.append({'instruction': iid, 'fn_type': None, 'operand': callee['inst']})
        elif isinstance(callee, dict) and isinstance(callee.get('ptr'), dict):
            # L11: a constant callee address (`ptrConst`) dispatches over the same table.
            indirect.append({'instruction': iid, 'fn_type': fn_type(types, callee.get('ty'))})
        for key, value in item.items():
            if key in ('callee', 'id', 'tag', 'ty'):
                continue
            if key in ('body', 'then', 'else'):
                stack.append(value)
            elif key == 'cases' and isinstance(value, list):
                for case in value:
                    if isinstance(case, dict):
                        refs([case.get('items'), case.get('ranges')], iid, values)
                        stack.append(case.get('body'))
            else:
                refs(value, iid, values)
    for site in indirect:
        if 'operand' in site:
            site['fn_type'] = fn_type(types, insts.get(site.pop('operand')))
    globals_ = []
    for index, entry in enumerate(air.get('globals') or []):
        if not isinstance(entry, dict):
            raise Invalid('malformed globals entry')
        init = entry.get('init')
        inner = []
        refs(init, None, inner)
        gty = types[entry['ty']] if isinstance(entry.get('ty'), int) and 0 <= entry['ty'] < len(types) else None
        top = init.get('func') if isinstance(init, dict) and isinstance(init.get('func'), str) else None
        globals_.append({'index': index, 'name': entry.get('name'), 'extern': entry.get('extern') is True,
                         'threadlocal': entry.get('threadlocal') is True, 'has_init': 'init' in entry,
                         'functions': [name for name, _ in inner],
                         # Memory.lean fnRefs: a global whose initial value is a function, typed `fn (...)`.
                         'fn_ref': (gty['name'], top) if top and isinstance(gty, dict) and gty.get('k') == 'other'
                                   and str(gty.get('name', '')).startswith('fn (') else None})
    return {'name': air['name'], 'zig_version': air.get('zig_version'), 'calls': calls,
            'values': values, 'indirect': indirect, 'globals': globals_}


class Closure:
    """Breadth-first closure over a function index keyed by `key(name)`."""

    def __init__(self, functions, zig_version, models=None, registry=(), key=lambda name: name):
        self.functions = functions
        self.version = zig_version
        self.models = std_models() if models is None else models
        self.registry = set(registry)
        self.key = key
        self.nodes = {}
        self.parent = {}
        self.boundaries = []
        self.indirect = []
        self.globals = {}

    def chain(self, name):
        path = []
        while name is not None:
            path.append(name)
            name = self.parent.get(name)
        return path[::-1]

    def std(self, name):
        return self.models.get(instance_base(name))

    def classify(self, name, panic=False):
        if panic:
            # Emitted as a typed error (`panicErrorFor?`); a handler body is never translated.
            return 'modelled', 'panic_handler', None
        model = self.std(name)
        if model is not None:
            status, versions, reason = model
            if status == 'rejected':
                return 'unresolvable', 'rejected_std_model', reason
            if self.version not in versions:
                return 'unresolvable', 'std_model_not_qualified', \
                    f'std model {instance_base(name)} is qualified only for Zig {", ".join(versions)}'
            if self.key(name) in self.functions:
                return 'unresolvable', 'std_model_air_conflict', \
                    'AIR exported for a built-in std model name; the translator rejects it (narrow the filter)'
            return 'modelled', 'std_model', None
        if name in self.registry:
            return 'modelled', 'registry_binding', None
        if self.key(name) in self.functions:
            return 'exported', 'air', None
        return 'missing', 'no_air', None

    def visit(self, caller, name, edge, instruction, queue, panic=False):
        name = self.key(name)
        if name not in self.nodes:
            cls, kind, reason = self.classify(name, panic)
            self.nodes[name] = {'name': name, 'class': cls, 'kind': kind, 'reason': reason, 'references': []}
            if caller is not None:
                self.parent[name] = caller
            if cls == 'exported':
                queue.append(name)
        refs = self.nodes[name]['references']
        if caller is not None and len(refs) < 16:
            ref = {'from': caller, 'edge': edge, 'instruction': instruction}
            if ref not in refs:
                refs.append(ref)
        return self.nodes[name]

    def boundary(self, function, instruction, cls, kind, target, reason):
        self.boundaries.append({'function': function, 'instruction': instruction, 'class': cls, 'kind': kind,
                                'target': target, 'reason': reason, 'chain': self.chain(function)})

    def run(self, roots):
        queue = []
        for root in roots:
            node = self.visit(None, root, 'root', None, queue)
            if node['class'] != 'exported':
                node['reason'] = node['reason'] or 'root function absent from the supplied AIR'
        cursor = 0
        while cursor < len(queue):
            caller = queue[cursor]
            cursor += 1
            info = self.functions[self.key(caller)]
            for call in info['calls']:
                target = call['target']
                if call['noreturn']:
                    if panic_handler(target):
                        self.visit(caller, target, 'panic_call', call['instruction'], queue, panic=True)
                    else:
                        self.boundary(caller, call['instruction'], 'unresolvable', 'unmodelled_noreturn_callee', target,
                                      'a noreturn callee other than a recognized panic handler is emitted as a panic')
                    continue
                node = self.visit(caller, target, 'direct_call', call['instruction'], queue)
                worker = call['comptime_fn']
                # The body of a non-exported generic instance is unavailable: its function-valued
                # comptime argument (a spawn worker) is a dependency of the call itself.
                if isinstance(worker, str) and node['class'] != 'exported':
                    self.visit(caller, worker, 'comptime_function_argument', call['instruction'], queue)
            for target, instruction in info['values']:
                self.visit(caller, target, 'function_value', instruction, queue)
            for entry in info['globals']:
                label = entry['name'] or f'{caller}#global{entry["index"]}'
                if entry['threadlocal'] and entry['extern']:
                    # C02 models defined `threadlocal` storage only (`docs/generated-code.md`
                    # §Thread-local storage); the translator checks its type.
                    cls, kind, reason = 'unresolvable', 'threadlocal_global', \
                        'extern thread-local storage is outside the model'
                elif entry['extern']:
                    cls, kind, reason = 'modelled', 'extern_initial_state', 'external storage is an explicit ExternInit parameter'
                elif not entry['has_init']:
                    cls, kind, reason = 'unresolvable', 'unresolved_global_initializer', 'the exporter wrote no initial value'
                else:
                    cls, kind, reason = 'exported', 'embedded_in_air', None
                record = self.globals.setdefault(label, {'name': label, 'class': cls, 'kind': kind,
                                                         'reason': reason, 'referenced_by': []})
                if caller not in record['referenced_by']:
                    record['referenced_by'].append(caller)
                if cls == 'unresolvable':
                    self.boundary(caller, None, cls, kind, label, reason)
                for target in entry['functions']:
                    self.visit(caller, target, 'global_function_reference', None, queue)
        # Qualified indirect targets: address-taken functions of the closure with the callee's type.
        refs = {}
        for name in queue:
            for entry in self.functions[self.key(name)]['globals']:
                if entry['fn_ref']:
                    refs.setdefault(entry['fn_ref'][0], set()).add(self.key(entry['fn_ref'][1]))
        for name in queue:
            for site in self.functions[self.key(name)]['indirect']:
                targets = sorted(refs.get(site['fn_type'], ())) if site['fn_type'] else []
                record = {'function': name, 'instruction': site['instruction'], 'fn_type': site['fn_type'],
                          'targets': [{'name': t, 'class': self.nodes[t]['class']} for t in targets]}
                if site['fn_type'] is None:
                    record['class'] = 'unresolvable'
                    self.boundary(name, site['instruction'], 'unresolvable', 'non_function_pointer_callee', None,
                                  'indirect callee is not a function pointer')
                elif not targets:
                    record['class'] = 'unresolvable'
                    self.boundary(name, site['instruction'], 'unresolvable', 'runtime_function_pointer', site['fn_type'],
                                  'no address-taken function of this type in the closure; the target is a runtime value')
                else:
                    record['class'] = 'qualified'
                self.indirect.append(record)
        for name, node in self.nodes.items():
            node['chain'] = self.chain(name)
            if node['class'] == 'unresolvable':
                self.boundary(self.parent.get(name, name), None, 'unresolvable', node['kind'], name, node['reason'])
        return self


def filter_prefixes(names, base_prefixes, models):
    """Prefixes covering `names`; a generic instance is covered by its base name."""
    prefixes = sorted({p for p in base_prefixes if p} | {filter_prefix(n) for n in names})
    reduced = [p for p in prefixes if not any(q != p and p.startswith(q) for q in prefixes)]
    collisions = sorted({p for p in reduced for symbol in models if symbol.startswith(p)})
    return reduced, collisions


def covered(name, prefixes):
    return any(name.startswith(p) for p in prefixes)


def report(closure, roots, base_prefixes, existing=None, source=None):
    nodes = sorted(closure.nodes.values(), key=lambda n: n['name'])
    exported = [n['name'] for n in nodes if n['class'] == 'exported']
    missing = [n for n in nodes if n['class'] == 'missing']
    prefixes, collisions = filter_prefixes([n['name'] for n in nodes if n['class'] in ('exported', 'missing')],
                                           base_prefixes, closure.models)
    unresolvable = sorted(closure.boundaries, key=lambda b: (b['function'], str(b['instruction']), b['kind'], str(b['target'])))
    result = {
        'schema': SCHEMA, 'kind': KIND, 'zig_version': closure.version, 'roots': list(roots),
        'status': 'closed' if not missing and not unresolvable else 'incomplete',
        'counts': {c: sum(n['class'] == c for n in nodes) for c in ('exported', 'modelled', 'missing', 'unresolvable')},
        'functions': nodes,
        'globals': sorted(closure.globals.values(), key=lambda g: g['name']),
        'indirect_calls': closure.indirect,
        'missing': [{'fqn': n['name'], 'filter_prefix': filter_prefix(n['name']), 'chain': n['chain'],
                     'references': n['references']} for n in missing],
        'unresolvable': unresolvable,
        'exported_outside_closure': sorted(set(closure.functions) - set(closure.nodes)),
        'model_boundaries': [{'name': n['name'], 'kind': n['kind']} for n in nodes if n['class'] == 'modelled'] +
                            [{'name': g['name'], 'kind': g['kind']} for g in closure.globals.values() if g['class'] == 'modelled'],
        'filter': {'prefixes': prefixes, 'value': ','.join(prefixes), 'std_model_collisions': collisions},
        'scope': 'exported AIR only: calls inside missing functions are unknown until they are exported; '
                 'indirect targets are the address-taken functions of the closure (fnRefs)',
    }
    if existing is not None:
        uncovered = sorted(n['name'] for n in nodes if n['class'] in ('exported', 'missing')
                           and not covered(n['name'], existing))
        result['filter']['existing'] = list(existing)
        result['filter']['existing_uncovered'] = uncovered
    if source is not None:
        result['reexport'] = ' '.join([
            'ZIG_AIR_JSON_DIR="$AIR_DIR"', 'ZIG_AIR_JSON_FILTER=' + shlex.quote(result['filter']['value']),
            f'zig-air-{closure.version}/bin/zig', 'build-obj', '-fno-emit-bin', '-OReleaseSafe',
            '-fno-error-tracing', shlex.quote(source)])
    return result


def load_registry(path):
    if path is None:
        return []
    data = json.loads(Path(path).read_text(encoding='utf-8'))
    if not isinstance(data, dict) or data.get('schema') != 1 or not isinstance(data.get('models'), list):
        raise Invalid('model registry must be {"schema": 1, "models": [...]}')
    return [m['symbol'] for m in data['models'] if isinstance(m, dict) and isinstance(m.get('symbol'), str)]


def _project():
    spec = importlib.util.spec_from_file_location('project', Path(__file__).resolve().with_name('project.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def manifest_closure(path, registry=None, models=None, project=None):
    project = project or _project()
    manifest, _, limits = project.load_manifest(path)
    bindings = load_registry(registry)
    out = {'schema': SCHEMA, 'kind': KIND + '-project', 'roots': [], 'status': 'closed'}
    for root in manifest['roots']:
        functions, errors, versions = {}, [], set()
        for name in root['air']:
            try:
                air = project.bounded_json(project.read_bounded(project.path_under(path.parent, name),
                                                                limits['max_file_bytes']), limits)
                info = scan(air)
            except (OSError, ValueError, UnicodeError) as error:
                errors.append({'path': name, 'message': str(error)})
                continue
            if info['name'] in functions:
                errors.append({'path': name, 'message': f'duplicate AIR function {info["name"]}'})
            functions[info['name']] = info
            versions.add(info['zig_version'])
        version = versions.pop() if len(versions) == 1 else None
        if len(versions) or version is None:
            errors.append({'path': None, 'message': 'AIR files do not share one zig_version'})
        closure = Closure(functions, version, models, bindings).run([root['function']])
        result = report(closure, [root['function']], [root['prefix']], source=manifest['source_closure'][0])
        result.update(id=root['id'], input_errors=errors)
        if errors or result['status'] != 'closed':
            out['status'] = 'incomplete'
        out['roots'].append(result)
    return out


def golden_sets(example, base=ROOT):
    """Effective golden AIR per (Zig version, host OS), with the check.sh overlay order."""
    versions_file = base / 'examples' / example / 'zig-versions'
    versions = versions_file.read_text().split() if versions_file.is_file() else list(VERSIONS)
    for version in versions:
        dirs = [base / 'tests/golden' / example / 'air', base / 'tests/golden' / version / example / 'air']
        if not any(d.is_dir() for d in dirs):
            continue
        # Hosts without an OS overlay use the shared directories alone.
        oses = [None] + [os for os in OSES if (base / 'tests/golden' / version / example / f'air-{os}').is_dir()]
        for os in oses:
            overlay = dirs + ([base / 'tests/golden' / version / example / f'air-{os}'] if os else [])
            functions = {}
            for directory in overlay:
                if not directory.is_dir():
                    continue
                layer = {}
                for file in sorted(directory.glob('*.json')):
                    info = scan(json.loads(file.read_text(encoding='utf-8')))
                    info['file'] = str(file.relative_to(base))
                    layer.setdefault(normalized(info['name']), []).append(info)
                # A later directory replaces every instance of a normalized name.
                functions.update(layer)
            yield version, os, functions


def merged(groups):
    """Normalized name -> one scan merging every instance of a generic function."""
    fields = ('calls', 'values', 'indirect', 'globals')
    return {key: dict({'name': key}, **{f: [item for info in infos for item in info[f]] for f in fields})
            for key, infos in groups.items()}


def golden_closure(examples=None, base=ROOT, models=None):
    models = std_models((base / 'Air2Lean/StdModels.lean').read_text(encoding='utf-8')) if models is None else models
    names = examples or sorted(p.name for p in (base / 'examples').iterdir() if p.is_dir())
    results = []
    for example in names:
        for version, os, groups in golden_sets(example, base):
            # `scripts/check.sh`: examples/<ex>/filter, then examples/<ex>/filter-<version>.
            existing = [f'{example}.']
            for filter_file in (base / 'examples' / example / 'filter',
                                base / 'examples' / example / f'filter-{version}'):
                existing += filter_file.read_text().split() if filter_file.is_file() else []
            functions = merged(groups)
            roots = sorted(name for name in functions if name.startswith(f'{example}.'))
            closure = Closure(functions, version, models, (), normalized).run(roots)
            result = report(closure, roots, [f'{example}.'], existing,
                            source=f'examples/{example}/{example}.zig')
            result.update(example=example, host_os=os or 'other')
            results.append(result)
    status = 'closed' if all(r['status'] == 'closed' and not r['filter']['existing_uncovered'] for r in results) \
        else 'incomplete'
    return {'schema': SCHEMA, 'kind': KIND + '-goldens', 'status': status, 'examples': results}


def text_summary(result):
    lines = []
    for r in result.get('roots', result.get('examples', [])):
        label = r.get('id') or f"{r['example']} {r['zig_version']} {r['host_os']}"
        lines.append(f"{label}: {r['status']} " + ' '.join(f'{k}={v}' for k, v in r['counts'].items()))
        for m in r['missing']:
            lines.append(f"  missing {m['fqn']} (filter prefix {m['filter_prefix']}): {' -> '.join(m['chain'])}")
        for b in r['unresolvable']:
            lines.append(f"  unresolvable {b['kind']} {b['target']} at {b['function']} inst {b['instruction']}: {b['reason']}")
        for name in r['filter'].get('existing_uncovered', []):
            lines.append(f'  filter file does not cover {name}')
        if r['filter']['std_model_collisions']:
            lines.append(f"  filter prefixes collide with std models: {', '.join(r['filter']['std_model_collisions'])}")
        if r['status'] != 'closed' and 'reexport' in r:
            lines.append(f"  re-export: {r['reexport']}")
    lines.append(f"status: {result['status']}")
    return '\n'.join(lines) + '\n'


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    sub = parser.add_subparsers(dest='command', required=True)
    m = sub.add_parser('manifest', help='closure of every project manifest root over its AIR list')
    m.add_argument('manifest', type=Path)
    m.add_argument('--model-registry', type=Path)
    g = sub.add_parser('goldens', help='closure of every example over its committed golden AIR')
    g.add_argument('--examples', help='comma-separated example names (default: all)')
    for p in (m, g):
        p.add_argument('--format', choices=('json', 'text'), default='json')
    args = parser.parse_args(argv)
    try:
        if args.command == 'manifest':
            result = manifest_closure(args.manifest.resolve(), args.model_registry)
        else:
            result = golden_closure(args.examples.split(',') if args.examples else None)
    except (OSError, ValueError) as error:
        print(json.dumps({'schema': SCHEMA, 'kind': KIND, 'error': str(error)}), file=sys.stderr)
        return 2
    print(text_summary(result) if args.format == 'text' else json.dumps(result, indent=2, sort_keys=True), end='' if args.format == 'text' else '\n')
    return 0 if result['status'] == 'closed' else 1


if __name__ == '__main__':
    sys.exit(main())
