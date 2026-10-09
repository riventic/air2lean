#!/usr/bin/env python3
"""I07 artifact manifest: chain source/AIR/Gen/patch/runtime/toolchain/profile/theorem identities.

A separate, explicitly versioned format (`air2lean-artifact-manifest-v1`); proof receipt schema 1
is unchanged. `check-manifest` recomputes every link and names exactly which one is stale. It never
runs Zig, Lake or Lean and does not authenticate anything. Also reachable as
`scripts/proof-receipt.py manifest|check-manifest`.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).absolute().parents[1]
_spec = importlib.util.spec_from_file_location('manifest_receipt', ROOT / 'scripts/proof-receipt.py')
receipt = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(receipt)
demand, fingerprint, read_file, parse_json = receipt.demand, receipt.fingerprint, receipt.read_file, receipt.parse_json
load, mapping, write_new, physical, tree = receipt.load, receipt.mapping, receipt.write_new, receipt.physical, receipt.tree
MAX_JSON, MAX_FILES = receipt.MAX_JSON, receipt.MAX_FILES

MANIFEST_FORMAT = 'air2lean-artifact-manifest-v1'
LINKS = ('source', 'compiler_patch', 'air', 'profile', 'translator', 'generated', 'runtime',
         'toolchain', 'proofs', 'theorems', 'receipt')
DIAGNOSIS = {
    'source': 'wrong source: the Zig source closure differs from the recorded export input',
    'compiler_patch': 'changed compiler patch: the AIR exporter/hook or pinned Zig release differs',
    'air': 'changed AIR: the exported AIR files differ (re-export, other compiler or other profile)',
    'profile': 'wrong profile: the target/build profile or Zig version differs from the recorded one',
    'translator': 'changed translator: Air2Lean or its generation/normalization scripts differ',
    'generated': 'edited or regenerated Gen.lean: generated Lean differs from the recorded output',
    'runtime': 'changed runtime semantics: ZigLean model files differ',
    'toolchain': 'changed toolchain/build configuration: lean-toolchain, lakefile or lake-manifest differs',
    'proofs': 'changed proof sources: theorem files differ from the recorded ones',
    'theorems': 'changed theorem inventory: theorem names differ from the recorded ones',
    'receipt': 'changed proof receipt: the bound receipt/audit evidence differs',
}
THEOREM = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*'
                     r'(?:theorem|lemma)\s+(«[^»]+»|[^\s:({\[⦃]+)')
SCOPE = re.compile(r'^\s*(?:(?:public|noncomputable)\s+)*(namespace|section|mutual|end)\b[ \t]*([^\s]*)')
TRANSLATOR = ('Air2Lean.lean', 'Air2Lean', 'scripts/check.sh', 'scripts/translate.sh',
              'scripts/normalize-generated.py', 'scripts/normalize-air.py')
RUNTIME = ('ZigLean.lean', 'ZigLean')
TOOLCHAIN = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
RECEIPT_FILES = ('receipt.json', 'plan.json', 'audit.json', 'after.json')


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False,
                      allow_nan=False).encode()


def digest_of(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def chain_step(previous, name, link_digest):
    return hashlib.sha256((previous + '\0' + name + '\0' + link_digest).encode()).hexdigest()


def git_at(root, *args):
    return subprocess.run(['git', '--literal-pathspecs', '-C', str(root), *args], check=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=10).stdout


def git_paths(root, *args):
    return sorted({p for p in git_at(root, *args).decode().split('\0') if p})


def label(root, path):
    path = Path(os.path.abspath(path))
    return path.relative_to(root).as_posix() if path.is_relative_to(root) else str(path)


def absolute(root, name):
    return Path(name) if Path(name).is_absolute() else root / name


def expand(root, names, suffix=None):
    """Tracked plus untracked-unignored repository files under each name; walked files elsewhere."""
    found = set()
    for name in names:
        path = Path(os.path.abspath(absolute(root, name)))
        if path.is_relative_to(root):
            listed = git_paths(root, 'ls-files', '-z', '--cached', '--others', '--exclude-standard',
                               '--', label(root, path))
            found.update(root / p for p in listed if (root / p).is_file() or (root / p).is_symlink())
            if not listed and (path.is_file() or path.is_symlink()):
                found.add(path)  # Ignored but explicitly named, e.g. a fresh export under .lake.
            elif not listed and path.is_dir():
                found.update(tree(path))
            demand(listed or path.exists(), 'missing artifact: ' + label(root, path))
        elif path.is_dir():
            found.update(tree(path))
        else:
            found.add(path)
    rows = sorted(found)
    if suffix is not None:
        rows = [p for p in rows if p.name.endswith(suffix)]
    demand(len(rows) <= MAX_FILES, 'link inventory exceeds bound')
    return rows


def file_identity(root, path):
    path = Path(os.path.abspath(path))
    demand(path.exists() or path.is_symlink(), 'missing artifact: ' + label(root, path))
    if path.is_symlink():
        target = Path(os.path.realpath(path))
        demand(target.is_relative_to(root) or not path.is_relative_to(root),
               'repository alias escapes repository: ' + label(root, path))
        row = fingerprint(target)
        return {'path': label(root, path), 'link': os.readlink(path), 'sha256': row['sha256'], 'bytes': row['bytes']}
    row = fingerprint(path)
    return {'path': label(root, path), 'sha256': row['sha256'], 'bytes': row['bytes']}


def link_record(root, files, value=None):
    body = {'files': [file_identity(root, p) for p in files], 'value': value}
    return dict(body, sha256=digest_of(body))


def default_inputs(root, example, zig_version):
    demand(isinstance(example, str) and re.fullmatch(r'[a-z][a-z0-9_]*', example), 'invalid example name')
    demand(isinstance(zig_version, str) and re.fullmatch(r'[0-9]+\.[0-9]+\.[0-9]+', zig_version),
           'invalid Zig version')
    module = example[:1].upper() + example[1:]
    proofs = sorted(label(root, p) for p in (root / 'Proofs' / module).glob('*.lean') if p.name != 'Gen.lean')
    if (root / 'Proofs' / (module + '.lean')).is_file():
        proofs.append('Proofs/' + module + '.lean')
    return {'example': example, 'zig_version': zig_version, 'sources': ['examples/' + example],
            'air_dir': 'tests/golden/%s/%s/air' % (zig_version, example),
            'generated': 'Proofs/%s/Gen.lean' % module, 'proofs': proofs,
            'audit': None, 'receipt': None}


def toml_pin(root, zig_version):
    import tomllib
    table = tomllib.loads(read_file(root / 'zig-patch/versions.toml', MAX_JSON).decode())
    entry = table.get(zig_version)
    demand(isinstance(entry, dict) and isinstance(entry.get('hook'), str),
           'zig-patch/versions.toml has no pin for Zig ' + str(zig_version))
    return {k: entry[k] for k in sorted(entry) if isinstance(entry[k], (str, int))}


def profile_value(root, inputs):
    """One validated target/build profile shared by every AIR file and any Gen.lean header."""
    normalize = receipt.helper('normalize-generated')
    air_files = expand(root, [inputs['air_dir']], '.json')
    demand(air_files, 'no AIR files in ' + inputs['air_dir'])
    distinct = {}
    for path in air_files:
        profile = normalize.profile_for_air(parse_json(read_file(path, MAX_JSON)))
        distinct[digest_of(profile)] = profile
    demand(len(distinct) == 1, 'AIR files carry %d different profiles' % len(distinct))
    profile = next(iter(distinct.values()))
    demand(profile['zig_version'] == inputs['zig_version'],
           'AIR zig_version %s differs from requested %s' % (profile['zig_version'], inputs['zig_version']))
    metadata, body = normalize.split_generated(read_file(absolute(root, inputs['generated']), MAX_JSON))
    demand(metadata is None or metadata['profile'] == profile,
           'Gen.lean profile header differs from the AIR profile')
    return {'zig_version': profile['zig_version'], 'profile': profile, 'profile_sha256': digest_of(profile),
            'generated_header': metadata,
            'scope': 'validated-header' if metadata else 'legacy-or-unannotated'}, body


def scan_theorems(root, files):
    """Source-level theorem names, qualified by enclosing namespaces. Not compiler-checked."""
    names = []
    for path in files:
        text = read_file(path, MAX_JSON).decode('utf-8')
        text = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), text, flags=re.S)
        scopes = []
        for line in text.splitlines():
            line = line.split('--', 1)[0]
            scope = SCOPE.match(line)
            if scope:
                kind, name = scope.groups()
                if kind != 'end':
                    scopes.append(name if kind == 'namespace' else '')
                elif scopes:
                    scopes.pop()
                continue
            match = THEOREM.match(line)
            if match:
                name = match.group(1)
                names.append(name[len('_root_.'):] if name.startswith('_root_.')
                             else '.'.join([s for s in scopes if s] + [name]))
    return sorted(names)


def proof_modules(root, inputs):
    return sorted(label(root, absolute(root, p))[:-len('.lean')].replace('/', '.') for p in inputs['proofs'])


def audit_theorems(root, inputs, audit_path):
    audit = load(audit_path)
    modules = set(proof_modules(root, inputs))
    theorems = audit.get('theorems')
    demand(isinstance(theorems, list) and all(isinstance(t, dict) for t in theorems),
           'audit has no theorem inventory')
    selected = [t for t in theorems if t.get('module') in modules]
    return {'status': audit.get('status'), 'names': sorted(t['name'] for t in selected),
            'not_allowed': sorted(t['name'] for t in selected if t.get('allowed') is not True)}


def patch_paths(version):
    return ['zig-patch/versions.toml', 'zig-patch/%s/hook.patch' % version, 'zig-patch/air-json',
            'zig-patch/build.sh', 'zig-patch/lock.sh']


def audit_input(inputs):
    if inputs['audit'] is None and inputs['receipt'] is not None:
        return str(Path(inputs['receipt']) / 'audit.json')
    return inputs['audit']


def link_scopes(inputs):
    """Every path named by a link, so provenance also sees deletions beneath it."""
    audit = audit_input(inputs)
    receipt_files = [] if inputs['receipt'] is None else [str(Path(inputs['receipt']) / n) for n in RECEIPT_FILES]
    return [*inputs['sources'], *patch_paths(inputs['zig_version']), inputs['air_dir'], *TRANSLATOR,
            inputs['generated'], *RUNTIME, *TOOLCHAIN, *inputs['proofs'],
            *([] if audit is None else [audit]), *receipt_files]


def compute_links(root, inputs):
    """Return {link: record or {'error': text}} for every link applicable to these inputs."""
    links, state = {}, {}

    def attempt(name, build):
        try:
            links[name] = build()
        except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
            links[name] = {'error': str(error)}

    def profile():
        value, state['body'] = profile_value(root, inputs)
        return link_record(root, [], value)

    def generated():
        path = absolute(root, inputs['generated'])
        body = state.get('body')
        if body is None:
            _, body = receipt.helper('normalize-generated').split_generated(read_file(path, MAX_JSON))
        return link_record(root, [path], {'body_sha256': hashlib.sha256(body).hexdigest()})

    proof_files = [absolute(root, p) for p in inputs['proofs']]
    audit_path = audit_input(inputs)

    def theorems():
        value = {'modules': proof_modules(root, inputs), 'source_scan': scan_theorems(root, proof_files),
                 'compiled_audit': None}
        if audit_path is None:
            return link_record(root, [], value)
        value['compiled_audit'] = audit_theorems(root, inputs, absolute(root, audit_path))
        return link_record(root, [absolute(root, audit_path)], value)

    version = inputs['zig_version']
    attempt('source', lambda: link_record(root, expand(root, inputs['sources'])))
    attempt('compiler_patch', lambda: link_record(root, expand(root, patch_paths(version)),
                                                  {'pin': toml_pin(root, version)}))
    attempt('air', lambda: link_record(root, expand(root, [inputs['air_dir']], '.json')))
    attempt('profile', profile)
    attempt('translator', lambda: link_record(root, expand(root, TRANSLATOR)))
    attempt('generated', generated)
    attempt('runtime', lambda: link_record(root, expand(root, RUNTIME)))
    attempt('toolchain', lambda: link_record(root, expand(root, TOOLCHAIN),
            {'lean_toolchain': read_file(root / 'lean-toolchain', 4096).decode().strip()}))
    attempt('proofs', lambda: link_record(root, proof_files))
    attempt('theorems', theorems)
    if inputs['receipt'] is not None:
        attempt('receipt', lambda: link_record(root, [Path(inputs['receipt']) / n for n in RECEIPT_FILES]))
    return links


def provenance(root, links, inputs):
    paths = sorted({row['path'] for record in links.values() for row in record.get('files', [])})
    inside = [p for p in paths if not Path(p).is_absolute()]
    scopes = sorted({label(root, absolute(root, s)) for s in link_scopes(inputs)})
    scopes = [s for s in scopes if not Path(s).is_absolute()]
    tracked_paths = set(git_paths(root, 'ls-files', '-z', '--', *scopes)) if scopes else set()
    # Diff the named scopes, not just hashed files, so deleted link files (staged or not) count.
    dirty = git_paths(root, 'diff', '--name-only', '--no-renames', '-z', 'HEAD', '--', *scopes) if scopes else []
    untracked = sorted(p for p in inside if p not in tracked_paths)
    return {'head': git_at(root, 'rev-parse', 'HEAD').decode().strip(),
            'tracked_dirty': bool(git_at(root, 'status', '--porcelain', '--untracked-files=no')),
            'modified_link_paths': dirty, 'untracked_link_paths': untracked,
            'external_link_paths': sorted(p for p in paths if Path(p).is_absolute()),
            'status': 'dirty' if dirty or untracked else 'clean'}


def seal_chain(links, inputs, provenance_record):
    """Chain every link, then bind the inputs and provenance so neither can be edited silently."""
    current = hashlib.sha256(MANIFEST_FORMAT.encode()).hexdigest()
    chain = []
    steps = [(name, links[name]['sha256']) for name in LINKS if name in links]
    steps.append(('inputs_provenance', digest_of({'inputs': inputs, 'provenance': provenance_record})))
    for name, link_digest in steps:
        current = chain_step(current, name, link_digest)
        chain.append({'link': name, 'sha256': link_digest, 'chain_sha256': current})
    return chain, current


def build_manifest(root, inputs):
    links = compute_links(root, inputs)
    broken = sorted('%s: %s' % (k, v['error']) for k, v in links.items() if 'error' in v)
    demand(not broken, 'cannot record manifest: ' + '; '.join(broken))
    record = provenance(root, links, inputs)
    chain, final = seal_chain(links, inputs, record)
    return {'format': MANIFEST_FORMAT, 'schema': 1, 'authentication': 'not_attested',
            'claim': 'byte identities of recorded inputs; no rebuild, proof check or source correspondence',
            'inputs': inputs, 'links': links, 'chain': chain, 'manifest_sha256': final,
            'provenance': record}


def manifest_integrity(manifest):
    demand(manifest.get('format') == MANIFEST_FORMAT and type(manifest.get('schema')) is int
           and manifest['schema'] == 1,
           'unsupported manifest format/schema (proof receipt schema 1 is checked with `verify`)')
    links = mapping(manifest.get('links'), 'manifest links')
    inputs = mapping(manifest.get('inputs'), 'manifest inputs')
    expected = set(LINKS) - ({'receipt'} if inputs.get('receipt') is None else set())
    demand(set(links) == expected, 'unknown or missing manifest link')
    for name, record in links.items():
        mapping(record, 'link ' + name)
        demand(record.get('sha256') == digest_of({'files': record.get('files'), 'value': record.get('value')}),
               'manifest link %s was edited after recording' % name)
    chain, final = seal_chain(links, inputs, mapping(manifest.get('provenance'), 'manifest provenance'))
    demand(manifest.get('chain') == chain and manifest.get('manifest_sha256') == final,
           'manifest chain was edited after recording')


def compare_link(name, recorded, current):
    result = {'recorded_sha256': recorded['sha256']}
    if 'error' in current:
        return dict(result, status='stale', diagnosis=DIAGNOSIS[name], error=current['error'])
    result['current_sha256'] = current['sha256']
    if current['sha256'] == recorded['sha256']:
        return dict(result, status='current')
    old = {r['path']: r for r in recorded['files']}
    new = {r['path']: r for r in current['files']}
    result.update(status='stale', diagnosis=DIAGNOSIS[name],
                  changed=sorted(p for p in old.keys() & new.keys() if old[p] != new[p]),
                  removed=sorted(old.keys() - new.keys()), added=sorted(new.keys() - old.keys()),
                  value_changed=recorded['value'] != current['value'])
    if name == 'theorems':
        before, after = set(recorded['value']['source_scan']), set(current['value']['source_scan'])
        result.update(theorems_added=sorted(after - before), theorems_removed=sorted(before - after))
    return result


def check_manifest(root, path, expect=(), allow_dirty=False, verify_receipt=False):
    report = {'format': MANIFEST_FORMAT, 'manifest': str(path), 'checking': 'not_rerun',
              'authentication': 'not_attested', 'problems': [], 'stale_links': []}
    manifest = load(path)
    try:
        manifest_integrity(manifest)
    except (ValueError, KeyError, TypeError) as error:
        return dict(report, status='invalid', problems=[str(error)])
    report['manifest_sha256'] = manifest['manifest_sha256']
    links = manifest['links']
    for item in expect:
        name, _, wanted = item.partition('=')
        if name == 'zig_version':
            got = links['profile']['value']['zig_version']
        elif name == 'profile':
            got = links['profile']['value']['profile_sha256']
        else:
            demand(name in links, 'unknown --expect link: ' + name)
            got = links[name]['sha256']
        if got != wanted:
            report['problems'].append('expected %s=%s but manifest records %s: proof is for another %s'
                                      % (name, wanted, got, name))
    current = compute_links(root, manifest['inputs'])
    report['links'] = {name: compare_link(name, links[name], current.get(name, {'error': 'link missing'}))
                       for name in LINKS if name in links}
    report['stale_links'] = [n for n, r in report['links'].items() if r['status'] != 'current']
    recorded = manifest['provenance']
    report['provenance'] = {'recorded': recorded}
    try:
        report['provenance']['current'] = provenance(root, {k: v for k, v in current.items() if 'error' not in v},
                                                 manifest['inputs'])
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report['provenance']['current'] = {'error': str(error)}
    if recorded.get('status') != 'clean' and not allow_dirty:
        report['problems'].append(
            'dirty-tree provenance: recorded at %s with modified %s and untracked %s link files; '
            'not reproducible from that revision (pass --allow-dirty to accept)'
            % (recorded.get('head'), recorded.get('modified_link_paths'), recorded.get('untracked_link_paths')))
    if 'receipt' in links and not allow_dirty:
        try:
            receipt.release_ready(load(Path(manifest['inputs']['receipt']) / 'receipt.json'))
        except (OSError, ValueError) as error:
            report['problems'].append('chained proof receipt: %s (pass --allow-dirty to accept)' % error)
    if verify_receipt:
        demand('receipt' in links, 'manifest has no chained proof receipt')
        try:
            report['receipt_verify'] = receipt.verify(Path(manifest['inputs']['receipt']))
        except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
            report['problems'].append('chained proof receipt is not current: ' + str(error))
    report['status'] = 'stale' if report['stale_links'] or report['problems'] else 'current'
    return report


def manifest_main(argv):
    parser = argparse.ArgumentParser(prog='artifact-manifest.py', description='Record or check an I07 artifact manifest.')
    parser.add_argument('action', choices=('manifest', 'check-manifest'))
    parser.add_argument('path', type=Path, help='manifest JSON; `manifest` never overwrites an existing file')
    parser.add_argument('--example')
    parser.add_argument('--zig-version')
    parser.add_argument('--air-dir')
    parser.add_argument('--generated')
    parser.add_argument('--source', action='append')
    parser.add_argument('--proof', action='append')
    parser.add_argument('--audit', help='assumption audit JSON supplying compiled theorem names')
    parser.add_argument('--receipt', help='sealed proof receipt attempt directory to chain')
    parser.add_argument('--expect', action='append', default=[],
                        help='LINK=SHA256, profile=PROFILE_SHA256 or zig_version=VERSION')
    parser.add_argument('--allow-dirty', action='store_true', help='accept a manifest recorded from a dirty tree')
    parser.add_argument('--verify-receipt', action='store_true',
                        help='also rerun proof-receipt verify on the chained attempt (needs its toolchain)')
    a = parser.parse_args(argv)
    root = Path(os.path.abspath(ROOT))
    path = Path(os.path.abspath(a.path))
    try:
        if a.action == 'manifest':
            demand(a.example and a.zig_version, 'manifest needs --example and --zig-version')
            inputs = default_inputs(root, a.example, a.zig_version)
            for key, value in (('air_dir', a.air_dir), ('generated', a.generated), ('sources', a.source),
                               ('proofs', a.proof), ('audit', a.audit), ('receipt', a.receipt)):
                if value is not None:
                    inputs[key] = str(Path(os.path.abspath(value))) if key in ('audit', 'receipt') else value
            demand(inputs['proofs'], 'no proof files selected')
            manifest = build_manifest(root, inputs)
            physical(path.parent)
            write_new(path, manifest)
            print(json.dumps({'manifest': str(path), 'manifest_sha256': manifest['manifest_sha256'],
                              'provenance': manifest['provenance']['status']}))
            return 0
        report = check_manifest(root, path, a.expect, a.allow_dirty, a.verify_receipt)
        print(json.dumps(report, indent=2, sort_keys=True))
        if report['status'] != 'current':
            print('artifact manifest %s: stale links %s; problems %s'
                  % (report['status'], report['stale_links'], report['problems']), file=sys.stderr)
        return 0 if report['status'] == 'current' else 2
    except (OSError, ValueError, KeyError, TypeError, RecursionError, subprocess.SubprocessError) as error:
        print('artifact manifest unavailable/stale: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(manifest_main(sys.argv[1:]))
