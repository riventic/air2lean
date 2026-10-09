#!/usr/bin/env python3
"""Release compatibility metadata (compatibility.json): consistency check and release manifest.

  compat.py check   [--root DIR] [--json]   compare compatibility.json with its sources of truth
  compat.py release [--root DIR] [--out F]  print the metadata plus computed exporter checksums

The sources of truth stay where they are: zig-patch/versions.toml (downloads and checksums),
lean-toolchain, lakefile.toml, lake-manifest.json, the version lists of the workflow scripts and
CI matrix, and the translator's schema/profile constants. compatibility.json is a committed,
reviewed copy that release users can read without parsing those files; `check` fails on any drift.
No network, builds or tool execution. Runs on Python 3.8+ (no tomllib) for first-use hosts.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

SCHEMA = 'air2lean-compatibility/1'
KNOWN_HOSTS = ('x86_64-linux', 'aarch64-macos')
SHA = re.compile(r'^[0-9a-f]{64}$')
# Files whose bytes determine a patched compiler (same set as scripts/local-ci.sh's cache key).
EXPORTER_FILES = ('zig-patch/versions.toml', 'zig-patch/toml-get.sh', 'zig-patch/build.sh',
                  'zig-patch/lock.sh', 'zig-patch/air-json/json.zig',
                  'zig-patch/air-json/pointer-offset.zig', 'zig-patch/air-json/identity.zig')


def read_versions_toml(path):
    """Tables of versions.toml keyed by their exact header line (toml-get.sh semantics)."""
    tables, current = {}, None
    for line in Path(path).read_text().splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        if line.startswith('['):
            current = tables.setdefault(line, {})
            continue
        match = re.match(r'^([A-Za-z0-9_-]+) *= *"(.*)"$', line)
        if current is None or not match:
            raise ValueError('unsupported versions.toml line: ' + line)
        current[match.group(1)] = match.group(2)
    return tables


def zig_version_tables(tables):
    out = []
    for header in tables:
        match = re.match(r'^\["([^"]+)"\]$', header)
        if match:
            out.append(match.group(1))
    return out


def load(root):
    return json.loads((Path(root) / 'compatibility.json').read_text())


def sha256_file(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def check(root):
    """Return a list of human-readable drift errors (empty when consistent)."""
    root = Path(root)
    errors = []

    def expect(label, actual, wanted, fix):
        if actual != wanted:
            errors.append('%s: compatibility.json has %r, %s has %r' % (label, actual, fix, wanted))

    try:
        meta = load(root)
    except (OSError, ValueError) as exc:
        return ['compatibility.json is missing or not JSON: %s' % exc]
    try:
        tables = read_versions_toml(root / 'zig-patch/versions.toml')
    except (OSError, ValueError) as exc:
        return ['zig-patch/versions.toml unreadable: %s' % exc]

    def text(rel):
        try:
            return (root / rel).read_text()
        except OSError:
            errors.append('missing source of truth: ' + rel)
            return ''

    def get(path, default=None):
        node = meta
        for key in path:
            if not isinstance(node, dict) or key not in node:
                errors.append('compatibility.json lacks ' + '.'.join(path))
                return default
            node = node[key]
        return node

    expect('schema', meta.get('schema'), SCHEMA, 'scripts/compat.py')

    # Lean toolchain and Lake package.
    toolchain = text('lean-toolchain').strip()
    expect('lean.toolchain', get(('lean', 'toolchain')), toolchain, 'lean-toolchain')
    if (root / 'tests/diff/lean-toolchain').exists():
        expect('lean.toolchain', get(('lean', 'toolchain')),
               text('tests/diff/lean-toolchain').strip(), 'tests/diff/lean-toolchain')
    try:
        manifest = json.loads(text('lake-manifest.json') or '{}')
        packages = sorted(p.get('name') for p in manifest.get('packages', []))
    except ValueError:
        packages = None
    expect('lean.lake_packages', get(('lean', 'lake_packages')), packages, 'lake-manifest.json')
    version = re.search(r'^version *= *"([^"]+)"', text('lakefile.toml'), re.M)
    expect('air2lean.package_version', get(('air2lean', 'package_version')),
           version.group(1) if version else None, 'lakefile.toml')
    elan = tables.get('[ci.elan]', {})
    for key in ('version', 'url', 'sha256'):
        expect('lean.elan.' + key, get(('lean', 'elan', key)), elan.get(key), 'versions.toml [ci.elan]')
    asset = get(('lean', 'elan', 'asset'), '')
    if asset and asset not in str(elan.get('url', '')):
        errors.append('lean.elan.asset %r is not the pinned elan URL asset' % asset)

    # Zig versions: the same set and order as versions.toml, with identical pins.
    pinned = zig_version_tables(tables)
    entries = get(('zig', 'versions'), []) or []
    listed = [e.get('version') for e in entries if isinstance(e, dict)]
    expect('zig.versions', listed, pinned, 'zig-patch/versions.toml')
    for entry in entries:
        if not isinstance(entry, dict):
            errors.append('zig.versions entries must be objects')
            continue
        v = entry.get('version')
        table = tables.get('["%s"]' % v, {})
        host = tables.get('[ci.host-zig."%s"]' % v, {})
        src = entry.get('source') or {}
        ci = entry.get('ci_host_zig') or {}
        expect('zig %s source.url' % v, src.get('url'), table.get('url'), 'versions.toml')
        expect('zig %s source.sha256' % v, src.get('sha256'), table.get('sha256'), 'versions.toml')
        expect('zig %s hook' % v, entry.get('hook'), table.get('hook'), 'versions.toml')
        expect('zig %s llvm' % v, entry.get('llvm'), table.get('llvm'), 'versions.toml')
        expect('zig %s ci_host_zig.url' % v, ci.get('url'), host.get('url'), 'versions.toml')
        expect('zig %s ci_host_zig.sha256' % v, ci.get('sha256'), host.get('sha256'), 'versions.toml')
        for label, value in (('source', src.get('sha256')), ('ci_host_zig', ci.get('sha256'))):
            if not SHA.match(str(value)):
                errors.append('zig %s %s.sha256 is not a lowercase sha256' % (v, label))
        if table.get('hook') and not (root / 'zig-patch' / table['hook']).is_file():
            errors.append('zig %s hook file is missing: zig-patch/%s' % (v, table['hook']))
        hosts = entry.get('hosts')
        if not isinstance(hosts, list) or not hosts or any(h not in KNOWN_HOSTS for h in hosts):
            errors.append('zig %s hosts must be a non-empty subset of %s' % (v, ', '.join(KNOWN_HOSTS)))
    default = get(('zig', 'default'))
    if default not in pinned:
        errors.append('zig.default %r is not a pinned version' % default)
    translate = text('scripts/translate.sh')
    found = re.search(r'AIR2LEAN_ZIG_VERSION:-([0-9.]+)\}', translate)
    expect('zig.default', default, found.group(1) if found else None, 'scripts/translate.sh')

    # Every hard-coded supported-version list agrees.
    common = text('scripts/workflow-common.sh')
    case = re.search(r'case "\$zig_version" in\n\s*([0-9. |]+)\)', common)
    expect('zig.versions', sorted(listed), sorted(case.group(1).replace(' ', '').split('|')) if case else None,
           'scripts/workflow-common.sh')
    local = re.search(r'case "\$version" in ([0-9.|]+)\)', text('scripts/local-ci.sh'))
    expect('zig.versions', sorted(listed), sorted(local.group(1).split('|')) if local else None,
           'scripts/local-ci.sh')
    matrix = sorted(set(re.findall(r'^\s*- zig: "([^"]+)"', text('.github/workflows/ci.yml'), re.M)))
    expect('zig.versions', sorted(listed), matrix, '.github/workflows/ci.yml matrix')
    linux_only = sorted(re.findall(r'"\$zig_version" = ([0-9.]+) \] && \[ "\$\(uname -s\)" != Linux', common))
    declared = sorted(e.get('version') for e in entries
                      if isinstance(e, dict) and 'aarch64-macos' not in (e.get('hosts') or []))
    expect('Linux-only zig versions', declared, linux_only, 'scripts/workflow-common.sh')

    # Translator constants.
    profile_src = text('Air2Lean/Air/Profile.lean')
    schema_max = re.search(r'unless 1 ≤ schema && schema ≤ (\d+) do', profile_src)
    expect('air2lean.air_json_schemas', get(('air2lean', 'air_json_schemas')),
           {'min': 1, 'max': int(schema_max.group(1))} if schema_max else None, 'Air2Lean/Air/Profile.lean')
    names = sorted(re.findall(r'def (?:legacy|current)Name : String := "([^"]+)"', profile_src))
    expect('profiles', sorted(p.get('name') for p in get(('profiles',), []) or []), names,
           'Air2Lean/Air/Profile.lean')
    tr = get(('translation',), {}) or {}
    flags = '-OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline'
    wanted = {'target': 'x86_64-linux', 'cpu': 'baseline', 'optimize': 'ReleaseSafe', 'error_tracing': False}
    if flags in translate:
        expect('translation', tr, wanted, 'scripts/translate.sh')
    else:
        errors.append('scripts/translate.sh no longer exports with: ' + flags + '; update compat.py and compatibility.json')

    # AIR-only lock.
    lock = get(('air_only_lock',), {}) or {}
    lock_src = text('zig-patch/lock.sh')
    if lock.get('marker') not in lock_src or 'zig-unlocked' not in lock_src:
        errors.append('air_only_lock.marker/compiler disagree with zig-patch/lock.sh')
    for word in ('version', 'env', 'targets', 'build-obj', 'build-exe', 'build-lib', 'test'):
        if not any(a.split()[0] == word for a in lock.get('allowed', [])):
            errors.append('air_only_lock.allowed lacks %s (zig-patch/lock.sh allows it)' % word)

    # Clean-environment recipe.
    clean = get(('clean_environment',), {}) or {}
    for key in ('recipe', 'tutorial'):
        if not (root / str(clean.get(key, ''))).is_file():
            errors.append('clean_environment.%s does not exist: %s' % (key, clean.get(key)))
    image = re.search(r'^FROM (\S+)', text('Dockerfile.clean-env'), re.M)
    expect('clean_environment.image', clean.get('image'), image.group(1) if image else None,
           'Dockerfile.clean-env')
    for profile in ('proofs', 'translate'):
        res = (meta.get('resources') or {}).get(profile) or {}
        if not all(isinstance(res.get(k), (int, float)) and res.get(k) > 0
                   for k in ('min_disk_gib', 'min_memory_gib')):
            errors.append('resources.%s needs positive min_disk_gib and min_memory_gib' % profile)
    return errors


def release(root):
    root = Path(root)
    meta = load(root)
    out = {'compatibility': meta, 'checksums': {}}
    for rel in EXPORTER_FILES:
        out['checksums'][rel] = sha256_file(root / rel)
    for entry in meta['zig']['versions']:
        rel = 'zig-patch/' + entry['hook']
        out['checksums'][rel] = sha256_file(root / rel)
    for rel in ('lean-toolchain', 'lake-manifest.json', 'compatibility.json'):
        out['checksums'][rel] = sha256_file(root / rel)
    key = hashlib.sha256()
    for rel in EXPORTER_FILES:
        key.update((root / rel).read_bytes())
    out['exporter_fingerprint'] = key.hexdigest()
    try:
        out['git_revision'] = subprocess.run(['git', '-C', str(root), 'rev-parse', 'HEAD'], check=True,
                                             stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                             universal_newlines=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        out['git_revision'] = None
    return out


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('command', choices=('check', 'release'))
    parser.add_argument('--root', default=str(Path(__file__).resolve().parents[1]))
    parser.add_argument('--json', action='store_true', help='check: machine-readable result')
    parser.add_argument('--out', help='release: write the manifest here instead of stdout')
    args = parser.parse_args(argv)
    if args.command == 'check':
        errors = check(args.root)
        if args.json:
            print(json.dumps({'schema': SCHEMA, 'consistent': not errors, 'errors': errors}, indent=2))
        else:
            for error in errors:
                print('error: ' + error, file=sys.stderr)
            if not errors:
                print('OK: compatibility.json agrees with versions.toml, lean-toolchain and the workflow scripts')
        return 1 if errors else 0
    errors = check(args.root)
    if errors:
        for error in errors:
            print('error: ' + error, file=sys.stderr)
        return 1
    text = json.dumps(release(args.root), indent=2, sort_keys=True) + '\n'
    if args.out:
        Path(args.out).write_text(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == '__main__':
    sys.exit(main())
