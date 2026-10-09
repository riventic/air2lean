#!/usr/bin/env python3
"""Gate for the L04 compiler-export qualification record (compiler-qualification.json).

`air-fresh/0.16.0` and `aliases/air-fresh/0.16.0` are unmodified schema-12 exports of
`try_pointers.zig` and `try_aliases.zig` from a patched 0.16.0 compiler. The retained schema-11
`air/` files and their `Gen.lean` stay as they are (their hashes are pinned by `provenance.json`
and the integration manifests). This gate checks the fresh files' hashes, inventory, Linux/baseline
ReleaseSafe profile and pointer-try tags, and, with `--translator`, that translating them gives
the retained generated module up to the profile header (the CI comparison). Hashes do not attest
that a compiler ran. `--fresh ROOT` validates a new export (`ROOT/try_pointers`,
`ROOT/try_aliases`, from `check.sh --export` and `aliases/check.sh --export`) the same way.
"""
import argparse
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import tempfile

REPO = Path(__file__).resolve().parents[3]
CASE = Path(__file__).resolve().parent
HELPERS = runpy.run_path(str(REPO / 'scripts/normalize-generated.py'))
SCRIPT = REPO / 'scripts/normalize-generated.py'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tags_of(value, tags):
    if isinstance(value, dict):
        if value.get('unsupported') is True:
            raise ValueError('unsupported AIR instruction')
        if 'tag' in value:
            tags.add(value['tag'])
        for child in value.values():
            tags_of(child, tags)
    elif isinstance(value, list):
        for child in value:
            tags_of(child, tags)


def check_air(directory, entry):
    files = sorted(directory.glob('*.json'))
    docs = [HELPERS['parse_json'](path.read_text()) for path in files]
    prefix = entry['name_prefix']
    if sorted(d['name'] for d in docs) != sorted(prefix + n for n in entry['functions']):
        raise ValueError(f'{prefix} AIR function inventory differs')
    profiles = [HELPERS['fresh_linux_profile'](d, '0.16.0') for d in docs]
    if any(p != profiles[0] for p in profiles):
        raise ValueError(f'{prefix} fresh AIR has mixed profiles')
    tags = set()
    for doc in docs:
        tags_of(doc.get('body', []), tags)
    if not set(entry['required_tags']) <= tags:
        raise ValueError(f'{prefix} AIR lacks required tags {sorted(set(entry["required_tags"]) - tags)}')
    return files


def translate_matches(translator, directory, entry, case):
    """The fresh export translates to the retained module, up to the profile header."""
    with tempfile.TemporaryDirectory() as temp:
        out, report = Path(temp) / 'Gen.lean', Path(temp) / 'report.json'
        subprocess.run([str(translator), str(directory), '-o', str(out), '--namespace', entry['namespace'],
                        '--prefix', entry['name_prefix']], check=True, capture_output=True)
        subprocess.run(['python3', str(SCRIPT), 'report', str(out), str(directory), str(report)],
                       check=True, capture_output=True)
        result = subprocess.run(['python3', str(SCRIPT), 'compare', str(case / entry['generated']),
                                 str(out), str(report)], capture_output=True, text=True)
        if result.returncode != 0:
            raise ValueError(f'{entry["name_prefix"]} fresh translation differs from {entry["generated"]}: '
                             + result.stderr.strip())


def inspect(case=CASE, repo=REPO, fresh=None, translator=None):
    manifest = HELPERS['parse_json']((case / 'compiler-qualification.json').read_text())
    inventory = {}
    for key, entry in manifest['fixtures'].items():
        source = repo / entry['source']
        if digest(source) != entry['source_sha256']:
            raise ValueError(f'stale {key} source')
        directory = Path(fresh) / key if fresh else case / entry['air_dir']
        files = check_air(directory, entry)
        if fresh is None:
            inventory.update({str(p.relative_to(case)): digest(p) for p in files})
        if translator is not None:
            translate_matches(translator, directory, entry, case)
    if fresh is None and inventory != manifest['artifacts']:
        raise ValueError('stale or incomplete artifact inventory')
    return inventory


def record(case=CASE, repo=REPO):
    path = case / 'compiler-qualification.json'
    manifest = json.loads(path.read_text())
    inventory = {}
    for entry in manifest['fixtures'].values():
        entry['source_sha256'] = digest(repo / entry['source'])
        inventory.update({str(p.relative_to(case)): digest(p)
                          for p in sorted((case / entry['air_dir']).glob('*.json'))})
    manifest['artifacts'] = inventory
    path.write_text(json.dumps(manifest, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true')
    parser.add_argument('--fresh', type=Path, metavar='ROOT')
    parser.add_argument('--translator', type=Path)
    args = parser.parse_args()
    try:
        if args.record:
            record()
        inspect(fresh=args.fresh, translator=args.translator)
    except (KeyError, OSError, ValueError, TypeError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error))
    print('pointer-try compiler export record passed')
