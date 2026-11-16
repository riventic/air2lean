#!/usr/bin/env python3
"""Gate for the L04 compiler-export qualification record (compiler-qualification.json).

`air-fresh/<version>` and `aliases/air-fresh/<version>` are unmodified schema-12 exports of
`try_pointers.zig` and `try_aliases.zig`, one per version of their `exports.json` entry; the
sources, the exporter and every file are pinned by `exports.lock.json`
(scripts/fixture-exports.py). The retained schema-11 `air/` files and their `Gen.lean` stay as
they are (their hashes are pinned by `provenance.json` and the integration manifests). This gate
checks each fresh export's function inventory, Linux/baseline ReleaseSafe profile and
pointer-try tags, and, with `--translator`, that translating it gives the retained generated
module up to the profile header (the CI comparison).
"""
import argparse
import json
from pathlib import Path
import runpy
import subprocess
import tempfile

REPO = Path(__file__).resolve().parents[3]
CASE = Path(__file__).resolve().parent
HELPERS = runpy.run_path(str(REPO / 'scripts/normalize-generated.py'))
SCRIPT = REPO / 'scripts/normalize-generated.py'


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


def check_air(directory, entry, version):
    files = sorted(directory.glob('*.json'))
    docs = [HELPERS['parse_json'](path.read_text()) for path in files]
    prefix = entry['name_prefix']
    if sorted(d['name'] for d in docs) != sorted(prefix + n for n in entry['functions']):
        raise ValueError(f'{prefix} AIR function inventory differs')
    profiles = [HELPERS['fresh_linux_profile'](d, version) for d in docs]
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


def inspect(case=CASE, translator=None):
    """The checked files: every version's export of each fixture of the record."""
    record = HELPERS['parse_json']((case / 'compiler-qualification.json').read_text())
    exports = {e['out']: e for e in json.loads((case / 'exports.json').read_text())['exports']}
    checked = []
    for key, entry in record['fixtures'].items():
        if entry['air_dir'] not in exports:
            raise ValueError(f'{key}: exports.json declares no {entry["air_dir"]}')
        for version in exports[entry['air_dir']]['versions']:
            directory = case / entry['air_dir'].format(version=version)
            checked += check_air(directory, entry, version)
            if translator is not None:
                translate_matches(translator, directory, entry, case)
    return checked


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--translator', type=Path)
    args = parser.parse_args()
    try:
        inspect(translator=args.translator)
    except (KeyError, OSError, ValueError, TypeError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error))
    print('pointer-try compiler export record passed')
