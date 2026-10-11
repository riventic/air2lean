#!/usr/bin/env python3
"""Inspect AIR dumps of the module-identity fixtures (tests/roadmap/module-identity/README.md).

  check_identity.py mods <air-dir>
      The two `util.helper` functions have their own files and modules, and `main.entry`
      calls each one by its module.
  check_identity.py thread <air-dir>
      The user `Thread` type and `Thread.spawn` belong to the root module.
  check_identity.py duplicate <air-dir> <out-dir>
      Copy <air-dir>'s root `util.helper` into <out-dir> twice, under two storage names and
      with different bodies: two files that claim one identity.
"""
import hashlib
import json
import pathlib
import shutil
import sys


def fail(message):
    sys.exit('module identity: ' + message)


def load_dir(air_dir):
    return {path.name: json.loads(path.read_text()) for path in pathlib.Path(air_dir).glob('*.json')}


def func_refs(value):
    if isinstance(value, dict):
        if 'func' in value:
            yield value['func'], value.get('module')
        for item in value.values():
            yield from func_refs(item)
    elif isinstance(value, list):
        for item in value:
            yield from func_refs(item)


def check_mods(air_dir):
    files = load_dir(air_dir)
    other = '~air2lean-sha256-' + hashlib.sha256(b'other:util.helper').hexdigest() + '.json'
    expected = {'main.entry.json': ('main.entry', 'root'), 'util.helper.json': ('util.helper', 'root'),
                other: ('util.helper', 'other')}
    actual = {name: (doc['name'], doc.get('module')) for name, doc in files.items()}
    if actual != expected:
        fail(f'mods export {actual}, expected {expected}')
    calls = sorted(func_refs(files['main.entry.json']['body']))
    if calls != [('util.helper', 'other'), ('util.helper', 'root')]:
        fail(f'main.entry calls {calls}')
    tags = {name: [inst['tag'] for inst in files[name]['body']] for name in ('util.helper.json', other)}
    if 'add_wrap' not in tags['util.helper.json'] or 'mul_wrap' not in tags[other]:
        fail(f'helper bodies {tags}')


def check_thread(air_dir):
    files = load_dir(air_dir)
    if sorted(files) != ['Thread.spawn.json', 'main.entry.json']:
        fail(f'thread export {sorted(files)}')
    for doc in files.values():
        if doc.get('module') != 'root':
            fail(f'{doc["name"]} has module {doc.get("module")!r}')
        named = [(t['name'], t.get('module')) for t in doc['types'] if t['k'] in ('struct', 'enum', 'union')]
        if ('Thread', 'root') not in named:
            fail(f'{doc["name"]}: user Thread type {named}')
    if list(func_refs(files['main.entry.json']['body'])) != [('Thread.spawn', 'root')]:
        fail('main.entry does not call the root Thread.spawn')


def duplicate(air_dir, out_dir):
    air_dir, out_dir = pathlib.Path(air_dir), pathlib.Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy(air_dir / 'util.helper.json', out_dir / 'util.helper.json')
    doc = json.loads((air_dir / 'util.helper.json').read_text())
    for inst in doc['body']:
        if inst['tag'] == 'add_wrap':
            inst['tag'] = 'mul_wrap'
    (out_dir / 'util.helper.copy.json').write_text(json.dumps(doc, indent=1))


def main(argv):
    if len(argv) == 3 and argv[1] == 'mods':
        check_mods(argv[2])
    elif len(argv) == 3 and argv[1] == 'thread':
        check_thread(argv[2])
    elif len(argv) == 4 and argv[1] == 'duplicate':
        duplicate(argv[2], argv[3])
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main(sys.argv)
