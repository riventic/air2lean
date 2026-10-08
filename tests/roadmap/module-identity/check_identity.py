#!/usr/bin/env python3
"""Inspect AIR dumps of the module-identity fixtures (tests/roadmap/module-identity/README.md).

  check_identity.py duplicate <air-dir> <out-dir>
      Copy <air-dir>'s `util.helper` export into <out-dir> twice, under two storage names and
      with different bodies: two files that claim one identity.
"""
import json
import pathlib
import shutil
import sys


def load(path):
    return json.loads(pathlib.Path(path).read_text())


def duplicate(air_dir, out_dir):
    air_dir, out_dir = pathlib.Path(air_dir), pathlib.Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy(air_dir / 'util.helper.json', out_dir / 'util.helper.json')
    doc = load(air_dir / 'util.helper.json')
    swap = {'add_wrap': 'mul_wrap', 'mul_wrap': 'add_wrap'}
    if not any(inst['tag'] in swap for inst in doc['body']):
        sys.exit('module identity: util.helper has no add_wrap/mul_wrap')
    for inst in doc['body']:
        inst['tag'] = swap.get(inst['tag'], inst['tag'])
    (out_dir / 'util.helper.copy.json').write_text(json.dumps(doc, indent=1))


def main(argv):
    if len(argv) == 4 and argv[1] == 'duplicate':
        duplicate(argv[2], argv[3])
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main(sys.argv)
