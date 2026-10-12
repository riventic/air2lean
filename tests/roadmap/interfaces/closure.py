#!/usr/bin/env python3
"""Keep the call closure of root functions: copy from SRC to DST every exported AIR file that a
root reaches by direct calls (`"func"` callees). Usage: closure.py SRC DST ROOT[,ROOT...].

Indirect calls need no edge here: the programs of this fixture take the addresses of their
closure's functions in the functions that reach them."""
import json
from pathlib import Path
import re
import shutil
import sys


def main(src, dst, roots):
    files = {}
    for path in Path(src).glob('*.json'):
        files[json.loads(path.read_text())['name']] = path
    seen, todo = set(), list(roots)
    while todo:
        name = todo.pop()
        if name in seen or name not in files:
            continue
        seen.add(name)
        todo += re.findall(r'"func": "([^"]+)"', files[name].read_text())
    missing = [r for r in roots if r not in seen]
    if missing:
        sys.exit(f'closure.py: no AIR for {missing}')
    Path(dst).mkdir(parents=True, exist_ok=True)
    for name in sorted(seen):
        shutil.copy(files[name], Path(dst) / files[name].name)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], sys.argv[3].split(','))
