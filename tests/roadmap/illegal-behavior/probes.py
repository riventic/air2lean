#!/usr/bin/env python3
"""Translate each probe.zig function alone and compare with expected.json (docs/illegal-behavior.md).

Each entry of expected.json names the AIR files of one probe (the function and its callees), the
expected translator result (`rejected` or `accepted`), and for `rejected` a fragment of the
diagnostic; for `accepted` the Lean text that must appear in the translation.

  python3 tests/roadmap/illegal-behavior/probes.py [path/to/air2lean]
"""
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def run(binary, probe):
    with tempfile.TemporaryDirectory() as tmp:
        air = Path(tmp) / 'air'
        air.mkdir()
        for name in probe['files']:
            shutil.copy(HERE / 'probe-air' / name, air / name)
        out = Path(tmp) / 'Gen.lean'
        proc = subprocess.run([binary, str(air), '-o', str(out), '--namespace', 'Probe', '--prefix', 'probe.'],
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=600)
        return proc.returncode, proc.stdout, out.read_text() if proc.returncode == 0 else ''


def main():
    binary = sys.argv[1] if len(sys.argv) > 1 else str(HERE.parents[2] / '.lake/build/bin/air2lean')
    expected = json.loads((HERE / 'expected.json').read_text())
    failures = []
    for name, probe in expected.items():
        rc, log, text = run(binary, probe)
        if probe['result'] == 'rejected':
            ok = rc != 0 and probe['diagnostic'] in log
        else:
            ok = rc == 0 and all(t in text for t in probe['contains'])
        print(f'{name}: {"ok" if ok else "FAIL"} (rc={rc})')
        if not ok:
            failures.append(f'{name}: rc={rc}: {log.strip()[:400]}')
    if failures:
        print('\n'.join(failures), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
