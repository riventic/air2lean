#!/usr/bin/env python3
"""Check first-use diagnostics against the built translator."""
from pathlib import Path
import subprocess
import tempfile

repo = Path(__file__).resolve().parents[2]
binary = repo / '.lake/build/bin/air2lean'


def check(args, status, message):
    result = subprocess.run([str(binary), *map(str, args)], capture_output=True, text=True)
    assert result.returncode == status, (args, result.returncode, result.stdout, result.stderr)
    assert message in result.stdout + result.stderr, (args, message, result.stdout, result.stderr)
    return result.stdout + result.stderr


for flag in ['--help', '-h']:
    check([flag], 0, 'Directory of JSON files from the patched Zig compiler')
check(['--namespce', 'My'], 1, 'unknown option')
check(['-o'], 1, 'missing value for -o')
with tempfile.TemporaryDirectory(prefix='air2lean CLI first use ') as temp:
    empty = Path(temp)
    output = empty / 'previous.lean'
    output.write_text('previous output\n')
    diagnostics = check([empty, '-o', output, '--namespace', 'My'], 1, 'no *.json files')
    assert 'export fn or comptime references' in diagnostics
    assert output.read_text() == 'previous output\n'
print('First-use CLI diagnostics passed')
