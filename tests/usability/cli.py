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
    complete = [empty, '-o', output, '--namespace', 'My']
    for policy in ['available', 'fallible']:
        check([*complete, '--spawn-policy', policy], 1, 'no *.json files')
    check([*complete, '--spawn-policy'], 1, 'missing value for --spawn-policy')
    check([*complete, '--spawn-policy', 'unknown'], 1,
          'invalid --spawn-policy (expected available or fallible)')
    for first, second in [('available', 'fallible'), ('fallible', 'available'), ('fallible', 'fallible')]:
        check([*complete, '--spawn-policy', first, '--spawn-policy', second], 1, 'duplicate --spawn-policy')
    # Existing nonduplicate parser precedence and literal option values remain intact.
    check([empty, '-o', output, '--spawn-policy', 'unknown'], 1, 'missing --namespace')
    check([*complete, '--float-semantics', 'unknown', '--spawn-policy', 'unknown'], 1,
          'invalid --spawn-policy (expected available or fallible)')
    check([*complete, '--spawn-policy', 'unknown', '--unknown'], 1, 'unknown option')
    for prefix_value in ['--spawn-policy', '--spawn-policy=anything']:
        check([*complete, '--prefix', prefix_value], 1, 'no *.json files')
    assert output.read_text() == 'previous output\n'
print('First-use CLI diagnostics passed')
