#!/usr/bin/env python3
"""Write five narrowly bound semantic mutant patches; never invoke the toolchain."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
FILE = 'ZigLean/Mem/Alloc.lean'
CHECK = 'tests/roadmap/resize-remap/Check.lean'
EXPECTED_ERRORS = {
    'in-place-wrong-length': 'in-place remap lost prefix, new undefinedness, size or address boundary',
    'copy-lost-prefix-and-defined-suffix': 'in-place remap lost prefix, new undefinedness, size or address boundary',
    'moved-old-stays-live': 'moved remap lost prefix, undefined suffix or old-block invalidation',
    'failure-mutates-old': 'failed remap changed bytes, capacity or lifetime',
    'in-place-frame-overlap': 'in-place growth overlapped a later allocation',
}
REPAIRS = {
    'in-place-wrong-length': ('bytes := remapBytes blk.bytes n }', 'bytes := remapBytes blk.bytes (n + 1) }'),
    'copy-lost-prefix-and-defined-suffix': ('padTo n (bs.extract 0 n)',
                                          'Array.replicate n (.int 0)'),
    'moved-old-stays-live': ('    poisonFree s.ptr s.len.toNat\n', '    pure ()\n'),
    'failure-mutates-old': ('  if m.allocPolicy.byteRemap = .fail then return none',
                            '  if m.allocPolicy.byteRemap = .fail then\n    poisonFree s.ptr s.len.toNat\n    return none'),
    'in-place-frame-overlap': ('    if blk.bytes.size < n ∧ m.byteRemapLast b blk ≠ true then return none\n', ''),
}


def generate(destination):
    source = (ROOT / FILE).read_text()
    check_sha256 = hashlib.sha256((ROOT / CHECK).read_bytes()).hexdigest()
    destination.mkdir(parents=True, exist_ok=False)
    rows = []
    for name, (before, after) in REPAIRS.items():
        if source.count(before) != 1:
            raise ValueError(f'{name}: source marker missing or ambiguous')
        changed = source.replace(before, after)
        patch = ''.join(difflib.unified_diff(source.splitlines(keepends=True), changed.splitlines(keepends=True),
                                           fromfile='a/' + FILE, tofile='b/' + FILE))
        output = destination / (name + '.patch')
        output.write_text(patch)
        mutant = destination / (name + '.lean')
        mutant.write_text(changed)
        rows.append(dict(name=name, mutant_source=mutant.name, patch_sha256=hashlib.sha256(output.read_bytes()).hexdigest(),
                         source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                         check_sha256=check_sha256, changed_source_sha256=hashlib.sha256(changed.encode()).hexdigest(),
                         expected_error=EXPECTED_ERRORS[name], compilation_must_succeed=True, check_elaboration_must_succeed=True,
                         expected_gate_failure=True, actual_execution='pending'))
    (destination / 'manifest.json').write_text(json.dumps(rows, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    generate(parser.parse_args().output)
