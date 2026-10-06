#!/usr/bin/env python3
"""Build a temporary allocator-injected producer; repository sources stay unchanged."""
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
ALLOCATOR = 'const out_gpa = std.heap.page_allocator;'
INJECTED_ALLOCATOR = '''var parent_oom = std.testing.FailingAllocator.init(std.heap.page_allocator, .{ .fail_index = 0 });
const out_gpa = parent_oom.allocator();'''


def injected_source(source):
    if source.count(ALLOCATOR) != 1:
        raise ValueError('expected exactly one default producer allocator')
    return source.replace(ALLOCATOR, INJECTED_ALLOCATOR, 1)


def main():
    zig = Path(sys.argv[1]).resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix='air2lean-parent-oom-') as name:
        work = Path(name)
        (work / 'common.zig').write_text(injected_source((ROOT / 'tests/diff/common.zig').read_text()))
        (work / 'compat.zig').write_bytes((ROOT / 'tests/diff/compat.zig').read_bytes())
        binary = work / 'parent-oom'
        subprocess.run([str(zig), 'build-exe', '-OReleaseSafe', '-lc', '--dep', 'common',
                        '-Mroot=' + str(ROOT / 'tests/roadmap/outcome-accounting/ParentOOM.zig'),
                        '-Mcommon=' + str(work / 'common.zig'), '-femit-bin=' + str(binary)], check=True)
        subprocess.run([str(binary)], check=True, timeout=5)
    print('parent allocation failure terminated and reaped its owned child')


if __name__ == '__main__':
    main()
