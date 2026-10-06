#!/usr/bin/env python3
"""Typed kernel mutants; only named assertion failures after a successful build count."""
import argparse
from pathlib import Path
import re

MUTANTS = {
    'forget-parent': ('const next = try add(try add(self.off, delta), parent_off);',
                      'const next = try add(try add(self.off, delta), parent_off - parent_off);',
                      'accumulates leaf, exact payload, and every parent offset'),
    'forget-payload': ('const next = try add(try add(self.off, delta), parent_off);',
                       'const next = try add(try add(self.off, delta - delta), parent_off);',
                       'accumulates leaf, exact payload, and every parent offset'),
    'wrap-offset': ('if (sum[1] != 0) return error.Overflow;',
                    'if (sum[1] != 0 and delta == 0) return error.Overflow;',
                    'both overflow additions fail without committing partial state'),
    'unbounded': ('if (self.remaining == 0) return error.Depth;',
                  'if (self.remaining == 0) self.remaining = 1;',
                  'bounded recursion rejects a cycle or deep chain at the same boundary'),
}

def mutate(source, name):
    old, new, _ = MUTANTS[name]
    if source.count(old) != 1:
        raise ValueError('mutation target must occur exactly once')
    return source.replace(old, new)

def classify(status, log, name):
    if status != 1:
        raise ValueError('expected test executable exit 1')
    target = MUTANTS[name][2]
    failures = re.findall(r'^\d+/\d+ [^\n]*test\.([^\n]+?)\.\.\.FAIL \(([^)]+)\)', log, re.M)
    if not failures or not any(title == target for title, _ in failures):
        raise ValueError('missing the named semantic assertion failure')
    if any(error not in ('TestExpectedEqual', 'TestUnexpectedError', 'TestExpectedError') for _, error in failures):
        raise ValueError('failure is not a testing assertion')
    if re.search(r'error:|panic:|Segmentation|signal|unable to|FileNotFound', log, re.I):
        raise ValueError('tool, panic, signal or import failure does not count')
    return True

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    create = sub.add_parser('create')
    create.add_argument('name', choices=MUTANTS)
    create.add_argument('source', type=Path)
    create.add_argument('output', type=Path)
    check = sub.add_parser('classify')
    check.add_argument('name', choices=MUTANTS)
    check.add_argument('status', type=int)
    check.add_argument('log', type=Path)
    args = parser.parse_args()
    if args.mode == 'create':
        if args.source.resolve() == args.output.resolve():
            raise ValueError('cannot overwrite baseline')
        args.output.write_text(mutate(args.source.read_text(), args.name))
    else:
        classify(args.status, args.log.read_text(), args.name)

if __name__ == '__main__':
    main()
