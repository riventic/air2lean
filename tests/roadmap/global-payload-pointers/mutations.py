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
    if (re.search(r'error:|\bpanic\b|\bpanicked\b|Segmentation|signal|unable to|FileNotFound|'
                  r'timeout|timed out|import failed|module not found|compiler failed|build failed',
                  log, re.I) or re.search(r'\bSIG[A-Z0-9]+\b', log)):
        raise ValueError('tool, panic, signal or import failure does not count')
    target = MUTANTS[name][2]
    titles = {row[2] for row in MUTANTS.values()}
    errors = {'TestExpectedEqual', 'TestUnexpectedError', 'TestExpectedError'}
    headers = list(re.finditer(r'^\d+/\d+ [^\n]*?test\.([^\n]+?)\.\.\.(.*)$', log, re.M))
    failures = []
    for index, header in enumerate(headers):
        end = headers[index + 1].start() if index + 1 < len(headers) else len(log)
        summary = re.search(r'^\d+ passed;|^All \d+ tests passed\.', log[header.end():end], re.M)
        if summary is not None:
            end = header.end() + summary.start()
        # Zig16 may print expected/actual diagnostics after the test title and place
        # FAIL on its own line. Keep that result inside this named test's frame.
        frame = header.group(2) + log[header.end():end]
        results = re.findall(r'^FAIL \(([^)\n]+)\)$', frame, re.M)
        if results and re.match(r'(?:OK|SKIP)\b', header.group(2)):
            raise ValueError('failure result follows a completed passing/skipped test')
        if len(results) > 1:
            raise ValueError('multiple failure results for one named test')
        for error in results:
            if header.group(1) not in titles:
                raise ValueError('failure is not a known kernel test')
            if error not in errors:
                raise ValueError('failure is not a testing assertion')
            failures.append((header.group(1), error))
    if len(failures) != len(re.findall(r'\bFAIL\b', log)):
        raise ValueError('unframed or malformed failure result')
    if not failures or not any(title == target for title, _ in failures):
        raise ValueError('missing the named semantic assertion failure')
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
