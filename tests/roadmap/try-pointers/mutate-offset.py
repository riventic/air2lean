#!/usr/bin/env python3
"""Create one typed offset mutant and accept only its located kernel proof failure."""
import argparse
from pathlib import Path
import re
import sys

CAP = 8 * 1024 * 1024
BEGIN = '-- MUTANT_BRIDGE_BEGIN: payload8_program'
END = '-- MUTANT_BRIDGE_END: payload8_program'


def bounded_text(path):
    with Path(path).open('rb') as stream:
        data = stream.read(CAP + 1)
    if len(data) > CAP:
        raise ValueError('mutation input exceeds byte limit')
    return data.decode('utf-8')


def mutate(source):
    starts = list(re.finditer(r'^def payload8 \(', source, re.MULTILINE))
    if len(starts) != 1:
        raise ValueError('expected exactly one generated payload8 definition')
    start = starts[0].start()
    rest = source[start:]
    stop = re.search(r'^structure |^end TryPointers\s*$', rest, re.MULTILINE)
    if stop is None:
        raise ValueError('cannot locate generated payload8 definition boundary')
    end = start + stop.start()
    body = source[start:end]
    needle = 'pure ((.ok v2) : Except Zig.ErrName (Zig.Ptr))'
    if body.count(needle) != 1:
        raise ValueError('expected one exact payload8 success return')
    replacement = 'pure ((.ok (v2.add 1)) : Except Zig.ErrName (Zig.Ptr))'
    return source[:start] + body.replace(needle, replacement) + source[end:]


def bridge_lines(proof):
    lines = proof.splitlines()
    starts = [i + 1 for i, line in enumerate(lines) if line == BEGIN]
    ends = [i + 1 for i, line in enumerate(lines) if line == END]
    if len(starts) != 1 or len(ends) != 1 or starts[0] >= ends[0]:
        raise ValueError('expected one ordered proof bridge marker pair')
    inside = lines[starts[0]:ends[0] - 1]
    if sum(line.startswith('theorem payload8_program (') for line in inside) != 1:
        raise ValueError('bridge markers must contain the actual payload8 theorem')
    return starts[0] + 1, ends[0] - 1


def classify(status, proof_path, proof, log):
    if status != 1:
        raise ValueError(f'expected exact Lean exit 1, got {status}')
    lo, hi = bridge_lines(proof)
    # Every error must have the expected absolute file and lie in the bridge. Unlocated
    # errors (tool/import/package/IO failures) and unrelated proof errors are rejected.
    expected = str(Path(proof_path).resolve())
    located = re.compile(r'^(.+):(\d+):(\d+):\s*error:\s*(.*)$', re.MULTILINE)
    errors = list(located.finditer(log))
    if not errors:
        raise ValueError('missing located kernel proof failure')
    stripped = located.sub('', log)
    if re.search(r'\berror\s*:', stripped, re.IGNORECASE):
        raise ValueError('unlocated error is not a semantic mutant rejection')
    for match in errors:
        path, line, _, message = match.groups()
        diagnostic_path = Path(path)
        if not diagnostic_path.is_absolute():
            raise ValueError('diagnostic path must be absolute')
        # Lean retains repeated separators from RUNNER_TEMP/TMPDIR. Resolve both
        # absolute paths consistently without broadening the accepted proof region.
        if str(diagnostic_path.resolve()) != expected or not lo <= int(line) <= hi:
            raise ValueError('error is outside the expected payload8 bridge')
        if not (message == 'unsolved goals' or message.startswith("Tactic `rfl` failed")):
            raise ValueError('expected a kernel equality proof failure, not another diagnostic')
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='mode', required=True)
    create = commands.add_parser('create')
    create.add_argument('--source', type=Path, required=True)
    create.add_argument('--output', type=Path, required=True)
    check = commands.add_parser('classify')
    check.add_argument('--status', type=int, required=True)
    check.add_argument('--proof', type=Path, required=True)
    check.add_argument('--log', type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.mode == 'create':
            if args.source.resolve() == args.output.resolve():
                raise ValueError('mutant output must not overwrite the baseline generated file')
            args.output.write_text(mutate(bounded_text(args.source)))
        else:
            classify(args.status, args.proof, bounded_text(args.proof), bounded_text(args.log))
            print('wrong payload offset rejected by the located generated-definition proof')
    except (OSError, UnicodeError, ValueError) as error:
        print(f'offset mutation gate: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
