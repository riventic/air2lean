#!/usr/bin/env python3
"""Typed actual-Gen mutations. ROOT compiles Gen and oracle definitions before refutation."""
import argparse
from pathlib import Path

ORACLE = '''import Gen
open Zig
private def value (program : MemM α) : Option (Except Error α) :=
  (program.run GlobalPayload.mem0).run.map (·.map Prod.fst)
private def semanticOracle : Bool :=
  decide (value GlobalPayload.optionalPtr = some (.ok (⟨some 0, 8 + 16 + 4⟩ : Ptr))) &&
  decide (value GlobalPayload.smallPtr = some (.ok (⟨some 0, 8 + 28 + 2⟩ : Ptr))) &&
  decide (value GlobalPayload.widePtr = some (.ok (⟨some 0, 8 + 0⟩ : Ptr)))
'''

def alter_function(source: str, name: str, before: str, after: str) -> str:
    start = source.index(f'def {name} ')
    end = source.find('\nstructure ', start)
    if end < 0:
        end = source.index('\nend GlobalPayload', start)
    body = source[start:end]
    if body.count(before) != 1:
        raise ValueError(f'actual generated shape changed: {name}')
    return source[:start] + body.replace(before, after) + source[end:]


def create(source: Path, output: Path) -> None:
    if output.exists():
        raise ValueError('mutant output must be fresh')
    text = source.read_text()
    variants = {
        'control': text,
        'wrong_global': alter_function(text, 'optionalPtr', '⟨some 0, 28⟩', '⟨some 1, 28⟩'),
        'missing_small_payload_offset': alter_function(text, 'smallPtr', '⟨some 0, 38⟩', '⟨some 0, 36⟩'),
        'forget_parent': alter_function(text, 'widePtr', '⟨some 0, 8⟩', '⟨some 0, 0⟩'),
    }
    output.mkdir()
    for name, body in variants.items():
        directory = output / name
        directory.mkdir()
        (directory / 'Gen.lean').write_text(body)
        (directory / 'Oracle.defs.lean').write_text(ORACLE)
        (directory / 'Oracle.lean').write_text(ORACLE + 'theorem semantic_oracle : semanticOracle = true := by native_decide\n')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    create(args.source, args.output)


if __name__ == '__main__':
    main()
