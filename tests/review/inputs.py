#!/usr/bin/env python3
"""Check that the differential corpus covers its deterministic boundary cases.

Accept a repository root to check a freshly generated scratch corpus against the
same dispatched-function inventory. Uses only the Python standard library.
"""

import json
from pathlib import Path
import re
import sys


SOURCE_ROOT = Path(__file__).resolve().parents[2]
ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else SOURCE_ROOT
DIFF = ROOT / "tests/diff"


def rows(example, function):
    path = DIFF / example / "inputs" / f"{function}.jsonl"
    assert path.is_file(), f"missing dispatched input: {path}"
    result = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    assert result, f"empty input file: {path}"
    return result


def dispatched_inputs():
    """Read the explicit function names from both harness dispatch conventions."""
    expected = set()
    for harness in sorted((SOURCE_ROOT / "tests/diff").glob("*/harness.zig")):
        example = harness.parent.name
        source = harness.read_text()
        direct = re.findall(
            r'common\.forEach(?:Mem)?Line\(gpa,\s*"' + example + r'",\s*"([^"\n]+)"',
            source,
        )
        indirect = re.findall(r'try run[A-Za-z]*\((?:gpa|arena),(?:\s*[A-Za-z0-9_]+,)?\s*"([^"\n]+)"', source)
        assert direct or indirect, f"no dispatched functions found in {harness}"
        expected.update((example, name) for name in direct + indirect)
    return expected


def float_edges(width, tokens, context):
    """Require critical exact edges and both infinity signs in the deterministic half."""
    exponent_bits, fraction_bits = {
        16: (5, 10), 32: (8, 23), 64: (11, 52), 80: (15, 63), 128: (15, 112)
    }[width]
    explicit_integer = width == 80
    exponent_shift = fraction_bits + explicit_integer
    exponent_max = (1 << exponent_bits) - 1
    sign = 1 << (width - 1)
    integer_bit = (1 << fraction_bits) if explicit_integer else 0
    bias = (1 << (exponent_bits - 1)) - 1
    bits = {int(token, 16) for token in tokens}
    positive_edges = {
        0, 1, (1 << fraction_bits) - 1,
        (1 << exponent_shift) | integer_bit,
        ((exponent_max - 1) << exponent_shift) | integer_bit | ((1 << fraction_bits) - 1),
        (exponent_max << exponent_shift) | integer_bit,
        ((bias + 1) << exponent_shift) | integer_bit | (1 << (fraction_bits - 2)),  # 2.5
    }
    expected = positive_edges | {value | sign for value in positive_edges}
    missing = expected - bits
    assert not missing, f"{context}: missing exact edge bits {sorted(hex(x) for x in missing)}"
    assert any(
        ((value >> exponent_shift) & exponent_max) == exponent_max
        and value & ((1 << fraction_bits) - 1)
        for value in bits
    ), f"{context}: no NaN edge"
    if explicit_integer:
        invalid = {0x00010000000000000001, 0x7fff0000000000000000,
                   0x7fff4000000000000000, 0x00008000000000000000}
        assert invalid <= bits, f"{context}: missing f80 unusual encodings"
        # A raw decrement across an x87 exponent boundary makes an unnormal, not a predecessor.
        for power in (31, 32, 63, 64):
            exponent = bias + power
            value = (exponent << 64) | integer_bit
            neighbors = {((exponent - 1) << 64) | ((1 << 64) - 1), value, value + 1}
            assert neighbors <= bits, f"{context}: missing valid f80 neighbors of 2^{power}"


TIE_ROWS = 5


def check_floats():
    checked = 0
    for width in (16, 32, 64, 80, 128):
        data = rows("floatops", f"op{width}")
        # 300 rows per selector, then the deterministic round-half-even tie rows
        # (`writeTieRows` in tests/diff/gen_inputs.zig) on selectors 0 and 1.
        ties = data[26 * 300:]
        assert len(ties) == TIE_ROWS and {row[0] for row in ties} <= {0, 1}, f"op{width}: tie rows"
        data = data[:26 * 300]
        for selector in range(26):
            selected = [row for row in data if row[0] == selector]
            assert len(selected) == 300
            edge_pairs = {(int(row[1], 16), int(row[2], 16)) for row in selected[:150]}
            sign = 1 << (width - 1)
            assert {(0, sign), (sign, 0)} <= edge_pairs, f"op{width} selector {selector}: no signed-zero corners"
            edge_count = 47 if width == 80 else 43
            edges = [int(row[1], 16) for row in selected[:edge_count]]
            assert {(value, value) for value in edges} <= edge_pairs, \
                f"op{width} selector {selector}: missing diagonal edges"
            corners = ((0, 1), (1, 0), (20, 21), (21, 20), (20, 0),
                       (0, 20), (21, 1), (1, 21), (22, 23))
            assert {(edges[a], edges[b]) for a, b in corners} <= edge_pairs, \
                f"op{width} selector {selector}: missing zero/infinity/NaN corners"
            # In particular, unary selectors ignore rhs, so rhs coverage cannot replace lhs.
            for operand in (1, 2):
                float_edges(width, [row[operand] for row in selected[:150]],
                            f"op{width} selector {selector} operand {operand}")
                checked += 1
            if selector == 4:
                float_edges(width, [row[3] for row in selected[:150]],
                            f"op{width} mulAdd addend")
                checked += 1
    for example, function in (("floatops", "cmp64"), ("floatops", "divExact64"),
                              ("floats", "hypot2")):
        data = rows(example, function)
        assert len(data) == 300
        for operand in (0, 1):
            float_edges(64, [row[operand] for row in data[:150]], f"{function} operand {operand}")
            checked += 1
    data = rows("floatconv", "f80ToF64")
    assert len(data) == 300
    float_edges(80, [row[0] for row in data[:47]], "f80ToF64 operand")
    checked += 1
    return checked


def check_vectors():
    minimum = -(1 << 31)
    for function in ("vDiv", "vMod"):
        data = rows("vectors", function)
        assert len(data) == 300
        for lane in range(4):
            assert any(
                a[lane] == minimum and b[lane] == -1 and all(value != 0 for value in b)
                and all((a[i], b[i]) != (minimum, -1) for i in range(4) if i != lane)
                for a, b in data
            ), f"{function}: no isolated minInt/-1 in lane {lane}"
            assert any(
                b[lane] == 0 and all(b[i] != 0 for i in range(4) if i != lane)
                and all((a[i], b[i]) != (minimum, -1) for i in range(4))
                for a, b in data
            ), f"{function}: no isolated zero divisor in lane {lane}"


def main():
    expected = dispatched_inputs()
    actual = {(path.parent.parent.name, path.stem) for path in DIFF.glob("*/inputs/*.jsonl")}
    assert actual == expected, f"input inventory: missing={sorted(expected - actual)}, extra={sorted(actual - expected)}"
    for example, function in sorted(expected):
        rows(example, function)
    assert rows("threads", "disjoint") == rows("threads", "race")
    for example, functions in {
        "threadsync": ("mutexCounter", "handoff", "waitGroup"),
        "iogroup": ("groupCounter", "groupConcurrent"),
        "sync": ("semaphoreCounter", "rwLockRead"),
    }.items():
        for function in functions:
            assert rows(example, function) == [[]] * 20, f"{example}.{function}: expected 20 no-argument runs"
    float_groups = check_floats()
    check_vectors()
    print(f"Input coverage passed: {len(expected)} dispatched files; {float_groups} float edge groups; "
          "8 isolated vector overflow cases and 8 isolated zero-divisor cases.")


if __name__ == "__main__":
    main()
