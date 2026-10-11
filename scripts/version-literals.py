#!/usr/bin/env python3
"""Lint: Zig version literals belong to the dialect registry (structure audit B3).

Only `Air2Lean/Air/Dialect.lean` (`ZigVersion`, the translator's version registry) may write a
Zig version as a Lean string literal (`"0.17.0"`, `"0.17"`). Every other translator module asks
the `Dialect` (or a `ZigVersion` fact) instead of comparing or listing version strings. Prose that
mentions a version inside a longer literal (a diagnostic, a fixture path) and comments are not
keys and are not checked. The registry's versions must
equal `compatibility.json`'s `zig.versions`, the version registry of the scripts and CI.

Usage: scripts/version-literals.py [--root DIR]. Exit 1 with one line per violation.
"""
import argparse
import json
from pathlib import Path
import re
import sys

REGISTRY = "Air2Lean/Air/Dialect.lean"
# A literal that is a version (`"0.17.0"`, `"0.17"`): a comparison or a version list. Messages
# and paths that mention a version (`"… Zig 0.17.0's …"`, `"air/0.16.0/…"`) are prose, not keys.
VERSION = re.compile(r"\d+\.\d+(\.\d+)?")
# A character literal that may hold a double quote (`'"'`, `'\\"'`), not a string delimiter.
CHAR_LITERAL = re.compile(r"'(?:\\.|\")'")
# The registry's spelling of each version: `| v0_17_0 => "0.17.0"`.
REGISTRY_ENTRY = re.compile(r'\|\s*\.?v(\d+)_(\d+)_(\d+)\s*=>\s*"(\d+\.\d+\.\d+)"')


def string_literals(text):
    """(line, literal body) of every string literal outside comments, in line order. Lean
    comments are `--` to end of line and nestable `/- … -/` blocks (doc comments included). The
    `{…}` interpolations of an `s!`/`m!`/`f!` literal are code: their own literals are listed
    too, and the outer literal's body keeps only the braces."""
    n = len(text)
    found = []

    def code(i, line, interpolation):
        """Scan code from `i`; inside an interpolation, up to and past its closing brace."""
        depth = braces = 0
        while i < n:
            c = text[i]
            if depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    line, i = line + (c == "\n"), i + 1
                continue
            if text.startswith("/-", i):
                depth, i = 1, i + 2
                continue
            if text.startswith("--", i):
                j = text.find("\n", i)
                i = n if j < 0 else j
                continue
            char = CHAR_LITERAL.match(text, i)
            if char:  # '"' or an escaped character such as '\"'
                i = char.end()
                continue
            if c == '"':
                i, line = literal(i + 1, line, text[i - 2:i] in ("s!", "m!", "f!"))
                continue
            if interpolation and c == "{":
                braces += 1
            elif interpolation and c == "}":
                if not braces:
                    return i + 1, line
                braces -= 1
            line, i = line + (c == "\n"), i + 1
        return i, line

    def literal(i, line, interpolated):
        """Scan a string literal whose opening quote precedes `i`; return past its closing one."""
        start, body = line, []
        while i < n and text[i] != '"':
            if text[i] == "\\":
                body.append(text[i:i + 2])  # the escaped character, possibly a line continuation
                line, i = line + (text[i + 1:i + 2] == "\n"), i + 2
            elif interpolated and text[i] == "{":
                body.append("{}")
                i, line = code(i + 1, line, True)
            else:
                body.append(text[i])
                line, i = line + (text[i] == "\n"), i + 1
        found.append((start, "".join(body)))
        return i + 1, line

    code(0, 1, False)
    return sorted(found, key=lambda entry: entry[0])


def violations(root):
    errors = []
    files = sorted((root / "Air2Lean").rglob("*.lean")) + [root / "Air2Lean.lean"]
    for path in files:
        rel = path.relative_to(root).as_posix()
        if rel == REGISTRY:
            continue
        for line, body in string_literals(path.read_text(encoding="utf-8")):
            if VERSION.fullmatch(body.strip()):
                errors.append(f"{rel}:{line}: Zig version literal \"{body}\" outside "
                              f"{REGISTRY}; ask the Dialect or a ZigVersion fact")
    registry = root / REGISTRY
    if not registry.is_file():
        return errors + [f"{REGISTRY}: missing"]
    spelled = []
    for a, b, c, text in REGISTRY_ENTRY.findall(registry.read_text(encoding="utf-8")):
        if text != f"{a}.{b}.{c}":
            errors.append(f"{REGISTRY}: v{a}_{b}_{c} is spelled '{text}'")
        spelled.append(text)
    compat = json.loads((root / "compatibility.json").read_text(encoding="utf-8"))
    expected = sorted(v["version"] for v in compat["zig"]["versions"])
    if sorted(spelled) != expected:
        errors.append(f"{REGISTRY}: ZigVersion registry {sorted(spelled)} differs from "
                      f"compatibility.json zig.versions {expected}")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    errors = violations(args.root.resolve())
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print("version literals: only the dialect registry spells Zig versions")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
