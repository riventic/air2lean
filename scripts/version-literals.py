#!/usr/bin/env python3
"""Lint: Zig version literals belong to the dialect registry (structure audit B3).

Only `Air2Lean/Air/Dialect.lean` (`ZigVersion`, the translator's version registry) may write a
Zig version as a Lean string literal (`"0.17.0"`, `"0.17"`). Every other translator module asks
the `Dialect` (or a `ZigVersion` fact) instead of comparing or listing version strings. Prose that
mentions a version inside a longer literal (a diagnostic, a fixture path) and comments are not
keys and are not checked. The registry's versions must
equal `compatibility.json`'s `zig.versions`, the version registry of the scripts and CI.

The default version is written once, in `compatibility.json` (`zig.default`), and read through
`scripts/compat.py default` (`scripts/zig-default.sh` in shell). The scripts, workflows and tests
must not spell a version in a defaulting position (`${V:-0.16.0}`, `environ.get('V', '0.16.0')`,
`default='0.16.0'`, `version="0.16.0"` keyword defaults); a test double or a check qualified on
exactly one version says so with a `zig-pin` comment on the line. `Dialect.defaultVersion` must
equal `zig.default`.

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
    declared = re.search(r"def defaultVersion : ZigVersion := \.v(\d+)_(\d+)_(\d+)\b",
                         registry.read_text(encoding="utf-8"))
    if not declared or ".".join(declared.groups()) != compat["zig"]["default"]:
        errors.append(f"{REGISTRY}: defaultVersion is {'.'.join(declared.groups()) if declared else 'missing'}, "
                      f"compatibility.json zig.default is {compat['zig']['default']}")
    expected = sorted(v["version"] for v in compat["zig"]["versions"])
    if sorted(spelled) != expected:
        errors.append(f"{REGISTRY}: ZigVersion registry {sorted(spelled)} differs from "
                      f"compatibility.json zig.versions {expected}")
    return errors


# A version literal in a defaulting position of a script, workflow or test.
LITERAL = r"""['"]?\d+\.\d+\.\d+['"]?"""
DEFAULTING = re.compile(
    r":-" + LITERAL +                                              # ${V:-0.16.0}
    r"|\.get\([^()]*," + r"\s*" + LITERAL + r"\s*\)"                 # environ.get('V', '0.16.0')
    r"|\bdefault\s*=\s*" + LITERAL +                              # default='0.16.0'
    r"|\b\w*version\w*\s*=\s*" + LITERAL + r"\s*[,)]"               # def f(version="0.16.0")
    r"|\|\|\s*" + LITERAL)                                         # x || '0.16.0'
# Tests build fixtures with a version parameter (`def fixtures(version="0.16.0")`); there only the
# environment defaults (shell `${V:-…}`, `environ.get`) are the default version.
ENV_DEFAULT = re.compile(r":-" + LITERAL + r"|environ\.get\([^()]*," + r"\s*" + LITERAL + r"\s*\)")
PIN = "zig-pin"
SCANNED = ("scripts", "tools", ".github", "tests")
SUFFIXES = {".sh", ".py", ".yml", ".yaml", ".toml"}
SELF = {"scripts/version-literals.py", "scripts/zig-default.sh", "tests/roadmap/version-literals/test_version_literals.py", "tests/roadmap/support-matrix/test_support_matrix.py"}


def defaulting(root):
    errors = []
    for top in SCANNED:
        if not (root / top).is_dir():
            continue
        for path in sorted((root / top).rglob("*")):
            rel = path.relative_to(root).as_posix()
            if (path.suffix not in SUFFIXES or not path.is_file() or rel in SELF
                    or "/golden/" in rel or "/air/" in rel or "/fixtures/" in rel):
                continue
            try:
                lines = path.read_text(encoding="utf-8").splitlines()
            except UnicodeDecodeError:
                continue
            for number, line in enumerate(lines, 1):
                pattern = ENV_DEFAULT if top == "tests" else DEFAULTING
                if pattern.search(line) and PIN not in line:
                    errors.append(f"{rel}:{number}: version literal in a defaulting position; "
                                  f"read zig.default (scripts/compat.py default, scripts/zig-default.sh) "
                                  f"or mark a test pinned to one version with a `{PIN}` comment")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    errors = violations(args.root.resolve()) + defaulting(args.root.resolve())
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print("version literals: only the dialect registry spells Zig versions")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
