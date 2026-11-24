#!/usr/bin/env python3
"""The translator's CPU-feature table of inline-asm instructions against the Zig compiler's own
tables (A02 decision D1, premise ASM-09; `Air2Lean/AsmFeatures.lean`).

    air2lean --print-asm-feature-table | feature_table.py - ZIG_SOURCE

ZIG_SOURCE is the pristine compiler source tree of Zig 0.17.1 (`scripts/cas.py src 0.17.1`).

1. Every feature name of the table is a `std.Target.<arch>.Feature` name
   (`lib/std/Target/x86.zig`, `aarch64.zig`): the spelling of `profile.features`.
2. x86_64: every mnemonic of the table is a mnemonic of `src/codegen/x86_64/encodings.zon`, and
   its features are the feature column of that file over the general-register rows, without
   the x86-64 base (`BASE`), except the documented stricter rows (`STRICTER`).
3. aarch64: no pattern of a feature-free mnemonic has a `.requires` in
   `src/codegen/aarch64/instructions.zon`. (That file has no `crc32*` pattern; `crc` is checked
   as a feature name only.)

A mnemonic of the Zig tables that the translator's table lacks is not an error: the translator
rejects it (fail closed). Exit status 1 with one line per difference.
"""
import json
import re
import sys
from pathlib import Path

# Features of the x86-64 base (psABI level x86-64-v1; every CPU that runs 64-bit code has them)
# and the encoding table's own mode markers.
BASE = {"none", "64bit", "cmov", "mmx", "sse", "sse2"}
# The table is stricter than encodings.zon here (LLVM X86.td `HasCX16`).
STRICTER = {"cmpxchg16b": {"cx16"}}
# Operand kinds outside the general-register subset.
OTHER_OPERAND = re.compile(r"^(xmm|ymm|zmm|mm|st|sreg|cr|dr)")
ROW = re.compile(r'^\s*\.\{\s*\.(@"[^"]+"|\w+),\s*\.\w+,\s*\.\{([^}]*)\},\s*\.\{[^}]*\},\s*\d+,\s*\.\w+,'
                 r'\s*\.(@"[^"]+"|\w+)\s*\},', re.M)


def unquote(name):
    return name[2:-1] if name.startswith('@"') else name


def feature_names(path):
    text = path.read_text()
    body = text[text.index("pub const Feature = enum {"):]
    return set(unquote(n) for n in re.findall(r'^\s+(@"[^"]+"|\w+),$', body[:body.index("};")], re.M))


def x86_encodings(path):
    """mnemonic -> features of its general-register rows, without BASE and 32-bit-only rows."""
    found = {}
    for mnemonic, operands, feature in ROW.findall(path.read_text()):
        kinds = [o.strip().lstrip(".") for o in operands.split(",") if o.strip()]
        feature = unquote(feature)
        if any(OTHER_OPERAND.match(k) for k in kinds) or feature.endswith("32bit"):
            continue
        feature = feature.removesuffix(" 64bit")
        found.setdefault(unquote(mnemonic), set()).update({feature} - BASE)
    return found


def aarch64_requires(path):
    """mnemonic -> union of `.requires` over its patterns."""
    found = {}
    for entry in re.split(r"\n    \.\{\n", path.read_text())[1:]:
        pattern = re.search(r'\.pattern = "([^"]*)"', entry)
        if pattern is None:
            continue
        requires = re.search(r"\.requires = \.\{([^}]*)\}", entry)
        names = {n.strip().lstrip(".") for n in requires.group(1).split(",") if n.strip()} if requires else set()
        found.setdefault(pattern.group(1).split()[0].lower(), set()).update(names)
    return found


def main(table_path, source):
    table = json.loads(sys.stdin.read() if table_path == "-" else Path(table_path).read_text())
    source = Path(source)
    errors = []
    lib = {"x86_64": "x86.zig", "aarch64": "aarch64.zig"}
    for arch, rows in table["targets"].items():
        known = feature_names(source / "lib/std/Target" / lib[arch])
        for row in rows:
            for feature in row["features"]:
                if feature not in known:
                    errors.append(f"{arch}: feature '{feature}' is not a std.Target feature name")
    encodings = x86_encodings(source / "src/codegen/x86_64/encodings.zon")
    checked = 0
    for row in table["targets"]["x86_64"]:
        if row["prefix"]:
            continue  # prefixes are not rows of encodings.zon (`Instruction.Prefix`)
        for mnemonic in row["mnemonics"]:
            if mnemonic not in encodings:
                errors.append(f"x86_64: '{mnemonic}' has no general-register row in encodings.zon")
                continue
            want = STRICTER.get(mnemonic, encodings[mnemonic])
            if mnemonic in STRICTER and not encodings[mnemonic] <= want:
                errors.append(f"x86_64: '{mnemonic}': STRICTER {sorted(want)} is weaker than encodings.zon")
            if set(row["features"]) != want:
                errors.append(f"x86_64: '{mnemonic}' has features {row['features']}, encodings.zon {sorted(want)}")
            checked += 1
    requires = aarch64_requires(source / "src/codegen/aarch64/instructions.zon")
    for row in table["targets"]["aarch64"]:
        for mnemonic in row["mnemonics"]:
            if mnemonic in requires:
                if requires[mnemonic] != set(row["features"]):
                    errors.append(f"aarch64: '{mnemonic}' has features {row['features']}, "
                                  f"instructions.zon {sorted(requires[mnemonic])}")
                checked += 1
            elif not row["features"]:
                errors.append(f"aarch64: feature-free '{mnemonic}' has no pattern in instructions.zon")
    for entry in table["allowlist"]:
        if "error" in entry:
            errors.append(f"allowlist {entry['template']!r}: {entry['error']}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"asm feature table: {checked} mnemonics agree with the Zig 0.17.1 tables; "
          f"{len(table['allowlist'])} allowlist entries covered")
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1], sys.argv[2]))
