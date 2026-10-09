#!/usr/bin/env python3
"""Property checks of content-addressed instance keys (docs/air-json.md §Instances).

usage: check_instances.py WORK PROGRAM...

WORK/<program>/ holds the AIR export of tests/roadmap/instance-identity/<program>.zig and
WORK/<program>.lean its translation. Each program function `<program>.<f>` calls one generic
instance; a function name stands for one instantiation in every program.

* every instance and every reference to it has a valid key, the same for one compiler name;
* the same function name (the same instantiation) has the same key in every program and
  source order, and two different instantiations never have the same key;
* one key is one instance body (AIR without compiler names) in every program;
* the translation names each instance `<generic>__anon_<key[:12]>`, and a shared instance has
  the same Lean definition in every program.
"""

import hashlib
import json
from pathlib import Path
import re
import runpy
import sys

INSTANCE = re.compile(r"(.*)__anon_([0-9]+)\Z")
KEY = re.compile(r"[0-9a-f]{64}\Z")
NORMALIZE = runpy.run_path(str(Path(__file__).resolve().parents[3] / "scripts" / "normalize-air.py"))["normalize"]


def fail(message):
    print(f"instance identity: {message}", file=sys.stderr)
    sys.exit(1)


def references(value):
    """Every function reference (an object with `func`) at any depth."""
    if isinstance(value, list):
        for item in value:
            yield from references(item)
    elif isinstance(value, dict):
        if isinstance(value.get("func"), str):
            yield value
        for item in value.values():
            yield from references(item)


def fingerprint(document):
    """The function's AIR without names that depend on the compilation (normalize-air.py)."""
    value = NORMALIZE(document)
    value.pop("name", None)
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def lean_definitions(text):
    """`def <name>` blocks of a generated Lean file, by name: the block up to the next line
    that starts in column 0."""
    blocks, name, lines = {}, None, []
    for line in text.splitlines() + [""]:
        if line and not line[0].isspace():
            if name is not None:
                blocks[name] = "\n".join(lines).rstrip()
            name, lines = None, []
            if line.startswith("def "):
                name = line.split()[1]
        if name is not None:
            lines.append(line)
    return blocks


def program(work, name):
    """(instances: compiler name -> (key, fingerprint), calls: function -> (callee, key),
    Lean definitions)."""
    instances, calls, keys_by_name = {}, {}, {}
    for path in sorted((work / name).glob("*.json")):
        document = json.loads(path.read_text())
        own = document["name"]
        refs = list(references(document.get("body", [])))
        for ref in refs:
            if INSTANCE.match(ref["func"]):
                key = ref.get("instance_key")
                if not isinstance(key, str) or not KEY.match(key):
                    fail(f"{name}: reference to {ref['func']} in {own} has no valid instance_key")
                if keys_by_name.setdefault(ref["func"], key) != key:
                    fail(f"{name}: two keys for {ref['func']}")
        if INSTANCE.match(own):
            key = document.get("instance_key")
            if not isinstance(key, str) or not KEY.match(key):
                fail(f"{name}: instance {own} has no valid instance_key")
            if keys_by_name.setdefault(own, key) != key:
                fail(f"{name}: {own} and a reference to it have different keys")
            instances[own] = (key, fingerprint(document))
        elif own.startswith(name + "."):
            callees = [r for r in refs if INSTANCE.match(r["func"])]
            if len(callees) != 1:
                fail(f"{name}: {own} calls {len(callees)} generic instances, not one")
            calls[own[len(name) + 1:]] = (callees[0]["func"], callees[0]["instance_key"])
    if not calls:
        fail(f"{name}: no program functions exported")
    lean = lean_definitions((work / f"{name}.lean").read_text())
    return instances, calls, lean


def main():
    work, names = Path(sys.argv[1]), sys.argv[2:]
    programs = {name: program(work, name) for name in names}

    # One instantiation (a function name), one key; two instantiations, two keys.
    key_of, call_of = {}, {}
    for name, (_, calls, _) in programs.items():
        for function, (callee, key) in calls.items():
            if key_of.setdefault(function, key) != key:
                fail(f"{function}: key {key} in {name}, {key_of[function]} elsewhere")
            if call_of.setdefault(key, function) != function:
                fail(f"key {key} is both {function} and {call_of[key]}")

    # One key, one instance body; the generic is the same.
    body_of = {}
    for name, (instances, _, _) in programs.items():
        for compiler_name, (key, body) in instances.items():
            if body_of.setdefault(key, body) != body:
                fail(f"key {key} ({compiler_name} in {name}) has two different bodies")

    # The translation: a keyed name, and the same definition in every program.
    definition_of = {}
    for name, (_, calls, lean) in programs.items():
        for function, (callee, key) in calls.items():
            generic = INSTANCE.match(callee).group(1)
            if not generic.startswith("lib."):
                continue
            lean_name = generic.replace(".", "_") + "__anon_" + key[:12]
            if lean_name not in lean:
                fail(f"{name}: no Lean definition {lean_name} for {function}")
            if definition_of.setdefault(lean_name, lean[lean_name]) != lean[lean_name]:
                fail(f"{name}: Lean definition {lean_name} differs from another program's")

    # The compiler's names differ between the programs: the keys do not.
    renamed = {}
    for function, key in key_of.items():
        compiler_names = {programs[n][1][function][0] for n in names if function in programs[n][1]}
        if len(compiler_names) > 1:
            renamed[function] = sorted(compiler_names)
    if not renamed:
        fail("no instance has two compiler names: the programs do not exercise the key")
    shared = sum(1 for f in key_of if sum(f in programs[n][1] for n in names) > 1)
    print(f"instance identity: {len(key_of)} instantiations, {len(key_of)} keys; "
          f"{shared} shared by several programs, {len(renamed)} of them with different compiler "
          f"names; {len(definition_of)} Lean definitions identical across programs")


if __name__ == "__main__":
    main()
