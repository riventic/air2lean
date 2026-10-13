#!/usr/bin/env python3
"""Record and gate the heartbeat budgets of proofs that raise `maxHeartbeats` (docs/perf-budgets.md).

Lean's heartbeats count elaboration work deterministically (the same toolchain and sources give
the same count on every machine), so a proof's budget is an exact gate: every
`set_option maxHeartbeats N in` of a gated file is the recorded budget of the declaration it
precedes, `N = ceil(measured * tolerance / step) * step` (in Lean's units of 1000 heartbeats), and
the Lean build fails when the proof grows past it. `assurance/heartbeat-budgets.json` lists the
gated files, the policy and one entry per raised declaration.

Subcommands:
  check            static, no Lean: every raise of a gated file is listed with exactly its budget,
                   every entry is a raise in its file, budgets follow the policy (preflight)
  record FILE...   elaborate a measuring copy of each gated FILE (`lake env lean`; run it under
                   scripts/build-guard.py) and rewrite the file's entries from the measurement:
                   every declaration above the default budget is listed
  show             the recorded entries, worst first (for the engine lane)

`record` only writes the JSON; the `set_option` lines are then set to the recorded budgets by hand
and `check` confirms them.
"""

import argparse
import json
import math
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FILE = "assurance/heartbeat-budgets.json"
SCHEMA = "air2lean-heartbeat-budgets/1"
RAISE = re.compile(r"^set_option maxHeartbeats (\d+) in\s*$")
DECL = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+([^\s:({\[]+)")
# Lines between a raise and its declaration: other `… in` prefixes, docstrings, attributes.
PREFIX = re.compile(r"^(?:set_option \S+ \S+ in|omit .* in|attribute \[.*\] .* in|include .* in|@\[.*\]|/--.*|.*-/|\s*)$")
MEASURE = '''
set_option Elab.async false
open Lean Elab Command in
elab "air2lean_count_heartbeats " n:str " in " cmd:command : command => do
  let h0 ← IO.getNumHeartbeats
  elabCommand cmd
  logInfo m!"AIR2LEAN_HEARTBEATS {n.getString} {(← IO.getNumHeartbeats) - h0}"
'''


def load(root):
    data = json.loads((root / FILE).read_text())
    if data.get("schema") != SCHEMA:
        raise ValueError(f"{FILE}: schema is not {SCHEMA}")
    return data


def budget_of(measured, policy):
    """The budget of a declaration measured at `measured` (units of 1000 heartbeats)."""
    step = policy["step"]
    return max(policy["default"], math.ceil(measured * policy["tolerance"] / step) * step)


def declarations(text):
    """(declaration, its raise or None, line of its first prefix) for every declaration, in order.
    Inside a docstring, only its last line (`-/`) ends it."""
    lines = text.splitlines()
    out, start, raise_, in_doc = [], None, None, False
    for number, line in enumerate(lines, 1):
        stripped = line.strip()
        if in_doc:
            in_doc = "-/" not in stripped
            continue
        if stripped.startswith("/--") and "-/" not in stripped:
            in_doc = True
            start = start or number
            continue
        m = RAISE.match(line)
        if m:
            raise_, start = int(m.group(1)), start or number
            continue
        d = DECL.match(line)
        if d:
            out.append((d.group(1), raise_, start or number))
            start, raise_ = None, None
            continue
        if stripped and PREFIX.match(line):
            start = start or number
        else:
            start, raise_ = None, None
    return out


def check(root):
    data = load(root)
    policy, errors = data["policy"], []
    listed = {(e["file"], e["declaration"]): e for e in data["budgets"]}
    for name in data["files"]:
        path = root / name
        if not path.is_file():
            errors.append(f"{name}: gated file is missing")
            continue
        seen = set()
        for decl, raised, _ in declarations(path.read_text()):
            entry = listed.get((name, decl))
            if raised is None:
                if entry:
                    errors.append(f"{name}: `{decl}` is listed but does not raise maxHeartbeats")
                continue
            seen.add(decl)
            if entry is None:
                errors.append(f"{name}: `{decl}` raises maxHeartbeats to {raised} without a recorded "
                              f"budget (scripts/heartbeat-budgets.py record {name})")
            elif raised != entry["budget"]:
                errors.append(f"{name}: `{decl}` raises maxHeartbeats to {raised}, its budget is "
                              f"{entry['budget']}")
        errors += [f"{name}: `{decl}` is listed but has no raise in the file"
                   for file, decl in listed if file == name and decl not in seen]
    for entry in data["budgets"]:
        if entry["file"] not in data["files"]:
            errors.append(f"{entry['file']}: listed but not a gated file")
        if entry["budget"] != budget_of(entry["measured"], policy):
            errors.append(f"{entry['file']}: `{entry['declaration']}` budget {entry['budget']} does not "
                          f"follow the policy for {entry['measured']} measured "
                          f"({budget_of(entry['measured'], policy)})")
        if entry["budget"] <= policy["default"]:
            errors.append(f"{entry['file']}: `{entry['declaration']}` fits the default budget; drop the raise")
    return sorted(set(errors))


def module_of(name):
    return ".".join(Path(name).with_suffix("").parts)


def measure(root, name):
    """{declaration: measured} for every declaration of a gated file (units of 1000)."""
    text = (root / name).read_text()
    lines = text.splitlines()
    starts = {start: decl for decl, _, start in declarations(text)}
    first = next(i for i, line in enumerate(lines) if not line.startswith(("import", "--")) and line.strip())
    body = list(lines[:first]) + MEASURE.splitlines()
    for number, line in enumerate(lines[first:], first + 1):
        if number in starts:
            body.append(f"air2lean_count_heartbeats {json.dumps(starts[number])} in")
        body.append(RAISE.sub("set_option maxHeartbeats 0 in", line))
    with tempfile.TemporaryDirectory(dir=root / ".lake") as work:
        copy = Path(work) / Path(name).name
        copy.write_text("\n".join(body) + "\n")
        run = subprocess.run(["lake", "env", "lean", str(copy)], cwd=root, text=True,
                             capture_output=True)
    if run.returncode != 0:
        raise RuntimeError(f"{name}: the measuring copy does not elaborate:\n{run.stdout}{run.stderr}")
    found = {m.group(1): int(m.group(2)) // 1000
             for m in re.finditer(r"AIR2LEAN_HEARTBEATS (\S+) (\d+)", run.stdout)}
    if set(found) != set(starts.values()):
        raise RuntimeError(f"{name}: measured {sorted(found)}, expected {sorted(starts.values())}")
    return found


def record(root, names):
    data = load(root)
    policy = data["policy"]
    for name in names:
        if name not in data["files"]:
            raise ValueError(f"{name} is not a gated file of {FILE}")
        found = measure(root, name)
        data["budgets"] = [e for e in data["budgets"] if e["file"] != name] + [
            {"file": name, "declaration": decl, "measured": hb, "budget": budget_of(hb, policy)}
            for decl, hb in found.items() if hb > policy["default"] / policy["tolerance"]]
    data["budgets"].sort(key=lambda e: (e["file"], e["declaration"]))
    (root / FILE).write_text(json.dumps(data, indent=2) + "\n")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("check")
    rec = sub.add_parser("record")
    rec.add_argument("files", nargs="+")
    sub.add_parser("show")
    args = parser.parse_args(argv)
    if args.cmd == "check":
        errors = check(ROOT)
        for e in errors:
            print(f"error: {e}")
        return 1 if errors else 0
    if args.cmd == "record":
        record(ROOT, args.files)
        return 0
    for e in sorted(load(ROOT)["budgets"], key=lambda e: -e["measured"]):
        print(f"{e['measured']:>9}  budget {e['budget']:>8}  {e['file']}  {e['declaration']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
