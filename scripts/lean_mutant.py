#!/usr/bin/env python3
"""Helpers of fixture-local Lean mutants (Q02, docs/mutation-map.md).

A fixture's `mutations.py` applies one well-typed change to a retained Lean file (`edit`), builds
the copy and runs the fixture's own check on it with `lean`. The mutant is killed only for the
right reason: `lean` fails, every error lies in the checked file and the declarations that contain
the errors (`error_decls`) include the ones the mutant must break, or the run's output carries the
check's own failure message. A mutant that still passes, or fails elsewhere (an import, a syntax or
type error of the copy), is no kill: `reject` exits with the finding.
"""
import os
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ERROR = re.compile(r"^(?P<file>[^\s:][^:]*):(?P<line>\d+):\d+: error", re.M)
DECL = re.compile(r"^(?:private |protected |partial |noncomputable )*(?:theorem|lemma|def|instance|abbrev)\s+([^\s:({\[]+)")


def edit(text, edits, name):
    """TEXT with each (old, new) of EDITS applied; each `old` occurs exactly once."""
    for old, new in edits:
        if text.count(old) != 1:
            raise SystemExit(f"{name}: mutation anchor not found exactly once: {old!r}")
        text = text.replace(old, new)
    return text


def lean_command():
    """The Lean command of the fixture checks: AIR2LEAN_LEAN, else `lake env lean`."""
    return [os.environ["AIR2LEAN_LEAN"]] if os.environ.get("AIR2LEAN_LEAN") else ["lake", "env", "lean"]


def run(args, *dirs):
    """Run `lean ARGS` with the DIRS first on LEAN_PATH; return (returncode, stdout and stderr)."""
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(d) for d in dirs] + ([env["LEAN_PATH"]] if env.get("LEAN_PATH") else []))
    done = subprocess.run(lean_command() + [str(a) for a in args], env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    return done.returncode, done.stdout


def build_gen(name, target, gen, text, work):
    """Write the mutated translation TEXT to TARGET/GEN and build its olean there (the other
    modules' oleans come from WORK on LEAN_PATH); an invalid mutant aborts the run."""
    (target / gen).parent.mkdir(parents=True, exist_ok=True)
    (target / gen).write_text(text, encoding="utf-8")
    rc, out = run(["-R", target, "-o", (target / gen).with_suffix(".olean"), target / gen], target, work)
    if rc != 0:
        sys.stderr.write(out[-4000:])
        raise SystemExit(f"{name}: the mutated translation does not build (an invalid mutant)")


def error_decls(output, source):
    """(declarations of SOURCE that contain an error, errors reported in another file)."""
    source = Path(source)
    lines = source.read_text(encoding="utf-8").splitlines()
    decls, stray = set(), []
    for match in ERROR.finditer(output):
        if Path(match["file"]).name != source.name:
            stray.append(match[0])
            continue
        for number in range(int(match["line"]) - 1, -1, -1):
            hit = DECL.match(lines[number])
            if hit:
                decls.add(hit[1])
                break
    return decls, stray


def reject(name, rc, output, source, broken):
    """Fail unless the run (RC, OUTPUT) rejected mutant NAME for the right reason: Lean failed, no
    error lies outside SOURCE and every declaration of SOURCE in BROKEN has an error."""
    decls, stray = error_decls(output, source)
    problems = []
    if rc == 0:
        problems.append("the check still passes")
    if stray:
        problems.append(f"errors outside {Path(source).name}: {stray[:3]}")
    missing = sorted(set(broken) - decls)
    if missing:
        problems.append(f"no error in {missing} (errors in {sorted(decls)})")
    if problems:
        sys.stderr.write(output[-4000:])
        raise SystemExit(f"{name}: SURVIVED or rejected for another reason: " + "; ".join(problems))
    print(f"{name}: rejected, errors in {sorted(decls)}")
