#!/usr/bin/env python3
"""Per-function verification-condition report for generated Lean code (P02).

Two modes, combinable:

* ``--import MOD --namespace NS``: write a temporary Lean file that imports ``ZigLean.VC`` and
  ``MOD`` and runs ``#vc_extract_all NS``. Every generated ``Zig.Result``/``Zig.MemM`` function
  of ``NS`` is reported as ``extracted``, ``loop-request`` (an explicit invariant + variant is
  required for the named loop/AIR instruction; nothing is guessed) or ``refused`` (with the
  reason, e.g. a call without a ``@[vc_contract]``).
* ``FILE.lean``: check a contract file. Each ``vc_gen?`` in it reports the obligations of one
  contracted function, separated into safety, functional result, memory effect and error
  return, with the path conditions each one is under.

The script only reads the ``vc-report {json}`` lines that ``ZigLean/VC/Extract.lean`` logs; the
Lean checker decides everything. It runs ``lake env lean --json`` from the repository root,
so the imported modules must already be built. The exit status is Lean's.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "vc-report "


def run_lean(path: Path) -> tuple[int, list[dict]]:
    proc = subprocess.run(["lake", "env", "lean", "--json", str(path)], cwd=ROOT,
                          capture_output=True, text=True)
    messages = []
    for line in proc.stdout.splitlines():
        try:
            messages.append(json.loads(line))
        except json.JSONDecodeError:
            messages.append({"severity": "error", "data": line})
    if proc.stderr.strip():
        messages.append({"severity": "error", "data": proc.stderr.strip()})
    return proc.returncode, messages


def reports(messages: list[dict]) -> list[dict]:
    out = []
    for message in messages:
        for line in str(message.get("data", "")).splitlines():
            if line.startswith(PREFIX):
                out.append(json.loads(line[len(PREFIX):]))
    return out


def lean_errors(messages: list[dict]) -> list[str]:
    return [str(m.get("data", "")) for m in messages
            if m.get("severity") == "error" and PREFIX not in str(m.get("data", ""))]


def namespace_source(imports: list[str], namespaces: list[str]) -> str:
    lines = ["import ZigLean.VC"] + [f"import {module}" for module in imports] + [""]
    lines += [f"#vc_extract_all {ns}" for ns in namespaces]
    return "\n".join(lines) + "\n"


def describe(report: dict) -> list[str]:
    name, status = report["function"], report["status"]
    if status == "extracted":
        return [f"{name}: extracted as {report['program']}"]
    if status == "refused":
        reason = " ".join(report["reason"].split())
        return [f"{name}: refused: {reason}"]
    if status == "loop-request":
        lines = [f"{name}: loop request (no invariant is guessed)"]
        for request in report["requests"]:
            where = (f"AIR instruction %{request['instruction']}"
                     if request["instruction"] is not None else "an unnamed AIR loop")
            lines.append(f"  invariant + variant required for {request['loop']} at {where}")
        return lines
    if status == "obligations":
        obligations = report["obligations"]
        counts: dict[str, int] = {}
        for item in obligations:
            counts[item["kind"]] = counts.get(item["kind"], 0) + 1
        summary = ", ".join(f"{kind} {counts[kind]}"
                            for kind in ("safety", "result", "memory", "error") if kind in counts)
        open_count = sum(1 for item in obligations if item["closed_by"] is None)
        lines = [f"{name}: {len(obligations)} obligations ({summary}); {open_count} open"]
        for item in obligations:
            closed = f" (closed by {item['closed_by']})" if item["closed_by"] else ""
            lines.append(f"  [{item['case']}] {item['kind']}: {item['label']}{closed}")
            for given in item["given"]:
                lines.append(f"      {given}")
            lines.append(f"      ⊢ {item['goal']}")
        return lines
    return [f"{name}: {status}"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("files", nargs="*", type=Path, help="contract files using vc_gen?")
    parser.add_argument("--import", dest="imports", action="append", default=[],
                        help="module with generated code (namespace mode)")
    parser.add_argument("--namespace", action="append", default=[],
                        help="namespace whose generated functions are extracted")
    parser.add_argument("--json", action="store_true", help="print the reports as JSON")
    args = parser.parse_args()
    if not args.files and not args.namespace:
        parser.error("give contract files and/or --namespace")
    if args.namespace and not args.imports:
        parser.error("--namespace needs at least one --import")

    status = 0
    collected: list[dict] = []
    errors: list[str] = []
    if args.namespace:
        with tempfile.TemporaryDirectory(prefix="vc-report-") as tmp:
            path = Path(tmp) / "VcReport.lean"
            path.write_text(namespace_source(args.imports, args.namespace))
            code, messages = run_lean(path)
        status = status or code
        collected += reports(messages)
        errors += lean_errors(messages)
    for path in args.files:
        code, messages = run_lean(path.resolve())
        status = status or code
        collected += reports(messages)
        errors += lean_errors(messages)

    if args.json:
        print(json.dumps(collected, indent=2, sort_keys=True, ensure_ascii=False))
    else:
        for report in collected:
            print("\n".join(describe(report)))
    for error in errors:
        print(f"lean error: {error}", file=sys.stderr)
    return status


if __name__ == "__main__":
    os.environ.setdefault("PYTHONDONTWRITEBYTECODE", "1")
    sys.exit(main())
