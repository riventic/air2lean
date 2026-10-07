#!/usr/bin/env python3
"""Built-translator check for `air2lean --timing-json` (run after `lake build air2lean`).

Preservation evidence for the timing flag: on every budgeted workload, the emitted
Lean is byte-identical with and without the flag, and the timing report has the
documented schema. Never invokes Zig, Lake or Lean.
"""

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("perf_budgets", ROOT / "scripts/perf-budgets.py")
perf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(perf)
PHASES = {"read", "renumber", "parse", "normalize", "check", "emit", "write"}


def run(command):
    return subprocess.run([str(part) for part in command], capture_output=True, text=True, timeout=120)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--air2lean", type=Path, default=ROOT / ".lake/build/bin/air2lean")
    args = parser.parse_args()
    budgets = perf.load_json(perf.BUDGETS)
    with tempfile.TemporaryDirectory(prefix="air2lean-timing-") as temporary:
        work = Path(temporary)
        for workload in budgets["workloads"]:
            ident = workload["id"]
            air = perf.stage_air(ROOT, workload["air"], work / ident / "air")
            base = [args.air2lean, air, "--namespace", workload["namespace"],
                    "--prefix", workload["prefix"], *workload["translate_args"]]
            plain, timed, report = (work / ident / name for name in ("plain.lean", "timed.lean", "t.json"))
            first = run([*base, "-o", plain])
            second = run([*base, "-o", timed, "--timing-json", report])
            assert first.returncode == 0 and second.returncode == 0, (ident, first.stderr, second.stderr)
            assert plain.read_bytes() == timed.read_bytes(), f"{ident}: --timing-json changed the output"
            data = json.loads(report.read_text())
            assert data["schema"] == perf.TIMING_SCHEMA, data
            assert set(data["phases_ns"]) == PHASES, data
            assert all(isinstance(value, int) and value >= 0 for value in data["phases_ns"].values())
            assert data["output_bytes"] == plain.stat().st_size, (ident, data)
            assert data["files"] == len(list(air.glob("*.json"))), (ident, data)
            print(f"{ident}: identical output, {data['functions']} functions, "
                  f"{sum(data['phases_ns'].values()) / 1e6:.1f} ms")
        air = work / "basic" / "air"
        duplicate = run([args.air2lean, air, "-o", work / "d.lean", "--namespace", "B",
                         "--timing-json", work / "a.json", "--timing-json", work / "b.json"])
        assert duplicate.returncode != 0 and "duplicate --timing-json" in duplicate.stderr, duplicate.stderr
        missing = run([args.air2lean, air, "-o", work / "m.lean", "--namespace", "B", "--timing-json"])
        assert missing.returncode != 0 and "missing value for --timing-json" in missing.stderr, missing.stderr
        clobber = run([args.air2lean, air, "-o", work / "c.lean", "--namespace", "B",
                       "--timing-json", work / "c.lean"])
        assert clobber.returncode != 0 and "must not name the -o output" in clobber.stderr, clobber.stderr
        assert not (work / "c.lean").exists()
        failing = run([args.air2lean, work / "nonexistent", "-o", work / "f.lean", "--namespace", "B",
                       "--timing-json", work / "f.json"])
        assert failing.returncode != 0 and not (work / "f.json").exists()
    print("timing CLI: ok")


if __name__ == "__main__":
    main()
