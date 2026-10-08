#!/usr/bin/env python3
"""CLI regression: Zig's shift-count safety check `shiftRhsTooBig` maps to `.overflow`.

`air/<version>/` is the patched-compiler AIR of `shift.zig` (x86_64-linux, ReleaseSafe) for
0.14.1, 0.15.2 and 0.16.0. Every version emits a noreturn call to
`debug.FullPanic((function 'defaultPanic')).shiftRhsTooBig` for the u40/i40 shifts and none for
the u64 one. The translator must accept them and throw `.overflow` (the constructor of the
`shlOverflow`/`shrOverflow` checks of the same Sema shift path, scripts/panic-policy.tsv) on
that branch only; a nearby foreign callee name stays rejected. Never builds or invokes compilers.
Native agreement is qualified by ../qualify.py (`panics` lanes).
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
VERSIONS = ["0.14.1", "0.15.2", "0.16.0"]
CALLEE = "debug.FullPanic((function 'defaultPanic')).shiftRhsTooBig"
ARGS = ["--namespace", "Shift", "--prefix", "shift."]


def translate(binary, air, directory):
    out = directory / "Gen.lean"
    out.write_text("sentinel\n")
    result = subprocess.run([str(binary), str(air), "-o", str(out), *ARGS], text=True,
                            capture_output=True, check=False, timeout=60)
    return result, out.read_text()


def defs(text):
    """Generated top-level `def` bodies by name."""
    out, name = {}, None
    for line in text.splitlines():
        if line.startswith("def "):
            name = line.split()[1]
            out[name] = []
        elif line and not line[0].isspace():
            name = None
        if name:
            out[name].append(line)
    return {k: "\n".join(v) for k, v in out.items()}


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else HERE.parents[3] / ".lake/build/bin/air2lean")
    checks = 0
    for version in VERSIONS:
        air = HERE / "air" / version
        texts = {p.name: p.read_text() for p in sorted(air.glob("*.json"))}
        assert sorted(texts) == ["shift.shl40.json", "shift.shl64.json", "shift.shr40.json"], texts.keys()
        for name, text in texts.items():
            assert (f'"{CALLEE}"' in text) == ("40" in name), (version, name)
        with tempfile.TemporaryDirectory(prefix="air2lean-shift-panic-") as d:
            result, gen = translate(binary, air, Path(d))
            assert result.returncode == 0, (version, result.stderr)
            bodies = defs(gen)
            for fn in ("shl40", "shr40"):
                assert bodies[fn].count("throw .overflow") == 1, (version, fn, bodies[fn])
            assert "throw" not in bodies["shl64"], (version, bodies["shl64"])
            checks += 1

        # A callee outside the table is still rejected, without replacing the output.
        with tempfile.TemporaryDirectory(prefix="air2lean-shift-panic-") as d:
            bad = Path(d) / "air"
            bad.mkdir()
            doc = json.loads(texts["shift.shl40.json"])
            (bad / "shift.shl40.json").write_text(
                json.dumps(doc).replace(json.dumps(CALLEE), json.dumps(CALLEE + "X")))
            result, gen = translate(binary, bad, Path(d))
            assert result.returncode == 1, (version, result.returncode, result.stderr)
            assert "is not a known panic-handler function" in result.stderr, result.stderr
            assert gen == "sentinel\n", "a rejected input replaced the output"
            checks += 1
    print(f"shift-count panic CLI regression: {checks} checks passed")


if __name__ == "__main__":
    main()
