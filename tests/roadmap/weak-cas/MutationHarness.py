#!/usr/bin/env python3
"""Bounded mutation-script tests using copied sources and mock tools only."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = (ROOT / "scripts/mutate.sh").read_text()
SOURCE_PATHS = re.findall(r'^[a-z_]+="((?:ZigLean|Proofs|tests)/[^"$]+)"$', SCRIPT, re.M)


class MutationHarnessTests(unittest.TestCase):
    def run_fixture(self, shard, mode="detected"):
        with tempfile.TemporaryDirectory(prefix="weak-cas-mutation-mock-") as temporary:
            work = Path(temporary) / "repo"
            work.mkdir()
            for relative in [*SOURCE_PATHS, "scripts/mutate.sh", "scripts/zig-default.sh", "scripts/compat.py",
                             "compatibility.json", "scripts/mutation-shards.txt", "scripts/example-selection.sh"]:
                dest = work / relative
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / relative, dest)
            for path in [*(ROOT / "examples").glob("*/*.zig"), *(ROOT / "examples").glob("*/zig-versions")]:
                dest = work / path.relative_to(ROOT)
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(path, dest)
            originals = {relative: (work / relative).read_bytes() for relative in SOURCE_PATHS}
            baseline = Path(temporary) / "baseline"
            shutil.copytree(work / "ZigLean", baseline / "ZigLean")
            tools = Path(temporary) / "mock-tools"
            tools.mkdir()
            # The mock translation is a pure function of the Zig source (mutate.sh aborts when a
            # mutation leaves every generated file unchanged): zig records the source, `lake exe
            # air2lean` writes it into the output as a Lean comment.
            (tools / "zig").write_text('#!/usr/bin/env bash\ncp "${@: -1}" "$ZIG_AIR_JSON_DIR/source.zig"\n')
            # The default example selection skips `asm` off x86_64, which would skip mutation (i)
            # on an arm64 host: pin the architecture so every shard runs all its mutations.
            (tools / "uname").write_text('#!/usr/bin/env bash\n[ "${1:-}" = -m ] && echo x86_64 || exec /usr/bin/uname "$@"\n')
            (tools / "lake").write_text('''#!/usr/bin/env bash
set -euo pipefail
if [ "$1" = exe ]; then
  air=$3
  out=
  while [ $# -gt 0 ]; do [ "$1" = -o ] && out=$2; shift; done
  { echo '/- mock translation'; cat "$air/source.zig"; echo '-/'; } > "$out"
  exit 0
fi
printf 'full-import:%s\n' "$*" >> "$MOCK_EVENTS"
if [ "$1" = build ] && ! diff -qr "$MOCK_BASELINE/ZigLean" ZigLean >/dev/null; then
  echo 'error: Fixture.lean:1:1: expected mock proof rejection'
  exit 1
fi
exit 0
''')
            (work / "scripts/diff.sh").write_text('''#!/usr/bin/env bash
set -euo pipefail
if ! grep -qx baseline "$MOCK_EVENTS" 2>/dev/null; then  # the first run is the unmutated baseline
  echo baseline >> "$MOCK_EVENTS"
  echo 'TOTAL: mismatch=0'
  exit 0
fi
echo differential >> "$MOCK_EVENTS"
case "$MOCK_MODE" in
  missing-total) echo 'error: Fixture.lean:1:1: mock build failure'; exit 1 ;;
  signal) kill -TERM "$PPID"; exit 143 ;;
  no-evidence) echo 'TOTAL: mismatch=0'; exit 1 ;;
  *) echo 'TOTAL: mismatch=1'; exit 1 ;;
esac
''')
            for path in tools.iterdir():
                path.chmod(0o755)
            events = Path(temporary) / "events"
            env = dict(os.environ, PATH=str(tools) + os.pathsep + os.environ["PATH"],
                       AIR2LEAN_ZIG_AIR=str(tools / "zig"), AIR2LEAN_MUTATION_SHARD=str(shard),
                       AIR2LEAN_MUTATION_SHARDS="5", MOCK_MODE=mode, MOCK_EVENTS=str(events),
                       MOCK_BASELINE=str(baseline), TMPDIR=temporary)
            env.pop("AIR2LEAN_EXAMPLES", None)
            result = subprocess.run(["bash", "scripts/mutate.sh"], cwd=work, env=env,
                                    capture_output=True, text=True, timeout=10)
            for relative, source in originals.items():
                self.assertEqual((work / relative).read_bytes(), source, relative)
            return result, events.read_text().splitlines()

    def test_all_five_shards_keep_baselines_and_proof_builds_full(self):
        for shard in range(1, 6):
            with self.subTest(shard=shard):
                result, events = self.run_fixture(shard)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                selected = (ROOT / "scripts/mutation-shards.txt").read_text().splitlines()[shard - 1].split()
                detected = re.findall(r'^mutation \(([a-z]+)\): detected', result.stdout, re.M)
                self.assertEqual(set(detected), set(selected))
                self.assertIn("baseline", events)
                self.assertIn("differential", events)
                # Shard 2 contains only differential mutations; every other shard
                # includes a proof-target mutation and its unmutated proof baseline.
                self.assertEqual(any(e.startswith("full-import:build") for e in events), shard != 2)

    def test_missing_total_is_rejected_and_restored(self):
        result, _ = self.run_fixture(1, "missing-total")
        self.assertEqual(result.returncode, 1)
        self.assertIn("no TOTAL line", result.stderr)
        self.assertNotIn("mutation (k): detected", result.stdout)

    def test_nonzero_exit_without_differential_evidence_is_rejected(self):
        result, _ = self.run_fixture(1, "no-evidence")
        self.assertEqual(result.returncode, 1)
        self.assertIn("mutation (k): NOT detected", result.stdout)

    def test_signal_restores_all_sources(self):
        result, _ = self.run_fixture(1, "signal")
        self.assertEqual(result.returncode, 143)
        self.assertIn("mutation interrupted by TERM", result.stderr)

    def test_mutate_does_not_edit_the_runtime_root(self):
        # The differential window builds the runtime root as committed: no import is cut out of
        # it (the proof-only modules are kept out by assurance/runtime-root.json instead).
        self.assertNotIn("ZigLean/Conc.lean", SCRIPT)
        self.assertNotIn("WeakCas", SCRIPT)

    def test_runtime_root_reaches_no_proof_only_module(self):
        result = subprocess.run([sys.executable, "-B", "scripts/lean-deps.py", "--runtime-root", "check"],
                                cwd=ROOT, capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
