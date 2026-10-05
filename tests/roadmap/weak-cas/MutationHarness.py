#!/usr/bin/env python3
"""Bounded mutation-script tests using copied sources and mock tools only."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = (ROOT / "scripts/mutate.sh").read_text()
SOURCE_PATHS = re.findall(r'^[a-z_]+="((?:ZigLean|Proofs|tests)/[^"$]+)"$', SCRIPT, re.M)


class MutationHarnessTests(unittest.TestCase):
    def run_fixture(self, shard, mode="detected", duplicate_import=False):
        with tempfile.TemporaryDirectory(prefix="weak-cas-mutation-mock-") as temporary:
            work = Path(temporary) / "repo"
            work.mkdir()
            for relative in [*SOURCE_PATHS, "scripts/mutate.sh", "scripts/mutation-shards.txt"]:
                dest = work / relative
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / relative, dest)
            for path in (ROOT / "examples").glob("*/*.zig"):
                dest = work / path.relative_to(ROOT)
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(path, dest)
            conc = work / "ZigLean/Conc.lean"
            if duplicate_import:
                conc.write_text(conc.read_text() + "import ZigLean.Conc.WeakCas\n")
            originals = {relative: (work / relative).read_bytes() for relative in SOURCE_PATHS}
            baseline = Path(temporary) / "baseline"
            shutil.copytree(work / "ZigLean", baseline / "ZigLean")
            tools = Path(temporary) / "mock-tools"
            tools.mkdir()
            (tools / "zig").write_text("#!/usr/bin/env bash\nexit 0\n")
            (tools / "lake").write_text('''#!/usr/bin/env bash
set -euo pipefail
grep -Fxq 'import ZigLean.Conc.WeakCas' ZigLean/Conc.lean || exit 91
printf 'full-import:%s\n' "$*" >> "$MOCK_EVENTS"
if [ "$1" = build ] && ! diff -qr "$MOCK_BASELINE/ZigLean" ZigLean >/dev/null; then
  echo 'error: Fixture.lean:1:1: expected mock proof rejection'
  exit 1
fi
exit 0
''')
            (work / "scripts/diff.sh").write_text('''#!/usr/bin/env bash
set -euo pipefail
if grep -Fxq 'import ZigLean.Conc.WeakCas' ZigLean/Conc.lean; then
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

    def test_exact_import_guard_restores_duplicate_input(self):
        result, _ = self.run_fixture(1, duplicate_import=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("expected exactly one WeakCas proof import", result.stderr)

    def test_only_new_proof_edge_is_omitted(self):
        modules = {"ZigLean": ROOT / "ZigLean.lean"}
        modules.update({".".join(p.relative_to(ROOT).with_suffix("").parts): p
                        for p in (ROOT / "ZigLean").rglob("*.lean")})
        def closure(omit):
            pending, seen = ["ZigLean"], set()
            while pending:
                name = pending.pop()
                if name in seen or name not in modules:
                    continue
                seen.add(name)
                for imported in re.findall(r'^import\s+(\S+)', modules[name].read_text(), re.M):
                    if omit and name == "ZigLean.Conc" and imported == "ZigLean.Conc.WeakCas":
                        continue
                    pending.append(imported)
            return seen
        full, runtime = closure(False), closure(True)
        self.assertIn("ZigLean.Mem.Lemmas", full)
        self.assertNotIn("ZigLean.Mem.Lemmas", runtime)
        self.assertIn("ZigLean.Conc.Call", runtime)
        self.assertIn("ZigLean.Mem.Thread", runtime)
        self.assertIn("ZigLean.Conc.WeakCas", full)
        self.assertIn("def cmpxchgWeakC", (ROOT / "ZigLean/Conc/Call.lean").read_text())


if __name__ == "__main__":
    unittest.main()
