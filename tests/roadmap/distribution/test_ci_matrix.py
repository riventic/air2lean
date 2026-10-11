#!/usr/bin/env python3
"""scripts/ci-matrix.py: the CI rows follow compatibility.json; a stale region fails. Offline."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts/ci-matrix.py'
COPIED = ('.github/workflows/ci.yml', 'compatibility.json', 'scripts/mutation-shards.txt',
          'scripts/example-selection.sh')


class CiMatrix(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='air2lean ci-matrix ')
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        for rel in COPIED:
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, self.root / rel)
        shutil.copytree(ROOT / 'examples', self.root / 'examples')

    def run_script(self, mode):
        return subprocess.run([sys.executable, str(SCRIPT), mode, '--root', str(self.root)],
                              capture_output=True, text=True)

    def test_committed_rows_are_current(self):
        self.assertEqual(self.run_script('check').returncode, 0)

    def test_new_version_is_stale_until_written(self):
        path = self.root / 'compatibility.json'
        data = json.loads(path.read_text())
        added = dict(data['zig']['versions'][0], version='9.9.9', hosts=['x86_64-linux', 'aarch64-macos'])
        data['zig']['versions'].append(added)
        path.write_text(json.dumps(data))
        result = self.run_script('check')
        self.assertEqual(result.returncode, 1)
        self.assertIn('matrix rows are stale', result.stderr)
        self.assertEqual(self.run_script('write').returncode, 0)
        workflow = (self.root / '.github/workflows/ci.yml').read_text()
        for part in ('golden', 'lean'):
            self.assertIn(f'- zig: "9.9.9"\n            part: "{part}"\n', workflow)
        self.assertEqual(workflow.count('- zig: "9.9.9"'), 3)  # golden, lean and macos
        self.assertEqual(self.run_script('check').returncode, 0)

    def test_hand_edited_row_is_stale(self):
        path = self.root / '.github/workflows/ci.yml'
        path.write_text(path.read_text().replace('part: "receipt"', 'part: "skipped"', 1))
        self.assertEqual(self.run_script('check').returncode, 1)

    def test_missing_region_fails_closed(self):
        path = self.root / '.github/workflows/ci.yml'
        path.write_text(path.read_text().replace('# END macos rows', '# end', 1))
        self.assertEqual(self.run_script('check').returncode, 2)


if __name__ == '__main__':
    unittest.main()
