#!/usr/bin/env python3
"""W2: every reviewed std source of `Air2Lean/StdModels.lean` names a supported Zig version, and
its SHA-256 is the hash of that std file wherever the std sources are present.

A changed hash means the std code a model row stands for changed: review the definition
against the model again and update the row, or drop the version. Std sources are looked up in
`$AIR2LEAN_STD_<version>` (a `lib/std` directory), `~/.cache/air2lean/host-<version>/lib/std`
and the local `/opt/dev/air2lean-build` trees; a version with no source present is skipped.
No Lean, Lake or Zig is run.
"""
import hashlib
import os
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[3]
TABLE = ROOT / 'Air2Lean/StdModels.lean'
REVIEW = re.compile(r'review "([^"]+)"\s*(?:<\|\s*)?\[(.*?)\]', re.S)
# `(.v0_16_0, "<sha256>")`: a `ZigVersion` constructor (`Air2Lean/Air/Dialect.lean`) and the hash.
ENTRY = re.compile(r'\(\.v(\d+)_(\d+)_(\d+),\s*"([^"]*)"\)')
BUILD = Path('/opt/dev/air2lean-build')
LOCAL = {'0.14.1': BUILD / '0.14.1/zig-0.14.1-pristine/lib/std',
         '0.15.2': BUILD / 'zig-0.15.2-pristine/lib/std',
         '0.16.0': BUILD / 'zig-0.16.0-src/lib/std'}


def reviews(text):
    """(file, version, sha256) of every `review "<file>" [...]` table in the std model table."""
    found = [(file, version, digest) for file, body in REVIEW.findall(text)
             for *parts, digest in ENTRY.findall(body) for version in ['.'.join(parts)]]
    if not found:
        raise ValueError('no std reviews found in Air2Lean/StdModels.lean')
    return found


def supported_versions():
    text = (ROOT / 'zig-patch/versions.toml').read_text()
    return set(re.findall(r'^\["(\d+\.\d+\.\d+)"\]$', text, re.M))


def std_dir(version):
    candidates = [os.environ.get('AIR2LEAN_STD_' + version.replace('.', '_')),
                  str(Path.home() / f'.cache/air2lean/host-{version}/lib/std'), str(LOCAL.get(version, ''))]
    return next((Path(c) for c in candidates if c and (Path(c) / 'std.zig').is_file()), None)


class StdSources(unittest.TestCase):
    def setUp(self):
        self.reviews = reviews(TABLE.read_text())

    def test_reviews_are_well_formed(self):
        versions = supported_versions()
        for file, version, digest in self.reviews:
            with self.subTest(file=file, version=version):
                self.assertIn(version, versions, 'reviewed version is not a supported Zig version')
                self.assertRegex(digest, r'^[0-9a-f]{64}$')
                self.assertTrue(file.endswith('.zig') and not file.startswith('/'))

    def test_reviewed_hashes_match_std_sources(self):
        checked = 0
        for file, version, digest in self.reviews:
            directory = std_dir(version)
            if directory is None:
                continue
            with self.subTest(file=file, version=version):
                actual = hashlib.sha256((directory / file).read_bytes()).hexdigest()
                self.assertEqual(actual, digest, f'{version} lib/std/{file} changed since review')
                checked += 1
        if checked == 0:
            self.skipTest('no reviewed Zig std source present')

    def test_parser_reads_a_changed_hash(self):
        text = TABLE.read_text()
        file, version, digest = self.reviews[0]
        changed = reviews(text.replace(digest, '0' * 64, 1))
        self.assertIn((file, version, '0' * 64), changed)


if __name__ == '__main__':
    unittest.main()
