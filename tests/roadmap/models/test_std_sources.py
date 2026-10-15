#!/usr/bin/env python3
"""W2: every reviewed std source of `Air2Lean/StdModels.lean` names a supported Zig version, and
its SHA-256 is the hash of that std file wherever the std sources are present. Every modelled row
names its premise, and every hand model of std code its transitional STD premise and retirement
row (`HandModels`).

A changed hash means the std code a model row stands for changed: review the definition
against the model again and update the row, or drop the version. Std sources are looked up in
`$AIR2LEAN_STD_<version>` (a `lib/std` directory), `~/.cache/air2lean/host-<version>/lib/std`
and the local `/opt/dev/air2lean-build` trees; a version with no source present is skipped.
No Lean, Lake or Zig is run.
"""
import hashlib
import json
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
    cas = os.environ.get('AIR2LEAN_CAS_DIR')
    patched = sorted(Path(cas).glob(f'zig/{version}-*/prefix/lib/zig/std')) if cas else []
    candidates = [os.environ.get('AIR2LEAN_STD_' + version.replace('.', '_')),
                  str(Path.home() / f'.cache/air2lean/host-{version}/lib/std'), str(LOCAL.get(version, '')),
                  str(ROOT / f'zig-air-{version}/lib/zig/std'), *map(str, patched)]
    return next((Path(c) for c in candidates if c and (Path(c) / 'std.zig').is_file()), None)


def std_namespaces():
    """`Identity.stdNamespaces`: the namespaces whose root names the translator qualifies."""
    text = (ROOT / 'Air2Lean/Air/Identity.lean').read_text()
    body = re.search(r'def stdNamespaces : Array String := #\[(.*?)\]', text, re.S)
    if body is None:
        raise ValueError('no stdNamespaces in Air2Lean/Air/Identity.lean')
    return set(re.findall(r'"([^"]+)"', body.group(1)))


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

    def test_std_namespaces_cover_lib_std(self):
        """S2 (soundness audit 2026-10-14): every top-level file or directory of `lib/std` is a
        std namespace, so a root file of that name gets `root:` keys and binds no std model."""
        known, checked = std_namespaces(), 0
        for version in sorted(supported_versions()):
            directory = std_dir(version)
            if directory is None:
                continue
            with self.subTest(version=version):
                present = {p.name.removesuffix('.zig') for p in directory.iterdir()
                           if not p.name.startswith('.') and (p.is_dir() or p.suffix == '.zig')}
                self.assertEqual(present - known, set(), f'{version} lib/std namespaces missing from Identity.stdNamespaces')
                checked += 1
        if checked == 0:
            self.skipTest('no Zig std source present')

    def test_parser_reads_a_changed_hash(self):
        text = TABLE.read_text()
        file, version, digest = self.reviews[0]
        changed = reviews(text.replace(digest, '0' * 64, 1))
        self.assertIn((file, version, '0' * 64), changed)


# A modelled row: `threadModel "Thread.spawn" "STD-02" .spawn ...` (`allocModel`, `osModel` alike).
ROW = re.compile(r'^\s*(?:allocModel|threadModel|osModel) "([^"]+)" "([A-Z]{3}-\d{2})"', re.M)
STD_ID = re.compile(r'\bSTD-\d{2}\b')
# The other hand model: the timed emitter's selection (`Air2Lean/TimedCheck.lean`).
TIMED = ROOT / 'Air2Lean/TimedCheck.lean'
CATALOG = ROOT / 'docs/premises.md'
CONFIG = ROOT / 'assurance/premises.json'
LEDGER = ROOT / 'docs/std-models.md'


def model_rows(text):
    """(symbol, premise) of every modelled row of the std model table."""
    rows = ROW.findall(text)
    if not rows:
        raise ValueError('no modelled rows found in Air2Lean/StdModels.lean')
    # A modelled row written as a record literal would escape the row pattern (and the ledger).
    if re.search(r'kind := \.(?:alloc|thread|os) (?!fn\b)', text):
        raise ValueError('a modelled std row bypasses allocModel/threadModel/osModel')
    return rows


def ledger_rows():
    """{premise: row text} of the table of docs/std-models.md §Retiring the hand models."""
    text = LEDGER.read_text()
    section = text.split('## Retiring the hand models', 1)[1].split('\n## ', 1)[0]
    return {m.group(1): line for line in section.splitlines()
            for m in [re.match(r'\| (STD-\d{2}) \|', line)] if m}


class HandModels(unittest.TestCase):
    """Every hand model of std code names a transitional STD premise that is defined, reaches
    every theorem through `implies`, and has its retirement row; an STD premise without a
    model left is deleted (docs/std-models.md §Retiring the hand models)."""

    def setUp(self):
        self.rows = model_rows(TABLE.read_text())
        self.defined = set(re.findall(r'^### (STD-\d{2}) — ', CATALOG.read_text(), re.M))
        implies = json.loads(CONFIG.read_text())['implies']
        self.implied = {p for ps in implies.values() for p in ps}
        self.ledger = ledger_rows()
        self.used = {p for _, p in self.rows} | set(STD_ID.findall(TIMED.read_text()))

    def test_rows_name_premises(self):
        for symbol, premise in self.rows:
            with self.subTest(symbol=symbol):
                self.assertTrue(premise == 'OSM-01' or premise.startswith('STD-'), premise)
                if premise.startswith('STD-'):
                    self.assertIn(premise, self.defined, 'premise not defined in docs/premises.md')
                    self.assertIn(f'`{symbol}`', self.ledger.get(premise, ''),
                                  'row missing from its retirement ledger entry')

    def test_std_premises_are_live(self):
        used = {p for p in self.used if p.startswith('STD-')}
        self.assertEqual(self.defined, used, 'an STD premise without a hand model, or one undefined')
        self.assertEqual(set(self.ledger), used, 'retirement ledger out of sync with the hand models')
        self.assertLessEqual(used, self.implied, 'an STD premise that no semantic premise implies')


if __name__ == '__main__':
    unittest.main()
