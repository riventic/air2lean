#!/usr/bin/env python3
"""I07 authentication regressions: signed manifests and receipts, and what tampering does to them.

`scripts/attest.py` signs artifact manifests and proof receipts with an SSH (Ed25519) signature
and verifies them offline against the verifier's allowed-signers file (premise TRU-05).

* `KnownAnswer` verifies a committed attestation (`fixture/`) made once with a key whose
  private half was discarded: no private key is needed, so the verification path and the
  signature format are pinned across `ssh-keygen` versions.
* `Tamper` signs scratch files with a fresh key and checks every way a forger could go on:
  an edited subject, statement, signature, principal, namespace, key or a replaced, added or
  missing artifact.
* `Fixtures` signs the real committed receipt-chained manifests and receipts of
  `assurance/provenance` and `assurance/provenance-gap` (whole-tree generated files: skipped
  when not materialized, `scripts/generated.py`), through `attest.py` and through
  `provenance-evidence.py check --attestation`.

The ephemeral keys prove only the mechanism. Nothing here is a release key.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
ATTEST = ROOT / 'scripts/attest.py'
EVIDENCE = ROOT / 'scripts/provenance-evidence.py'
KNOWN = Path(__file__).resolve().parent / 'fixture'
ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')


def run(script, *args):
    return subprocess.run([sys.executable, '-B', str(script), *map(str, args)], capture_output=True, text=True, env=ENV)


def keypair(directory, name, principal='signer'):
    key = Path(directory) / name
    assert not key.exists(), key
    subprocess.run(['ssh-keygen', '-q', '-t', 'ed25519', '-N', '', '-C', name, '-f', str(key)], check=True, stdin=subprocess.DEVNULL)
    allowed = Path(directory) / (name + '.allowed')
    allowed.write_text('%s %s\n' % (principal, ' '.join(Path(str(key) + '.pub').read_text().split()[:2])))
    return key, allowed


class KnownAnswer(unittest.TestCase):
    def verify(self, *extra, attestation='attestation.json'):
        return run(ATTEST, 'verify', KNOWN / attestation, '--allowed-signers', KNOWN / 'allowed_signers',
                   '--file', KNOWN / 'subject.txt', *extra)

    def test_committed_attestation_verifies_without_a_private_key(self):
        done = self.verify('--principal', 'release-signer')
        self.assertEqual(done.returncode, 0, done.stderr)
        report = json.loads(done.stdout)
        self.assertEqual((report['status'], report['principal']), ('attested', 'release-signer'))
        self.assertEqual(report['key_fingerprint'], 'SHA256:2ncTTuXQA7aN7hI4g/n1pSwgtoe5KG4TFUDoLDtcEfM')

    def test_pinned_fingerprint(self):
        self.assertEqual(self.verify('--pin-fingerprint', 'SHA256:2ncTTuXQA7aN7hI4g/n1pSwgtoe5KG4TFUDoLDtcEfM').returncode, 0)
        done = self.verify('--pin-fingerprint', 'SHA256:' + 'A' * 43)
        self.assertEqual(done.returncode, 2)
        self.assertIn('not the pinned key', done.stderr)

    def test_other_principal_is_refused(self):
        done = self.verify('--principal', 'someone-else')
        self.assertEqual(done.returncode, 2)
        self.assertIn('expected', done.stderr)


class Tamper(unittest.TestCase):
    def setUp(self):
        self.work = Path(tempfile.mkdtemp(prefix='air2lean-attest-test-')).resolve()
        self.key, self.allowed = keypair(self.work, 'key')
        self.subject = self.work / 'manifest-like.json'
        self.subject.write_text('{"payload":"one"}\n')
        self.att = self.work / 'att.json'
        done = run(ATTEST, 'sign', '--key', self.key, '--principal', 'signer', '--file', self.subject, '--out', self.att)
        self.assertEqual(done.returncode, 0, done.stderr)

    def tearDown(self):
        shutil.rmtree(self.work, ignore_errors=True)

    def verify(self, att=None, allowed=None, subject=None, *extra):
        return run(ATTEST, 'verify', att or self.att, '--allowed-signers', allowed or self.allowed,
                   '--file', subject or self.subject, *extra)

    def rejected(self, done, text):
        self.assertEqual(done.returncode, 2, done.stdout)
        self.assertIn(text, done.stderr)

    def edit(self, mutate):
        document = json.loads(self.att.read_text())
        mutate(document)
        path = self.work / 'edited.json'
        path.write_text(json.dumps(document))
        return path

    def test_genuine(self):
        self.assertEqual(self.verify().returncode, 0)

    def test_edited_artifact(self):
        self.subject.write_text('{"payload":"two"}\n')
        self.rejected(self.verify(), 'matches no supplied artifact')

    def test_edited_digest_in_statement_breaks_the_signature(self):
        att = self.edit(lambda d: d['statement']['subjects'][0]['files'][0].update(sha256='0' * 64))
        self.rejected(self.verify(att), 'does not verify')

    def test_edited_principal_breaks_the_signature(self):
        other = self.work / 'other.allowed'
        other.write_text(self.allowed.read_text().replace('signer', 'mallory'))
        att = self.edit(lambda d: d['statement'].update(principal='mallory'))
        self.rejected(self.verify(att, other), 'does not verify')

    def test_signature_of_another_key(self):
        key2, allowed2 = keypair(self.work, 'key2')
        att2 = self.work / 'att2.json'
        self.assertEqual(run(ATTEST, 'sign', '--key', key2, '--principal', 'signer', '--file', self.subject,
                             '--out', att2).returncode, 0)
        self.assertEqual(self.verify(att2, allowed2).returncode, 0)
        self.rejected(self.verify(att2, self.allowed), 'does not verify')  # not the allowed key
        forged = self.edit(lambda d: d.update(signature=json.loads(att2.read_text())['signature']))
        self.rejected(self.verify(forged), 'does not verify')  # key 2's signature in key 1's statement slot

    def test_signature_from_a_statement_with_other_subjects(self):
        other = self.work / 'other.json'
        other.write_text('{"payload":"other"}\n')
        att2 = self.work / 'att2.json'
        run(ATTEST, 'sign', '--key', self.key, '--principal', 'signer', '--file', other, '--out', att2)
        forged = self.edit(lambda d: d.update(signature=json.loads(att2.read_text())['signature']))
        self.rejected(self.verify(forged), 'does not verify')

    def test_other_namespace_is_not_an_attestation(self):
        message = self.work / 'msg'
        document = json.loads(self.att.read_text())
        import importlib.util
        spec = importlib.util.spec_from_file_location('attest', ATTEST)
        attest = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(attest)
        message.write_bytes(attest.signed_message(document['statement']))
        subprocess.run(['ssh-keygen', '-Y', 'sign', '-f', str(self.key), '-n', 'file', str(message)],
                       check=True, capture_output=True)
        forged = self.edit(lambda d: d.update(signature=(self.work / 'msg.sig').read_text()))
        self.rejected(self.verify(forged), 'does not verify')

    def test_trust_anchor_is_the_verifiers_not_the_attestations(self):
        key2, allowed2 = keypair(self.work, 'key2')
        self.rejected(self.verify(None, allowed2), 'does not verify')
        self.rejected(run(ATTEST, 'verify', self.att, '--allowed-signers', self.work / 'missing',
                          '--file', self.subject), 'not found')

    def test_added_or_missing_artifact(self):
        extra = self.work / 'extra.json'
        extra.write_text('{}\n')
        done = run(ATTEST, 'verify', self.att, '--allowed-signers', self.allowed, '--file', self.subject, '--file', extra)
        self.rejected(done, 'not covered')
        done = run(ATTEST, 'verify', self.att, '--allowed-signers', self.allowed)
        self.rejected(done, 'nothing to attest')

    def test_kind_confusion(self):
        # The same bytes attested as a file are not a manifest.
        done = run(ATTEST, 'verify', self.att, '--allowed-signers', self.allowed, '--manifest', self.subject)
        self.rejected(done, 'attestation rejected')

    def test_malformed_documents(self):
        for mutate in (lambda d: d.update(format='other'), lambda d: d.update(extra=1),
                       lambda d: d['statement'].update(namespace='x'), lambda d: d['statement'].update(subjects=[]),
                       lambda d: d.update(signature='nope'),
                       lambda d: d['statement']['subjects'][0].update(kind='weird')):
            self.assertEqual(self.verify(self.edit(mutate)).returncode, 2)
        duplicate = self.work / 'dup.json'
        duplicate.write_text(self.att.read_text().replace('{"format"', '{"format":"x","format"', 1))
        self.assertEqual(self.verify(duplicate).returncode, 2)

    def test_expired_key(self):
        expired = self.work / 'expired.allowed'
        expired.write_text(self.allowed.read_text().replace('signer ', 'signer valid-before="20200101" '))
        self.assertEqual(self.verify(None, expired, None, '--verify-time', '20190101').returncode, 0)
        self.rejected(self.verify(None, expired, None, '--verify-time', '20260101'), 'does not verify')

    def test_never_overwrites(self):
        done = run(ATTEST, 'sign', '--key', self.key, '--principal', 'signer', '--file', self.subject, '--out', self.att)
        self.assertEqual(done.returncode, 2)


class Fixtures(unittest.TestCase):
    """The real receipt-chained fixtures. Skipped unless materialized (scripts/generated.py)."""
    NAMES = {'provenance': 'assurance/provenance', 'gap': 'assurance/provenance-gap'}

    def setUp(self):
        for directory in self.NAMES.values():
            if not (ROOT / directory / 'manifest.json').is_file() or not (ROOT / directory / 'receipt/receipt.json').is_file():
                self.skipTest('provenance fixtures not materialized (scripts/generated.py)')
        self.work = Path(tempfile.mkdtemp(prefix='air2lean-attest-fixture-')).resolve()
        self.key, self.allowed = keypair(self.work, 'key', 'release')

    def tearDown(self):
        shutil.rmtree(self.work, ignore_errors=True)

    def sign(self, fixture, *kinds):
        directory = ROOT / self.NAMES[fixture]
        args = []
        if 'manifest' in kinds:
            args += ['--manifest', directory / 'manifest.json']
        if 'receipt' in kinds:
            args += ['--receipt', directory / 'receipt']
        att = self.work / (fixture + '-' + '-'.join(kinds) + '.json')
        done = run(ATTEST, 'sign', '--key', self.key, '--principal', 'release', *args, '--out', att)
        self.assertEqual(done.returncode, 0, done.stderr)
        return att, args

    def test_signed_manifest_and_receipt_verify_for_both_fixtures(self):
        for fixture in self.NAMES:
            att, args = self.sign(fixture, 'manifest', 'receipt')
            done = run(ATTEST, 'verify', att, '--allowed-signers', self.allowed, *args)
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertEqual([s['kind'] for s in json.loads(done.stdout)['subjects']], ['manifest', 'receipt'])

    def test_an_attestation_is_for_its_own_fixture(self):
        att, _ = self.sign('provenance', 'manifest')
        other = ROOT / self.NAMES['gap'] / 'manifest.json'
        done = run(ATTEST, 'verify', att, '--allowed-signers', self.allowed, '--manifest', other)
        self.assertEqual(done.returncode, 2)
        self.assertIn('matches no supplied artifact', done.stderr)

    def copy_fixture(self, fixture):
        target = self.work / ('copy-' + fixture)
        shutil.copytree(ROOT / self.NAMES[fixture], target, ignore=shutil.ignore_patterns('air', 'src'))
        return target

    def test_tampered_manifest_or_receipt_is_not_the_attested_artifact(self):
        for fixture in self.NAMES:
            att, _ = self.sign(fixture, 'manifest', 'receipt')
            copy = self.copy_fixture(fixture)
            args = ['--manifest', copy / 'manifest.json', '--receipt', copy / 'receipt']
            self.assertEqual(run(ATTEST, 'verify', att, '--allowed-signers', self.allowed, *args).returncode, 0)
            for name in ('receipt/receipt.json', 'receipt/plan.json', 'receipt/audit.json'):
                with open(copy / name, 'a') as stream:
                    stream.write('\n')
                done = run(ATTEST, 'verify', att, '--allowed-signers', self.allowed, *args)
                self.assertEqual(done.returncode, 2, name)
                self.assertIn('matches no supplied artifact', done.stderr)
                shutil.copy2(ROOT / self.NAMES[fixture] / name, copy / name)
            # Even a self-consistent re-recorded manifest (here: one link's digest and the chain are
            # not recomputed) is refused by the chain check before it could be signed or accepted.
            document = json.loads((copy / 'manifest.json').read_text())
            document['links']['source']['sha256'] = '0' * 64
            (copy / 'manifest.json').write_text(json.dumps(document))
            done = run(ATTEST, 'sign', '--key', self.key, '--principal', 'release', '--manifest', copy / 'manifest.json',
                       '--out', self.work / (fixture + '-forged.json'))
            self.assertEqual(done.returncode, 2)
            self.assertIn('attestation rejected', done.stderr)

    def check(self, fixture, *args):
        done = run(EVIDENCE, '--fixture', fixture, 'check', *args)
        return done, json.loads(done.stdout) if done.stdout.strip() else None

    def test_provenance_check_reports_authentication(self):
        for fixture in self.NAMES:
            plain_done, plain = self.check(fixture)
            self.assertEqual(plain['authentication'], 'not_attested')
            att, _ = self.sign(fixture, 'manifest')
            done, report = self.check(fixture, '--attestation', att, '--allowed-signers', self.allowed,
                                      '--require-attestation')
            self.assertEqual(report['authentication']['status'], 'attested', done.stderr)
            self.assertEqual(report['status'], plain['status'])
            self.assertEqual(report['problems'], plain['problems'])
            # Required but absent: not current.
            done, report = self.check(fixture, '--require-attestation')
            self.assertEqual(done.returncode, 2)
            self.assertIn('attestation required', ' '.join(report['problems']))
            # Another key: rejected, and the manifest is no longer reported current.
            _, other_allowed = keypair(self.work, 'other-' + fixture, 'release')
            done, report = self.check(fixture, '--attestation', att, '--allowed-signers', other_allowed)
            self.assertEqual((done.returncode, report['authentication']), (2, 'rejected'))
            self.assertIn('attestation rejected', ' '.join(report['problems']))


if __name__ == '__main__':
    unittest.main()
