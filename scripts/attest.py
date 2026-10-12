#!/usr/bin/env python3
"""I07 attestations: authenticate artifact manifests and proof receipts with an SSH signature.

A manifest (`artifact-manifest.py`) or a proof receipt (`proof-receipt.py`) detects drift of
the bytes it names; it does not say who produced it. An attestation signs the exact bytes of
those artifacts with an Ed25519 (or any `ssh-keygen -Y` capable) key, so a reviewer who holds
the signer's public key can tell the artifact from a forgery. The scheme is OpenSSH's file
signature format (`ssh-keygen -Y sign|verify`, namespace `air2lean-attestation-v1`): no
cryptography is implemented here and no Python package is needed.

    attest.py sign --key KEY --principal NAME --out ATT.json  [--manifest M]... [--receipt DIR]... [--file F]...
    attest.py verify ATT.json --allowed-signers FILE  [--manifest M]... [--receipt DIR]... [--file F]...
                      [--principal NAME] [--pin-fingerprint SHA256:...] [--verify-time YYYYMMDD]

`verify` is offline and fails closed. It checks that the signature is a valid signature of the
statement by a key that `--allowed-signers` (the trust anchor, supplied by the verifier and never
read from the attestation) lists for the principal and namespace; that every subject of the
statement is covered by a supplied artifact whose bytes hash to the recorded digest; and that a
manifest subject is internally consistent (its chain recomputes). It does not check freshness: a
validly signed manifest can still be stale against the tree (`check-manifest` reports that). See
docs/artifact-manifest.md#authentication and premise TRU-05 (docs/premises.md).
"""
import argparse
import functools
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parents[1]
_spec = importlib.util.spec_from_file_location('attest_receipt', ROOT / 'scripts/proof-receipt.py')
receipt = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(receipt)
demand, read_file, parse_json, mapping = receipt.demand, receipt.read_file, receipt.parse_json, receipt.mapping

FORMAT = 'air2lean-attestation-v1'
NAMESPACE = 'air2lean-attestation-v1'
KINDS = ('manifest', 'receipt', 'file')
RECEIPT_FILES = ('receipt.json', 'plan.json', 'audit.json', 'after.json')
FINGERPRINT = re.compile(r'SHA256:[A-Za-z0-9+/]{43}')
PRINCIPAL = re.compile(r'[A-Za-z0-9][A-Za-z0-9._@+-]{0,127}')
STATEMENT_KEYS = {'namespace', 'principal', 'subjects'}
SUBJECT_KEYS = {'kind', 'name', 'files', 'manifest_sha256'}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False, allow_nan=False).encode()


def signed_message(statement):
    """The bytes that are signed: a domain tag, then the canonical statement."""
    return (FORMAT + '\n').encode() + canonical(statement)


def file_digest(path):
    return hashlib.sha256(read_file(path, receipt.MAX_FILE)).hexdigest()


@functools.cache
def manifest_module():
    spec = importlib.util.spec_from_file_location('attest_manifest', ROOT / 'scripts/artifact-manifest.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def subject_of(kind, path):
    """The subject record of one artifact: kind, a relocatable name and the sha256 of every file."""
    path = Path(os.path.abspath(path))
    if kind == 'receipt':
        demand(path.is_dir(), 'receipt must be a directory: ' + str(path))
        files = [{'path': n, 'sha256': file_digest(path / n)} for n in RECEIPT_FILES if (path / n).exists()]
        demand(any(f['path'] == 'receipt.json' for f in files), 'receipt directory has no receipt.json: ' + str(path))
        return {'kind': 'receipt', 'name': path.name, 'files': files}
    subject = {'kind': kind, 'name': path.name, 'files': [{'path': path.name, 'sha256': file_digest(path)}]}
    if kind == 'manifest':
        am = manifest_module()
        document = am.load(path)
        am.manifest_integrity(document)  # An inconsistent manifest is never signed.
        subject['manifest_sha256'] = document['manifest_sha256']
    return subject


def collect(manifests, receipts, files):
    subjects = [subject_of('manifest', p) for p in manifests or ()]
    subjects += [subject_of('receipt', p) for p in receipts or ()]
    subjects += [subject_of('file', p) for p in files or ()]
    demand(subjects, 'nothing to attest: pass --manifest, --receipt or --file')
    return subjects


def keygen(*args, data=None, timeout=60):
    return subprocess.run(['ssh-keygen', *args], input=data, capture_output=True, timeout=timeout)


def sign(key, principal, subjects, out):
    demand(PRINCIPAL.fullmatch(principal) is not None, 'invalid principal name')
    demand(Path(key).is_file(), 'signing key not found: ' + str(key))
    statement = {'namespace': NAMESPACE, 'principal': principal, 'subjects': subjects}
    with tempfile.TemporaryDirectory(prefix='air2lean-attest-') as scratch:
        message = Path(scratch) / 'statement'
        message.write_bytes(signed_message(statement))
        done = keygen('-Y', 'sign', '-f', str(key), '-n', NAMESPACE, str(message))
        demand(done.returncode == 0, 'ssh-keygen -Y sign failed: ' + done.stderr.decode(errors='replace').strip())
        signature = (Path(scratch) / 'statement.sig').read_text()
    document = {'format': FORMAT, 'statement': statement, 'signature': signature}
    receipt.write_new(out, document)
    return document


def check_document(document):
    """Strict shape of an attestation; returns (statement, signature)."""
    document = mapping(document, 'attestation')
    demand(document.get('format') == FORMAT and set(document) == {'format', 'statement', 'signature'},
           'not an %s document' % FORMAT)
    statement = mapping(document['statement'], 'statement')
    demand(set(statement) == STATEMENT_KEYS and statement['namespace'] == NAMESPACE, 'malformed statement')
    demand(isinstance(statement['principal'], str) and PRINCIPAL.fullmatch(statement['principal']) is not None,
           'invalid principal name')
    subjects = statement['subjects']
    demand(isinstance(subjects, list) and subjects, 'statement has no subjects')
    for subject in subjects:
        subject = mapping(subject, 'subject')
        demand(set(subject) <= SUBJECT_KEYS and {'kind', 'name', 'files'} <= set(subject)
               and subject['kind'] in KINDS and isinstance(subject['name'], str)
               and isinstance(subject['files'], list) and subject['files'], 'malformed subject')
        demand(('manifest_sha256' in subject) == (subject['kind'] == 'manifest'), 'malformed subject')
        for entry in subject['files']:
            demand(set(mapping(entry, 'subject file')) == {'path', 'sha256'} and isinstance(entry['path'], str)
                   and isinstance(entry['sha256'], str) and re.fullmatch('[0-9a-f]{64}', entry['sha256']) is not None,
                   'malformed subject file')
    signature = document['signature']
    demand(isinstance(signature, str) and signature.startswith('-----BEGIN SSH SIGNATURE-----'), 'malformed signature')
    return statement, signature


def verify_signature(statement, signature, allowed_signers, principal, verify_time=None):
    """Run `ssh-keygen -Y verify`; return the signer's key fingerprint."""
    demand(Path(allowed_signers).is_file(), 'allowed signers file not found: ' + str(allowed_signers))
    with tempfile.TemporaryDirectory(prefix='air2lean-attest-') as scratch:
        sig = Path(scratch) / 'statement.sig'
        sig.write_text(signature)
        args = ['-Y', 'verify', '-f', str(allowed_signers), '-I', principal, '-n', NAMESPACE, '-s', str(sig)]
        if verify_time:
            demand(re.fullmatch(r'\d{8}(\d{4}(\d{2})?)?Z?', verify_time) is not None, 'invalid --verify-time')
            args += ['-O', 'verify-time=' + verify_time]
        done = keygen(*args, data=signed_message(statement))
    text = done.stdout.decode(errors='replace')
    demand(done.returncode == 0, 'signature does not verify against the allowed signers: '
           + (done.stderr.decode(errors='replace') + text).strip())
    found = FINGERPRINT.search(text)
    demand(found is not None, 'could not read the signer fingerprint from ssh-keygen')
    return found.group(0)


def verify(path, allowed_signers, manifests=(), receipts=(), files=(), principal=None, pin=None, verify_time=None):
    """Offline check of an attestation against the trust anchor and the supplied artifacts."""
    statement, signature = check_document(parse_json(read_file(path, receipt.MAX_JSON)))
    named = statement['principal']
    demand(principal is None or principal == named, 'attestation is for principal %r, expected %r' % (named, principal))
    fingerprint = verify_signature(statement, signature, allowed_signers, named, verify_time)
    demand(pin is None or fingerprint == pin, 'signing key %s is not the pinned key %s' % (fingerprint, pin))
    supplied = collect(manifests, receipts, files)
    matched = set()
    for subject in statement['subjects']:
        hits = [i for i, s in enumerate(supplied)
                if s['kind'] == subject['kind'] and s['files'] == subject['files']
                and s.get('manifest_sha256') == subject.get('manifest_sha256')]
        demand(hits, 'attested %s %r matches no supplied artifact (edited, replaced or missing)'
               % (subject['kind'], subject['name']))
        matched.update(hits)
    demand(len(matched) == len(supplied), 'a supplied artifact is not covered by the attestation')
    return {'status': 'attested', 'principal': named, 'key_fingerprint': fingerprint,
            'subjects': [{'kind': s['kind'], 'name': s['name']} for s in statement['subjects']]}


def main(argv):
    parser = argparse.ArgumentParser(prog='attest.py', description=__doc__.split('\n\n')[0])
    sub = parser.add_subparsers(dest='action', required=True)
    for name in ('sign', 'verify'):
        p = sub.add_parser(name)
        p.add_argument('--manifest', action='append', type=Path)
        p.add_argument('--receipt', action='append', type=Path)
        p.add_argument('--file', action='append', type=Path)
    s = sub.choices['sign']
    s.add_argument('--key', required=True, type=Path, help='private key (ssh-keygen format)')
    s.add_argument('--principal', required=True)
    s.add_argument('--out', required=True, type=Path, help='attestation JSON; never overwritten')
    v = sub.choices['verify']
    v.add_argument('attestation', type=Path)
    v.add_argument('--allowed-signers', required=True, type=Path, help='the verifier\'s trust anchor')
    v.add_argument('--principal')
    v.add_argument('--pin-fingerprint', help='require this signing key (SHA256:...)')
    v.add_argument('--verify-time', help='YYYYMMDD[HHMM[SS]][Z]: honour valid-after/valid-before at that time')
    a = parser.parse_args(argv)
    try:
        if a.action == 'sign':
            sign(a.key, a.principal, collect(a.manifest, a.receipt, a.file), a.out)
            print(json.dumps({'attestation': str(a.out)}))
            return 0
        report = verify(a.attestation, a.allowed_signers, a.manifest, a.receipt, a.file, a.principal,
                        a.pin_fingerprint, a.verify_time)
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print('attestation rejected: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
