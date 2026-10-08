#!/usr/bin/env python3
"""I06 end to end on genuine evidence: example-project.json, the real translator and a real sealed proof receipt.

usage: real_run.py ATTEMPT TRANSLATOR

ATTEMPT is a sealed attempt from tests/roadmap/proof-receipts/check.sh whose modules include
Proofs.Basic.Proofs. Nothing here runs Lean, Lake or Zig; the receipt tool's own `verify` is
the staleness oracle. Goal variants are applied in memory (a manifest copy outside the
repository would not share its contract paths with the receipt), so the receipt, artifact,
sources and hashes stay real.

Asserted: the declared theorem binds directly and reaches a functional level, while a wrapper
or unrelated theorem, a sampled differential run alone, and any missing/legacy export
evidence under --require-export-evidence never count as fully functionally verified.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
PROJECT = ROOT / 'example-project.json'
VERIFIER = ROOT / 'scripts/proof-receipt.py'
FUNCTIONAL = ('functionally_verified_partial', 'functionally_verified_total')


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'scripts' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


project = load('project')


def goals_variant(goals):
    """Replace every root's declared goals in memory, leaving all evidence untouched."""
    original = project.load_manifest

    def patched(path):
        manifest, raw, limits = original(path)
        for root in manifest['roots']:
            root['goals'] = goals
        return manifest, raw, limits
    return original, patched


def coverage(goals=None, **kwargs):
    original, patched = goals_variant(goals) if goals is not None else (None, None)
    if patched:
        project.load_manifest = patched
    try:
        return project.coverage(PROJECT, **kwargs)['roots'][0]
    finally:
        if original:
            project.load_manifest = original


def check(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)
    print('ok:', message)


def not_functional(root, why):
    check(root['level'] not in FUNCTIONAL and not root['fully_functionally_verified'],
          f'{why}: level {root["level"]}, blockers {root["blockers"][:2]}')


def sampled_summary(work):
    sha = hashlib.sha256((ROOT / 'examples/basic/basic.zig').read_bytes()).hexdigest()
    summary = work / 'sampled-diff.json'
    summary.write_text(json.dumps({'schema': 1, 'complete': True, 'qualified': False,
                                   'runner_runtime_sources': {'examples/basic/basic.zig': sha}}))
    Path(str(summary) + '.jsonl').write_text(''.join(
        json.dumps({'schema': 1, 'example': 'basic', 'function': 'tardiness', 'status': 'value_match'}) + '\n'
        for _ in range(8)))
    return summary


def exported_manifest(work, attempt):
    """A real I07 manifest over the committed legacy basic example, chained to the receipt."""
    path = work / 'export-manifest.json'
    run = subprocess.run([sys.executable, str(VERIFIER), 'manifest', str(path), '--example', 'basic',
                          '--zig-version', '0.15.2', '--air-dir', 'tests/golden/basic/air',
                          '--generated', 'Proofs/Basic/Gen.lean', '--source', 'examples/basic',
                          '--receipt', str(attempt)], capture_output=True, text=True, timeout=600, cwd=ROOT)
    check(run.returncode == 0, 'recorded a real artifact manifest chained to the receipt: ' + run.stderr.strip()[:200])
    return path


def main(argv):
    attempt, translator = Path(argv[0]).resolve(), Path(argv[1]).resolve()
    with tempfile.TemporaryDirectory() as temp:
        work = Path(temp).resolve()
        artifact = work / 'artifact'
        translated = subprocess.run([sys.executable, str(ROOT / 'scripts/project.py'), 'translate', str(PROJECT),
                                     '--translator', str(translator), '--out', str(artifact)],
                                    capture_output=True, text=True, timeout=600)
        check(translated.returncode == 0, 'real translation artifact: ' + translated.stderr.strip()[:200])
        evidence = dict(artifact=artifact, receipt=attempt, verifier=VERIFIER)

        root = coverage(**evidence)
        check(root['stages']['compiled']['status'] == 'passed', 'real receipt compiled the byte-identical generated Lean: '
              + root['stages']['compiled']['reason'])
        goal = root['goals'][0]
        check(goal['binding'] == 'direct' and goal['derived_strength'] == 'total_correctness',
              f'tardiness_spec binds directly with derived strength: {goal["binding"]} {goal["reason"]}')
        check(root['level'] == 'functionally_verified_total', f'real receipt reaches total correctness: {root["blockers"]}')

        wrapper = [{'theorem': 'weightedTardiness_ok', 'strength': 'total_correctness', 'domain': 'wrapper variant'}]
        row = coverage(wrapper, **evidence)
        check(row['goals'][0]['binding'] == 'wrapper_or_unrelated', 'wrapper theorem does not bind: ' + row['goals'][0]['binding'])
        not_functional(row, 'wrapper-only theorem on a real receipt')

        diff = sampled_summary(work)
        row = coverage(artifact=artifact, diffs=[diff])
        check(row['stages']['tested']['status'] == 'passed' and row['stages']['tested']['scope'] == 'sampled',
              'sampled differential evidence is recorded as sampled')
        not_functional(row, 'sampled differential tests alone')
        row = coverage(wrapper, diffs=[diff], **evidence)
        check(row['level'] == 'tested_sampled', 'wrapper theorem plus sampled tests on a real receipt stop at tested_sampled')
        not_functional(row, 'wrapper theorem plus sampled tests')

        manifest = exported_manifest(work, attempt)
        row = coverage(export_manifest=manifest, repo_root=ROOT, **evidence)
        check(row['stages']['exported']['status'] == 'passed', 'real legacy export manifest binds the exported AIR/source')
        check(row['stages']['analyzed']['status'] == 'failed' and 'legacy AIR' in row['stages']['analyzed']['reason'],
              'legacy AIR is not analyzed evidence: ' + row['stages']['analyzed']['reason'])
        not_functional(row, 'failed analyzed evidence')
        row = coverage(require_export=True, **evidence)
        check(row['level'] == 'proved_scoped', 'no export manifest under --require-export-evidence is not functional')
    print('coverage real-receipt run passed')
    return 0


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    raise SystemExit(main(sys.argv[1:]))
