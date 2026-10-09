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
import contextlib
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


@contextlib.contextmanager
def declared_goals(goals):
    """Replace every root's declared goals in memory, leaving all evidence untouched."""
    original = project.load_manifest

    def patched(path):
        manifest, raw, limits = original(path)
        for root in manifest['roots']:
            root['goals'] = goals
        return manifest, raw, limits
    project.load_manifest = patched
    try:
        yield
    finally:
        project.load_manifest = original


def coverage(goals=None, **kwargs):
    with declared_goals(goals) if goals is not None else contextlib.nullcontext():
        return project.coverage(PROJECT, **kwargs)['roots'][0]


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


def analyzed_idle_loop(work):
    """Analyzed/exported evidence from the retained schema-12 AIR of tests/roadmap/idle-loops.

    The project directory holds byte copies; binding is by hash to a real I07 manifest of the repository."""
    sources = {'progress.zig': 'tests/roadmap/progress/progress.zig', 'idle.json': 'tests/roadmap/idle-loops/air/progress.idle.json',
               'patch': 'zig-patch/air-json/json.zig', 'runtime': 'ZigLean.lean', 'toolchain': 'lean-toolchain'}
    project_dir = work / 'idle'
    project_dir.mkdir()
    for name, source in sources.items():
        (project_dir / name).write_bytes((ROOT / source).read_bytes())
    (project_dir / 'profile.json').write_text(json.dumps(json.loads((project_dir / 'idle.json').read_text())['profile']))
    manifest = project_dir / 'project.json'
    manifest.write_text(json.dumps({
        'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['progress.zig'],
        'components': {'compiler_patch': ['patch'], 'runtime': ['runtime'], 'toolchain': ['toolchain']},
        'allowed_assumptions': [], 'roots': [{'id': 'idle', 'function': 'progress.idle', 'air': ['idle.json'],
                                              'namespace': 'IdleLoop', 'prefix': 'progress.', 'contracts': [],
                                              'goals': [], 'assumptions': [], 'exclusions': []}]}))
    recorded = work / 'idle-manifest.json'
    run = subprocess.run([sys.executable, str(VERIFIER), 'manifest', str(recorded), '--example', 'progress',
                          '--zig-version', '0.16.0', '--air-dir', 'tests/roadmap/idle-loops/air',
                          '--generated', 'tests/roadmap/idle-loops/IdleLoop/Gen.lean',
                          '--source', 'tests/roadmap/progress/progress.zig',
                          '--proof', 'tests/roadmap/idle-loops/IdleLoop/Total.lean'],
                         capture_output=True, text=True, timeout=600, cwd=ROOT)
    check(run.returncode == 0, 'recorded a real artifact manifest for the schema-12 idle-loop AIR: ' + run.stderr.strip()[:200])
    stages = project.coverage(manifest, export_manifest=recorded, repo_root=ROOT)['roots'][0]['stages']
    check(stages['exported']['status'] == stages['analyzed']['status'] == 'passed',
          f'schema-12 AIR bound by hash: analyzed {stages["analyzed"]["status"]}, exported {stages["exported"]["status"]}')
    (project_dir / 'idle.json').write_text((project_dir / 'idle.json').read_text().replace('"progress.idle"', '"progress.idle" ', 1))
    stages = project.coverage(manifest, export_manifest=recorded, repo_root=ROOT)['roots'][0]['stages']
    check(stages['exported']['status'] == stages['analyzed']['status'] == 'failed', 'edited AIR is not covered by the recorded export')


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
        analyzed_idle_loop(work)
    print('coverage real-receipt run passed')
    return 0


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    raise SystemExit(main(sys.argv[1:]))
