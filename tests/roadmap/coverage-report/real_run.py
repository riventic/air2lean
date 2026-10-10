#!/usr/bin/env python3
"""I06 end to end on genuine evidence: example-project.json, the real translator and a real sealed proof receipt.

usage: real_run.py ATTEMPT TRANSLATOR

ATTEMPT is a sealed attempt from tests/roadmap/proof-receipts/check.sh whose modules include
Proofs.Basic.Proofs and Proofs.Provenance.Proofs. Nothing here runs Lean, Lake or Zig; the
receipt tool's own `verify` is the staleness oracle. Goal variants are applied in memory (a manifest copy outside the
repository would not share its contract paths with the receipt), so the receipt, artifact,
sources and hashes stay real.

Asserted: the declared theorem binds directly and reaches a functional level, while a wrapper
or unrelated theorem, a sampled differential run alone, and any missing/legacy export
evidence under --require-export-evidence never count as fully functionally verified.

The I07 provenance fixture (provenance-project.json, assurance/provenance) is covered on one root
with analyzed AIR evidence and the same real receipt: a schema-12 export manifest chained to the
receipt binds `analyzed` and `exported`, the receipt binds `compiled` and `proved`, and `double_eq`
reaches total correctness. The fixture's `double_refl` is a real audited theorem whose conclusion
names the root and fixes no result: it is a `trivial_conclusion`, never a direct goal.
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
PROVENANCE = ROOT / 'provenance-project.json'
VERIFIER = ROOT / 'scripts/proof-receipt.py'
FUNCTIONAL = ('correct_if_returns', 'functionally_verified_total')


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


def coverage(goals=None, manifest=PROJECT, **kwargs):
    with declared_goals(goals) if goals is not None else contextlib.nullcontext():
        return project.coverage(manifest, **kwargs)['roots'][0]


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


def provenance_root(work, attempt, translator):
    """The I07 provenance fixture's root: analyzed AIR, translation and the real receipt on one root."""
    artifact = work / 'provenance-artifact'
    translated = subprocess.run([sys.executable, str(ROOT / 'scripts/project.py'), 'translate', str(PROVENANCE),
                                 '--translator', str(translator), '--out', str(artifact)],
                                capture_output=True, text=True, timeout=600)
    check(translated.returncode == 0, 'provenance fixture translation artifact: ' + translated.stderr.strip()[:200])
    manifest = work / 'provenance-manifest.json'
    run = subprocess.run([sys.executable, str(VERIFIER), 'manifest', str(manifest), '--example', 'provenance',
                          '--zig-version', '0.16.0', '--source', 'assurance/provenance/src',
                          '--air-dir', 'assurance/provenance/air', '--generated', 'Proofs/Provenance/Gen.lean',
                          '--proof', 'Proofs/Provenance/Proofs.lean', '--receipt', str(attempt)],
                         capture_output=True, text=True, timeout=600, cwd=ROOT)
    check(run.returncode == 0, 'recorded a fixture artifact manifest chained to the real receipt: ' + run.stderr.strip()[:200])
    declared = project.load_manifest(PROVENANCE)[0]['roots'][0]['goals']
    evidence = dict(manifest=PROVENANCE, artifact=artifact, receipt=attempt, verifier=VERIFIER,
                    export_manifest=manifest, repo_root=ROOT)
    root = coverage(**evidence)
    stages = {name: row['status'] for name, row in root['stages'].items()}
    check(all(stages[name] == 'passed' for name in ('analyzed', 'exported', 'translated', 'compiled', 'proved')),
          f'analyzed, exported, translated, compiled and proved all pass on the fixture root: {stages}')
    goal = root['goals'][0]
    check((goal['binding'], goal['audited_theorem'], goal['derived_strength']) == ('direct', 'double_eq', 'total_correctness'),
          f'double_eq binds directly to Provenance.double at derived total correctness: {goal["binding"]} {goal["reason"]}')
    check(root['level'] == 'functionally_verified_total', f'the fixture root is fully functionally verified: {root["blockers"]}')
    # The committed fixture manifest chains the same source, AIR and profile as the covered root.
    committed = json.loads((ROOT / 'assurance/provenance/manifest.json').read_text())['links']
    fresh = json.loads(manifest.read_text())['links']
    check(all(committed[name]['sha256'] == fresh[name]['sha256'] for name in ('source', 'air', 'profile')),
          'the committed I07 fixture manifest chains the same source, AIR and profile as the covered root')
    # A real audited reflexive theorem names the root, derives no strength and is not a direct goal.
    reflexive = [{'theorem': 'double_refl', 'strength': 'total_correctness', 'domain': 'all pairs of unsigned 32-bit inputs'}]
    row = coverage(reflexive, **evidence)
    check((row['goals'][0]['binding'], row['goals'][0]['derived_strength']) == ('trivial_conclusion', None),
          f'real reflexive theorem double_refl is a trivial_conclusion: {row["goals"][0]["binding"]} {row["goals"][0]["reason"]}')
    check(row['stages']['proved']['status'] == 'failed' and row['level'] == 'compiled',
          f'a trivial conclusion proves nothing about the root: level {row["level"]}')
    not_functional(row, 'trivial conclusion on a real receipt')
    row = coverage(reflexive + declared, **evidence)
    check([g['binding'] for g in row['goals']] == ['trivial_conclusion', 'direct'] and row['level'] == 'proved_scoped',
          f'a trivial goal beside the real theorem keeps the root below functional levels: {row["level"]}')
    not_functional(row, 'trivial goal beside a real theorem')
    # The analysed evidence is the exported AIR itself: another AIR file is not covered by the manifest.
    edited = work / 'provenance-edited'
    row = coverage(manifest=copy_project(edited), artifact=None, export_manifest=manifest, repo_root=ROOT)
    check(row['stages']['analyzed']['status'] == row['stages']['exported']['status'] == 'failed',
          'edited AIR is not covered by the recorded fixture manifest')


def copy_project(target):
    """provenance-project.json with its double AIR edited, in a directory that shares nothing else."""
    target.mkdir()
    for name in ('assurance/provenance/profile.json', 'assurance/provenance/src/provenance.zig',
                 'assurance/provenance/air/provenance.add.json', 'ZigLean.lean', 'ZigLean/Basic.lean',
                 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'zig-patch/air-json/json.zig',
                 'zig-patch/0.16.0/hook.patch', 'Proofs/Provenance/Gen.lean', 'Proofs/Provenance/Proofs.lean'):
        (target / name).parent.mkdir(parents=True, exist_ok=True)
        (target / name).write_bytes((ROOT / name).read_bytes())
    air = target / 'assurance/provenance/air/provenance.double.json'
    air.parent.mkdir(parents=True, exist_ok=True)
    text = (ROOT / 'assurance/provenance/air/provenance.double.json').read_text()
    air.write_text(text.replace('"provenance.double"', '"provenance.double" ', 1))
    (target / 'provenance-project.json').write_bytes(PROVENANCE.read_bytes())
    return target / 'provenance-project.json'


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
        provenance_root(work, attempt, translator)
    print('coverage real-receipt run passed')
    return 0


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    raise SystemExit(main(sys.argv[1:]))
