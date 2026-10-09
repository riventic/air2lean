"""Lake evidence for `--split-modules` (I04): cold build, isolated edit, warm rebuild, cold rebuild.

A scratch Lake package requires this repository by path (reusing its built `ZigLean`) and holds
`Demo.Layout.Gen`: the layout example split into one module per call group, plus copies of the
layout proofs. `Demo.Layout.Proofs` imports the umbrella `Demo.Layout.Gen`, as committed proofs
import `Proofs.Layout.Gen`; `Demo.Layout.Mem` imports only the group modules it uses.

1. Cold: translate and build everything.
2. Edit `layout.digit` (a comparison flips; a semantic change), translate again (only changed
   files are rewritten) and rebuild. The rebuilt generated modules must be exactly the modules
   whose invalidation key changed (`scripts/module-split.py compare`): `F_digit`, its caller
   `F_bumpDigit` and the umbrella. `Demo.Layout.Mem` must not rebuild; `Demo.Layout.Proofs`
   rebuilds through the umbrella and still proves.
3. Cold again: delete the scratch build and rebuild the edited sources. Each module's `.olean`
   must be byte-identical to the warm build's, and every proof module builds in both.

Requires a built translator and Lake; run it under scripts/build-guard.py. Usage:
  python3 -B tests/roadmap/modular-output/lake_incremental.py .lake/build/bin/air2lean \
    [--work DIR] [--report report.json]
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
SPLIT = ROOT / 'scripts/module-split.py'
GEN = 'Demo.Layout.Gen'
EDITED = 'layout.digit'
MEM_IMPORTS = ['F_bump', 'F_numInt', 'F_setNum', 'F_writeTable']


def instructions(body):
    for inst in body:
        yield inst
        for key in ('body', 'then', 'else'):
            yield from instructions(inst.get(key, []))
        for case in inst.get('cases', []):
            yield from instructions(case['body'])


def translate(binary, air, package, label):
    out = package / 'Demo/Layout/Gen.lean'
    out.parent.mkdir(parents=True, exist_ok=True)
    source_map = package.parent / f'{label}.source-map.json'
    subprocess.run([str(binary), str(air), '-o', str(out), '--namespace', 'Layout', '--prefix', 'layout.',
                    '--split-modules', GEN, '--source-map-json', str(source_map)], check=True, timeout=600)
    # `module-split.py` hashes the files beside the manifest: keep this translation's copy.
    snapshot = package.parent / f'{label}-sources'
    shutil.rmtree(snapshot, ignore_errors=True)
    shutil.copytree(package / 'Demo', snapshot / 'Demo')
    return snapshot / 'Demo/Layout/Gen.modules.json', source_map


def oleans(package):
    lib = package / '.lake/build/lib/lean'
    return {'.'.join(p.relative_to(lib).with_suffix('').parts): (p.stat().st_mtime_ns, hashlib.sha256(p.read_bytes()).hexdigest())
            for p in sorted(lib.glob('Demo/**/*.olean'))}


def build(package, log):
    result = subprocess.run(['lake', 'build', 'Demo'], cwd=package, capture_output=True, text=True, timeout=10800)
    log.write_text(result.stdout + result.stderr)
    if result.returncode:
        sys.exit(f'lake build failed (exit {result.returncode}); see {log}')
    return sorted(set(re.findall(r'Built (Demo[\w.]*?)(?::\S+)? \(', result.stdout)))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('translator', type=Path)
    parser.add_argument('--work', type=Path, default=Path('/tmp/air2lean-modular-output'))
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    binary = args.translator.resolve(strict=True)
    work = args.work.resolve()
    shutil.rmtree(work, ignore_errors=True)
    package = work / 'pkg'
    (package / 'Demo/Layout').mkdir(parents=True)
    (package / 'lean-toolchain').write_text((ROOT / 'lean-toolchain').read_text())
    (package / 'lakefile.toml').write_text(
        f'name = "modular_output_demo"\ndefaultTargets = ["Demo"]\n\n[[require]]\nname = "air2lean"\npath = {json.dumps(str(ROOT))}\n\n'
        '[[lean_lib]]\nname = "Demo"\nglobs = ["Demo.+"]\n')
    proofs = (ROOT / 'Proofs/Layout/Proofs.lean').read_text().replace('import Proofs.Layout.Gen', f'import {GEN}')
    (package / 'Demo/Layout/Proofs.lean').write_text(proofs)
    mem = (ROOT / 'Proofs/Layout/Mem.lean').read_text().replace(
        'import Proofs.Layout.Gen', '\n'.join(f'import {GEN}.{m}' for m in MEM_IMPORTS))
    (package / 'Demo/Layout/Mem.lean').write_text(mem)

    golden = ROOT / 'tests/golden/layout/air'
    edited = work / 'air-edited'
    shutil.copytree(golden, edited)
    path = edited / f'{EDITED}.json'
    doc = json.loads(path.read_text())
    inst = next(i for i in instructions(doc['body']) if i['tag'] == 'cmp_gt')
    inst['tag'] = 'cmp_lt'
    path.write_text(json.dumps(doc, indent=1))

    old_manifest, old_map = translate(binary, golden, package, 'cold')
    cold_built = build(package, work / 'cold.log')
    before = oleans(package)
    new_manifest, new_map = translate(binary, edited, package, 'edited')
    warm_built = build(package, work / 'warm.log')
    after = oleans(package)
    compared = subprocess.run([sys.executable, '-I', '-B', str(SPLIT), 'compare', str(old_manifest), str(new_manifest),
                               '--old-source-map', str(old_map), '--new-source-map', str(new_map)],
                              capture_output=True, text=True, check=True)
    keys = json.loads(compared.stdout)
    rewritten = sorted(n for n in after if before.get(n, (None,))[0] != after[n][0])

    shutil.rmtree(package / '.lake/build')
    rebuilt_cold = build(package, work / 'cold-edited.log')
    cold = oleans(package)
    differing = sorted(n for n in set(cold) | set(after) if cold.get(n, (0, ''))[1] != after.get(n, (0, ''))[1])

    generated = [n for n in warm_built if n == GEN or n.startswith(GEN + '.')]
    report = dict(edited_function=EDITED, generated_modules=len([n for n in before if n.startswith(GEN)]),
                  changed_text=keys['changed'], invalidated=keys['invalidated'],
                  warm_built=warm_built, warm_rewritten_oleans=rewritten,
                  cold_built=len(cold_built), cold_after_edit_built=len(rebuilt_cold),
                  warm_vs_cold_olean_differences=differing)
    text = json.dumps(report, indent=2)
    print(text)
    if args.report:
        args.report.write_text(text + '\n')
    assert keys['changed'] == [f'{GEN}.F_digit'], keys
    assert keys['invalidated'] == sorted([GEN, f'{GEN}.F_bumpDigit', f'{GEN}.F_digit']), keys
    assert generated == keys['invalidated'], (generated, keys['invalidated'])
    assert sorted(set(warm_built) - set(generated)) == ['Demo.Layout.Proofs'], warm_built
    assert 'Demo.Layout.Mem' not in rewritten and 'Demo.Layout.Mem' in cold, rewritten
    assert set(rewritten) <= set(warm_built), (rewritten, warm_built)
    assert not differing, differing
    print('modular-output Lake incremental checks passed')


if __name__ == '__main__':
    main()
