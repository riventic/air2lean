#!/usr/bin/env python3
"""T06: the stage2_x86_64 translations that a self-hosted x86_64 differential run tests.

  stage2-translations.py --version V --examples "EX ..." --out DIR [--zig-air ZIG]

For each example, export its AIR with the patched compiler (scripts/zig-air.sh V, or --zig-air)
for the self-hosted x86_64 backend (`build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing
-fno-llvm -target x86_64-linux-gnu -mcpu=baseline`, the filters of scripts/check.sh), and translate
it under that stage2_x86_64 profile (`--allow-unqualified-build-mode`, plus the example's
translate.args). Then:

* the translator accepts it: its semantics must equal the translation the run's Lean side builds
  (the run is scripts/diff.sh in the checkout: tests/golden/V/<ex>/Gen.lean, else
  Proofs/<Ex>/Gen.lean), compared after the profile header (scripts/normalize-generated.py), so
  the native stage2 binary is compared with its own backend's translation. A different
  translation is an error: the run would test the wrong model.
* the translator rejects it (a stage2_x86_64 rule, `CheckCtx.checkStage2Backend`): the example
  is left out of the run, with the diagnostics, in DIR/excluded-examples.json (the format of
  scripts/build-modes.py record --excluded-examples).

DIR/examples gets the accepted examples (space-separated). Exit 0 unless an export fails or an
accepted translation differs.
"""
import argparse
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPRODUCER = 'tests/roadmap/build-modes/reproducers/stage2-x86_64-divergences.zig'
# Examples that the self-hosted backend cannot compile (no code, nothing to compare).
COMPILE_ERRORS = ROOT / 'tests/roadmap/build-modes/reproducers/excluded-asm-stage2.json'
# Diagnostic fragments of the translator's backend rules: `CheckCtx.checkStage2Backend` ("outside
# the stage2_x86_64 profile") and the LLVM-only layouts ("for the LLVM backend").
BACKEND_RULES = ('stage2_x86_64', 'LLVM backend')


def namespace(ex):
    return ex[:1].upper() + ex[1:]


def filters(ex, version):
    out = [f'{ex}.']
    for name in ('filter', f'filter-{version}'):
        path = ROOT / 'examples' / ex / name
        if path.is_file():
            out += [line for line in path.read_text(encoding='utf-8').splitlines() if line]
    return ','.join(out)


def committed_gen(ex, version):
    golden = ROOT / 'tests/golden' / version / ex / 'Gen.lean'
    return golden if golden.is_file() else ROOT / 'Proofs' / namespace(ex) / 'Gen.lean'


def run(argv, **kw):
    return subprocess.run(argv, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, check=False, **kw)


def translate(ex, version, zig_air, tmp):
    air = tmp / ex / 'air'
    air.mkdir(parents=True)
    env = dict(os.environ, ZIG_AIR_JSON_DIR=str(air), ZIG_AIR_JSON_FILTER=filters(ex, version))
    exported = run([zig_air, 'build-obj', '-fno-emit-bin', '-OReleaseSafe', '-fno-error-tracing',
                    '-fno-llvm', '-target', 'x86_64-linux-gnu', '-mcpu=baseline',
                    f'examples/{ex}/{ex}.zig'], env=env)
    if exported.returncode or not any(air.glob('*.json')):
        raise RuntimeError(f'{ex}: the stage2_x86_64 AIR export failed:\n{exported.stderr[-2000:]}')
    args_file = ROOT / 'examples' / ex / 'translate.args'
    extra = shlex.split(args_file.read_text(encoding='utf-8')) if args_file.is_file() else []
    gen = tmp / ex / 'Gen.lean'
    done = run(['.lake/build/bin/air2lean', str(air), '-o', str(gen), '--namespace', namespace(ex),
                '--prefix', f'{ex}.', '--allow-unqualified-build-mode', *extra])
    if done.returncode:
        report = run(['.lake/build/bin/air2lean', '--diagnostics-json', str(air),
                      '--allow-unqualified-build-mode'])
        try:
            diagnostics = [f'{d["function"]}: {d["message"]}' for d in json.loads(report.stdout)['diagnostics']
                           if d.get('function')]
        except (ValueError, KeyError):
            diagnostics = [done.stderr.strip()[-1000:]]
        # Only a backend rule excludes the example: any other rejection of the export (a
        # translator regression, a construct outside the subset) fails the run, never shrinks it.
        if not any(rule in text for rule in BACKEND_RULES for text in [done.stderr, *diagnostics]):
            raise RuntimeError(f'{ex}: the stage2_x86_64 export is rejected by no backend rule:\n'
                               f'{done.stderr[-2000:]}')
        return None, diagnostics
    receipt = tmp / ex / 'report.json'
    for argv in (['scripts/normalize-generated.py', 'report', str(gen), str(air), str(receipt)],
                 ['scripts/normalize-generated.py', 'compare', str(committed_gen(ex, version)),
                  str(gen), str(receipt)]):
        checked = run([sys.executable, '-B', *argv])
        if checked.returncode:
            raise RuntimeError(f'{ex}: the stage2_x86_64 translation is not the run\'s '
                               f'{committed_gen(ex, version).relative_to(ROOT)}:\n'
                               f'{checked.stdout[-1500:]}{checked.stderr[-1500:]}')
    return gen, []


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    parser.add_argument('--version', required=True)
    parser.add_argument('--examples', required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--zig-air')
    args = parser.parse_args(argv)
    zig_air = args.zig_air or run(['scripts/zig-air.sh', args.version]).stdout.strip()
    if not zig_air or not Path(zig_air).is_file():
        print(f'error: no patched compiler for {args.version}', file=sys.stderr)
        return 1
    # The translator of this checkout, not a stale .lake/build/bin/air2lean.
    built = run(['lake', 'build', 'air2lean'])
    if built.returncode:
        print(f'error: lake build air2lean failed:\n{built.stdout[-2000:]}{built.stderr[-2000:]}', file=sys.stderr)
        return 1
    compile_errors = {e['example']: e for e in json.loads(COMPILE_ERRORS.read_text(encoding='utf-8'))}
    accepted, excluded = [], []
    with tempfile.TemporaryDirectory(prefix='air2lean-stage2-') as tmp:
        for ex in args.examples.split():
            if ex in compile_errors:
                excluded.append(compile_errors[ex])
                continue
            try:
                gen, diagnostics = translate(ex, args.version, zig_air, Path(tmp))
            except RuntimeError as error:
                print(f'error: {error}', file=sys.stderr)
                return 1
            if gen is None:
                excluded.append({'example': ex, 'reason': 'rejected by the translator',
                                 'reproducer': REPRODUCER,
                                 'note': 'The stage2_x86_64 export is outside the subset '
                                         '(CheckCtx.checkStage2Backend): ' + ' | '.join(diagnostics)})
                print(f'{ex}: rejected on the stage2_x86_64 profile ({len(diagnostics)} diagnostics)')
            else:
                accepted.append(ex)
                print(f'{ex}: stage2_x86_64 translation = {committed_gen(ex, args.version).relative_to(ROOT)}')
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / 'excluded-examples.json').write_text(json.dumps(excluded, indent=2) + '\n', encoding='utf-8')
    (args.out / 'examples').write_text(' '.join(accepted) + '\n', encoding='utf-8')
    return 0


if __name__ == '__main__':
    sys.exit(main())
