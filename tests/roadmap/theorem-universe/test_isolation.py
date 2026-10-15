#!/usr/bin/env python3
"""Real compile/extract/replay regression; run under the ordinary workspace build guard."""
import json
from pathlib import Path
import sys
import tempfile
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
import assumptions
import theorem_universe as universe


def check():
    with tempfile.TemporaryDirectory(prefix='air2lean-module-isolation-') as temp:
        root = Path(temp)
        (root / 'lean-toolchain').write_bytes((ROOT / 'lean-toolchain').read_bytes())
        (root / 'lakefile.toml').write_bytes((ROOT / 'lakefile.toml').read_bytes())
        (root / 'scripts').symlink_to(ROOT / 'scripts', target_is_directory=True)
        built = root / '.lake/build/lib/lean'
        built.mkdir(parents=True)
        actual = ROOT / '.lake/build/lib/lean'
        for name in assumptions.LAKE_ROOTS:
            for source in actual.glob(name + '*'):
                if source.name == name or source.name.startswith(name + '.'):
                    (built / source.name).symlink_to(source, target_is_directory=source.is_dir())
        standard = Path(assumptions.lake_env('LEAN_SYSROOT')) / 'lib/lean'
        stale = root / 'stale'
        (stale / 'tests').mkdir(parents=True)
        source = stale / 'tests/Picked.lean'
        source.write_text('namespace IsolationFixture\ndef value : Nat := 1\nend IsolationFixture\n')
        shared = built / 'tests/Picked.olean'
        with patch.object(universe, 'ROOT', root):
            error = universe.compile_unit(str(source), str(stale), shared,
                                          [built, standard], root / 'stale.log')
            if error:
                raise AssertionError(error)
            original = shared.read_bytes()
            (root / 'tests').mkdir()
            (root / 'tests/Picked.lean').write_text(
                'namespace IsolationFixture\ndef value : Nat := 2\n'
                'theorem checked : value = 2 := rfl\nend IsolationFixture\n')
            (root / 'tests/Client.lean').write_text(
                'import tests.Picked\ntheorem IsolationFixture.client : '
                'IsolationFixture.value = 2 := rfl\n')
            picked = universe.Unit('tests/Picked.lean', '.', 'tests.Picked', (), (), None,
                                   ('IsolationFixture.value', 'IsolationFixture.checked'))
            client = universe.Unit('tests/Client.lean', '.', 'tests.Client', (picked.file,), (), None,
                                   ('IsolationFixture.client',))
            units = [picked, client]
            by_file = {u.file: u for u in units}
            output = root / '.lake/universe'
            base = universe.base_paths(output)
            errors = universe.compile_all(units, by_file, output, base=base)
            if errors:
                raise AssertionError(errors)
            runs, errors = universe.audit_bundles(units, by_file, output, None, base=base)
            if errors or any(r['status'] != 'pass' for r in runs):
                raise AssertionError((runs, errors))
            report = json.loads(Path(runs[0]['report']).read_text())
            if not {'tests.Picked', 'tests.Client'} <= set(report['module_imports']):
                raise AssertionError('actual extractor omitted the private import metadata')
            selected = next(r for r in report['freshness']['artifacts'] if r['module'] == picked.module)
            private = universe.lib_of(output, '.') / 'tests/Picked.olean'
            if Path(selected['olean']).resolve() != private.resolve():
                raise AssertionError('audit did not bind the actual private artifact')
            if shared.read_bytes() != original:
                raise AssertionError('the shared cache fixture was changed')
            # A foreign cache-only import is blocked even though the canonical Lake root
            # is available for the stock checker's real-path module-name enumeration.
            blocked_source = root / 'ForeignOnly.lean'
            blocked_source.write_text('import tests.Picked\n')
            error = universe.compile_unit(str(blocked_source), str(root),
                                          output / 'blocked/ForeignOnly.olean',
                                          universe.private_paths(base, [output / 'blocked']), output / 'blocked.log')
            if not error:
                raise AssertionError('a foreign cache-only import escaped its prefix blocker')
            diagnostic = (output / 'blocked.log').read_text()
            if str(base[1][0]) not in diagnostic or 'Picked.olean' not in diagnostic:
                raise AssertionError('the foreign import failed for an unrelated reason: ' + diagnostic)
            child_source = stale / 'tests/Picked/Child.lean'
            child_source.parent.mkdir(parents=True)
            child_source.write_text('theorem IsolationFixture.cachedChild : True := True.intro\n')
            child_olean = built / 'tests/Picked/Child.olean'
            error = universe.compile_unit(str(child_source), str(stale), child_olean,
                                          [built, standard], output / 'cached-child.log')
            if error:
                raise AssertionError(error)
            private_paths = universe.private_paths(base, [universe.lib_of(output, '.')])
            rejected = assumptions.kernel_replay({picked.module: assumptions.file_sha256(private)},
                                                  standard.parent.parent,
                                                  universe.path_text(private_paths))
            rejection = next((r['output'] for r in rejected['rejected'] if r['module'] == picked.module), '')
            if rejected['status'] != 'fail' or 'Picked/Child.olean' not in rejection:
                raise AssertionError('the cached child did not fail closed at private resolution: ' + rejection)
            print('cached child blocked: ' + rejection.strip())
            assumptions.remove_module_outputs(child_olean)  # Only this test's temporary artifact.
            private.unlink()
            try:
                universe.audit_bundles(units, by_file, output, None, base=base)
            except (FileNotFoundError, ValueError):
                pass
            else:
                raise AssertionError('missing private output silently reused the shared artifact')
            # A previous Lake replay must not survive a changed external import, even
            # when the Lake artifact and the aggregate Lake-library key stay identical.
            if (built / 'Proofs').is_symlink():
                (built / 'Proofs').unlink()  # Only our fixture alias; preserve the actual library.
            (built / 'Proofs').mkdir()
            (root / 'Proofs').mkdir()
            foreign = root / 'foreign'
            foreign.mkdir()
            foreign_source = foreign / 'Foo.lean'
            foreign_source.write_text('namespace CacheBoundary\ndef value : Nat := 1\nend CacheBoundary\n')
            cache_source = root / 'Proofs/CacheImport.lean'
            cache_source.write_text('import Foo\nnamespace CacheBoundary\n'
                                    'theorem cached : value = 1 := rfl\nend CacheBoundary\n')
            foreign_olean = foreign / 'Foo.olean'
            cache_olean = built / 'Proofs/CacheImport.olean'
            paths = universe.private_paths(universe.base_paths(output), [foreign])
            for file, source_root, artifact in ((foreign_source, foreign, foreign_olean),
                                                 (cache_source, root, cache_olean)):
                error = universe.compile_unit(str(file), str(source_root), artifact, paths,
                                              output / (artifact.stem + '.log'))
                if error:
                    raise AssertionError(error)
            # Inspect the actual fixture import headers directly. This test-only library
            # intentionally replaces Proofs; the production extractor rejects such paths.
            driver = root / 'ImportHeaders.lean'
            driver.write_text('import Lean\nimport Proofs.CacheImport\nopen Lean Elab Command Meta in\nrun_cmd do\n'
                              '  let env ← getEnv\n'
                              '  let rows := (env.header.modules.zip env.header.moduleData).map '
                              'fun (entry, data) => (entry.module.toString, '
                              'if entry.hasData then toJson (data.imports.map (·.module.toString)) else Json.null)\n'
                              '  liftIO <| IO.println ("IMPORTS:" ++ (Json.mkObj rows.toList).compress)\n')
            inspected = universe.run(assumptions.lean_command([str(driver)], universe.path_text(paths)))
            lines = [line[len('IMPORTS:'):] for line in inspected.stdout.splitlines() if line.startswith('IMPORTS:')]
            if inspected.returncode or len(lines) != 1:
                raise AssertionError(inspected.stdout)
            imports = json.loads(lines[0])
            toolchain = standard.parent.parent
            with patch.object(assumptions, 'ROOT', root):
                lake_key = assumptions.compiled_inputs_sha256([built], toolchain)
                digests = {'Foo': assumptions.file_sha256(foreign_olean),
                           'Proofs.CacheImport': assumptions.file_sha256(cache_olean)}
                cache = output / 'cross-root-replay.json'
                seeded = assumptions.kernel_replay(digests, toolchain, universe.path_text(paths), cache,
                                                    frozenset({'Proofs.CacheImport'}), lake_key)
                if seeded['status'] != 'pass':
                    raise AssertionError(seeded)
                foreign_source.write_text('namespace CacheBoundary\ndef value : Nat := 2\nend CacheBoundary\n')
                error = universe.compile_unit(str(foreign_source), str(foreign), foreign_olean, paths,
                                              output / 'changed-foreign.log')
                if error:
                    raise AssertionError(error)
                if assumptions.file_sha256(cache_olean) != digests['Proofs.CacheImport']:
                    raise AssertionError('the cached Lake artifact changed')
                if assumptions.compiled_inputs_sha256([built], toolchain) != lake_key:
                    raise AssertionError('the Lake-library key changed')
                cacheable = assumptions.cacheable_modules(imports, ['Proofs.CacheImport'],
                                                         paths, toolchain)
                if cacheable:
                    raise AssertionError('an external import was admitted to cached replay')
                digests['Foo'] = assumptions.file_sha256(foreign_olean)
                checked = assumptions.kernel_replay(digests, toolchain, universe.path_text(paths), cache,
                                                     cacheable, lake_key)
                rejection = next((r['output'] for r in checked['rejected']
                                  if r['module'] == 'Proofs.CacheImport'), '')
                if checked['status'] != 'fail' or 'kernel' not in rejection.lower():
                    raise AssertionError('the changed import did not force rejection of the old proof')
                print('changed import rejected: ' + rejection.strip())
        print('module isolation pass: private source compiled, extracted and replayed; '
              'shared artifact preserved; missing private output rejected; '
              'changed external import forces fresh kernel rejection')


if __name__ == '__main__':
    check()
