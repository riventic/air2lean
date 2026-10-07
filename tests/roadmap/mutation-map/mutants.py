#!/usr/bin/env python3
"""Python-side semantic mutants for Q02 (assurance/mutation-map.json). No Lean, Lake or Zig.

Each mutant replaces one exact anchor in a repository script, compiles the result under the
script's real path (so `__file__`-relative roots are unchanged) and swaps it into the module
global of an existing regression test that loaded the script. Only the named killing tests run.

A mutant is killed only when
  * the unmutated script passes every named test (control), and
  * at least one named test then reports an assertion *failure*.
An exception (`ERROR`) in a test is not a kill: a mutant that merely crashes does not show that a
negative test detects the wrong behaviour. Nothing is written to disk.

Usage: mutants.py [--list] [NAME ...]   (default: every mutant; exit 1 if any survives)
"""
import argparse
import importlib.util
import io
from pathlib import Path
import sys
import types
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]

PROFILES = 'tests/roadmap/profiles/test_golden_pipeline.py'
FLOATS = 'tests/roadmap/float-semantics/test_labels.py'

# name -> (script, anchor, replacement, test file, module global holding the script, killing tests)
MUTANTS = {
    # T01: legacy (pre-12) AIR selects the named legacy profile, not schema-12 validation.
    'profile-legacy-schema-misrouted': (
        'scripts/normalize-generated.py', '    if schema < 12:\n', '    if schema < 11:\n',
        PROFILES, 'HELPER', ('ReceiptTests.test_legacy_schema_selects_legacy_profile',)),
    # T01: an unknown profile name must not be selected as abi64-le-v1.
    'profile-name-unchecked': (
        'scripts/normalize-generated.py', '    if (p["name"] != "abi64-le-v1" or p["zig_version"]',
        '    if (p["zig_version"]', PROFILES, 'HELPER',
        ('ReceiptTests.test_unknown_profile_name_is_rejected',)),
    # V05: a future AIR schema must fail closed.
    'profile-future-schema-accepted': (
        'scripts/normalize-generated.py', 'not 1 <= schema <= 12', 'not 1 <= schema <= 13',
        PROFILES, 'HELPER', ('ReceiptTests.test_future_schema_fails_closed',)),
    # F01: translate.args selects compiler-rt; the label check must see that selection.
    'float-args-selection-ignored': (
        'scripts/float-semantics.py', "            return tokens[i + 1]\n", "            return 'ieee'\n",
        FLOATS, 'fs', ('SourceTests.test_compiler_rt_label_needs_compiler_rt_translation',)),
    # F01: the generated header's float mode takes precedence over translate.args.
    'float-header-selection-ignored': (
        'scripts/float-semantics.py', "            return metadata.get('float_semantics')\n", '',
        FLOATS, 'fs', ('SourceTests.test_compiler_rt_label_needs_compiler_rt_translation',)),
    # I09: release metadata must reject a host outside the supported host set.
    'compat-unknown-host-accepted': (
        'scripts/compat.py', ' or any(h not in KNOWN_HOSTS for h in hosts)', '',
        'tests/roadmap/distribution/test_compat.py', 'compat', ('Compat.test_hosts_default_and_linux_only_rule',)),
    # V04: a trust violation reached only through a dependency must transfer to the theorem.
    'audit-dependency-violation-not-transferred': (
        'scripts/assumptions.py', '                pending.extend(nodes[name]["dependencies"])\n',
        '                pass\n', 'tests/roadmap/assurance/test_policy.py', 'audit',
        ('PolicyTests.test_violation_transfers_through_dependencies',)),
    # D01: the ROADMAP header counts must be checked against the register.
    'support-matrix-header-unchecked': (
        'scripts/support-matrix.py', "    if header not in read(root, 'ROADMAP.md'):",
        '    if False:', 'tests/roadmap/support-matrix/test_support_matrix.py', 'MATRIX',
        ('Stale.test_register_status_change_is_stale',)),
}


def load_test_module(path):
    spec = importlib.util.spec_from_file_location('q02_mutant_target_' + Path(path).stem, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def mutated_binding(original, script, anchor, replacement):
    """Build the mutated script in the same shape (module or runpy dict) as `original`."""
    path = ROOT / script
    source = path.read_text()
    if source.count(anchor) != 1:
        raise ValueError(f'{script}: mutation anchor must occur exactly once: {anchor!r}')
    code = compile(source.replace(anchor, replacement), str(path), 'exec')
    if isinstance(original, dict):
        namespace = {'__name__': '<run_path>', '__file__': str(path)}
        exec(code, namespace)
        return namespace
    if not isinstance(original, types.ModuleType):
        raise TypeError(f'{script}: unsupported binding {type(original).__name__}')
    module = types.ModuleType(original.__name__)
    module.__file__ = str(path)
    saved = sys.modules.get(original.__name__)
    sys.modules[original.__name__] = module  # dataclasses and the like resolve their module
    try:
        exec(code, module.__dict__)
    finally:
        if saved is None:
            sys.modules.pop(original.__name__, None)
        else:
            sys.modules[original.__name__] = saved
    return module


def run_tests(module, names):
    suite = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromName(n, module) for n in names)
    result = unittest.TextTestRunner(stream=io.StringIO(), verbosity=0).run(suite)
    if result.testsRun != len(names):
        raise ValueError(f'expected {len(names)} killing tests, ran {result.testsRun}')
    return result


def run_mutant(name, mutants=None):
    """Return the killing test ids; raise if the control fails or the mutant survives."""
    script, anchor, replacement, test, binding, kills = (mutants or MUTANTS)[name]
    control = run_tests(load_test_module(test), kills)
    if not control.wasSuccessful():
        raise AssertionError(f'{name}: control does not pass its killing tests')
    module = load_test_module(test)
    setattr(module, binding, mutated_binding(getattr(module, binding), script, anchor, replacement))
    result = run_tests(module, kills)
    killed = [case.id() for case, _ in result.failures]
    if not killed:
        detail = 'errors only (not a kill)' if result.errors else 'no failing test'
        raise AssertionError(f'{name}: mutant survived: {detail}')
    return killed


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    parser.add_argument('--list', action='store_true', help='print mutant names and exit')
    parser.add_argument('names', nargs='*')
    args = parser.parse_args(argv)
    if args.list:
        print('\n'.join(MUTANTS))
        return 0
    unknown = sorted(set(args.names) - set(MUTANTS))
    if unknown:
        parser.error('unknown mutant: ' + ', '.join(unknown))
    survivors = 0
    for name in args.names or MUTANTS:
        try:
            killed = run_mutant(name)
        except (AssertionError, ValueError) as error:
            survivors += 1
            print(f'SURVIVED {error}')
        else:
            print(f'killed {name}: ' + ', '.join(t.rsplit('.', 2)[-2] + '.' + t.rsplit('.', 1)[-1] for t in killed))
    return 1 if survivors else 0


if __name__ == '__main__':
    sys.exit(main())
