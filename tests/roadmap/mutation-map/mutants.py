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
INVENTORY = 'tests/roadmap/inventory/test_inventory.py'
THEOREMS = 'tests/roadmap/theorem-inventory/test_inventory.py'
PREMISES = 'tests/roadmap/premises/test_premises.py'
RELEASE = 'tests/roadmap/release-record/test_release_record.py'
VC_REPORT = 'tests/roadmap/vcs/test_vc_report.py'
CLOSURE = 'tests/roadmap/dependency-closure/test_dependency_closure.py'
EXPORT = 'tests/roadmap/project-export/test_project_export.py'
MODULE_KEYS = 'tests/roadmap/modular-output/test_keys.py'
PROJECT_CHECK = 'tests/roadmap/project-check/test_check.py'
ACCOUNTING = 'tests/roadmap/host-accounting/test_accounting.py'

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
    # L01: an inventory row left as the unclassified placeholder must fail generate/check.
    'inventory-forbidden-row-accepted': (
        'scripts/coverage.py', " or row['disposition'] == FORBIDDEN:", ':',
        INVENTORY, 'coverage', ('InventoryTests.test_disposition_problems_fail_closed',)),
    # L01: a reviewed override whose mechanical premise changed must become unclassified.
    'inventory-stale-override-applied': (
        'scripts/coverage.py', "    elif override['replaces'] == row['disposition']:\n", '    elif True:\n',
        INVENTORY, 'coverage', ('InventoryTests.test_stale_override_is_forbidden',)),
    # E04: a rejected row of the std model table must not be inventoried as a recognized model.
    'std-model-rejected-row-recognized': (
        'scripts/coverage.py',
        "'disposition': 'translation-rejected' if fn == 'rejectedThreadFn?' else 'recognized-model-boundary'",
        "'disposition': 'recognized-model-boundary'",
        INVENTORY, 'coverage', ('InventoryTests.test_model_recognition_is_not_verification',)),
    # E01: a proved contract whose evidence uses a non-standard axiom stays an assumption.
    'contract-nonstandard-axiom-verified': (
        'scripts/external-contracts.py', '    extra = sorted(set(axioms) - STANDARD_AXIOMS)\n', '    extra = []\n',
        'tests/roadmap/models/test_external_contracts.py', 'contracts',
        ('ContractReportTests.test_nonstandard_axioms_stay_assumptions',)),
    # D02: a recorded check result goes stale when an imported proof source changes.
    # F05: a per-version theorem (e.g. `op128_spec_full`) needs a check result against each
    # version's own translation (`tests/golden/<v>/<ex>/Gen.lean`), not only the committed one.
    'theorem-inventory-version-translation-collapsed': (
        'scripts/theorem-inventory.py', '        if not (root / default).is_file():\n',
        '        if True:\n', THEOREMS, 'ti',
        ('FixtureTests.test_translations_follow_check_sh',)),
    'theorem-inventory-stale-proof-accepted': (
        'scripts/theorem-inventory.py',
        '                return sources.get(mod) == sha256(root / module_path(mod))\n',
        '                return True\n', THEOREMS, 'ti',
        ('FixtureTests.test_edited_proof_or_translation_is_stale',)),
    # D02: a document must not say "every schedule" of a single-schedule theorem.
    'theorem-inventory-narrow-claim-accepted': (
        'scripts/theorem-inventory.py',
        "                    narrower = by_name.get(token, set()) - {'all-schedules'}\n",
        '                    narrower = set()\n', THEOREMS, 'ti',
        ('FixtureTests.test_narrow_theorem_labeled_all_schedules_in_docs',)),
    # T06: a probe profile of another optimize mode must not qualify a mode/backend record.
    'build-mode-profile-mode-unchecked': (
        'scripts/build-modes.py', "        if profile.get('build_mode') != mode:\n", '        if False:\n',
        'tests/roadmap/build-modes/test_build_modes.py', 'bm',
        ('NegativeControls.test_profile_mode_mismatch',)),
    # P08: an automation limit (timeout, cap, fuel) is never a counterexample.
    'counterexample-automation-limit-is-bug': (
        'scripts/counterexample.py', '        return UNSOLVED, automation, None\n',
        '        return COUNTEREXAMPLE, automation, None\n',
        'tests/roadmap/counterexamples/test_counterexample.py', 'CX',
        ('Bundles.test_verdict_table_never_calls_an_automation_limit_a_bug',)),
    # Q05: a CI job on another host must not back a declared target path.
    'target-matrix-foreign-host-accepted': (
        'scripts/target-matrix.py', '    if job_host != host:\n', '    if False:\n',
        'tests/roadmap/target-matrix/test_target_matrix.py', 'TM',
        ('ForeignGoldens.test_linux_job_compiling_the_darwin_golden_cannot_back_a_darwin_path',)),
    # D03: a premise the kernel graph reaches but the source index misses is a source gap
    # (`premises.py compiled --strict` fails on it).
    'premises-compiled-source-gap-hidden': (
        'scripts/premises.py',
        '                entry["source_gaps"] = sorted(set(entry["premises"]) - known, key=premise_key)\n',
        '                entry["source_gaps"] = []\n', PREMISES, 'premises',
        ('CompiledTests.test_compiled_source_gaps',)),
    # D03: a runtime module reached by a theorem must map to premises.
    'premises-compiled-runtime-module-unmapped': (
        'scripts/premises.py',
        '                errors.append(f"{theorem[\'name\']}: runtime module {module} has no premise mapping")\n',
        '                pass\n', PREMISES, 'premises',
        ('CompiledTests.test_compiled_unmapped_module_and_axiom',)),
    # Q08: a pull_request run tests a merge commit, not the recorded revision.
    'release-record-pull-request-run-accepted': (
        'scripts/release-record.py', "    if data['event'] not in ('push', 'workflow_dispatch'):\n",
        "    if data['event'] not in ('push', 'workflow_dispatch', 'pull_request'):\n", RELEASE, 'rr',
        ('RecordTests.test_evidence_for_another_revision_is_refused',)),
    # Q08: a failed step must never be published as passed when other evidence passes.
    'release-record-failure-masked': (
        'scripts/release-record.py',
        "            gate['status'] = 'failed' if 'failed' in statuses else 'passed' if statuses else 'missing'\n",
        "            gate['status'] = 'passed' if statuses else 'missing'\n", RELEASE, 'rr',
        ('RecordTests.test_failures_and_skips_are_never_passed_or_hidden',
         'RecordTests.test_conflicting_evidence_fails_the_gate')),
    # Q08: every review ledger entry names the revision it reviewed.
    'release-ledger-revision-unchecked': (
        'scripts/release-record.py', '        if not SHA1.fullmatch(reviewed):\n', '        if False:\n',
        RELEASE, 'rr', ('LedgerTests.test_entry_without_reviewed_revision_fails',)),
    # P02: a Lean error (e.g. a failed vc_gen? contract) must not be hidden by the report.
    'vc-report-lean-error-masked': (
        'scripts/vc-report.py',
        '            if m.get("severity") == "error" and PREFIX not in str(m.get("data", ""))]',
        '            if False]', VC_REPORT, 'VC',
        ('ReportTests.test_lean_errors_are_surfaced_and_reports_are_not_errors',)),
    # P02: an obligation without a closing hypothesis stays open in the report.
    'vc-report-open-obligations-hidden': (
        'scripts/vc-report.py',
        '        open_count = sum(1 for item in obligations if item["closed_by"] is None)\n',
        '        open_count = 0\n', VC_REPORT, 'VC',
        ('ReportTests.test_open_obligations_are_counted_and_closed_ones_named',)),
    # I02: a callee without AIR must be reported missing, never counted as exported.
    'closure-missing-callee-hidden': (
        'scripts/dependency-closure.py', "    missing = [n for n in nodes if n['class'] == 'missing']\n",
        '    missing = []\n', CLOSURE, 'closure',
        ('ClassTests.test_missing_transitive_callee_reports_exact_fqn_chain_and_filter',)),
    # I01: a module whose bytes differ from its manifest pin must stop the export.
    'export-source-pin-unchecked': (
        'scripts/project-export.py', "        if 'sha256' in module and actual != module['sha256']:\n",
        '        if False:\n', EXPORT, 'export', ('ExportTest.test_source_pins',)),
    # I04: a module key must cover the keys of the generated modules it imports.
    'module-key-imports-ignored': (
        'scripts/module-split.py',
        '            imports=[[i, result[i]["key"] if i in result else None] for i in sorted(m["imports"])]))\n',
        '            imports=[]))\n', MODULE_KEYS, 'ms', ('KeyTests.test_keys',)),
    # I03: two records reproduce each other only if both checks passed.
    'record-comparison-status-ignored': (
        'scripts/project.py',
        "    reproduced = not differences and all(s == 'reproduced' for s in statuses.values())\n",
        '    reproduced = not differences\n', PROJECT_CHECK, 'project',
        ('CompareRecordsTests.test_failed_record_with_equal_sections_is_not_reproduced',)),
    # Q04: a published headline that counts excluded cases as successful comparisons must fail.
    'accounting-headline-unchecked': (
        'scripts/accounting.py', "    if headline != totals.get('exact_matches'):\n", '    if False:\n',
        ACCOUNTING, 'ACC', ('Check.test_headline_including_exclusions_fails',)),
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
