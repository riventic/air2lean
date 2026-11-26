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
CLOSURE = 'tests/roadmap/dependency-closure/test_dependency_closure.py'
EXPORT = 'tests/roadmap/project-export/test_project_export.py'
MODULE_KEYS = 'tests/roadmap/modular-output/test_keys.py'
PROJECT_CHECK = 'tests/roadmap/project-check/test_check.py'
ACCOUNTING = 'tests/roadmap/host-accounting/test_accounting.py'
TUTORIALS = 'tests/roadmap/tutorials/test_tutorials.py'
DIAGNOSTICS = 'tests/roadmap/project-diagnostics/test_project_diagnostics.py'
UNIVERSE = 'tests/roadmap/theorem-universe/test_universe.py'
RECEIPTS = 'tests/roadmap/proof-receipts/test_receipt.py'
POLICY = 'tests/roadmap/assurance/test_policy.py'
CLAIMS = 'tests/roadmap/claims/test_claims.py'
COVERAGE = 'tests/roadmap/coverage-report/test_coverage.py'
OUTCOMES = 'tests/roadmap/outcome-accounting/test_report.py'
OUTCOME_CONTRACTS = 'tests/roadmap/outcome-taxonomy/test_theorem_contracts.py'
PERF = 'tests/roadmap/perf-budgets/test_perf_budgets.py'
SAFE = 'tests/roadmap/safe-output/test_safe_output.py'
QUALIFY = 'tests/roadmap/upgrade-qualification/test_qualify.py'
SCHEDULES = 'tests/roadmap/schedule-caps/test_exploration.py'
AIR_VALIDATE = 'tests/roadmap/export-validation/test_validate_air.py'
TRUST = 'tests/roadmap/export-validation/test_trust_report.py'
ABI = 'tests/roadmap/abi-probes/test_probe.py'
FUZZ = 'tests/roadmap/fuzz/test_fuzz.py'
FINGERPRINTS = 'tests/roadmap/stable-generation/test_fingerprints.py'
FINGERPRINT_TEST = 'FingerprintTests.test_fold_invalidation_and_sidecar_checks'
WASM = 'tests/roadmap/wasm-correspondence/test_correspondence.py'
C_FRONTEND = 'tests/roadmap/c-frontend/test_run.py'

# name -> (script, anchor, replacement, test file, module global holding the script, killing tests)
MUTANTS = {
    # V06: the declaration must contain every outcome the audited postcondition permits.
    'outcome-contract-ignores-theorem': (
        'scripts/outcomes.py', '    if missing:\n', '    if False:\n',
        OUTCOME_CONTRACTS, 'outcomes', ('TheoremContractTests.test_narrower_than_theorem_fails_without_samples',)),
    # V06 (F3): a host allowance must type each differing float, not accept any difference.
    'diff-host-difference-untyped': (
        'scripts/diff-report.py', '        kinds = leaf_host_kinds(*pair) & allowed\n', '        kinds = allowed\n',
        OUTCOMES, 'REPORT', ('Outcomes.test_untyped_host_differences_are_mismatches',
                             'Outcomes.test_host_kind_predicates_check_the_values')),
    # V06 (F3): a host-listed function's native signal against a model value is a mismatch.
    'diff-host-masks-non-values': (
        'scripts/diff-report.py', '    if host and nkind == mkind == Kind.VALUE: return Status.HOST\n',
        '    if host: return Status.HOST\n', OUTCOMES, 'REPORT',
        ('Outcomes.test_native_signal_is_excluded_only_for_model_exclusion',)),
    # V06 (F3): a model exclusion counts only on an input pinned for it.
    'diff-exclusion-unpinned': (
        'scripts/diff-report.py', "        if pinned or (search and (search['status'] == 'capped' or search['saw_no_result'])):\n",
        '        if True:\n', OUTCOMES, 'REPORT', ('Outcomes.test_model_exclusion_needs_a_pin_for_its_input',)),
    # L13 (S7): a claim over an asm opaque carries the allowlist fault-condition premise.
    'claims-asm-fault-premise-dropped': (
        'scripts/claims.py', "    if ABSENCE_CLAIMS & set(claims) and FAULT_PREMISE not in found \\\n",
        "    if False and FAULT_PREMISE not in found \\\n", 'tests/roadmap/claims/test_claims.py', 'claims',
        ('ClassifyTests.test_asm_closure_carries_fault_premise',)),
    # C12: a concurrency claim must list the memory-model adequacy premise.
    'claims-memory-model-premise-dropped': (
        'scripts/claims.py', "    return [model['premise']] if set(model['concurrency']) & set(reached) else []\n",
        "    return []\n", 'tests/roadmap/claims/test_claims.py', 'claims',
        ('ClassifyTests.test_concurrency_claim_lists_memory_model_premise',)),
    # C12: a claim that rests on a target-qualified premise (ORD-06) needs a qualified target.
    'claims-target-binding-dropped': (
        'scripts/claims.py', "    if unqualified:\n", "    if False:\n",
        'tests/roadmap/claims/test_claims.py', 'claims',
        ('ClassifyTests.test_concurrency_claim_needs_a_qualified_target',)),
    # C12: a theorem that carries a target-qualified premise over a translation for a target
    # without a qualification entry fails the premise index.
    'premises-target-binding-dropped': (
        'scripts/premises.py', '            elif target not in record["targets"]:\n', '            elif False:\n',
        PREMISES, 'premises', ('FixtureTests.test_target_qualified_premise_needs_a_qualified_target',
                               'CompiledTests.test_compiled_concurrency_needs_a_qualified_target')),
    # T01: legacy (pre-12) AIR selects the named legacy profile, not schema-12 validation.
    'profile-legacy-schema-misrouted': (
        'scripts/normalize-generated.py', '    if schema < 12:\n', '    if schema < 11:\n',
        PROFILES, 'HELPER', ('ReceiptTests.test_legacy_schema_selects_legacy_profile',)),
    # T01: an unknown profile name must not be selected as abi64-le-v1.
    'profile-name-unchecked': (
        'scripts/normalize-generated.py',
        '    if (p["name"] != ("abi64-be-v1" if big else "abi64-le-v1") or p["zig_version"]',
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
    # F03: a `*_optimized` tag is supported by no semantics, so its inventory row must carry the
    # translator's current rejection (deleting the rejection is not support).
    'fast-math-rejection-unchecked': (
        'scripts/coverage.py', "            if not rejection.get('reason') or rejection['reason'] != current:\n",
        "            if disposition != 'rejected-fast-math' and (not rejection.get('reason') or rejection['reason'] != current):\n",
        INVENTORY, 'coverage', ('InventoryTests.test_l14_gate_fails_closed',)),
    # F03: a tested source that sets the optimized float mode cannot support a build-mode record.
    'fast-math-tested-source-accepted': (
        'scripts/build-modes.py', '        for source in float_mode_sources(root):\n', '        for source in ():\n',
        'tests/roadmap/build-modes/test_build_modes.py', 'bm', ('RunControls.test_fast_math_in_tested_sources',)),
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
    # F05: a per-version theorem (e.g. `op128_spec_full`) needs a check result against each
    # version's own translation (`tests/golden/<v>/<ex>/Gen.lean`), not only the committed one.
    'theorem-inventory-version-translation-collapsed': (
        'scripts/theorem-inventory.py', '        if not (root / default).is_file():\n',
        '        if True:\n', THEOREMS, 'ti',
        ('FixtureTests.test_translations_follow_check_sh',)),
    # D02: a recorded check result goes stale when an imported proof source changes.
    'theorem-inventory-stale-proof-accepted': (
        'scripts/theorem-inventory.py',
        "            return run.get('sources', {}).get(module) == _sha256(source, info.st_mtime_ns, info.st_size)\n",
        '            return True\n', THEOREMS, 'ti',
        ('FixtureTests.test_edited_proof_or_translation_is_stale',)),
    # D02: a document must not say "every schedule" of a single-schedule theorem.
    'theorem-inventory-narrow-claim-accepted': (
        'scripts/theorem-inventory.py',
        "                    narrower = by_name.get(token, set()) - {'all-schedules'}\n",
        '                    narrower = set()\n', THEOREMS, 'ti',
        ('FixtureTests.test_narrow_theorem_labeled_all_schedules_in_docs',)),
    # D02/S6: an all-schedules completion witness must complete a run of the same program.
    'theorem-inventory-completion-unchecked': (
        'scripts/theorem-inventory.py',
        "    if not (sched_programs(statement) & sched_programs(decl['statement'])) or not re.search(r'=\\s*some\\b', statement):",
        '    if False:', THEOREMS, 'ti', ('FixtureTests.test_completion_witness',)),
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
        '        gaps = theorem["source_gaps"] = sorted(set(theorem["premises"]) - known, key=premise_key)\n',
        '        gaps = theorem["source_gaps"] = []\n', PREMISES, 'premises',
        ('CompiledTests.test_compiled_source_gaps',)),
    # D03: a runtime module reached by a theorem must map to premises.
    'premises-compiled-runtime-module-unmapped': (
        'scripts/premises.py',
        '                errors.append(f"{theorem[\'name\']}: runtime module {module} has no premise mapping")\n',
        '                pass\n', PREMISES, 'premises',
        ('CompiledTests.test_compiled_unmapped_module_and_axiom',)),
    # D03 (W1): a generated def's Allocator/Io caller obligation must reach every theorem using it.
    'premises-interface-marker-dropped': (
        'scripts/premises.py', '        apply_markers(via, target.name, target.markers)\n', '',
        PREMISES, 'premises', ('FixtureTests.test_interface_marker_reaches_theorems',)),
    # D03 (W1): a marker that is not directly above a def must fail, not silently vanish.
    'premises-interface-marker-misplaced-accepted': (
        'scripts/premises.py',
        '    lean.errors += [f"{lean.rel}:{number - 1}: air2lean-premises marker does not precede a def"\n'
        '                    for number in markers]\n', '',
        PREMISES, 'premises', ('FixtureTests.test_interface_marker_fails_closed',)),
    # D03 (W1): the kernel-graph reader of generated markers fails closed on a misplaced marker.
    'premise-markers-misplaced-accepted': (
        'scripts/premise_markers.py',
        '            errors.append(f"{rel}:{number - 1}: air2lean-premises marker does not precede a def")\n',
        '            pass\n', PREMISES, 'markers', ('CompiledTests.test_caller_obligations_reach_users_transitively',)),
    # D03 (W1): the kernel-graph derivation applies the same markers.
    'premises-compiled-interface-marker-dropped': (
        'scripts/premises.py', '                apply_markers(via, user(name), markers.of(module, user(name)))\n', '',
        PREMISES, 'premises', ('CompiledTests.test_compiled_interface_marker',)),
    # E04 (W3): a native result outside the model that is not a known divergence must fail.
    'inclusion-new-divergence-ignored': (
        'tests/roadmap/model-inclusion/inclusion.py', "            if r['status'] == 'fail':\n",
        "            if False:\n", 'tests/roadmap/model-inclusion/test_inclusion.py', 'inclusion', ('Inclusion.test_judge',)),
    # E04 (W3): a known divergence that no longer diverges is stale, not silently passing.
    'inclusion-stale-known-divergence-accepted': (
        'tests/roadmap/model-inclusion/inclusion.py', "        elif r['status'] == 'pass':\n",
        "        elif False:\n", 'tests/roadmap/model-inclusion/test_inclusion.py', 'inclusion', ('Inclusion.test_judge',)),
    # E04 (W3): a data race admits any value, but a native hang needs a model deadlock.
    'inclusion-hang-included-by-race': (
        'tests/roadmap/model-inclusion/inclusion.py', "(m == ILLEGAL and t != DEADLOCK)",
        "(m == ILLEGAL)", 'tests/roadmap/model-inclusion/test_inclusion.py', 'inclusion', ('Inclusion.test_io_hang_needs_a_model_deadlock',)),
    # E04 (W3): an input the capped model cannot evaluate is never counted as included.
    'inclusion-cap-limited-counted-included': (
        'tests/roadmap/model-inclusion/inclusion.py',
        "                        None if json.loads(group[0]).get('ok') == OUT_OF_MEMORY else False\n",
        "                        True if json.loads(group[0]).get('ok') == OUT_OF_MEMORY else False\n",
        'tests/roadmap/model-inclusion/test_inclusion.py', 'inclusion', ('Inclusion.test_cap_limited_input_is_unevaluated_not_included',)),
    # D03 (W1): a claim about a function with an Allocator/Io parameter names its premise.
    'claims-caller-obligations-dropped': (
        'scripts/claims.py', "                         'caller_obligations': obligations.get(theorem['name'], []),\n",
        "                         'caller_obligations': [],\n", 'tests/roadmap/claims/test_claims.py', 'claims',
        ('ClassifyTests.test_caller_obligations_follow_the_kernel_graph',)),
    # D03 (W1): receipts and claims derive caller obligations from the kernel graph transitively.
    'premises-caller-obligations-not-transitive': (
        'scripts/premise_markers.py', "        pending += [(user, premise) for user in reverse.get(name, ())]\n", '',
        PREMISES, 'markers', ('CompiledTests.test_caller_obligations_reach_users_transitively',)),
    # Q08: a pull_request run tests a merge commit, not the recorded revision.
    'release-record-pull-request-run-accepted': (
        'scripts/release-record.py', "    if data['event'] not in EVIDENCE_EVENTS:\n",
        "    if data['event'] not in (*EVIDENCE_EVENTS, 'pull_request'):\n",
        RELEASE, 'rr',
        ('RecordTests.test_evidence_for_another_revision_is_refused',)),
    # Q08: a failed step must never be published as passed when other evidence passes.
    'release-record-failure-masked': (
        'scripts/release-record.py',
        "            gate['status'] = next((s for s in ('failed', 'passed', 'by-reference') if s in statuses), 'missing')\n",
        "            gate['status'] = next((s for s in ('passed', 'by-reference') if s in statuses), 'missing')\n", RELEASE, 'rr',
        ('RecordTests.test_failures_and_skips_are_never_passed_or_hidden',
         'RecordTests.test_conflicting_evidence_fails_the_gate')),
    # Q08: every review ledger entry names the revision it reviewed.
    'release-ledger-revision-unchecked': (
        'scripts/release-record.py', '        if not SHA1.fullmatch(reviewed):\n', '        if False:\n',
        RELEASE, 'rr', ('LedgerTests.test_entry_without_reviewed_revision_fails',)),
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
    # D04: a tutorial's negative control must name the error it is expected to fail with.
    'tutorial-expected-error-unchecked': (
        'scripts/tutorials.py', '        if not EXPECT.search(negative):\n', '        if False:\n',
        TUTORIALS, 'tutorials', ('Fixture.test_missing_expected_error',)),
    # I05: a diagnostic's exporter source span must be well formed and match its status.
    'diagnostics-source-span-unchecked': (
        'scripts/project-diagnostics.py', "        demand(valid_span(d), 'invalid source span')\n", '',
        DIAGNOSTICS, 'adapter', ('AdapterTests.test_invalid_protocol_controls',)),
    # V04/S1: a module the kernel replay rejected must not be trusted (debug.skipKernelTC oleans).
    'audit-kernel-replay-rejection-ignored': (
        'scripts/assumptions.py', '        if node["module"] in rejected:\n', '        if False:\n',
        POLICY, 'audit', ('PolicyTests.test_kernel_replay_rejection_fails_dependent_theorems',)),
    # V04/S1: a project module outside the replayed set must not be trusted.
    'audit-unreplayed-module-trusted': (
        'scripts/assumptions.py',
        '        elif needs_replay(node["module"]) and node["module"] not in replayed:\n', '        elif False:\n',
        POLICY, 'audit', ('PolicyTests.test_module_outside_replay_is_not_trusted',)),
    # V04/S1: a changed Lake olean invalidates every cached replay (its dependents may break).
    'audit-replay-cache-ignores-digest': (
        'scripts/assumptions.py', '            passed = {}  # Another build: a reused module could depend on a changed one.\n',
        '            pass\n',
        UNIVERSE, 'assumptions', ('ReplayTests.test_cache_reuses_only_identical_passed_lake_oleans',)),
    # V04/H1: a report whose recorded artifacts changed is stale.
    'audit-freshness-digest-unchecked': (
        'scripts/assumptions.py',
        'if path and (not path.is_file() or file_sha256(path) != row[kind + "_sha256"]):', 'if False:',
        UNIVERSE, 'assumptions', ('FreshnessTests.test_changed_artifact_or_revision_is_stale',)),
    # V04/F2: `declaration uses 'sorry'` fails compilation of an indexed module (examples too).
    'universe-sorry-warning-ignored': (
        'scripts/theorem_universe.py', '    if SORRY_WARNING in result.stdout:\n', '    if False:\n',
        UNIVERSE, 'universe', ('UniverseTests.test_compile_rejects_sorry_warnings',)),
    # V04/S1: the source scan rejects debug.skipKernelTC and set_option debug.*.
    'universe-kernel-bypass-unscanned': (
        'scripts/theorem_universe.py', 'if bypass := FORBIDDEN.search(line):', 'if bypass := None:',
        UNIVERSE, 'universe', ('UniverseTests.test_scan_rejects_kernel_bypass_and_placeholders',)),
    # I07/H1: a release receipt from a dirty tree needs the recorded --allow-dirty.
    'receipt-dirty-tree-accepted': (
        'scripts/proof-receipt.py',
        "    demand(not plan['revision']['tracked_dirty'] or plan['allow_dirty'], 'tracked changes: a release receipt needs a clean tree')\n",
        '', RECEIPTS, 'r', ('ReceiptTests.test_dirty_tree_receipt_needs_recorded_permission',)),
    # V04/S1: the receipt's kernel replay must come from the planned toolchain's leanchecker.
    'receipt-replay-tool-unchecked': (
        'scripts/proof-receipt.py',
        "and replay['tool_sha256'] == fingerprint(toolchain / 'bin/leanchecker')['sha256']", '',
        RECEIPTS, 'r', ('ReceiptTests.test_receipt_requires_kernel_replay_by_planned_toolchain',)),
    # P05/S2: a claim head counts only as the registered declaration (module and fingerprint).
    'claim-head-identity-unchecked': (
        'scripts/claims.py', "    if found != expected or (node is not None and node.get('module') != entry['module']):",
        '    if False:', CLAIMS, 'claims', ('ClassifyTests.test_heads_are_registered_declarations',)),
    # P05: a reserved (retired) claim-head name supports no claim, whatever its declaration.
    'claim-reserved-head-accepted': (
        'scripts/claims.py', '    if name in (reserved_names() if reserved is None else reserved):',
        '    if False:', CLAIMS, 'claims', ('ClassifyTests.test_reserved_names_support_no_claim',)),
    # I06/S5: the conclusion must be about the root, not merely mention it.
    'claim-subject-unchecked': (
        'scripts/claims.py', "    elif subject is not None and subject.get('fn') == definition:",
        "    elif definition in _list(theorem.get('conclusion_dependencies')) or subject is not None:",
        CLAIMS, 'claims', ('AssessTests.test_subject_must_be_the_root',)),
    # I06/S4: a fixed root argument or initial state scopes the derived domain.
    'claim-fixed-argument-universal': (
        'scripts/claims.py', '    scoped = bool(fixed or repeated or constrained)',
        '    scoped = bool(repeated or constrained)', CLAIMS, 'claims', ('AssessTests.test_domain_is_derived',)),
    # P05/S3: a hypothesis about generated code or a claim head rejects the goal.
    'claim-hypothesis-unchecked': (
        'scripts/claims.py', "            bad = sorted(set(_list(binder.get('defs'))) & blocked)",
        '            bad = []', CLAIMS, 'claims', ('AssessTests.test_hypotheses_about_generated_code_are_rejected',)),
    # P05/S3, audit 2026-10-14 S1: every strength needs a non-vacuity witness.
    'claim-nonvacuity-not-required': (
        'scripts/claims.py', '    if strength is not None and not nonvacuous:', '    if False:',
        CLAIMS, 'claims', ('AssessTests.test_witnesses_cap_strength',)),
    # P05/F2: a satisfiable client cannot turn a vacuous allocator contract into a claim.
    'claim-allocator-creation-not-required': (
        'scripts/claims.py', '    if creation_problem := uncreated(result):', '    if False:',
        CLAIMS, 'claims', ('AssessTests.test_allocator_creation_is_required',)),
    'claim-allocator-admit-unaudited': (
        'scripts/claims.py', "            elif _witness(statement_of(creation) or {}, 'nonvacuity', audited) != 'verified':",
        '            elif False:', CLAIMS, 'claims', ('AssessTests.test_allocator_creation_is_exact_and_audited',)),
    # P05/S6: partial correctness needs a liveness witness.
    'claim-liveness-not-required': (
        'scripts/claims.py', "    if strength == 'partial_correctness' and witnesses['liveness'] != 'verified':",
        '    if False:', CLAIMS, 'claims', ('AssessTests.test_witnesses_cap_strength',)),
    # P05/S3: a witness counts only as an allowed audited theorem.
    'claim-witness-unaudited-accepted': (
        'scripts/claims.py', "        if not isinstance(companion, dict) or companion.get('allowed') is not True:",
        '        if False:', CLAIMS, 'claims', ('AssessTests.test_witnesses_cap_strength',)),
    # P05, audit 2026-10-14 S1: an unwitnessed theorem is never a direct goal.
    'coverage-unwitnessed-direct': (
        'scripts/project.py', '    if nonvacuity not in claims.NONVACUOUS:', '    if False:',
        COVERAGE, 'project', ('CoverageTests.test_hypotheses_and_witnesses',)),
    'coverage-allocator-creation-unchecked': (
        'scripts/project.py', '    if creation_problem:', '    if False:',
        COVERAGE, 'project', ('CoverageTests.test_allocator_creation_blocks_binding_and_absence',)),
    # P05, audit 2026-10-14 S1: an absence claim needs a witnessed goal.
    'absence-claim-witness-unchecked': (
        'scripts/project.py', "            and (goal.get('witnesses') or {}).get('nonvacuity') in claims.NONVACUOUS",
        '            and True', COVERAGE, 'project',
        ('CoverageTests.test_unsupported_air_is_an_outcome_and_not_proved_absence',)),
    # I06/S4: a scoped domain caps coverage at proved_scoped.
    'coverage-scoped-domain-functional': (
        'scripts/project.py',
        "        elif goal['strength'] in FUNCTIONAL and goal.get('scope') != 'universal':",
        '        elif False:',
        COVERAGE, 'project', ('CoverageTests.test_fixed_arguments_scope_the_domain',)),
    # Q06: emitted Lean that differs from the baseline is a preservation failure, never a speedup.
    'perf-output-change-ignored': (
        'scripts/perf-budgets.py', '        if expected.get("sha256") != actual.get("sha256"):\n', '        if False:\n',
        PERF, 'perf', ('Gate.test_output_change_is_a_preservation_failure',)),
    # Q06: a peak-RSS regression fails the gate.
    'perf-memory-limit-ignored': (
        'scripts/perf-budgets.py', '                elif rss > limits[rss_key]:\n', '                elif False:\n',
        PERF, 'perf', ('Gate.test_memory_regression',)),
    # Q06: a budgeted workload absent from the measurement is a failure, not a pass.
    'perf-missing-workload-ignored': (
        'scripts/perf-budgets.py', '            add("missing-workload", ident, "budgeted workload is absent from the measurement")\n',
        '            pass\n', PERF, 'perf', ('Gate.test_missing_workload',)),
    # Q06: a measurement taken with parallel Lean threads is unserialized and not comparable.
    'perf-unserialized-measurement-accepted': (
        'scripts/perf-budgets.py',
        '    if measurement.get("lean_num_threads") != "1":\n        add("unserialized-measurement", None,\n',
        '    if False:\n        add("unserialized-measurement", None,\n',
        PERF, 'perf', ('Gate.test_platform_and_serialization',)),
    # Q06: the portable gate uses the generous portable limits, not the reference ones.
    'perf-portable-limits-not-selected': (
        'scripts/perf-budgets.py', '    prefix = "portable_" if portable else ""\n', '    prefix = ""\n',
        PERF, 'perf', ('PortableGate.test_ignores_platform_and_absorbs_runner_noise',)),
    # Q06: a measurement run against another calibration file must not normalize times.
    'perf-foreign-calibration-accepted': (
        'scripts/perf-budgets.py', '        elif calibration.get("sha256") != expected["sha256"]:\n',
        '        elif False:\n', PERF, 'perf', ('NormalizedGate.test_a_missing_or_foreign_calibration_fails_closed',)),
    # I08: the temporary file of an interrupted publish is removed.
    'safe-output-partial-file-left': (
        'scripts/safe-output.py', '            temporary.unlink(missing_ok=True)\n', '            pass\n',
        SAFE, 'safe', ('Publish.test_interrupt_mid_write_keeps_prior_and_no_partial',)),
    # I08: publishing keeps the mode of the artifact it replaces.
    'safe-output-mode-not-preserved': (
        'scripts/safe-output.py', '                os.fchmod(handle.fileno(), mode)\n', '                pass\n',
        SAFE, 'safe', ('Publish.test_overwrite_replaces_atomically_and_keeps_mode',)),
    # I08: a symlink destination is refused (no write through the link).
    'safe-output-symlink-destination-followed': (
        'scripts/safe-output.py', '    if path.is_symlink() or (path.exists() and not path.is_file()):\n',
        '    if (path.exists() and not path.is_file()):\n',
        SAFE, 'safe', ('Publish.test_rejects_symlink_and_directory_destinations_and_missing_policy',)),
    # I08: --no-clobber is atomic: an output created after the early check is not replaced.
    'safe-output-noclobber-race-overwrites': (
        'scripts/safe-output.py', '                    os.link(temporary, destination)  # Atomic no-clobber, including concurrent writers.\n',
        '                    os.replace(temporary, destination)\n',
        SAFE, 'safe', ('Publish.test_no_clobber_is_atomic_against_a_concurrent_writer',)),
    # Q07: edited obligations or inputs after `plan` must fail the record check.
    'qualify-plan-digest-unchecked': (
        'scripts/qualify-upgrade.py', "    if record.get('plan_sha256') != plan_digest(record):\n", '    if False:\n',
        QUALIFY, 'q', ('RecordTests.test_removed_obligation_and_stale_plan_fail',)),
    # Q07: a plan that no longer matches the before/after inventories is stale.
    'qualify-stale-plan-accepted': (
        'scripts/qualify-upgrade.py', "        if fresh['plan_sha256'] != record['plan_sha256']:\n", '        if False:\n',
        QUALIFY, 'q', ('RecordTests.test_removed_obligation_and_stale_plan_fail',)),
    # Q07: a failed obligation result is never a passing qualification.
    'qualify-failed-result-accepted': (
        'scripts/qualify-upgrade.py', "        if result.get('status') != 'pass':\n", '        if False:\n',
        QUALIFY, 'q', ('RecordTests.test_run_records_and_check_passes',)),
    # Q07: the recorded log must match its digest.
    'qualify-log-tamper-unchecked': (
        'scripts/qualify-upgrade.py', "            if not log.is_file() or sha256_bytes(log.read_bytes()) != result.get('log_sha256'):\n",
        '            if False:\n', QUALIFY, 'q', ('RecordTests.test_tampered_log_fails_check',)),
    # Q07: a model review needs an accepted decision from a named reviewer.
    'qualify-unaccepted-review-passes': (
        'scripts/qualify-upgrade.py', "            if result.get('decision') != 'accepted' or not result.get('reviewer'):\n",
        '            if False:\n', QUALIFY, 'q', ('RecordTests.test_model_review_needs_accepted_decision_and_evidence',)),
    # Q07: a result for an obligation the plan does not contain is rejected.
    'qualify-unknown-result-accepted': (
        'scripts/qualify-upgrade.py', "    for oid in sorted(set(record['results']) - ids):\n", '    for oid in []:\n',
        QUALIFY, 'q', ('RecordTests.test_unknown_result_fails',)),
    # Q07: a recorded external result without evidence is rejected by `check`, not only by `record`.
    'qualify-evidence-free-result-accepted': (
        'scripts/qualify-upgrade.py', "        elif not result.get('evidence'):\n", '        elif False:\n',
        QUALIFY, 'q', ('RecordTests.test_hand_edited_result_without_evidence_fails',)),
    # Q03: a capped search that matched is never counted as demonstrated correspondence.
    'schedule-capped-match-counted': (
        'scripts/diff-report.py', '    return Status.SEARCH_CAP if status in MATCHES and capped_search(search) else status\n',
        '    return status\n', SCHEDULES, 'REPORT',
        ('Exploration.test_capped_value_match_lands_in_cap_bucket',
         'Exploration.test_one_capped_case_disqualifies_otherwise_matching_scope')),
    # Q03: a truncated enumeration blocks correspondence for its scope.
    'schedule-truncated-enumeration-not-blocking': (
        'scripts/diff-report.py', "            if scope['enumeration']['truncated']:blockers.append('enumeration_truncated')\n",
        '            pass\n', SCHEDULES, 'REPORT', ('Exploration.test_truncated_enumeration_disqualifies_matching_scope',)),
    # Q03: a schedule that reached a no-result branch blocks correspondence.
    'schedule-no-result-branch-not-blocking': (
        'scripts/diff-report.py', "            if scope['observed']['bounded'] or scope['enumeration']['saw_no_result']:blockers.append('bounded_no_result')\n",
        '            pass\n', SCHEDULES, 'REPORT',
        ('Exploration.test_bounded_no_result_blocks_correspondence_but_is_not_cap',
         'Exploration.test_enumerated_no_result_branch_blocks_correspondence')),
    # Q03: a "capped" search must have consumed its run cap.
    'schedule-cap-unconsumed-accepted': (
        'scripts/diff-report.py', "        if search['status'] == 'capped' and search['runs'] != search['cap']:\n",
        '        if False:\n', SCHEDULES, 'REPORT', ('Exploration.test_capped_status_must_consume_its_run_cap',)),
    # V03: an instruction id may be defined once.
    'air-validate-duplicate-id-accepted': (
        'scripts/validate-air.py', '            elif ident in seen:\n', '            elif False:\n',
        AIR_VALIDATE, 'v', ('ValidateAir.test_duplicate_instruction_id',)),
    # V03: br/repeat must target an enclosing block/loop of the right kind.
    'air-validate-branch-target-unchecked': (
        'scripts/validate-air.py', '                if not any(t == target and k in TARGET_KINDS[tag] for t, k in scopes):\n',
        '                if False:\n', AIR_VALIDATE, 'v',
        ('ValidateAir.test_br_to_non_enclosing_block', 'ValidateAir.test_repeat_must_target_loop')),
    # V03: a body must end in a noreturn terminator.
    'air-validate-missing-terminator-accepted': (
        'scripts/validate-air.py', '            if last and not noreturn:\n', '            if False:\n',
        AIR_VALIDATE, 'v', ('ValidateAir.test_missing_terminator',)),
    # V03: a noreturn instruction cannot sit in the middle of a body.
    'air-validate-noreturn-in-middle-accepted': (
        'scripts/validate-air.py', "            if noreturn and not last and not tag.startswith('call'):\n",
        '            if False:\n', AIR_VALIDATE, 'v', ('ValidateAir.test_noreturn_in_the_middle',)),
    # V03: a tag outside the Zig version's AIR universe is rejected.
    'air-validate-tag-universe-unchecked': (
        'scripts/validate-air.py', '        if not isinstance(tag, str) or tag not in self.universe:\n',
        '        if not isinstance(tag, str):\n', AIR_VALIDATE, 'v', ('ValidateAir.test_tag_outside_version_universe',)),
    # V03: an "unsupported" marker on a tag the exporter decodes is rejected.
    'air-validate-unsupported-marker-on-decoded-tag': (
        'scripts/validate-air.py', "        if marked and 'unsupported-marker' not in status:\n", '        if False:\n',
        AIR_VALIDATE, 'v', ('ValidateAir.test_unsupported_marker_matches_inventory',)),
    # V03: decoded operands on a tag the exporter marks unsupported are rejected.
    'air-validate-decoded-operands-on-unsupported-tag': (
        'scripts/validate-air.py', "        if not marked and 'unsupported-marker' in status:\n", '        if False:\n',
        AIR_VALIDATE, 'v', ('ValidateAir.test_unsupported_marker_matches_inventory',)),
    # V03: a kernel-checked stage must cite the trusted base.
    'trust-kernel-base-uncited': (
        'scripts/trust-report.py', "        if cls == 'kernel-checked' and 'TRU-01' not in ids:\n", '        if False:\n',
        TRUST, 't', ('TrustReport.test_kernel_checked_needs_trusted_base',)),
    # V03: a check whose test CI does not run is not a check.
    'trust-test-not-run-by-ci-accepted': (
        'scripts/trust-report.py', "            if test_ok and not runs_in_ci(check['test'], ci, commands, root):\n",
        '            if False:\n', TRUST, 't', ('TrustReport.test_check_must_run_in_ci',)),
    # V03: an unverified assumption cannot claim checks.
    'trust-unverified-stage-lists-checks': (
        'scripts/trust-report.py', "        if cls == 'unverified-assumption' and checks:\n", '        if False:\n',
        TRUST, 't', ('TrustReport.test_unverified_stage_cannot_list_checks',)),
    # V03: a required pipeline stage must be present.
    'trust-required-stage-unchecked': (
        'scripts/trust-report.py', '        if sid not in seen:\n', '        if False:\n',
        TRUST, 't', ('TrustReport.test_missing_required_stage',)),
    # V03: a cited premise must be defined.
    'trust-undefined-premise-accepted': (
        'scripts/trust-report.py', '            if pid not in premises:\n', '            if False:\n',
        TRUST, 't', ('TrustReport.test_undefined_premise',)),
    # V03: every compiler/tool trust premise must be cited by a stage.
    'trust-uncited-premise-accepted': (
        'scripts/trust-report.py', '        if pid not in cited:\n', '        if False:\n',
        TRUST, 't', ('TrustReport.test_uncited_trust_premise',)),
    # V03: a checked stage must name a checker and test.
    'trust-checked-stage-without-checks': (
        'scripts/trust-report.py', "        if cls in ('kernel-checked', 'independently-checked-metadata') and not checks:\n",
        '        if False:\n', TRUST, 't', ('TrustReport.test_checked_classes_need_checks',)),
    # Q01: the generator's type checker rejects code after an exit (the oracle must stay UB-free).
    'fuzz-typecheck-unreachable-code-accepted': (
        'tests/roadmap/fuzz/zig_gen.py', '            if _exits(s) and k != len(stmts) - 1:\n', '            if False:\n',
        FUZZ, 'zig_gen', ('ZigGenerator.test_typecheck_rejects_invalid_programs',)),
    # Q01: literals outside their type's range are rejected.
    'fuzz-typecheck-literal-range-unchecked': (
        'tests/roadmap/fuzz/zig_gen.py', '        if isinstance(v, bool) or not isinstance(v, int) or wrap(ty, v) != v:\n',
        '        if isinstance(v, bool) or not isinstance(v, int):\n',
        FUZZ, 'zig_gen', ('ZigGenerator.test_typecheck_rejects_invalid_programs',)),
    # Q01: Zig forbids shadowing; a rendered program that shadows would not compile.
    'fuzz-typecheck-shadowing-accepted': (
        'tests/roadmap/fuzz/zig_gen.py', '        if not isinstance(name, str) or name in names:\n',
        '        if not isinstance(name, str):\n',
        FUZZ, 'zig_gen', ('ZigGenerator.test_typecheck_rejects_invalid_programs',)),
    # Q01: the oracle evaluator loads a compound assignment's target before its operand.
    'fuzz-eval-compound-assignment-order': (
        'tests/roadmap/fuzz/zig_gen.py',
        '                old = cell[0]\n                value = self.expr(s[3], env)\n',
        '                value = self.expr(s[3], env)\n                old = cell[0]\n',
        FUZZ, 'zig_gen', ('ZigGenerator.test_evaluator_semantics',)),
    # P07: a callee's change must invalidate its callers (the call-graph fold).
    'fingerprint-callers-not-invalidated': (
        'scripts/semantic-fingerprints.py', '            callees=[[c, result[c]["fingerprint"]] for c in outside]))\n',
        '            callees=outside))\n', FINGERPRINTS, 'fp', (FINGERPRINT_TEST,)),
    # P07: a semantic (body) change must invalidate the function's own fingerprint.
    'fingerprint-body-ignored': (
        'scripts/semantic-fingerprints.py', 'canonical=r["canonical"])) for s, r in records.items()}',
        'canonical=r["air_name"])) for s, r in records.items()}', FINGERPRINTS, 'fp', (FINGERPRINT_TEST,)),
    # P07: a translator (emitter) change invalidates every fingerprint.
    'fingerprint-translator-revision-ignored': (
        'scripts/semantic-fingerprints.py', '                          translator=doc["translator"]["revision"],\n',
        '', FINGERPRINTS, 'fp', (FINGERPRINT_TEST,)),
    # P07: a sidecar whose runtime revision does not match its module digests is rejected.
    'sidecar-runtime-revision-unchecked': (
        'scripts/semantic-fingerprints.py', '    if not valid_translator(doc["runtime"]):\n', '    if False:\n',
        FINGERPRINTS, 'fp', (FINGERPRINT_TEST,)),
    # T04: the native probe profile is exactly 64-bit.
    'abi-probe-pointer-width-unchecked': (
        'scripts/abi-probe.py', " or profile['pointer_bits'] != 64\n", '\n',
        ABI, 'abi', ('ContractTests.test_profiles_fail_closed',)),
    # T04: feature names are sorted and unique.
    'abi-probe-features-unordered': (
        'scripts/abi-probe.py', " or profile['features'] != sorted(set(profile['features']))):\n", '):\n',
        ABI, 'abi', ('ContractTests.test_profiles_fail_closed',)),
    # T04: observed layouts (size, alignment) must equal the bounded contract.
    'abi-probe-layout-unchecked': (
        'scripts/abi-probe.py', "'layout': layouts(profile['error_set_bits']), ", "'layout': data['layout'], ",
        ABI, 'abi', ('ContractTests.test_observations_require_complete_exact_values',)),
    # T04: the two Linux observations of a pair come from one Zig version.
    'abi-probe-pair-version-unchecked': (
        'scripts/abi-probe.py', "    if left['profile']['zig_version'] != right['profile']['zig_version']:\n",
        '    if False:\n', ABI, 'abi', ('ContractTests.test_pair_requires_one_zig_version',)),
    # T05: each side of a target-specific kernel meets its own profile's model (pointer width).
    'wasm-profile-model-native-width': (
        'scripts/wasm-correspondence.py', "        want = evaluate(entry['expect'], expect_env(args, bits[side], zig))\n",
        "        want = evaluate(entry['expect'], expect_env(args, bits['native'], zig))\n",
        WASM, 'wc', ('Relation.test_committed_records_hold', 'Relation.test_target_specific_model_is_per_profile')),
    # T05: a NaN on one side only is not in the tolerated float relation.
    'wasm-one-sided-nan-tolerated': (
        'scripts/wasm-correspondence.py', '        if is_nan(native, fmt) and is_nan(wasm, fmt):\n',
        '        if is_nan(native, fmt) or is_nan(wasm, fmt):\n', WASM, 'wc', ('Relation.test_float_tolerance',)),
    # T05: the declared ulp bound limits a tolerated pair.
    'wasm-ulp-bound-ignored': (
        'scripts/wasm-correspondence.py', "        return None if distance <= entry['ulp'] else",
        '        return None if True else', WASM, 'wc', ('Relation.test_float_tolerance',)),
    # T05: a record of other kernel sources is stale, never compared.
    'wasm-stale-sources-accepted': (
        'scripts/wasm-correspondence.py', "    if data.get('sources_sha256') != sources(relation, root):\n",
        '    if False:\n', WASM, 'wc', ('Relation.test_stale_record_fails',)),
    # X01: a file with a function translate-c demoted to an extern is never a verified program.
    'c-demoted-file-counted-translated': (
        'tests/roadmap/c-frontend/run.py', '.get("status") in ("failed", "demoted", None):\n',
        '.get("status") in ("failed", None):\n', C_FRONTEND, 'run', ('Gates.test_a_demoted_file_is_never_lean_ok',)),
    # X01: a deferred Lean elaboration is not `lean_ok`.
    'c-deferred-lean-ok': (
        'tests/roadmap/c-frontend/run.py', '    if s.get("lean", {}).get("status") != "ok":\n',
        '    if s.get("lean", {}).get("status") not in ("ok", "deferred"):\n', C_FRONTEND, 'run',
        ('Gates.test_deferred_lean_is_not_ok',)),
    # X01: a translated program whose results differ from C's is gated as a divergence.
    'c-native-mismatch-ungated': (
        'tests/roadmap/c-frontend/run.py', '    if native in ("mismatch", "runtime_error"):\n',
        '    if native == "runtime_error":\n', C_FRONTEND, 'run', ('Gates.test_setjmp_variadic_and_divergence',)),
}


def load_test_module(path):
    spec = importlib.util.spec_from_file_location('q02_mutant_target_' + Path(path).stem, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    # A test may import a sibling helper (proof-receipts: `rss_budget`), as when run as a script.
    sys.path.insert(0, str((ROOT / path).parent))
    try:
        spec.loader.exec_module(module)
    finally:
        sys.path.remove(str((ROOT / path).parent))
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
        # Name each failing test and the last line of its traceback: a control failure is a
        # finding about the test itself, and the run must say which assertion or error it was.
        details = '; '.join(f'{case.id()}: {trace.strip().splitlines()[-1]}'
                            for case, trace in control.failures + control.errors)
        raise AssertionError(f'{name}: control does not pass its killing tests ({details})')
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
