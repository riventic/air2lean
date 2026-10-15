#!/usr/bin/env python3
"""Claim-strength regressions. fixture-report.json holds statement structures extracted by
tools/Assurance.lean from Fixture.lean; check.sh regenerates and compares them."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts' / 'claims.py'
SPEC = importlib.util.spec_from_file_location('claims', SCRIPT)
claims = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(claims)
FIXTURE = json.loads((Path(__file__).parent / 'fixture-report.json').read_text())
AUDIT_SPEC = importlib.util.spec_from_file_location('assumptions', ROOT / 'scripts' / 'assumptions.py')
assumptions = importlib.util.module_from_spec(AUDIT_SPEC)
AUDIT_SPEC.loader.exec_module(assumptions)
HEADS = claims.load_heads()
RESERVED = claims.reserved_names()
RESERVED_MODULES = claims.load_registry()[1]
FTOTAL = 'Zig.Full.FTotalTriple'
EVENTUALLY = 'Zig.Conc.Total.EventuallyReturns'
WITHIN = 'Zig.Conc.Total.ReturnsWithin'
UNDER = 'Zig.Conc.Total.EventuallyReturnsUnder'
# The retired legacy claim heads. A reserved name is never registered again, so this set only grows.
LEGACY_HEADS = {'Zig.Triple', 'Zig.TTriple', 'Zig.TotalTriple', 'Zig.Returns', 'Zig.TotalTripleWithin',
                EVENTUALLY, WITHIN, UNDER}
SPOOFS = ('ClaimFixture.spoof_eventually', 'ClaimFixture.spoof_within', 'ClaimFixture.spoof_within_sym',
          'ClaimFixture.spoof_under')

# (claim class, strength after witness caps); classification ignores the root binding.
EXPECTED = {
    'ClaimFixture.ret_run': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_run_ground': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_some': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_pure_ok': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.panic_run': ('unclassified', None),
    'ClaimFixture.panic_some': ('unclassified', None),
    'ClaimFixture.panic_pure': ('unclassified', None),
    'ClaimFixture.fret_total': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.fret_partial': ('correct-if-returned', 'partial_correctness'),
    'ClaimFixture.fpremise_total': ('guaranteed-return', 'total_correctness'),
    # Partial correctness of a program that never returns: no liveness witness, so safety only.
    'ClaimFixture.fdiverge_partial': ('correct-if-returned', 'safety'),
    # An unsatisfiable precondition: the telescope reaches the inner FTriple, so no witness and
    # no claim.
    'ClaimFixture.ffalse_total': ('guaranteed-return', None),
    'ClaimFixture.cret_partial': ('correct-if-returned', 'partial_correctness'),
    'ClaimFixture.tret_total': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.tret_partial': ('correct-if-returned', 'partial_correctness'),
    # Not claims: a refutation, a wrapper definition and a conjunction.
    'ClaimFixture.fdiverge_not_total': ('unclassified', None),
    'ClaimFixture.fwrapped_total': ('unclassified', None),
    'ClaimFixture.fpartial_and_returns': ('unclassified', None),
    # Spoofs of reserved head names: no claim.
    **{name: ('unclassified', None) for name in SPOOFS},
    'ClaimFixture.fret_total.nonvacuous': ('unclassified', None),
    'ClaimFixture.fret_partial.nonvacuous': ('unclassified', None),
    'ClaimFixture.fret_partial.returns': ('unclassified', None),
    'ClaimFixture.fpremise_total.nonvacuous': ('unclassified', None),
    'ClaimFixture.fdiverge_partial.nonvacuous': ('unclassified', None),
    'ClaimFixture.cret_partial.nonvacuous': ('unclassified', None),
    'ClaimFixture.cret_partial.returns': ('unclassified', None),
    'ClaimFixture.tret_total.nonvacuous': ('unclassified', None),
    'ClaimFixture.tret_partial.nonvacuous': ('unclassified', None),
    'ClaimFixture.tret_partial.returns': ('unclassified', None),
}
# Bounds of the bounded spoof, once registered as a head (`spoof_registry`).
BOUNDS = {'ClaimFixture.spoof_within': {'unit': 'scheduler_turns', 'value': 2, 'expr': '2'},
          'ClaimFixture.spoof_within_sym': {'unit': 'scheduler_turns', 'value': None, 'expr': 'n + 1'}}


def classified(report, heads=None, reserved=None):
    return {t['name']: t for t in claims.classify(report, heads, reserved)['theorems']}


def theorems_of(report):
    return {t['name']: t for t in report['theorems']}


def pure(monad, value):
    return {'head': 'Pure.pure', 'args': [{'head': monad}, value]}


def with_head(theorem, **change):
    spoof = copy.deepcopy(theorem)
    spoof['statement']['head'].update(change)
    return spoof


def spoof_registry():
    """(heads, reserved): the registry with the fixture's spoofs registered as heads of their
    shapes, as a later head of the same shape would plug in. Only a test does this: a reserved
    name is never registered, and `load_registry` rejects a name that is both."""
    shapes = {EVENTUALLY: {'claims': list(claims.CLAIMS), 'program': 1, 'state': [2]},
              WITHIN: {'claims': list(claims.CLAIMS), 'program': 2, 'state': [],
                       'bound': 'scheduler_turns', 'bound_arg': 1},
              UNDER: {'claims': [claims.GUARANTEED_RETURN_UNDER_PREMISE], 'program': 2, 'state': []}}
    seen = claims.head_identities(FIXTURE)
    heads = dict(HEADS, **{name: dict(entry, module=seen[name]['module'], fingerprint=seen[name]['fingerprint'])
                           for name, entry in shapes.items()})
    return heads, RESERVED - set(shapes)


class ClassifyTests(unittest.TestCase):
    def test_fixture_classification_from_types(self):
        theorems = classified(FIXTURE)
        self.assertEqual(set(theorems), set(EXPECTED))
        for name, (klass, strength) in EXPECTED.items():
            with self.subTest(name=name):
                self.assertEqual((theorems[name]['claim_class'], theorems[name]['derived_strength']),
                                 (klass, strength))

    def test_partial_and_total_claims_are_distinct(self):
        theorems = classified(FIXTURE)
        self.assertEqual(theorems['ClaimFixture.fret_partial']['claims'], ['no-panic', 'correct-if-returned'])
        self.assertEqual(theorems['ClaimFixture.fret_total']['claims'],
                         ['no-panic', 'correct-if-returned', 'guaranteed-return'])

    def test_bounds_are_reported_only_for_bounded_heads(self):
        for name in EXPECTED:
            with self.subTest(name=name):
                self.assertIsNone(classified(FIXTURE)[name]['bound'])
        theorems = classified(FIXTURE, *spoof_registry())
        for name in EXPECTED:
            with self.subTest(name=name, registry='spoofs'):
                self.assertEqual(theorems[name]['bound'], BOUNDS.get(name))
        # A bounded return is a guaranteed return; the bound is additional.
        self.assertEqual(theorems['ClaimFixture.spoof_within']['claims'],
                         ['no-panic', 'correct-if-returned', 'guaranteed-return'])

    def test_premise_return_is_not_an_unconditional_claim(self):
        theorem = classified(FIXTURE, *spoof_registry())['ClaimFixture.spoof_under']
        self.assertEqual(theorem['claims'], ['guaranteed-return-under-premise'])
        self.assertIsNone(theorem['derived_strength'])

    def test_names_do_not_drive_classification(self):
        report = copy.deepcopy(FIXTURE)
        for theorem in report['theorems']:
            if theorem['name'] == 'ClaimFixture.fdiverge_partial':
                theorem['name'] = 'ClaimFixture.total_correctness_guaranteed_return'
        theorems = classified(report)
        self.assertEqual(theorems['ClaimFixture.total_correctness_guaranteed_return']['derived_strength'], 'safety')

    def test_heads_are_registered_declarations(self):
        theorem = theorems_of(FIXTURE)['ClaimFixture.fret_total']
        self.assertEqual(claims.claims_of(theorem, HEADS), claims.EXACT_SUCCESS)
        for change in ({'name': 'FTotalTriple'}, {'name': 'Foo.FTotalTriple'}, {'name': 'Zig.FTotalTriple'},
                       {'name': 'Zig.Full.FTotalTriple.toPartial'}, {'name': 'Zig.Full.FTriple.frame'},
                       {'module': 'tests.roadmap.claims.Fixture'}, {'fingerprint': '0' * 32}):
            with self.subTest(change=change):
                self.assertEqual(claims.claims_of(with_head(theorem, **change), HEADS), frozenset())
        # The audit's declaration graph must agree on the head's module as well.
        self.assertEqual(claims.claims_of(theorem, HEADS, {FTOTAL: {'module': 'Elsewhere'}}), frozenset())

    def test_reserved_names_support_no_claim(self):
        """Every reserved name is rejected as a conclusion head, whatever declaration it is: the
        retired module's, a spoof's or one with the registered fingerprint of a live head."""
        self.assertLessEqual(LEGACY_HEADS, RESERVED)
        self.assertFalse(RESERVED & set(HEADS))
        theorem = theorems_of(FIXTURE)['ClaimFixture.fret_total']
        live = theorem['statement']['head']
        for name in sorted(RESERVED):
            for module, fingerprint in ((RESERVED_MODULES[name],'0' * 32), ('tests.roadmap.claims.Fixture', None),
                                        (live['module'], live['fingerprint'])):
                with self.subTest(name=name, module=module):
                    spoof = with_head(theorem, name=name, module=module, fingerprint=fingerprint)
                    self.assertEqual(claims.claims_of(spoof, HEADS), frozenset())
                    _, entry, problem = claims.head_entry(spoof, HEADS)
                    self.assertIsNone(entry)
                    self.assertIn('reserved claim-head name', problem or '')
                    goal = claims.check_goal({'theorem': theorem['name'], 'strength': 'safety', 'domain': 'all'},
                                             {theorem['name']: spoof}, definition='ClaimFixture.ret')
                    self.assertEqual((goal['status'], goal['derived_strength']), ('rejected', None))
                    self.assertIn('reserved claim-head name', goal['reason'])

    def test_reserved_spoofs_are_extracted_and_rejected(self):
        """The fixture's spoofs of reserved names are audited (no name clash: the audit imports no
        retired module) and concluded in their own module; they support no claim."""
        theorems = classified(FIXTURE)
        for name in SPOOFS:
            with self.subTest(name=name):
                head = theorems_of(FIXTURE)[name]['statement']['head']
                self.assertIn(head['name'], RESERVED)
                self.assertEqual(head['module'], 'tests.roadmap.claims.Fixture')
                self.assertEqual(theorems[name]['claims'], [])
                self.assertIn('reserved claim-head name', theorems[name]['head_problem'])
        # The same spoofs, registered under their own declaration, would claim total correctness:
        # the reserved name is what rejects them.
        self.assertEqual(classified(FIXTURE, *spoof_registry())['ClaimFixture.spoof_eventually']['derived_strength'],
                         'total_correctness')

    def test_registry_matches_extracted_heads(self):
        seen = claims.head_identities(FIXTURE)
        for name, entry in HEADS.items():
            with self.subTest(head=name):
                self.assertEqual((seen[name]['module'], seen[name]['fingerprint']), (entry['module'], entry['fingerprint']))

    def test_registry_modules_are_imported_by_the_extractor(self):
        source = (ROOT / 'tools/Assurance.lean').read_text()
        for entry in HEADS.values():
            self.assertIn(f'import {entry["module"]}\n', source)
        # Reserved names need no import: their retired modules are not imported.
        for module in RESERVED_MODULES.values():
            self.assertNotIn(f'import {module}\n', source)

    def test_invalid_registry_rejected(self):
        entry = HEADS['Zig.Full.FTriple']
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'heads.json'
            for heads, reserved in (({'Eq': entry}, {}), ({'X': dict(entry, fingerprint='short')}, {}),
                                    ({'X': dict(entry, claims=['everything'])}, {}), ({'X': dict(entry, program=-1)}, {}),
                                    # A reserved name is never registered, `Eq` is never reserved.
                                    ({'X': entry}, {'X': 'M'}), ({'X': entry}, {'Eq': 'M'}),
                                    ({'X': entry}, {'Y': ''}), ({'X': entry}, ['Y']), ({'X': entry}, None)):
                with self.subTest(heads=heads, reserved=reserved):
                    data = {'schema_version': 1, 'heads': heads}
                    if reserved is not None:
                        data['reserved'] = reserved
                    path.write_text(json.dumps(data))
                    with self.assertRaises(ValueError):
                        claims.load_heads(path)

    def test_caller_obligations_follow_the_kernel_graph(self):
        """W1: a claim about a function with an Allocator parameter names ALC-09 (and only then)."""
        report = copy.deepcopy(FIXTURE)
        first, second = report['theorems'][0]['name'], report['theorems'][1]['name']
        # `Lists.push` carries `-- air2lean-premises: {"ALC-09":[0]}` in Proofs/Lists/Gen.lean.
        report['nodes'] = [{'name': first, 'module': 'Proofs.Lists.Proofs', 'kind': 'theorem',
                            'dependencies': ['Lists.push']},
                           {'name': 'Lists.push', 'module': 'Proofs.Lists.Gen', 'kind': 'definition',
                            'dependencies': []},
                           {'name': second, 'module': 'Proofs.Lists.Proofs', 'kind': 'theorem',
                            'dependencies': []}]
        theorems = classified(report)
        self.assertEqual(theorems[first]['caller_obligations'], ['ALC-09'])
        self.assertEqual(theorems[second]['caller_obligations'], [])
        self.assertEqual(classified(FIXTURE)[first]['caller_obligations'], [])

    def test_malformed_shapes_support_nothing(self):
        eq = {'statement': {'head': {'name': 'Eq', 'module': 'Init.Prelude'}}}
        for shape in (None, 3, {}, {'head': None}, {'head': 'Eq'}, {'head': 'Eq', 'args': 'x'},
                      {'head': 'Eq', 'args': [{'head': 'Option.some'}]},
                      {'head': 'Eq', 'args': [{'head': 'Option.some', 'args': [{'head': 'Except.error'}]}]},
                      {'head': 'Eq', 'args': [{'head': 'Pure.pure'}, {'head': 'Pure.pure'}]},
                      # `pure` without its monad, in `Option` around an error, or in an unknown monad.
                      {'head': 'Eq', 'args': [{'head': 'Pure.pure'}]},
                      {'head': 'Eq', 'args': [pure('Option', {'head': 'Except.error'})]},
                      {'head': 'Eq', 'args': [pure('Option', {'head': None})]},
                      {'head': 'Eq', 'args': [pure('Id', {'head': 'Prod.mk'})]}):
            self.assertEqual(claims.claims_of(dict(eq, conclusion=shape), HEADS), frozenset(), shape)
        self.assertEqual(claims.claims_of({'conclusion': {'head': 'Eq'}}, HEADS), frozenset())

    def test_asm_effect_opaque_carries_fault_premise(self):
        """airAsmFx_ is classified by the same policy rule table as airAsm_ and, over an absence
        claim, carries ASM-04 too (ASM-03 implies ASM-01 implies ASM-04)."""
        report = copy.deepcopy(FIXTURE)
        for theorem in report['theorems']:
            if theorem['name'] in ('ClaimFixture.ret_run', 'ClaimFixture.panic_pure'):
                theorem['opaque_dependencies'] = ['Asm.airAsmFx_3653072158']
        theorems = classified(report)
        self.assertEqual(theorems['ClaimFixture.ret_run']['premises'], ['ASM-03', 'ASM-04'])
        self.assertEqual(theorems['ClaimFixture.panic_pure']['premises'], ['ASM-03'])

    def test_asm_closure_carries_fault_premise(self):
        """S7: a no-panic or guaranteed-return claim over an inline-asm opaque carries ASM-04
        (the allowlist entry's fault condition); a report without the closure is rejected."""
        report = copy.deepcopy(FIXTURE)
        for theorem in report['theorems']:
            if theorem['name'] in ('ClaimFixture.ret_run', 'ClaimFixture.panic_pure'):
                theorem['opaque_dependencies'] = ['Asm.airAsm_3653072158']
        theorems = classified(report)
        self.assertEqual(theorems['ClaimFixture.ret_run']['premises'], ['ASM-01', 'ASM-04'])
        self.assertEqual(theorems['ClaimFixture.panic_pure']['premises'], ['ASM-01'])
        self.assertEqual(theorems['ClaimFixture.ret_some']['premises'], [])
        audited = theorems_of(report)
        goal = claims.check_goal({'theorem': 'ClaimFixture.ret_run', 'strength': 'total_correctness',
                                  'domain': 'all'}, audited, definition='ClaimFixture.ret')
        self.assertEqual((goal['status'], goal['premises']), ('accepted', ['ASM-01', 'ASM-04']))
        del audited['ClaimFixture.ret_run']['opaque_dependencies']
        goal = claims.check_goal({'theorem': 'ClaimFixture.ret_run', 'strength': 'safety', 'domain': 'all'},
                                 audited, definition='ClaimFixture.ret')
        self.assertEqual(goal['status'], 'rejected')
        self.assertIn('opaque_dependencies', goal['reason'])

    def test_concurrency_claim_lists_memory_model_premise(self):
        """C12: a claim whose closure reaches the scheduler or the atomics model lists the
        memory-model adequacy premise (ORD-06); a report without `runtime_modules`, or with an
        unmapped runtime module, is rejected."""
        theorems = classified(copy.deepcopy(FIXTURE))
        self.assertEqual(theorems['ClaimFixture.cret_partial']['premises'], ['ORD-06'])
        self.assertEqual(theorems['ClaimFixture.ret_run']['premises'], [])
        report = copy.deepcopy(FIXTURE)
        for theorem in report['theorems']:
            if theorem['name'] == 'ClaimFixture.ret_run':
                theorem['runtime_modules'] = theorem['runtime_modules'] + ['ZigLean.Conc.Word']
        goal = claims.check_goal({'theorem': 'ClaimFixture.ret_run', 'strength': 'total_correctness',
                                  'domain': 'all'}, theorems_of(report), definition='ClaimFixture.ret')
        self.assertEqual((goal['status'], goal['premises']), ('accepted', ['ORD-06']))
        for change in ({'runtime_modules': None}, {'runtime_modules': ['ZigLean.Unmapped']}):
            audited = theorems_of(copy.deepcopy(FIXTURE))
            audited['ClaimFixture.ret_run'].update(change)
            goal = claims.check_goal({'theorem': 'ClaimFixture.ret_run', 'strength': 'safety', 'domain': 'all'},
                                     audited, definition='ClaimFixture.ret')
            self.assertEqual(goal['status'], 'rejected')
            self.assertIn('runtime_modules', goal['reason'])

    def test_old_or_failed_reports_are_rejected(self):
        for field in ('conclusion', 'statement'):
            old = copy.deepcopy(FIXTURE)
            del old['theorems'][0][field]
            with self.assertRaisesRegex(ValueError, 'regenerate'):
                claims.classify(old)
        with self.assertRaisesRegex(ValueError, 'completed audit'):
            claims.classify({'schema_version': 1, 'status': 'error', 'error': 'build failed'})
        duplicate = copy.deepcopy(FIXTURE)
        duplicate['theorems'].append(duplicate['theorems'][0])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            claims.classify(duplicate)


class AssessTests(unittest.TestCase):
    """Binding, domain, hypotheses and witnesses from the extracted kernel statements."""

    def goal(self, theorem, strength, definition, domain='all', report=FIXTURE, heads=None, bound=None, **extra):
        goal = {'theorem': theorem, 'strength': strength, 'domain': domain}
        if bound is not None:
            goal['bound'] = bound
        return claims.check_goal(goal, theorems_of(report), definition=definition, heads=heads, **extra)

    def spoof_goal(self, theorem, strength, domain='all', **extra):
        heads, reserved = spoof_registry()
        return self.goal(theorem, strength, 'ClaimFixture.ret', domain, heads=heads, reserved=reserved, **extra)

    def test_subject_must_be_the_root(self):
        self.assertEqual(self.goal('ClaimFixture.fret_total', 'total_correctness', 'ClaimFixture.ret')['status'],
                         'accepted')
        for definition in ('ClaimFixture.boom', 'ClaimFixture.diverge'):
            goal = self.goal('ClaimFixture.fret_total', 'total_correctness', definition)
            self.assertEqual((goal['status'], goal['binding']), ('rejected', 'unrelated'))
            self.assertIn('ClaimFixture.ret', goal['reason'])
        # Runners (`StateT.run`, `ExceptT.run`) are peeled to the computation.
        for name in ('ClaimFixture.ret_run', 'ClaimFixture.ret_some', 'ClaimFixture.ret_pure_ok'):
            self.assertEqual(self.goal(name, 'total_correctness', 'ClaimFixture.ret')['binding'], 'direct', name)
        # An unregistered head (a wrapper definition) has no recognised computation.
        goal = self.goal('ClaimFixture.fwrapped_total', 'safety', 'ClaimFixture.ret')
        self.assertEqual((goal['status'], goal['binding']), ('rejected', 'mentions'))

    def test_domain_is_derived(self):
        goal = self.goal('ClaimFixture.ret_run', 'total_correctness', 'ClaimFixture.ret')
        self.assertEqual(goal['derived_domain']['scope'], 'universal')
        self.assertEqual(goal['derived_domain']['arguments'], [{'position': 0, 'argument': 'v'}, {'state': 0, 'argument': 'm'}])
        for name, field, value in (('ClaimFixture.ret_run_ground', 'fixed', ['parameter 0']),
                                   ('ClaimFixture.fpremise_total', 'constrained_by', ['_h'])):
            with self.subTest(theorem=name):
                goal = self.goal(name, 'total_correctness', 'ClaimFixture.ret')
                self.assertEqual(goal['status'], 'rejected')
                self.assertIn('not marked scoped', goal['reason'])
                self.assertEqual(goal['derived_domain'][field], value)
                goal = self.goal(name, 'total_correctness', 'ClaimFixture.ret', domain='scoped: one input')
                self.assertEqual(goal['status'], 'accepted', goal['reason'])

    def test_hypotheses_about_generated_code_are_rejected(self):
        report = copy.deepcopy(FIXTURE)
        theorem = theorems_of(report)['ClaimFixture.fpremise_total']
        theorem['statement']['binders'][2]['defs'] = ['ClaimFixture.ret']
        goal = self.goal('ClaimFixture.fpremise_total', 'safety', 'ClaimFixture.ret', 'scoped: v > 0', report=report)
        self.assertEqual(goal['status'], 'rejected')
        self.assertIn('_h mentions ClaimFixture.ret', goal['reason'])
        # A proposition wrapped in a non-Prop type (`PLift (ret v = ...)`) is still a premise.
        theorem['statement']['binders'][2]['prop'] = False
        goal = self.goal('ClaimFixture.fpremise_total', 'safety', 'ClaimFixture.ret', 'scoped: v > 0', report=report)
        self.assertIn('_h mentions ClaimFixture.ret', goal['reason'] or '')
        self.assertEqual(goal['derived_domain']['constrained_by'], ['_h'])
        theorem['statement']['binders'][2]['prop'] = True
        # Allowed only as a declared root assumption; a claim head, registered or reserved, never,
        # even when declared.
        goal = self.goal('ClaimFixture.fpremise_total', 'total_correctness', 'ClaimFixture.ret', 'scoped: v > 0',
                         report=report, allowed=['ClaimFixture.ret'])
        self.assertEqual(goal['status'], 'accepted', goal['reason'])
        for head in (FTOTAL, *sorted(RESERVED)):
            with self.subTest(head=head):
                theorem['statement']['binders'][2]['defs'] = [head]
                goal = self.goal('ClaimFixture.fpremise_total', 'safety', 'ClaimFixture.ret', 'scoped: v > 0',
                                 report=report, allowed=[head])
                self.assertEqual(goal['status'], 'rejected')
                self.assertIn(f'mentions {head}', goal['reason'])
        # Any definition of the generated module counts, not only the root.
        theorem['statement']['binders'][2]['defs'] = ['ClaimFixture.boom']
        goal = self.goal('ClaimFixture.fpremise_total', 'safety', 'ClaimFixture.ret', 'scoped: v > 0', report=report,
                         generated={'ClaimFixture.boom'})
        self.assertEqual(goal['status'], 'rejected')

    def test_witnesses_cap_strength(self):
        goal = self.goal('ClaimFixture.fdiverge_partial', 'partial_correctness', 'ClaimFixture.diverge')
        self.assertEqual((goal['status'], goal['derived_strength']), ('rejected', 'safety'))
        self.assertIn('liveness witness absent', goal['reason'])
        self.assertEqual(self.goal('ClaimFixture.fdiverge_partial', 'safety', 'ClaimFixture.diverge')['status'],
                         'accepted')
        self.assertEqual(self.goal('ClaimFixture.fret_partial', 'partial_correctness', 'ClaimFixture.ret')['status'],
                         'accepted')
        # A companion must itself be an allowed audited theorem, with the recomputed statement.
        report = copy.deepcopy(FIXTURE)
        theorems = theorems_of(report)
        theorems['ClaimFixture.fret_total.nonvacuous']['allowed'] = False
        goal = self.goal('ClaimFixture.fret_total', 'total_correctness', 'ClaimFixture.ret', report=report)
        self.assertEqual(goal['status'], 'rejected')
        self.assertIn('non-vacuity witness unaudited', goal['reason'])
        theorems['ClaimFixture.fret_partial']['statement']['witnesses']['liveness']['status'] = 'mismatch'
        goal = self.goal('ClaimFixture.fret_partial', 'partial_correctness', 'ClaimFixture.ret', report=report)
        self.assertIn('liveness witness mismatch', goal['reason'])

    def test_full_state_heads(self):
        ret = 'ClaimFixture.ret'
        for name, strength in (('ClaimFixture.fret_total', 'total_correctness'),
                               ('ClaimFixture.fret_partial', 'partial_correctness'),
                               ('ClaimFixture.tret_total', 'total_correctness'),
                               ('ClaimFixture.tret_partial', 'partial_correctness')):
            with self.subTest(name=name):
                goal = self.goal(name, strength, ret)
                self.assertEqual((goal['status'], goal['binding']), ('accepted', 'direct'), goal['reason'])
        # A total full-state head's liveness is its own `FReturns` half: none is asked for.
        self.assertEqual(theorems_of(FIXTURE)['ClaimFixture.fret_total']['statement']['witnesses']['liveness']['status'],
                         'not_required')
        goal = self.goal('ClaimFixture.cret_partial', 'partial_correctness', 'Pure.pure')
        self.assertEqual((goal['status'], goal['binding']), ('accepted', 'direct'), goal['reason'])
        goal = self.goal('ClaimFixture.fdiverge_partial', 'partial_correctness', 'ClaimFixture.diverge')
        self.assertIn('liveness witness absent', goal['reason'])
        # `FTotalTriple False c Q` holds for any c; its premises are not trivially inhabited.
        # Without a witness it supports no claim, not even safety (audit 2026-10-14 S1).
        for strength in ('total_correctness', 'safety'):
            goal = self.goal('ClaimFixture.ffalse_total', strength, 'ClaimFixture.diverge', 'scoped: none')
            self.assertEqual((goal['status'], goal['derived_strength']), ('rejected', None))
            self.assertIn('non-vacuity witness absent', goal['reason'])

    def test_bounded_return(self):
        goal = self.spoof_goal('ClaimFixture.spoof_within', 'total_correctness')
        self.assertEqual((goal['status'], goal['bound']), ('accepted', BOUNDS['ClaimFixture.spoof_within']), goal['reason'])

    def test_declared_bounds_are_checked_against_the_theorem(self):
        within, sym = 'ClaimFixture.spoof_within', 'ClaimFixture.spoof_within_sym'
        accepted = [(within, {'unit': 'scheduler_turns', 'max': 2}), (within, {'unit': 'scheduler_turns', 'max': 5}),
                    (sym, {'unit': 'scheduler_turns', 'expr': 'n  + 1'})]
        for theorem, bound in accepted:
            with self.subTest(bound=bound):
                goal = self.spoof_goal(theorem, 'total_correctness', bound=bound)
                self.assertEqual(goal['status'], 'accepted', goal['reason'])
        rejected = [(within, {'unit': 'scheduler_turns', 'max': 1}, 'exceeds the declared max'),
                    (within, {'unit': 'loop_body_runs', 'max': 9}, 'bounds scheduler_turns'),
                    (sym, {'unit': 'scheduler_turns', 'max': 100}, 'not a closed number'),
                    (sym, {'unit': 'scheduler_turns', 'expr': 'n'}, 'is not the declared'),
                    (within, {'unit': 'scheduler_turns'}, 'a declared bound is'),
                    (within, {'unit': 'scheduler_turns', 'max': -1}, 'a declared bound is'),
                    (within, {'unit': 'scheduler_turns', 'max': 2, 'expr': '2'}, 'a declared bound is'),
                    ('ClaimFixture.fret_total', {'unit': 'loop_body_runs', 'max': 3}, 'states no bound')]
        for theorem, bound, reason in rejected:
            with self.subTest(bound=bound):
                goal = self.spoof_goal(theorem, 'total_correctness', bound=bound)
                self.assertEqual(goal['status'], 'rejected')
                self.assertIn(reason, goal['reason'])
        # Unregistered again, the bounded spoof meets no goal at all.
        goal = self.goal(within, 'safety', 'ClaimFixture.ret', bound={'unit': 'scheduler_turns', 'max': 5})
        self.assertEqual(goal['status'], 'rejected')
        self.assertIn('reserved claim-head name', goal['reason'])

    def test_bound_without_recorded_argument_fails_closed(self):
        report = copy.deepcopy(FIXTURE)
        for arg in theorems_of(report)['ClaimFixture.spoof_within']['statement']['args']:
            arg.pop('nat', None)
        goal = self.spoof_goal('ClaimFixture.spoof_within', 'total_correctness', report=report,
                               bound={'unit': 'scheduler_turns', 'max': 1000})
        self.assertEqual(goal['status'], 'rejected')

    def test_registry_bound_needs_its_argument_position(self):
        heads, _ = spoof_registry()
        bounded = {k: v for k, v in heads[WITHIN].items() if k != 'bound_arg'}
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'heads.json'
            path.write_text(json.dumps({'schema_version': 1, 'heads': {'X': bounded}, 'reserved': {}}))
            with self.assertRaises(ValueError):
                claims.load_heads(path)
            path.write_text(json.dumps({'schema_version': 1, 'heads': {'X': heads[WITHIN]}, 'reserved': {}}))
            self.assertEqual(claims.load_heads(path)['X']['bound_arg'], 1)

    def test_premise_dependent_return_cannot_meet_unconditional_goals(self):
        for strength in ('total_correctness', 'partial_correctness', 'safety'):
            with self.subTest(strength=strength):
                goal = self.spoof_goal('ClaimFixture.spoof_under', strength)
                self.assertEqual((goal['status'], goal['claim_class']),
                                 ('rejected', 'guaranteed-return-under-premise'))
                self.assertIn('premise', goal['reason'])

    def test_new_heads_plug_into_the_same_mechanism(self):
        heads, reserved = spoof_registry()
        self.assertEqual(classified(FIXTURE, heads, reserved)['ClaimFixture.spoof_eventually']['derived_strength'],
                         'total_correctness')
        goal = self.spoof_goal('ClaimFixture.spoof_eventually', 'total_correctness')
        # The initial memory `{}` is fixed: the claim is scoped to it.
        self.assertEqual((goal['binding'], goal['derived_domain']['fixed']), ('direct', ['initial state 0']))
        self.assertEqual(goal['status'], 'rejected')
        goal = self.spoof_goal('ClaimFixture.spoof_eventually', 'total_correctness', domain='scoped: initial memory {}')
        self.assertEqual(goal['status'], 'accepted', goal['reason'])
        heads[EVENTUALLY] = dict(heads[EVENTUALLY], fingerprint='1' * 32)
        goal = self.goal('ClaimFixture.spoof_eventually', 'total_correctness', 'ClaimFixture.ret',
                         heads=heads, reserved=reserved)
        self.assertIn('not the registered one', goal['reason'])


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        (self.base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        self.report = self.base / 'assurance.json'
        # A report bound (H1) to this checkout's revision and to one artifact digest.
        self.olean = self.base / 'Fixture.olean'
        self.olean.write_bytes(b'compiled fixture')
        self.fixture = dict(FIXTURE, freshness={
            'revision': assumptions.git_revision(), 'lake_trace_check': {'modules': [], 'status': 'up-to-date'},
            'artifacts': [{'module': 'Fixture', 'olean': str(self.olean),
                           'olean_sha256': assumptions.file_sha256(self.olean), 'source': None, 'source_sha256': None}]})
        self.report.write_text(json.dumps(self.fixture))

    def manifest(self, goals, function='ret', bounds=None):
        manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['a.zig'],
                    'components': {'compiler_patch': ['p'], 'runtime': ['r'], 'toolchain': ['t']},
                    'allowed_assumptions': [],
                    'roots': [{'id': 'root', 'function': function, 'air': ['f.json'], 'namespace': 'ClaimFixture',
                               'prefix': '', 'contracts': ['Fixture.lean'],
                               'goals': [{'theorem': t, 'strength': s,
                                          'domain': 'scoped: fixture' if bounds else 'fixture',
                                          **({'bound': bounds[t]} if bounds and t in bounds else {})}
                                         for t, s in goals],
                               'assumptions': [], 'exclusions': []}]}
        path = self.base / 'project.json'
        path.write_text(json.dumps(manifest))
        return path

    def cli(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), *map(str, args)],
                              capture_output=True, text=True, timeout=30)

    def check(self, goals, function='ret', flags=('--allow-dirty',), bounds=None):
        # The checkout under test may have uncommitted changes; refusal tests pass no flag.
        result = self.cli('check', self.manifest(goals, function, bounds), '--assurance', self.report, *flags)
        return result.returncode, json.loads(result.stdout) if result.stdout else None, result.stderr

    def test_matching_and_weaker_goals_accepted(self):
        code, result, err = self.check([('ClaimFixture.fret_total', 'total_correctness'),
                                        ('ClaimFixture.fret_total', 'partial_correctness'),
                                        ('ClaimFixture.ret_run', 'total_correctness'),
                                        ('ClaimFixture.fret_partial', 'partial_correctness'),
                                        ('ClaimFixture.fret_partial', 'safety'),
                                        ('ClaimFixture.tret_total', 'total_correctness')])
        self.assertEqual(code, 0, err)
        self.assertEqual(result['status'], 'pass')
        self.assertTrue(all(g['status'] == 'accepted' for g in result['roots'][0]['goals']))
        code, result, err = self.check([('ClaimFixture.fdiverge_partial', 'safety')], function='diverge')
        self.assertEqual(code, 0, err)

    def test_declared_bound_is_checked_in_the_manifest(self):
        goals = [('ClaimFixture.fret_total', 'total_correctness')]
        for bound in ({'unit': 'loop_body_runs', 'max': 1}, {'unit': 'scheduler_turns', 'max': 9}, {'unit': 'loop_body_runs'}):
            with self.subTest(bound=bound):
                code, result, err = self.check(goals, bounds={goals[0][0]: bound})
                self.assertEqual(code, 1, err)
                self.assertIn('bound', result['roots'][0]['goals'][-1]['reason'])

    def test_diverging_program_cannot_be_declared_correct(self):
        for strength in ('total_correctness', 'partial_correctness'):
            code, result, err = self.check([('ClaimFixture.fdiverge_partial', strength)], function='diverge')
            self.assertEqual(code, 1)
            goal = result['roots'][0]['goals'][0]
            self.assertEqual((goal['status'], goal['derived_strength']), ('rejected', 'safety'))
            self.assertIn('exceeds', goal['reason'])
            self.assertIn('fdiverge_partial', err)

    def test_overstated_goals_rejected(self):
        for name, strength, function in [('ClaimFixture.fret_partial', 'total_correctness', 'ret'),
                                         ('ClaimFixture.fwrapped_total', 'total_correctness', 'ret'),
                                         ('ClaimFixture.fpartial_and_returns', 'total_correctness', 'ret'),
                                         ('ClaimFixture.panic_run', 'safety', 'boom'),
                                         ('ClaimFixture.panic_some', 'safety', 'boom'),
                                         ('ClaimFixture.panic_pure', 'safety', 'boom'),
                                         ('ClaimFixture.fdiverge_not_total', 'safety', 'diverge'),
                                         ('ClaimFixture.ffalse_total', 'total_correctness', 'diverge'),
                                         ('ClaimFixture.fret_total', 'resource_bound', 'ret'),
                                         ('ClaimFixture.fret_total', 'correspondence', 'ret'),
                                         ('ClaimFixture.fret_total', 'total_correctness', 'boom'),
                                         ('ClaimFixture.ret_run_ground', 'total_correctness', 'ret'),
                                         *((name, 'safety', 'ret') for name in SPOOFS)]:
            with self.subTest(name=name, strength=strength):
                code, result, _ = self.check([(name, strength)], function)
                self.assertEqual(code, 1)
                self.assertEqual(result['roots'][0]['goals'][0]['status'], 'rejected')

    def test_one_overstated_goal_fails_the_manifest(self):
        code, result, _ = self.check([('ClaimFixture.fret_total', 'total_correctness'),
                                      ('ClaimFixture.fret_partial', 'total_correctness')])
        self.assertEqual(code, 1)
        self.assertEqual([g['status'] for g in result['roots'][0]['goals']], ['accepted', 'rejected'])

    def test_missing_and_unaudited_theorems_rejected(self):
        code, result, _ = self.check([('fret_total', 'safety')])
        self.assertEqual(code, 1)
        self.assertIn('absent', result['roots'][0]['goals'][0]['reason'])
        report = copy.deepcopy(self.fixture)
        for theorem in report['theorems']:
            theorem['allowed'] = False
        self.report.write_text(json.dumps(report))
        code, result, _ = self.check([('ClaimFixture.fret_total', 'safety')])
        self.assertEqual(code, 1)
        self.assertIn('violations', result['roots'][0]['goals'][0]['reason'])

    def test_invalid_inputs_exit_2(self):
        self.report.write_text(json.dumps({'schema_version': 1, 'status': 'error', 'error': 'x'}))
        code, _, err = self.check([('ClaimFixture.fret_total', 'safety')])
        self.assertEqual(code, 2)
        self.assertIn('claims error', err)
        self.report.write_text(json.dumps(self.fixture))
        code, _, _ = self.check([('ClaimFixture.fret_total', 'proved')])
        self.assertEqual(code, 2)

    def test_report_must_be_fresh_for_this_tree(self):
        goal = [('ClaimFixture.fret_total', 'total_correctness')]
        code, result, err = self.check(goal)
        self.assertEqual(code, 0, err)
        self.assertEqual(result['freshness']['artifacts'], 1)
        cases = {'no freshness binding': {k: v for k, v in self.fixture.items() if k != 'freshness'},
                 'revision': dict(self.fixture, freshness=dict(self.fixture['freshness'],
                                                               revision={'head': '0' * 40, 'tracked_dirty': False})),
                 'trace check': dict(self.fixture, freshness=dict(self.fixture['freshness'], lake_trace_check={}))}
        for reason, report in cases.items():
            with self.subTest(reason=reason):
                self.report.write_text(json.dumps(report))
                code, _, err = self.check(goal)
                self.assertEqual(code, 2)
                self.assertIn(reason, err)
        self.report.write_text(json.dumps(self.fixture))
        self.olean.write_bytes(b'recompiled fixture')
        code, _, err = self.check(goal)
        self.assertEqual(code, 2)
        self.assertIn('stale', err)

    def test_dirty_report_needs_explicit_recorded_permission(self):
        goal = [('ClaimFixture.fret_total', 'total_correctness')]
        dirty = copy.deepcopy(self.fixture)
        dirty['freshness']['revision']['tracked_dirty'] = True
        self.report.write_text(json.dumps(dirty))
        code, _, err = self.check(goal, flags=())
        self.assertEqual(code, 2)
        self.assertIn('--allow-dirty', err)
        code, result, err = self.check(goal)
        self.assertEqual(code, 0, err)
        self.assertEqual((result['freshness']['tracked_dirty'], result['freshness']['dirty_allowed']), (True, True))

    def test_report_and_heads_commands(self):
        result = self.cli('report', '--assurance', self.report)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(json.loads(result.stdout)['theorems']), len(EXPECTED))
        result = self.cli('heads', '--assurance', self.report)
        self.assertEqual(result.returncode, 0, result.stderr)
        seen = json.loads(result.stdout)
        self.assertIn(FTOTAL, seen)
        self.assertEqual(seen[EVENTUALLY]['module'], 'tests.roadmap.claims.Fixture')


if __name__ == '__main__':
    unittest.main()
