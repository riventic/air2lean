#!/usr/bin/env python3
"""Offline typed accounting tests. Every subprocess has a short timeout."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location('diff_report', ROOT/'scripts/diff-report.py')
REPORT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REPORT)
K = REPORT.Kind
S = REPORT.Status

class Outcomes(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        (self.root/'examples/basic').mkdir(parents=True)
        self.summary=self.root/'summary.json'
        (self.root/'scripts').mkdir()
        (self.root/'scripts/panic-policy.tsv').write_text((ROOT/'scripts/panic-policy.tsv').read_text())

    def seed(self, native, model, nk=K.VALUE, mk=K.VALUE, search=None):
        paths={name:self.root/'tests/diff'/name for name in ('basic/inputs','out/zig/basic','out/lean/basic')}
        for path in paths.values():path.mkdir(parents=True,exist_ok=True)
        (paths['basic/inputs']/'foo.jsonl').write_text('[1]\n')
        for side,value,kind in [('zig',native,nk),('lean',model,mk)]:
            file=paths['out/'+side+'/basic']/'foo.jsonl'
            file.write_text(json.dumps(value,separators=(',',':'))+'\n')
            meta={'schema':1,'kind':kind.value,'legacy':value}
            if side=='lean' and search:meta['search']=search
            Path(str(file)+'.outcomes').write_text(json.dumps(meta)+'\n')

    def compare(self):
        status=REPORT.compare(self.root,['basic'],'0.16.0','Linux-x86_64',self.summary)
        return status,json.loads(self.summary.read_text())

    def search(self,status='capped',saw=False):
        return dict(prefix=[0],options=[2],runs=1,fuel=4,cap=1,status=status,saw_no_result=saw)

    def test_package_registers_imported_observation_module(self):
        package=tomllib.loads((ROOT/'tests/diff/lakefile.toml').read_text())
        libraries={item['name'] for item in package.get('lean_lib',[])}
        self.assertIn('Outcome',libraries)
        self.assertTrue((ROOT/'tests/diff/Outcome.lean').is_file())
        self.assertIn('import Outcome',(ROOT/'tests/diff/Diff.lean').read_text().splitlines())
        self.assertIn('import Outcome',(ROOT/'tests/roadmap/outcome-accounting/Check.lean').read_text().splitlines())
        self.assertNotIn('  prefix :',(ROOT/'tests/diff/Outcome.lean').read_text())

    def test_observation_constructors_use_named_fields_with_default_search(self):
        outcome=(ROOT/'tests/diff/Outcome.lean').read_text()
        self.assertIn('search : Option Search := none',outcome)
        self.assertIn('instance : Nonempty Observation := ⟨noResult⟩',outcome)
        for name in ('tests/diff/Outcome.lean','tests/diff/Diff.lean','tests/roadmap/outcome-accounting/Search.lean'):
            source=(ROOT/name).read_text()
            self.assertNotIn('⟨"',source,name)
            self.assertIn('line := "',source,name)

    def test_metadata_binding_rejects_nested_boolean_integer_aliases(self):
        for payload,bound in [(True,1),({'x':[False]}, {'x':[0]}),(1,1.0),(0.0,-0.0)]:
            native={'ok':payload}
            metadata=json.dumps({'schema':1,'kind':'value','legacy':{'ok':bound}})
            with self.assertRaises(REPORT.Invalid):REPORT.observation(metadata,native,'native')

    def test_metadata_binding_ignores_object_order_only(self):
        self.assertTrue(REPORT.json_equal({'x':[1,False],'y':2},{'y':2,'x':[1,False]}))
        self.assertFalse(REPORT.json_equal({'x':1},{'x':True}))
        self.assertTrue(REPORT.json_equal(1.0,1e0))

    def test_arbitrary_glob_masks_and_pointer_fragments_never_match(self):
        for mask in ('*','[ab]1','a*','pp','???','?'):
            self.assertFalse(REPORT.same_value({'ok':0,'bufs':['a1']},{'ok':0,'bufs':[mask]}),mask)
        self.assertFalse(REPORT.buffer_match('A1','?1'))
        self.assertTrue(REPORT.buffer_match('a1b2','??b?'))
        self.assertFalse(REPORT.buffer_match('a1b2','?1'))
        self.assertFalse(REPORT.buffer_match('a','?'))

    def test_pointer_fragment_remains_mismatch_not_setup_failure(self):
        self.seed({'ok':0,'bufs':['0011']},{'ok':0,'bufs':['pppp']})
        code,data=self.compare()
        self.assertEqual(code,1)
        self.assertEqual(data['counts'],{'mismatch':1})
        self.assertEqual(data['setup_failures'],0)

    def test_native_signal_domain_is_native_unknown_only(self):
        meta={'schema':1,'kind':'native_signal','legacy':{'fail':'unknown'}}
        self.assertEqual(REPORT.observation(json.dumps(meta),{'fail':'unknown'},'native')[0],K.NATIVE_SIGNAL)
        with self.assertRaises(REPORT.Invalid):REPORT.observation(json.dumps(meta),{'fail':'unknown'},'model')
        for wire in ({'fail':'panic'},{'ok':7},{'fail':'unknown','signal':8}):
            meta['legacy']=wire
            with self.assertRaises(REPORT.Invalid):REPORT.observation(json.dumps(meta),wire,'native')

    def test_native_signal_is_excluded_only_for_model_exclusion(self):
        self.seed({'fail':'unknown'},{'fail':'Zig.Error.illegal'},K.NATIVE_SIGNAL,K.ILLEGAL)
        (self.root/'tests/diff/basic/unspecified.txt').write_text('foo 1\n')
        code,data=self.compare()
        self.assertEqual(code,0)
        self.assertEqual(data['counts'],{'illegal_exclusion':1})
        self.assertEqual(data['setup_failures'],0)
        self.assertEqual(data['mutation_eligible'],0)
        self.seed({'fail':'unknown'},{'ok':7},K.NATIVE_SIGNAL,K.VALUE)
        (self.root/'tests/diff/basic/unspecified.txt').write_text('')
        code,data=self.compare()
        self.assertEqual(code,1)
        self.assertEqual(data['counts'],{'mismatch':1})
        self.assertEqual(data['mutation_eligible'],1)
        self.assertEqual(REPORT.classify({'fail':'unknown'},{'ok':7},K.NATIVE_SIGNAL,K.VALUE,None,True),S.MISMATCH)
        self.assertEqual(REPORT.classify({'fail':'unknown'},{'fail':'Zig.Error.panic'},K.NATIVE_SIGNAL,K.MODEL_PANIC,None),S.MISMATCH)

    def test_renderer_and_resource_failure_remain_fatal_against_illegal(self):
        self.seed({'fail':'unknown'},{'fail':'Zig.Error.illegal'},K.NATIVE_HARNESS_FAILURE,K.ILLEGAL)
        (self.root/'tests/diff/basic/unspecified.txt').write_text('foo 1\n')
        code,data=self.compare()
        self.assertEqual(code,1)
        self.assertEqual(data['counts'],{'native_harness_failure':1})
        self.assertEqual(data['setup_failures'],1)
        self.assertEqual(data['mutation_eligible'],0)

    def test_illegal_pin_change_with_raw_incomplete_search_is_not_detection(self):
        for search in (self.search('capped'),self.search('bounded',True),self.search('exhausted',True)):
            self.seed({'ok':1},{'fail':'Zig.Error.illegal'},K.VALUE,K.ILLEGAL,search)
            code,data=self.compare()
            self.assertEqual(code,1)
            self.assertEqual(data['counts'],{'illegal_exclusion':1})
            self.assertEqual(data['mutation_eligible'],0)
            self.assertEqual(data['legacy_counts'],{'unspecified':1})

    def test_value_comparison_is_computed_once_per_report_case(self):
        self.seed({'ok':1},{'ok':1})
        with patch.object(REPORT,'same_value',wraps=REPORT.same_value) as same:
            self.assertEqual(self.compare()[0],0)
        self.assertEqual(same.call_count,1)

    def test_shared_panic_policy_matches_shell_consumer_without_subshell_lookup(self):
        source=(ROOT/'scripts/diff.sh').read_text()
        start=source.index('panic_kinds=()');end=source.index('# The pin of function',start)
        body=source[start:end]
        self.assertNotIn('$(expected_ctor_for_zig_kind',source)
        cases=list(REPORT.PANICS)+['unknown','noreturnReturned']
        script='repo_root="$1"\n'+body+'\nshift\nfor kind in "$@"; do expected_ctor_for_zig_kind "$kind"; printf "%s=%s\\n" "$kind" "$expected_ctor"; done\n'
        result=subprocess.run(['bash','-c',script,'bash',str(ROOT),*cases],capture_output=True,text=True,timeout=3)
        self.assertEqual(result.returncode,0,result.stderr)
        mapping=dict(row.split('=',1) for row in result.stdout.splitlines())
        self.assertEqual(mapping,{kind:REPORT.PANICS.get(kind,'') for kind in cases})

    def test_panic_policy_rejects_duplicate_and_unknown_constructor(self):
        path=self.root/'policy.tsv'
        for text in ('panic\tpanic\npanic\tpanic\n','panic\tunmodeled\n'):
            path.write_text(text)
            with self.assertRaises(REPORT.Invalid):REPORT.load_panic_policy(path)

    def test_exponent_overflow_rejected_at_shared_json_boundary(self):
        for token in ('1e999','2e999','-1e999','-2e999'):
            for raw in (token,'[0,'+token+']','{"nested":{"number":'+token+'}}'):
                with self.subTest(raw=raw),self.assertRaises(REPORT.Invalid):REPORT.decode(raw)
            for raw in ('{"ok":'+token+'}','{"ok":{"nested":['+token+']}}'):
                with self.subTest(wire=raw),self.assertRaises(REPORT.Invalid):REPORT.wire(raw)
            metadata='{"schema":1,"kind":"value","legacy":{"ok":{"nested":['+token+']}}}'
            with self.subTest(binding=token),self.assertRaises(REPORT.Invalid):
                REPORT.observation(metadata,{'ok':{'nested':[1.0]}},'native')

    def test_finite_exponents_keep_type_zero_sign_and_spelling_policy(self):
        self.assertEqual(REPORT.decode('1e308'),1e308)
        self.assertEqual(REPORT.decode('-1e308'),-1e308)
        self.assertTrue(REPORT.json_equal(REPORT.decode('1.0'),REPORT.decode('1e0')))
        self.assertFalse(REPORT.json_equal(REPORT.decode('1'),REPORT.decode('1e0')))
        self.assertFalse(REPORT.json_equal(REPORT.decode('0.0'),REPORT.decode('-0e0')))
        metadata='{"schema":1,"kind":"value","legacy":{"ok":{"x":1e0}}}'
        kind,_=REPORT.observation(metadata,REPORT.wire('{"ok":{"x":1.0}}'),'native')
        self.assertEqual(kind,K.VALUE)

    def test_native_regression_checker_rejects_lost_prefix_and_false_panic(self):
        spec=importlib.util.spec_from_file_location('native_check',ROOT/'tests/roadmap/outcome-accounting/test_native.py')
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        directory=self.root/'tests/diff/out/zig/outcome-accounting';directory.mkdir(parents=True)
        def records(name,values):
            (directory/name).write_text(''.join(json.dumps(v,separators=(',',':'))+'\n' for v in values))
        prefix=[{'schema':1,'kind':'value','legacy':{'ok':7}},{'schema':1,'kind':'input_failure'}]
        records('prefix.jsonl',[{'ok':7}]);records('prefix.jsonl.outcomes',prefix[1:])
        with self.assertRaisesRegex(AssertionError,'prefix or failure row lost'):module.verify(self.root)
        records('prefix.jsonl.outcomes',prefix)
        records('renderer.jsonl',[{'fail':'harnessRenderFailure'}])
        records('renderer.jsonl.outcomes',[{'schema':1,'kind':'native_panic','legacy':{'fail':'harnessRenderFailure'}}])
        with self.assertRaisesRegex(AssertionError,'semantic mismatch'):module.verify(self.root)

    def test_native_phase_checker_rejects_signal_on_renderer_or_interruption(self):
        spec=importlib.util.spec_from_file_location('native_phase_check',ROOT/'tests/roadmap/outcome-accounting/test_native.py')
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        for wrong in (None,'interrupt','renderer-fault'):
            root=self.root/('valid' if wrong is None else wrong)
            directory=root/'tests/diff/out/zig/outcome-accounting';directory.mkdir(parents=True)
            payloads={'prefix':{'ok':7},'renderer':{'fail':'harnessRenderFailure'},
                      'source':{'fail':'panic'},'signal':{'fail':'unknown'},
                      'interrupt':{'fail':'unknown'},'renderer-fault':{'fail':'unknown'}}
            kinds={'prefix':'value','renderer':'native_harness_failure','source':'native_panic',
                   'signal':'native_signal','interrupt':'native_harness_failure','renderer-fault':'native_harness_failure'}
            if wrong:kinds[wrong]='native_signal'
            for name,legacy in payloads.items():
                (directory/(name+'.jsonl')).write_text(json.dumps(legacy)+'\n')
                metadata=[dict(schema=1,kind=kinds[name],legacy=legacy)]
                if name=='prefix':metadata.append(dict(schema=1,kind='input_failure'))
                (directory/(name+'.jsonl.outcomes')).write_text(''.join(json.dumps(row)+'\n' for row in metadata))
            if wrong:
                with self.assertRaisesRegex(AssertionError,'classification changed'):module.verify(root)
            else:module.verify(root)

    def test_actual_diff_setup_failures_invalidate_old_completed_report(self):
        cases=('missing_compiler','version_failure','unknown_example','invalid_example',
               'empty_selection','selection_failure','temporary_directory_failure','native_build_failure')
        for case in cases:
            with self.subTest(case=case):
                root=self.root/case;scripts=root/'scripts';scripts.mkdir(parents=True)
                for name in ('diff.sh','diff-report.py','panic-policy.tsv','example-selection.sh'):
                    (scripts/name).write_text((ROOT/'scripts'/name).read_text())
                (root/'examples/basic').mkdir(parents=True)
                harness=root/'tests/diff/basic/harness.zig';harness.parent.mkdir(parents=True);harness.touch()
                stale=root/'tests/diff/out/zig/basic/foo.jsonl.outcomes';stale.parent.mkdir(parents=True)
                stale.write_text('{"schema":1,"kind":"input_failure"}\n')
                summary=root/'summary.json';summary.write_text('{"schema":1,"complete":true,"mutation_eligible":999}')
                Path(str(summary)+'.jsonl').write_text('old evidence\n')
                compiler=root/'fake-compiler'
                compiler.write_text('#!/bin/bash\nif [ "$1" = version ]; then '+('exit 17' if case=='version_failure' else 'echo 0.16.0')+'; else exit 23; fi\n')
                compiler.chmod(0o755)
                env=dict(os.environ,AIR2LEAN_ZIG=str(compiler),AIR2LEAN_EXAMPLES='basic',AIR2LEAN_DIFF_REPORT=str(summary))
                if case=='missing_compiler':env['AIR2LEAN_ZIG']=str(root/'missing-compiler')
                if case=='unknown_example':env['AIR2LEAN_EXAMPLES']='not-known'
                if case=='invalid_example':env['AIR2LEAN_EXAMPLES']='../bad'
                if case in ('empty_selection','selection_failure'):
                    env.pop('AIR2LEAN_EXAMPLES',None)
                    (scripts/'example-selection.sh').write_text('air2lean_default_examples() { '+('return 19' if case=='selection_failure' else ':')+'; }\n')
                if case=='temporary_directory_failure':env['TMPDIR']=str(root/'absent-directory')
                result=subprocess.run(['bash',str(scripts/'diff.sh')],env=env,capture_output=True,text=True,timeout=3)
                self.assertNotEqual(result.returncode,0,result.stdout)
                report=REPORT.read_summary(summary)
                self.assertFalse(report['complete'])
                self.assertEqual(report['mutation_eligible'],0)
                self.assertEqual(report['failure'],'setup_failure')
                self.assertEqual(report['phase'],'build_native' if case in ('temporary_directory_failure','native_build_failure') else 'setup')
                self.assertFalse(Path(str(summary)+'.jsonl').exists())

    def test_report_initialization_failure_stops_before_mock_compiler(self):
        scripts=self.root/'scripts';(scripts/'diff.sh').write_text((ROOT/'scripts/diff.sh').read_text())
        (scripts/'diff-report.py').write_text('import sys\nraise SystemExit(42)\n')
        compiler=self.root/'fake-compiler';marker=self.root/'compiler-called'
        compiler.write_text('#!/bin/bash\ntouch "'+str(marker)+'"\nexit 23\n');compiler.chmod(0o755)
        env=dict(os.environ,AIR2LEAN_ZIG=str(compiler),AIR2LEAN_DIFF_REPORT=str(self.summary))
        result=subprocess.run(['bash',str(scripts/'diff.sh')],env=env,capture_output=True,text=True,timeout=3)
        self.assertEqual(result.returncode,42,result.stderr)
        self.assertFalse(marker.exists())
        self.assertIn('could not record differential failure evidence',result.stderr)

    def test_actual_review_comparison_fixture_supplies_policy_context(self):
        source=(ROOT/'scripts/review-checks.sh').read_text()
        fixture=source[source.index('compare="$test_dir/compare"'):source.index('expect_pass "healthy comparison"')]
        command='set -euo pipefail\nrepo_root="$1"\ntest_dir="$2"\n'+fixture+'\nbash "$compare/run.sh"\n'
        env=dict(os.environ,AIR2LEAN_DIFF_REPORT=str(self.root/'inherited-report.json'))
        result=subprocess.run(['bash','-c',command,'bash',str(ROOT),str(self.root)],env=env,capture_output=True,text=True,timeout=3)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertIn('TOTAL: ok=2 fail_match=0 unspecified=0 capped=0 mismatch=0',result.stdout)
        self.assertFalse((self.root/'inherited-report.json').exists())

    def test_normal_value_and_legacy_leaf(self):
        self.seed({'ok':'7'},{'ok':7})
        code,data=self.compare()
        self.assertEqual(code,0)
        self.assertEqual(data['counts'],{'value_match':1})
        self.assertEqual(data['legacy_counts'],{'ok':1})
        self.assertFalse(data['qualified'])

    def test_returned_error_is_value_not_panic(self):
        self.seed({'ok':{'err':'AllocationFailed'}},{'ok':{'err':'AllocationFailed'}},K.ERROR_RETURN,K.ERROR_RETURN)
        self.assertEqual(self.compare()[1]['counts'],{'error_return_match':1})

    def test_panics_are_distinct(self):
        self.seed({'fail':'integerOverflow'},{'fail':'Zig.Error.overflow'},K.NATIVE_PANIC,K.MODEL_PANIC)
        self.assertEqual(self.compare()[1]['counts'],{'panic_match':1})

    def test_panic_witness_survives_other_bounded_branches(self):
        self.seed({'fail':'integerOverflow'},{'fail':'Zig.Error.overflow'},K.NATIVE_PANIC,K.MODEL_PANIC,self.search('exhausted',True))
        self.assertEqual(self.compare()[1]['counts'],{'panic_match':1})

    def test_illegal_and_unspecified_split_with_same_legacy_pin(self):
        for kind,name,status in [(K.ILLEGAL,'illegal','illegal_exclusion'),(K.UNSPECIFIED,'unspecified','unspecified_exclusion')]:
            self.seed({'ok':1},{'fail':'Zig.Error.'+name},K.VALUE,kind)
            (self.root/'tests/diff/basic/unspecified.txt').write_text('foo 1\n')
            code,data=self.compare()
            self.assertEqual(code,0)
            self.assertEqual(data['counts'],{status:1})
            self.assertEqual(data['legacy_counts'],{'unspecified':1})
            self.assertEqual(data['mutation_eligible'],0)

    def test_native_unknown_cannot_hide_behind_illegal(self):
        self.seed({'fail':'unknown'},{'fail':'Zig.Error.illegal'},K.NATIVE_HARNESS_FAILURE,K.ILLEGAL)
        code,data=self.compare()
        self.assertEqual(code,1)
        self.assertEqual(data['counts'],{'native_harness_failure':1})
        self.assertEqual(data['mutation_eligible'],0)
        self.assertEqual(data['legacy_counts'],{'unspecified':1})

    def test_bounded_none_is_inconclusive_and_not_mutation(self):
        self.seed({'ok':1},{'diverge':True},K.VALUE,K.BOUNDED_NO_RESULT)
        code,data=self.compare()
        self.assertEqual(code,1)
        self.assertEqual(data['counts'],{'bounded_no_result':1})
        self.assertEqual(data['mutation_eligible'],0)

    def test_any_unmatched_no_result_branch_blocks_semantic_detection(self):
        self.seed({'ok':2},{'ok':1},K.VALUE,K.VALUE,self.search('bounded',True))
        self.assertEqual(self.compare()[1]['mutation_eligible'],0)
        self.assertEqual(self.compare()[1]['counts'],{'bounded_no_result':1})

    def test_real_match_is_a_witness_even_with_bounded_other_branches(self):
        self.seed({'ok':1},{'ok':1},K.VALUE,K.VALUE,self.search('witness',True))
        self.assertEqual(self.compare()[1]['counts'],{'value_match':1})

    def test_cap_pin_change_is_not_semantic_detection(self):
        self.seed({'ok':1},{'fail':'Zig.Error.capped'},K.VALUE,K.SEARCH_CAP,self.search())
        code,data=self.compare()
        self.assertEqual(code,1)
        self.assertEqual(data['counts'],{'search_cap':1})
        self.assertEqual(data['mutation_eligible'],0)
        self.assertEqual(data['pin_violations'][0]['counter'],'capped')
        (self.root/'tests/diff/basic/capped.txt').write_text('foo 1\n')
        self.assertEqual(self.compare()[0],0)

    def test_pin_drop_caused_by_cap_is_not_semantic_detection(self):
        self.seed({'ok':1},{'fail':'Zig.Error.capped'},K.VALUE,K.SEARCH_CAP,self.search())
        (self.root/'tests/diff/basic/unspecified.txt').write_text('foo 1\n')
        self.assertEqual(len(self.compare()[1]['pin_violations']),2)
        self.assertEqual(self.compare()[1]['mutation_eligible'],0)

    def test_return_kind_disagreement_is_not_a_match(self):
        self.seed({'ok':{'err':'A'}},{'ok':{'err':'A'}},K.ERROR_RETURN,K.VALUE)
        code,data=self.compare()
        self.assertEqual(code,1)
        self.assertEqual(data['counts'],{'mismatch':1})
        self.assertEqual(data['legacy_counts'],{'ok':1})

    def test_matching_error_name_changes_are_genuine_mismatches(self):
        self.seed({'ok':{'err':'A'}},{'ok':{'err':'B'}},K.ERROR_RETURN,K.ERROR_RETURN)
        self.assertEqual(self.compare()[1]['mutation_eligible'],1)

    def test_pinned_illegal_change_remains_detection(self):
        self.seed({'ok':1},{'ok':1})
        (self.root/'tests/diff/basic/unspecified.txt').write_text('foo 1\n')
        self.assertEqual(self.compare()[1]['mutation_eligible'],1)

    def test_deadlock_not_panic_or_divergence(self):
        self.seed({'ok':1},{'fail':'Zig.Error.deadlock'},K.VALUE,K.DEADLOCK)
        code,data=self.compare()
        self.assertEqual(code,1)
        row=json.loads(Path(data['cases_path']).read_text())
        self.assertEqual(row['model_kind'],'deadlock')
        self.assertEqual(row['status'],'mismatch')

    def test_host_difference_is_not_an_exact_match(self):
        self.seed({'ok':1},{'ok':2})
        (self.root/'tests/diff/basic/host.txt').write_text('foo\n')
        code=REPORT.compare(self.root,['basic'],'0.16.0','Darwin-arm64',self.summary)
        data=json.loads(self.summary.read_text())
        self.assertEqual(code,0)
        self.assertEqual(data['counts'],{'host_difference':1})
        self.assertEqual(data['exact_matches'],0)
        self.assertEqual(data['mutation_eligible'],0)

    def test_skipped_examples_are_separate_from_comparisons(self):
        self.seed({'ok':1},{'ok':1})
        (self.root/'examples/asm').mkdir()
        skipped=self.root/'tests/diff/asm/inputs';skipped.mkdir(parents=True)
        (skipped/'first.jsonl').write_text('[]\n');(skipped/'second.jsonl').write_text('[]\n')
        REPORT.compare(self.root,['basic'],'0.16.0','Darwin-arm64',self.summary)
        data=json.loads(self.summary.read_text())
        self.assertEqual(data['case_count'],1)
        self.assertEqual(data['skipped_examples'],1)
        self.assertEqual(data['skipped_functions'],2)
        self.assertEqual(data['exact_matches'],1)
        rows=[json.loads(line) for line in Path(data['cases_path']).read_text().splitlines()]
        self.assertEqual(rows[0]['reason'],'host_excluded')
        self.assertEqual(rows[0]['functions'],['first','second'])

    def test_matching_cases_do_not_claim_proof_applicability(self):
        self.seed({'ok':1},{'ok':1})
        proofs=self.root/'Proofs/Basic';proofs.mkdir(parents=True)
        (proofs/'Claim.lean').write_text('example : True := True.intro\n')
        _,data=self.compare()
        self.assertEqual(data['exact_matches'],1)
        self.assertEqual(data['proof_applicability'],'not_evaluated_by_differential_runner')
        self.assertEqual(data['proof_exclusions'],[dict(example='basic',reason='proof_applicability_not_evaluated',sources=['Proofs/Basic/Claim.lean'])])
        self.assertFalse(data['qualified'])

    def test_stale_or_inconsistent_metadata_rejected(self):
        self.seed({'ok':1},{'ok':1})
        file=self.root/'tests/diff/out/lean/basic/foo.jsonl.outcomes'
        file.write_text('{"schema":1,"kind":"value","legacy":{"ok":9}}\n')
        with self.assertRaisesRegex(REPORT.Invalid,'stale'):self.compare()
        file.write_text('{"schema":1,"kind":"illegal","legacy":{"ok":1}}\n')
        with self.assertRaises(REPORT.Invalid):self.compare()

    def test_unknown_schema_is_unsupported_not_mismatch(self):
        with self.assertRaises(REPORT.Unsupported):
            REPORT.observation('{"schema":2,"kind":"value","legacy":{"ok":1}}',{'ok':1},'model')

    def test_bool_schema_and_duplicate_keys_rejected(self):
        with self.assertRaises(REPORT.Invalid):REPORT.observation('{"schema":true,"kind":"value","legacy":{"ok":1}}',{'ok':1},'model')
        with self.assertRaises(REPORT.Invalid):REPORT.decode('{"ok":1,"ok":2}')

    def test_opaque_bytes_and_bool_values_never_normalized_as_numbers(self):
        self.assertFalse(REPORT.same_value({'ok':{'bytes':'0011'}},{'ok':{'bytes':'11'}}))
        self.assertFalse(REPORT.same_value({'ok':False},{'ok':0}))

    def test_memory_masks_and_live_counts(self):
        self.assertTrue(REPORT.same_value({'ok':0,'bufs':['a1'],'live':0},{'ok':0,'bufs':['?1'],'live':0}))
        self.assertFalse(REPORT.same_value({'ok':0,'bufs':['a1'],'live':1},{'ok':0,'bufs':['?1'],'live':0}))

    def test_truncated_rows_fail(self):
        self.seed({'ok':1},{'ok':1})
        (self.root/'tests/diff/out/zig/basic/foo.jsonl').write_text('')
        with self.assertRaisesRegex(REPORT.Invalid,'row count'):self.compare()

    def test_size_bounds_and_unterminated_lines(self):
        path=self.root/'large'
        path.write_text('x'*33+'\n')
        with patch.object(REPORT,'MAX_LINE',32):
            with self.assertRaises(REPORT.Invalid):list(REPORT.lines(path))
        path.write_text('{}')
        with self.assertRaises(REPORT.Invalid):list(REPORT.lines(path))

    def test_invalid_pins_and_schedule_metadata(self):
        pin=self.root/'pins';pin.write_text('foo 2-1\n')
        with self.assertRaises(REPORT.Invalid):REPORT.pins(pin)
        meta={'schema':1,'kind':'value','legacy':{'ok':1},'search':self.search('bounded',False)}
        with self.assertRaises(REPORT.Invalid):REPORT.observation(json.dumps(meta),{'ok':1},'model')

    def test_cli_input_failure_and_setup_are_never_eligible(self):
        self.seed({'ok':1},{'ok':1})
        meta=self.root/'tests/diff/out/lean/basic/foo.jsonl.outcomes'
        meta.write_text('{"schema":1,"kind":"input_failure","legacy_line":"{}"}\n')
        command=[sys.executable,str(ROOT/'scripts/diff-report.py'),'failure','--root',str(self.root),'--examples','basic','--summary',str(self.summary),'--phase','run_model']
        result=subprocess.run(command,capture_output=True,text=True,timeout=3)
        self.assertEqual(result.returncode,0,result.stderr)
        data=json.loads(self.summary.read_text())
        self.assertEqual(data['failure'],'input_failure')
        self.assertFalse(data['complete'])
        result=subprocess.run([sys.executable,str(ROOT/'scripts/diff-report.py'),'eligible','--summary',str(self.summary)],capture_output=True,text=True,timeout=3)
        self.assertEqual(result.returncode,2)

    def test_init_removes_stale_sidecars(self):
        self.seed({'ok':1},{'ok':1})
        result=subprocess.run([sys.executable,str(ROOT/'scripts/diff-report.py'),'init','--root',str(self.root),'--examples','basic','--summary',str(self.summary)],capture_output=True,text=True,timeout=3)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertFalse((self.root/'tests/diff/out/lean/basic/foo.jsonl.outcomes').exists())

    def test_unmapped_reported_native_panic_is_comparable_mismatch(self):
        self.seed({'fail':'noreturnReturned'},{'fail':'Zig.Error.panic'},K.NATIVE_PANIC,K.MODEL_PANIC)
        code,data=self.compare()
        self.assertEqual(code,1)
        self.assertEqual(data['counts'],{'mismatch':1})
        self.assertEqual(data['mutation_eligible'],1)

    def test_native_harness_allocation_failure_cannot_be_mutation_detection(self):
        self.seed({'fail':'harnessOutOfMemory'},{'fail':'Zig.Error.panic'},K.NATIVE_HARNESS_FAILURE,K.MODEL_PANIC)
        code,data=self.compare()
        self.assertEqual(code,1)
        self.assertEqual(data['counts'],{'native_harness_failure':1})
        self.assertEqual(data['mutation_eligible'],0)

    def test_init_discards_previous_case_evidence(self):
        cases=Path(str(self.summary)+'.jsonl');cases.write_text('stale\n')
        result=subprocess.run([sys.executable,str(ROOT/'scripts/diff-report.py'),'init','--root',str(self.root),'--examples','basic','--summary',str(self.summary)],capture_output=True,text=True,timeout=3)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertFalse(cases.exists())

    def test_shared_default_selection_filters_arch_and_version(self):
        for name in ('asm','sync','threadsync'):(self.root/'examples'/name).mkdir()
        (self.root/'examples/sync/zig-versions').write_text('0.16.0\n')
        (self.root/'examples/threadsync/zig-versions').write_text('0.15.2\n')
        command=['bash','-c','source "$1"; air2lean_default_examples "$2" "$3" "$4"','bash',str(ROOT/'scripts/example-selection.sh'),str(self.root)]
        arm=subprocess.run(command+['0.16.0','arm64'],capture_output=True,text=True,timeout=3)
        self.assertEqual(arm.returncode,0,arm.stderr)
        self.assertEqual(arm.stdout.split(),['basic','sync'])
        x86=subprocess.run(command+['0.15.2','x86_64'],capture_output=True,text=True,timeout=3)
        self.assertEqual(x86.stdout.split(),['asm','basic','threadsync'])

    def test_explicit_selection_does_not_silently_exclude_requested_examples(self):
        text=(ROOT/'scripts/mutate.sh').read_text()
        start=text.index('if [ -n "${AIR2LEAN_EXAMPLES:-}" ]; then')
        end=text.index('\nfi',start)+3
        script=self.root/'selection.sh'
        script.write_text('set -euo pipefail\nAIR2LEAN_EXAMPLES="asm sync"\n'+text[start:end]+'\nprintf "%s" "$examples"\n')
        result=subprocess.run(['bash',str(script)],capture_output=True,text=True,timeout=3)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertEqual(result.stdout,'asm sync')

    def _run_comparison_tail(self, optional_transform=None):
        scripts=self.root/'scripts';scripts.mkdir(exist_ok=True)
        for name in ('diff-report.py','panic-policy.tsv'):
            (scripts/name).write_text((ROOT/'scripts'/name).read_text())
        source=(ROOT/'scripts/diff.sh').read_text()
        start=source.index('functions_of()')
        functions=source[start:source.index('\n}',start)+2]
        tail=source[source.index('# Classifies one JSONL'):]
        if optional_transform is not None:tail=optional_transform(tail)
        runner=self.root/'compare.sh'
        runner.write_text('set -euo pipefail\ncd "$(dirname "$0")"\nrepo_root=$PWD\nexamples=basic\nbuild_dir=$PWD\nzig_version=0.16.0\nAIR2LEAN_DIFF_REPORT=$PWD/summary.json\n'+functions+'\n'+tail)
        return subprocess.run(['bash',str(runner)],capture_output=True,text=True,timeout=3)

    def test_actual_comparison_tail_keeps_total_and_reports_native_setup_failure(self):
        self.seed({'fail':'unknown'},{'fail':'Zig.Error.illegal'},K.NATIVE_HARNESS_FAILURE,K.ILLEGAL)
        (self.root/'tests/diff/basic/unspecified.txt').write_text('foo 1\n')
        result=self._run_comparison_tail()
        self.assertEqual(result.returncode,1,result.stderr)
        self.assertIn('TOTAL: ok=0 fail_match=0 unspecified=1 capped=0 mismatch=0',result.stdout,result.stderr)
        report=json.loads(self.summary.read_text())
        self.assertEqual(report['counts'],{'native_harness_failure':1})
        self.assertEqual(report['mutation_eligible'],0)

    def test_actual_successful_comparison_skips_panic_policy_lookup(self):
        self.seed({'ok':1},{'ok':1})
        def reject_lookup(tail):
            anchor='# The pin of function'
            return tail.replace(anchor,'expected_ctor_for_zig_kind() { echo "UNEXPECTED_PANIC_LOOKUP" >&2; return 99; }\n\n'+anchor,1)
        result=self._run_comparison_tail(reject_lookup)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertNotIn('UNEXPECTED_PANIC_LOOKUP',result.stderr)
        self.assertIn('TOTAL: ok=1 fail_match=0 unspecified=0 capped=0 mismatch=0',result.stdout)
        self.assertEqual(json.loads(self.summary.read_text())['counts'],{'value_match':1})

    def mutation_mock(self, native, model, nk, mk, search=None, host=False, legacy=False, total=True, retain=False):
        self.seed(native,model,nk,mk,search)
        scripts=self.root/'scripts';scripts.mkdir(exist_ok=True)
        (scripts/'diff-report.py').write_text((ROOT/'scripts/diff-report.py').read_text())
        if host:(self.root/'tests/diff/basic/host.txt').write_text('foo\n')
        original=(ROOT/'ZigLean/Conc.lean').read_bytes()
        conc=self.root/'ZigLean/Conc.lean';conc.parent.mkdir(exist_ok=True);conc.write_bytes(original)
        backup=self.root/'Conc.before.lean';backup.write_bytes(original)
        diff='#!/usr/bin/env bash\nset -euo pipefail\n'
        diff+='if grep -Fqx \'import ZigLean.Conc.WeakCas\' ZigLean/Conc.lean; then echo \'proof isolation missing\' >&2; exit 77; fi\n'
        if legacy:
            diff+='echo "TOTAL: mismatch=1"\nexit 1\n'
        else:
            diff+='status=0\npython3 scripts/diff-report.py compare --root "$PWD" --examples basic --version 0.16.0 --host '+('Darwin-arm64' if host else 'Linux-x86_64')+' --summary "$AIR2LEAN_DIFF_REPORT" || status=$?\n'
            if total:
                diff+='python3 - "$AIR2LEAN_DIFF_REPORT" <<\'PYMOCK\'\nimport json,sys\ns=json.load(open(sys.argv[1]));l=s.get("legacy_counts",{});print("TOTAL: mismatch="+str(l.get("mismatch",0)))\nfor p in s.get("pin_violations",[]):print(p["counter"].upper()+" COUNT synthetic")\nPYMOCK\n'
            diff+='exit "$status"\n'
        (scripts/'diff.sh').write_text(diff)
        source=(ROOT/'scripts/mutate.sh').read_text();start=source.index('run_and_report() {');end=source.index('\nall_detected=',start)
        runner=self.root/'mutant.sh'
        runner.write_text(('AIR2LEAN_MUTATION_REPORT_DIR='+str(self.root/'retained')+'\n' if retain else '')+'set -euo pipefail\ncd "$(dirname "$0")"\nmutations_run=0\nconc_lean=\"$PWD/ZigLean/Conc.lean\"\nconc_backup=\"$PWD/Conc.before.lean\"\n'+source[start:end]+'\nrun_and_report "mutation (x)" basic\necho "RESULT=$detected"\n')
        result=subprocess.run(['bash',str(runner)],capture_output=True,text=True,timeout=3)
        self.assertEqual(conc.read_bytes(),original,'WeakCas proof import was not restored')
        return result

    def test_mutation_wrapper_can_retain_bounded_typed_evidence(self):
        result=self.mutation_mock({'ok':2},{'ok':1},K.VALUE,K.VALUE,retain=True)
        self.assertEqual(result.returncode,0,result.stderr)
        reports=list((self.root/'retained').glob('case.*/summary.json'))
        self.assertEqual(len(reports),1)
        self.assertEqual(json.loads(reports[0].read_text())['mutation_eligible'],1)
        self.assertTrue(Path(str(reports[0])+'.jsonl').is_file())

    def test_mutation_wrapper_detects_genuine_mismatch(self):
        result=self.mutation_mock({'ok':2},{'ok':1},K.VALUE,K.VALUE)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertIn('RESULT=1',result.stdout)

    def test_mutation_wrapper_rejects_bounded_and_cap_pin_evidence(self):
        result=self.mutation_mock({'ok':1},{'diverge':True},K.VALUE,K.BOUNDED_NO_RESULT)
        self.assertIn('RESULT=0',result.stdout)
        result=self.mutation_mock({'ok':1},{'fail':'Zig.Error.capped'},K.VALUE,K.SEARCH_CAP,self.search())
        self.assertIn('RESULT=0',result.stdout)

    def test_mutation_wrapper_host_exclusion_is_not_detection(self):
        result=self.mutation_mock({'ok':1},{'ok':2},K.VALUE,K.VALUE,host=True)
        self.assertIn('RESULT=0',result.stdout)

    def test_mutation_wrapper_aborts_on_setup_and_missing_total(self):
        result=self.mutation_mock({'fail':'unknown'},{'ok':1},K.NATIVE_HARNESS_FAILURE,K.VALUE)
        self.assertEqual(result.returncode,1)
        self.assertIn('typed differential setup/accounting failed',result.stderr)
        result=self.mutation_mock({'ok':1},{'ok':2},K.VALUE,K.VALUE,total=False)
        self.assertEqual(result.returncode,1)
        self.assertIn('produced no TOTAL',result.stderr)

    def test_mutation_wrapper_keeps_legacy_mock_compatibility(self):
        result=self.mutation_mock({'ok':1},{'ok':2},K.VALUE,K.VALUE,legacy=True)
        self.assertIn('RESULT=1',result.stdout)

if __name__=='__main__':unittest.main()
