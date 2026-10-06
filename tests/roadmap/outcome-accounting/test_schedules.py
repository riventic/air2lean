#!/usr/bin/env python3
"""Portable CLI oracles; the compiled model process is mocked."""
import copy
import hashlib
import importlib.util
import json
import io
from types import SimpleNamespace
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[3]
SPEC=importlib.util.spec_from_file_location('schedule_cli',ROOT/'scripts/schedules.py')
CLI=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(CLI)

class Schedules(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.output=self.root/'receipt.json'
        p=self.root/'tests/diff/atomics/inputs/mpRelAcq.jsonl';p.parent.mkdir(parents=True);p.write_text('[]\n')
        p=self.root/'ZigLean/Basic.lean';p.parent.mkdir();p.write_text('-- runtime\n')

    def args(self,*extra):
        return CLI.parser().parse_args([*extra,'--output',str(self.output)])

    def enum_args(self,*extra):
        return self.args('enumerate','--example','atomics','--function','mpRelAcq',*extra)

    def response(self,request):
        observation=dict(schema=1,kind='value',legacy_line='{"ok":1}')
        prefix=request.get('prefix',[0,0]);options=[2,1]
        return dict(schema=1,qualified=False,mode=request['mode'],fuel=request['fuel'],node_cap=request['node_cap'],prefix_cap=request['prefix_cap'],
                    runs=1,truncated=False,node_cap_reached=False,prefix_cap_reached=False,exploration_complete=request['mode']=='enumerate',saw_no_result=False,
                    executions=[dict(prefix=prefix,options=options,choice_count=2,trace_complete=True,observation=observation)],outcomes=[observation])

    def run_enum(self):
        with patch.object(CLI,'invoke',side_effect=lambda _,r,__:self.response(r)) as invoke:
            CLI.execute(self.enum_args(),self.root)
        return json.loads(self.output.read_text()),invoke

    def test_enum_receipt_records_context_and_limits_without_proof(self):
        data,invoke=self.run_enum();self.assertEqual(invoke.call_count,1)
        self.assertEqual(data['request']['node_cap'],128);self.assertFalse(data['qualified'])
        self.assertEqual(data['input_sha256'],hashlib.sha256(b'[]\n').hexdigest())
        self.assertEqual(data['runner_runtime_sources'],CLI.REPORT.source_hashes(self.root))

    def test_replay_uses_complete_recorded_trace_and_exact_expectations(self):
        data,_=self.run_enum();self.output=self.root/'replayed.json'
        with patch.object(CLI,'invoke',side_effect=lambda _,r,__:self.response(r)) as invoke:
            CLI.execute(self.args('replay','--receipt',str(self.root/'receipt.json')),self.root)
        request=invoke.call_args.args[1]
        self.assertEqual(request['prefix'],[0,0]);self.assertEqual(request['expected'],dict(line='{"ok":1}',kind='value',options=[2,1]))
        self.assertEqual(json.loads(self.output.read_text())['result']['mode'],'replay')

    def test_stale_input_or_model_source_rejects_before_process(self):
        self.run_enum()
        for path,value in [('tests/diff/atomics/inputs/mpRelAcq.jsonl','[1]\n'),('ZigLean/Basic.lean','-- changed\n')]:
            file=self.root/path;old=file.read_text();file.write_text(value)
            with patch.object(CLI,'invoke') as invoke,self.assertRaises(CLI.REPORT.Invalid):
                CLI.execute(self.args('replay','--receipt',str(self.output)),self.root)
            invoke.assert_not_called();file.write_text(old)

    def test_refuses_incomplete_trace_and_noninteger_schema(self):
        data,_=self.run_enum()
        for mutate in (lambda d:d.update(schema=True),lambda d:d['result']['executions'][0].update(choice_count=3,trace_complete=False)):
            changed=copy.deepcopy(data);mutate(changed);self.output.write_text(json.dumps(changed))
            with patch.object(CLI,'invoke') as invoke,self.assertRaises(CLI.REPORT.Invalid):
                CLI.execute(self.args('replay','--receipt',str(self.output)),self.root)
            invoke.assert_not_called()

    def test_current_sources_and_input_checked_after_process(self):
        def changed(_,request,__):
            (self.root/'ZigLean/Basic.lean').write_text('-- changed\n');return self.response(request)
        with patch.object(CLI,'invoke',side_effect=changed),self.assertRaises(CLI.REPORT.Invalid):CLI.execute(self.enum_args(),self.root)
        self.assertFalse(self.output.exists())

    def test_output_cannot_overwrite_input(self):
        self.output=self.root/'tests/diff/atomics/inputs/mpRelAcq.jsonl'
        with patch.object(CLI,'invoke') as invoke,self.assertRaises(CLI.REPORT.Invalid):CLI.execute(self.enum_args(),self.root)
        invoke.assert_not_called();self.assertEqual(self.output.read_text(),'[]\n')

    def test_bounds_and_bad_response_do_not_publish_receipt(self):
        for args in (self.enum_args('--fuel','100001'),self.enum_args('--node-cap','2001'),self.enum_args('--prefix-cap','4097'),self.enum_args('--timeout','0')):
            with patch.object(CLI,'invoke') as invoke,self.assertRaises(CLI.REPORT.Invalid):CLI.execute(args,self.root)
            invoke.assert_not_called()
        for field,value in [('qualified',True),('runs',True),('truncated',True),('outcomes',[]),('saw_no_result',True)]:
            def bad(_,request,__):r=self.response(request);r[field]=value;return r
            with patch.object(CLI,'invoke',side_effect=bad),self.assertRaises(CLI.REPORT.Invalid):CLI.execute(self.enum_args(),self.root)
        self.assertFalse(self.output.exists())

    def test_observed_witness_pads_only_recorded_default_choices(self):
        summary=self.root/'summary.json';summary.write_text(json.dumps(dict(schema=1,qualified=False,complete=True,case_count=1,skipped_examples=0,runner_runtime_sources=CLI.REPORT.source_hashes(self.root))))
        model=self.root/'tests/diff/out/lean/atomics/mpRelAcq.jsonl';model.parent.mkdir(parents=True);model.write_text('{"ok":1}\n')
        case=dict(example='atomics',function='mpRelAcq',input_index=1,input_sha256=hashlib.sha256(b'[]\n').hexdigest(),model_sha256=hashlib.sha256(model.read_bytes()).hexdigest(),model_kind='value',schedule=dict(status='witness',prefix=[1],options=[2,1],fuel=8))
        Path(str(summary)+'.jsonl').write_text(json.dumps(case)+'\n')
        args=self.args('replay','--summary',str(summary),'--example','atomics','--function','mpRelAcq')
        with patch.object(CLI,'invoke',side_effect=lambda _,r,__:self.response(r)) as invoke:CLI.execute(args,self.root)
        self.assertEqual(invoke.call_args.args[1]['prefix'],[1,0])
        evidence=Path(str(summary)+'.jsonl');before=evidence.read_bytes()
        protected_args=copy.copy(args);protected_args.output=evidence
        with patch.object(CLI,'invoke') as child,self.assertRaises(CLI.REPORT.Invalid):CLI.execute(protected_args,self.root)
        child.assert_not_called();self.assertEqual(evidence.read_bytes(),before)
        case['schedule']['status']='capped';Path(str(summary)+'.jsonl').write_text(json.dumps(case)+'\n')
        with patch.object(CLI,'invoke') as invoke,self.assertRaises(CLI.REPORT.Invalid):CLI.execute(args,self.root)
        invoke.assert_not_called()

    def test_sidecar_skip_rows_do_not_consume_actual_case_budget(self):
        (self.root/'examples/asm').mkdir(parents=True)
        summary=self.root/'summary.json'
        summary.write_text(json.dumps(dict(schema=1,qualified=False,complete=True,case_count=2,skipped_examples=1,runner_runtime_sources=CLI.REPORT.source_hashes(self.root))))
        model=self.root/'tests/diff/out/lean/atomics/mpRelAcq.jsonl';model.parent.mkdir(parents=True);model.write_text('{"ok":1}\n')
        witness=dict(example='atomics',function='mpRelAcq',input_index=1,input_sha256=hashlib.sha256(b'[]\n').hexdigest(),model_sha256=hashlib.sha256(model.read_bytes()).hexdigest(),model_kind='value',schedule=dict(status='witness',prefix=[1],options=[2,1],fuel=8))
        skip=dict(status='skipped',example='asm')
        other=dict(example='atomics',function='sbRelaxed',input_index=1)
        sidecar=Path(str(summary)+'.jsonl')
        args=self.args('replay','--summary',str(summary),'--example','atomics','--function','mpRelAcq')
        def write(rows):sidecar.write_text(''.join(json.dumps(r)+'\n' for r in rows))
        write([skip,witness,other])
        with patch.object(CLI.REPORT,'MAX_CASES',2),patch.object(CLI,'invoke',side_effect=lambda _,r,__:self.response(r)) as child:
            CLI.execute(args,self.root)
        self.assertEqual(child.call_count,1)
        # The reader must continue past an early witness: duplicates are still rejected.
        write([skip,witness,witness])
        with patch.object(CLI.REPORT,'MAX_CASES',2),patch.object(CLI,'invoke') as child,self.assertRaisesRegex(CLI.REPORT.Invalid,'ambiguous'):
            CLI.execute(args,self.root)
        child.assert_not_called()
        # Input streams keep their original case cap; skip allowances are report-only.
        with patch.object(CLI.REPORT,'MAX_CASES',2),self.assertRaises(CLI.REPORT.Invalid):list(CLI.REPORT.lines(sidecar))
        write([skip,witness,other])
        with patch.object(CLI.REPORT,'MAX_REPORT',10),patch.object(CLI,'invoke') as child,self.assertRaises(CLI.REPORT.Invalid):CLI.execute(args,self.root)
        child.assert_not_called()

    def test_two_oracle_choices_per_turn_keep_large_truncated_history(self):
        request,_,_,_=CLI.prepare(self.enum_args('--fuel','100000'),self.root)
        response=self.response(request)
        response.update(truncated=True,prefix_cap_reached=True,exploration_complete=False)
        entry=response['executions'][0];entry.update(choice_count=200000,trace_complete=False)
        CLI.validate_response(response,request)
        entry['choice_count']=200001
        with self.assertRaises(CLI.REPORT.Invalid):CLI.validate_response(response,request)

    def test_process_output_cap_kills_and_reaps_before_return(self):
        class Selector:
            def __enter__(self):return self
            def __exit__(self,*_):pass
            def register(self,stream,_):self.stream=stream;self.active=True
            def unregister(self,_):self.active=False
            def get_map(self):return {1:True} if self.active else {}
            def select(self,_):return [(SimpleNamespace(fileobj=self.stream),0)]
        class Process:
            def __init__(self,data,status=0):self.stdout=io.BytesIO(data);self.status=status;self.killed=False;self.waits=0
            def poll(self):return None if not self.killed else -9
            def kill(self):self.killed=True
            def wait(self,**_):self.waits+=1;return -9 if self.killed else self.status
        for payload,status,error in [(b'x'*101,0,'exceeds'),(b'{"error":"bad input"}',1,'bad input'),(b'[]',1,'invalid error')]:
            process=Process(payload,status)
            with patch.object(CLI.subprocess,'Popen',return_value=process),patch.object(CLI.selectors,'DefaultSelector',Selector),patch.object(CLI,'LIMIT',100),self.assertRaisesRegex(CLI.REPORT.Invalid,error):
                CLI.invoke(self.root/'fake',{},1)
            self.assertTrue(process.killed);self.assertGreaterEqual(process.waits,1);self.assertTrue(process.stdout.closed)

if __name__=='__main__':unittest.main()
