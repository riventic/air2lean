#!/usr/bin/env python3
"""Bounded model schedule enumeration and source-bound deterministic replay."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import selectors
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent


def load_report():
    """Reuse an already-loaded diff-report module so both share one Invalid class."""
    loaded = sys.modules.get('diff_report')
    if loaded is not None: return loaded
    spec = importlib.util.spec_from_file_location('diff_report', ROOT/'scripts/diff-report.py')
    module = importlib.util.module_from_spec(spec)
    sys.modules['diff_report'] = module
    try: spec.loader.exec_module(module)
    except BaseException:
        del sys.modules['diff_report']; raise
    return module


REPORT = load_report()
LIMIT = 64 * 1024 * 1024


def nat(value, limit, name):
    if type(value) is not int or not 0 <= value <= limit:
        raise REPORT.Invalid(f'invalid {name}')
    return value


def read_bytes(path):
    with Path(path).open('rb') as stream:
        raw = stream.read(LIMIT + 1)
    if len(raw) > LIMIT: raise REPORT.Invalid('receipt exceeds 64 MiB')
    return raw


def read_json(path):
    return REPORT.decode(read_bytes(path).decode('utf-8'))


def row(path, index):
    nat(index, REPORT.MAX_CASES, 'input index')
    if index == 0: raise REPORT.Invalid('input indices start at 1')
    for i, raw in enumerate(REPORT.lines(path), 1):
        if i == index: return raw
    raise REPORT.Invalid(f'missing row {index} in {path}')


def current_input(root, example, function, index):
    if not REPORT.IDENT.fullmatch(example) or not REPORT.IDENT.fullmatch(function):
        raise REPORT.Invalid('invalid example/function')
    raw = row(root/'tests/diff'/example/'inputs'/f'{function}.jsonl', index)
    return REPORT.decode(raw), hashlib.sha256(raw.encode()).hexdigest()


def bound_context(receipt, sources):
    if type(receipt) is not dict or type(receipt.get('schema')) is not int or receipt.get('schema') != 1 or receipt.get('qualified') is not False:
        raise REPORT.Invalid('unsupported receipt')
    if not REPORT.json_equal(receipt.get('runner_runtime_sources'), sources):
        raise REPORT.Invalid('stale runner/runtime source fingerprints')


def load_receipt(root, path, sources, examples=None):
    """Read and validate a receipt against current sources and input; return (receipt, raw bytes).
    `examples`, when given, restricts the receipt to selected examples before any input is read."""
    raw = read_bytes(path)
    receipt = REPORT.decode(raw.decode('utf-8')); bound_context(receipt, sources)
    request = receipt.get('request')
    if type(request) is not dict: raise REPORT.Invalid('invalid receipt request')
    if examples is not None and request.get('example') not in examples: raise REPORT.Invalid('schedule receipt outside selected examples')
    validate_response(receipt.get('result'), request)
    raw_input, digest = current_input(root, request.get('example'), request.get('function'), receipt.get('input_index'))
    if digest != receipt.get('input_sha256') or not REPORT.json_equal(raw_input, request.get('input')): raise REPORT.Invalid('stale input')
    return receipt, raw


def invoke(binary, request, timeout):
    """Drain a single product process under explicit time and combined-output byte caps."""
    encoded = json.dumps(request, separators=(',', ':'), ensure_ascii=False).encode()
    if len(encoded) > REPORT.MAX_LINE: raise REPORT.Invalid('request exceeds 8 MiB')
    with tempfile.TemporaryDirectory(prefix='air2lean-schedule-') as temp:
        path = Path(temp)/'request.json'
        path.write_bytes(encoded)
        process = subprocess.Popen([str(binary), str(path)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = bytearray()
        try:
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout, selectors.EVENT_READ)
                deadline = time.monotonic() + timeout
                while selector.get_map():
                    remaining = deadline - time.monotonic()
                    if remaining <= 0: raise REPORT.Invalid('schedule command timed out')
                    for key, _ in selector.select(min(remaining, 0.1)):
                        chunk = key.fileobj.read1(65536)
                        if not chunk:
                            selector.unregister(key.fileobj)
                        else:
                            if len(output) + len(chunk) > LIMIT: raise REPORT.Invalid('response exceeds 64 MiB')
                            output.extend(chunk)
                try: status = process.wait(timeout=max(0.001, deadline-time.monotonic()))
                except subprocess.TimeoutExpired: raise REPORT.Invalid('schedule command timed out')
        finally:
            if process.poll() is None: process.kill()
            process.wait()
            process.stdout.close()
    response = REPORT.decode(output.decode('utf-8'))
    if status != 0:
        error=response.get('error','execution failed') if type(response) is dict else 'invalid error response'
        raise REPORT.Invalid(f'schedule rejected: {error}')
    return response


def validate_response(response, request):
    if type(response) is not dict or type(response.get('schema')) is not int or response.get('schema') != 1 or response.get('qualified') is not False:
        raise REPORT.Invalid('invalid schedule response')
    nat(request.get('fuel'),100000,'fuel'); nat(request.get('node_cap'),2000,'node cap'); nat(request.get('prefix_cap'),4096,'prefix cap')
    if request.get('mode') not in ('enumerate','replay'): raise REPORT.Invalid('invalid request mode')
    for key in ('mode', 'fuel', 'node_cap', 'prefix_cap'):
        if not REPORT.json_equal(response.get(key), request[key]): raise REPORT.Invalid(f'response {key} differs')
    executions = response.get('executions')
    if type(executions) is not list or len(executions) > request['node_cap']:
        raise REPORT.Invalid('invalid execution count')
    nat(response.get('runs'), 2000, 'runs')
    if response['runs'] != len(executions): raise REPORT.Invalid('run count differs')
    for flag in ('truncated', 'node_cap_reached', 'prefix_cap_reached', 'exploration_complete', 'saw_no_result'):
        if type(response.get(flag)) is not bool: raise REPORT.Invalid(f'invalid {flag}')
    if response['truncated'] != (response['node_cap_reached'] or response['prefix_cap_reached']):
        raise REPORT.Invalid('inconsistent cap flags')
    for entry in executions:
        if type(entry) is not dict: raise REPORT.Invalid('invalid execution')
        prefix, options = entry.get('prefix'), entry.get('options')
        if type(prefix) is not list or type(options) is not list or len(prefix) != len(options) or len(prefix) > request['prefix_cap']:
            raise REPORT.Invalid('invalid execution trace')
        for choice, count in zip(prefix, options):
            nat(choice, 2**64-1, 'choice'); nat(count, 2**64-1, 'option count')
            if choice >= max(1, count): raise REPORT.Invalid('choice outside option range')
        count = nat(entry.get('choice_count'), 2 * request['fuel'], 'choice count')
        if type(entry.get('trace_complete')) is not bool or count < len(options) or entry['trace_complete'] != (count == len(options)):
            raise REPORT.Invalid('invalid trace completeness')
        observation = entry.get('observation')
        if type(observation) is not dict or type(observation.get('legacy_line')) is not str:
            raise REPORT.Invalid('invalid typed observation')
        REPORT.observation(json.dumps(observation), REPORT.decode(observation['legacy_line']), 'model')
    expected_outcomes=[]
    for entry in executions:
        if entry['observation'] not in expected_outcomes: expected_outcomes.append(entry['observation'])
    if not REPORT.json_equal(response.get('outcomes'),expected_outcomes): raise REPORT.Invalid('outcome set differs')
    if response['saw_no_result'] != any(e['observation']['kind']=='bounded_no_result' for e in executions): raise REPORT.Invalid('no-result history differs')
    if any(not e['trace_complete'] for e in executions) != response['prefix_cap_reached']: raise REPORT.Invalid('prefix truncation differs')
    if request['mode'] == 'replay':
        if len(executions) != 1 or not executions[0]['trace_complete'] or executions[0]['prefix'] != request['prefix'] or response['truncated']:
            raise REPORT.Invalid('replay trace differs')
        expected = request.get('expected', {})
        entry = executions[0]
        actual = dict(line=entry['observation']['legacy_line'], kind=entry['observation']['kind'], options=entry['options'])
        for key, value in expected.items():
            if not REPORT.json_equal(actual[key], value): raise REPORT.Invalid(f'replay {key} differs')
    elif response['exploration_complete'] != (not response['truncated']):
        raise REPORT.Invalid('inconsistent exploration flag')


def prepare(args, root):
    sources = REPORT.source_hashes(root)
    if args.command == 'enumerate':
        raw_input, digest = current_input(root, args.example, args.function, args.input_index)
        request = dict(schema=1, mode='enumerate', example=args.example, function=args.function, input=raw_input,
                       fuel=nat(args.fuel,100000,'fuel'), node_cap=nat(args.node_cap,2000,'node cap'), prefix_cap=nat(args.prefix_cap,4096,'prefix cap'))
        return request, args.input_index, digest, sources
    if args.receipt:
        receipt, _ = load_receipt(root, args.receipt, sources)
        original = receipt['request']
        if original.get('mode') != 'enumerate': raise REPORT.Invalid('not an enumeration receipt')
        index = receipt['input_index']
        digest = receipt['input_sha256']
        i = nat(args.execution_index,1999,'execution index')
        executions = receipt['result']['executions']
        if i >= len(executions): raise REPORT.Invalid('missing execution')
        entry = executions[i]
        if not entry['trace_complete']: raise REPORT.Invalid('cannot replay a truncated trace')
        request = dict(original, mode='replay', node_cap=1, prefix=entry['prefix'], expected=dict(
            line=entry['observation']['legacy_line'],kind=entry['observation']['kind'],options=entry['options']))
    else:
        summary = read_json(args.summary); bound_context(summary, sources)
        if summary.get('complete') is not True: raise REPORT.Invalid('incomplete differential summary')
        index = args.input_index
        raw_input, digest = current_input(root, args.example, args.function, index)
        examples=root/'examples'
        available={p.name for p in examples.iterdir() if p.is_dir()} if examples.is_dir() else set()
        skipped_limit=nat(summary.get('skipped_examples'),len(available),'skipped examples')
        expected_cases=nat(summary.get('case_count'),REPORT.MAX_CASES,'case count')
        matches=[];skipped=set();cases=0
        for line in REPORT.lines(Path(str(args.summary)+'.jsonl'),max_records=REPORT.MAX_CASES+skipped_limit,max_bytes=REPORT.MAX_REPORT):
            case=REPORT.decode(line)
            if type(case) is not dict: raise REPORT.Invalid('invalid differential case')
            if case.get('status') == 'skipped':
                name=case.get('example')
                if name not in available or name in skipped: raise REPORT.Invalid('invalid or duplicate skipped example')
                skipped.add(name)
                if len(skipped)>skipped_limit: raise REPORT.Invalid('skipped example count exceeded')
                continue
            cases+=1
            if cases>REPORT.MAX_CASES: raise REPORT.Invalid('actual case bound exceeded')
            if case.get('example') == args.example and case.get('function') == args.function and case.get('input_index') == index:
                matches.append(case)
                if len(matches)>1: raise REPORT.Invalid('ambiguous differential case')
        if cases!=expected_cases or len(skipped)!=skipped_limit: raise REPORT.Invalid('summary/sidecar counts differ')
        if len(matches) != 1: raise REPORT.Invalid('missing or ambiguous differential case')
        case = matches[0]; search = case.get('schedule')
        if type(search) is not dict or search.get('status') != 'witness': raise REPORT.Invalid('case has no observed matching witness')
        options, sparse = search.get('options'), search.get('prefix')
        if type(options) is not list or type(sparse) is not list or len(options) > 4096 or len(sparse) > len(options): raise REPORT.Invalid('invalid witness trace')
        model = row(root/'tests/diff/out/lean'/args.example/f'{args.function}.jsonl', index)
        if digest != case.get('input_sha256') or hashlib.sha256(model.encode()).hexdigest() != case.get('model_sha256'): raise REPORT.Invalid('stale input/model line')
        request = dict(schema=1,mode='replay',example=args.example,function=args.function,input=raw_input,
            fuel=nat(search.get('fuel'),100000,'fuel'),node_cap=1,prefix_cap=4096,
            prefix=sparse+[0]*(len(options)-len(sparse)),expected=dict(line=model.strip(),kind=case['model_kind'],options=options))
    return request, index, digest, sources


def parser():
    p = argparse.ArgumentParser(description=__doc__)
    subs = p.add_subparsers(dest='command',required=True)
    enum = subs.add_parser('enumerate')
    enum.add_argument('--fuel',type=int,default=100000)
    enum.add_argument('--node-cap',type=int,default=128)
    enum.add_argument('--prefix-cap',type=int,default=4096)
    replay = subs.add_parser('replay')
    group = replay.add_mutually_exclusive_group(required=True)
    group.add_argument('--receipt',type=Path); group.add_argument('--summary',type=Path)
    replay.add_argument('--execution-index',type=int,default=0)
    for sub in (enum,replay):
        sub.add_argument('--example');sub.add_argument('--function');sub.add_argument('--input-index',type=int,default=1)
        sub.add_argument('--binary',type=Path,default=ROOT/'tests/diff/.lake/build/bin/schedules')
        sub.add_argument('--timeout',type=int,default=60);sub.add_argument('--output',type=Path,required=True)
    return p


def execute(args, root=ROOT):
    nat(args.timeout,900,'timeout')
    if args.timeout == 0: raise REPORT.Invalid('timeout must be positive')
    if args.command == 'enumerate' or args.summary:
        if not args.example or not args.function: raise REPORT.Invalid('--example and --function are required')
    request,index,digest,sources = prepare(args,root)
    protected={root/path for path in sources}
    protected.add(root/'tests/diff'/request['example']/'inputs'/f"{request['function']}.jsonl")
    protected.add(root/'tests/diff/out/lean'/request['example']/f"{request['function']}.jsonl")
    protected.add(args.binary)
    if getattr(args,'summary',None): protected.add(Path(str(args.summary)+'.jsonl'))
    protected.update(p for p in (getattr(args,'receipt',None),getattr(args,'summary',None)) if p)
    if args.output.resolve() in {p.resolve() for p in protected}: raise REPORT.Invalid('output would overwrite an input/source')
    response = invoke(args.binary.resolve(),request,args.timeout)
    validate_response(response,request)
    if not REPORT.json_equal(sources,REPORT.source_hashes(root)): raise REPORT.Invalid('sources changed during execution')
    if current_input(root,request['example'],request['function'],index)[1] != digest: raise REPORT.Invalid('input changed during execution')
    REPORT.atomic_json(args.output,dict(schema=1,qualified=False,request=request,input_index=index,input_sha256=digest,
                                      runner_runtime_sources=sources,result=response))


def main():
    args=parser().parse_args()
    try: execute(args)
    except (REPORT.Invalid,OSError,UnicodeError,KeyError,TypeError,ValueError) as error:
        print(f'schedules: {error}',file=__import__('sys').stderr)
        return 1
    return 0

if __name__ == '__main__': raise SystemExit(main())
