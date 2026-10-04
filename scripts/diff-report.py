#!/usr/bin/env python3
"""Typed differential accounting. Legacy counters remain a compatibility projection."""
import argparse
from collections import Counter
from enum import Enum
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile

SCHEMA = 1
MAX_LINE = 8 * 1024 * 1024
MAX_CASES = 100000
MAX_REPORT = 128 * 1024 * 1024

class Failure(str, Enum):
    SETUP = 'setup_failure'
    INPUT = 'input_failure'
    UNSUPPORTED = 'unsupported_input'

class Kind(str, Enum):
    VALUE = 'value'
    ERROR_RETURN = 'error_return'
    MODEL_PANIC = 'model_panic'
    NATIVE_PANIC = 'native_panic'
    ILLEGAL = 'illegal'
    UNSPECIFIED = 'unspecified'
    DEADLOCK = 'deadlock'
    BOUNDED_NO_RESULT = 'bounded_no_result'
    SEARCH_CAP = 'search_cap'
    INPUT_FAILURE = 'input_failure'
    NATIVE_HARNESS_FAILURE = 'native_harness_failure'

class Status(str, Enum):
    VALUE_MATCH = 'value_match'
    ERROR_RETURN_MATCH = 'error_return_match'
    PANIC_MATCH = 'panic_match'
    ILLEGAL = 'illegal_exclusion'
    UNSPECIFIED = 'unspecified_exclusion'
    SEARCH_CAP = 'search_cap'
    BOUNDED_NO_RESULT = 'bounded_no_result'
    HOST = 'host_difference'
    MISMATCH = 'mismatch'
    INPUT_FAILURE = 'input_failure'
    NATIVE_HARNESS_FAILURE = 'native_harness_failure'
    SKIPPED = 'skipped'

PANICS = {
    **dict.fromkeys(('integerOverflow', 'shlOverflow', 'shrOverflow', 'integerOutOfBounds', 'integerPartOutOfBounds'), 'overflow'),
    **dict.fromkeys(('outOfBounds', 'startGreaterThanEnd'), 'outOfBounds'),
    'divideByZero': 'divByZero', 'doubleFree': 'illegal', 'reachedUnreachable': 'unreachable',
    **dict.fromkeys(('exactDivisionRemainder', 'unwrapNull', 'unwrapError', 'forLenMismatch', 'invalidEnumValue',
                    'inactiveUnionField', 'corruptSwitch', 'sentinelMismatch', 'copyLenMismatch', 'memcpyAlias',
                    'castToNull', 'incorrectAlignment', 'panic'), 'panic'),
}
ERRORS = {'overflow', 'outOfBounds', 'divByZero', 'unreachable', 'panic', 'illegal', 'unspecified', 'deadlock'}
IDENT = re.compile(r'[a-zA-Z0-9_-]+\Z')

class Invalid(ValueError):
    pass

class Unsupported(Invalid):
    pass

def no_duplicates(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise Invalid('duplicate JSON key')
        out[key] = value
    return out

def decode(line):
    try:
        return json.loads(line, object_pairs_hook=no_duplicates, parse_constant=lambda _: (_ for _ in ()).throw(Invalid('non-finite JSON')))
    except (ValueError, RecursionError) as exc:
        raise Invalid('invalid JSON record') from exc

def read_summary(path):
    with path.open('rb') as stream:
        content=stream.read(MAX_LINE+1)
    if len(content)>MAX_LINE:raise Invalid('summary byte bound exceeded')
    result=decode(content.decode('utf-8'))
    if not isinstance(result,dict):raise Invalid('summary must be an object')
    return result

def lines(path):
    with path.open('rb') as stream:
        count = 0
        while True:
            line = stream.readline(MAX_LINE + 1)
            if not line:
                break
            count += 1
            if len(line) > MAX_LINE or count > MAX_CASES:
                raise Invalid('input/report bound exceeded')
            if not line.endswith(b'\n') or not line.strip():
                raise Invalid('unterminated or empty JSONL record')
            yield line.decode('utf-8')

def wire(line):
    value = decode(line) if isinstance(line, str) else line
    if not isinstance(value, dict):
        raise Invalid('wire result must be an object')
    tags = set(value) & {'ok', 'fail', 'diverge'}
    if len(tags) != 1:
        raise Invalid('wire result requires one outcome')
    if 'ok' in tags:
        if set(value) - {'ok', 'bufs', 'live'}:
            raise Invalid('unknown value-result field')
        if 'bufs' in value and (not isinstance(value['bufs'], list) or any(not isinstance(x, str) for x in value['bufs'])):
            raise Invalid('invalid buffers')
        if 'live' in value and (type(value['live']) is not int or value['live'] < 0):
            raise Invalid('invalid live count')
    elif set(value) != tags or ('fail' in tags and not isinstance(value['fail'], str)) or ('diverge' in tags and value['diverge'] is not True):
        raise Invalid('invalid terminal result')
    return value

def observation(line, legacy, side):
    record = decode(line)
    if not isinstance(record, dict) or type(record.get('schema')) is not int:
        raise Invalid('invalid observation schema')
    if record['schema'] != SCHEMA:
        raise Unsupported('unsupported observation schema')
    try:
        kind = Kind(record['kind'])
    except (KeyError, ValueError, TypeError) as exc:
        raise Invalid('unknown observation kind') from exc
    if set(record) - {'schema', 'kind', 'legacy', 'legacy_line', 'search'}:
        raise Invalid('unknown observation field')
    if ('legacy' in record) == ('legacy_line' in record):
        raise Invalid('observation needs exactly one legacy binding')
    if wire(record.get('legacy', record.get('legacy_line'))) != legacy:
        raise Invalid('stale/misaligned observation')
    allowed = {Kind.VALUE, Kind.ERROR_RETURN, Kind.NATIVE_PANIC, Kind.NATIVE_HARNESS_FAILURE, Kind.INPUT_FAILURE} if side == 'native' else set(Kind) - {Kind.NATIVE_PANIC}
    if kind not in allowed:
        raise Invalid('observation kind is invalid for producer')
    if kind in {Kind.VALUE, Kind.ERROR_RETURN}:
        if 'ok' not in legacy:
            raise Invalid('return observation lacks value')
        is_error = isinstance(legacy['ok'], dict) and set(legacy['ok']) == {'err'} and isinstance(legacy['ok']['err'], str)
        if kind == Kind.ERROR_RETURN and not is_error:
            raise Invalid('returned-error tag disagrees with payload')
    elif kind == Kind.BOUNDED_NO_RESULT:
        if legacy != {'diverge': True}:
            raise Invalid('no-result observation lacks legacy no-result')
    elif kind == Kind.SEARCH_CAP:
        if legacy != {'fail': 'Zig.Error.capped'}:
            raise Invalid('search-cap observation lacks cap marker')
    elif kind == Kind.NATIVE_HARNESS_FAILURE:
        if set(legacy) != {'fail'} or not isinstance(legacy['fail'],str):
            raise Invalid('native failure lacks failure marker')
    elif kind == Kind.NATIVE_PANIC:
        if set(legacy) != {'fail'} or not isinstance(legacy['fail'],str) or not IDENT.fullmatch(legacy['fail']):
            raise Invalid('invalid reported native panic tag')
    elif kind != Kind.INPUT_FAILURE:
        error = legacy.get('fail', '').removeprefix('Zig.Error.')
        expected = {'illegal': Kind.ILLEGAL, 'unspecified': Kind.UNSPECIFIED, 'deadlock': Kind.DEADLOCK}.get(error, Kind.MODEL_PANIC)
        if error not in ERRORS or legacy.get('fail') != 'Zig.Error.' + error or kind != expected:
            raise Invalid('model error tag disagrees with constructor')
    search = record.get('search')
    if search is not None:
        if side != 'model' or not isinstance(search, dict) or set(search) != {'prefix','options','runs','fuel','cap','status','saw_no_result'}:
            raise Invalid('invalid search metadata')
        for field in ('prefix','options'):
            if not isinstance(search[field], list) or len(search[field]) > MAX_CASES or any(type(n) is not int or n < 0 for n in search[field]):
                raise Invalid('invalid schedule trace')
        for field in ('runs','fuel','cap'):
            if type(search[field]) is not int or search[field] < 0:
                raise Invalid('invalid search bound')
        if search['runs'] == 0 or search['runs'] > search['cap'] or search['status'] not in {'witness','exhausted','capped','bounded'} or type(search['saw_no_result']) is not bool:
            raise Invalid('inconsistent search status')
        if search['status'] == 'bounded' and not search['saw_no_result']:
            raise Invalid('bounded search lacks no-result observation')
        if kind == Kind.SEARCH_CAP and search['status'] != 'capped':
            raise Invalid('cap observation lacks capped search')
    elif kind == Kind.SEARCH_CAP:
        raise Invalid('cap observation requires search evidence')
    return kind, search

def normalized(value):
    # Only a top-level decimal leaf has the legacy bare/quoted equivalence.
    if isinstance(value, str) and re.fullmatch(r'-?[0-9]+', value):
        return int(value)
    return value

def same_value(native, model):
    if 'ok' not in native or 'ok' not in model or json.dumps(normalized(native['ok']), sort_keys=True) != json.dumps(normalized(model['ok']), sort_keys=True):
        return False
    if native.get('live') != model.get('live') or ('bufs' in native) != ('bufs' in model):
        return False
    return len(native.get('bufs', [])) == len(model.get('bufs', [])) and all(
        fnmatch.fnmatchcase(z, l) for z,l in zip(native.get('bufs', []), model.get('bufs', [])))

def legacy_bucket(native, model, host):
    if same_value(native, model): return 'ok'
    if model.get('fail') in {'Zig.Error.illegal','Zig.Error.unspecified'}: return 'unspecified'
    if model.get('fail') == 'Zig.Error.capped': return 'capped'
    if 'fail' in native and PANICS.get(native['fail']) is not None and model.get('fail') == 'Zig.Error.' + PANICS[native['fail']]: return 'fail_match'
    return 'host' if host else 'mismatch'

def classify(native, model, nkind, mkind, search, host=False):
    if Kind.INPUT_FAILURE in (nkind,mkind): return Status.INPUT_FAILURE
    if Kind.NATIVE_HARNESS_FAILURE in (nkind,mkind): return Status.NATIVE_HARNESS_FAILURE
    if same_value(native, model):
        if nkind != mkind:return Status.MISMATCH
        return Status.ERROR_RETURN_MATCH if mkind == Kind.ERROR_RETURN else Status.VALUE_MATCH
    if mkind == Kind.ILLEGAL: return Status.ILLEGAL
    if mkind == Kind.UNSPECIFIED: return Status.UNSPECIFIED
    if mkind == Kind.SEARCH_CAP: return Status.SEARCH_CAP
    if nkind == Kind.NATIVE_PANIC and mkind == Kind.MODEL_PANIC and PANICS.get(native['fail']) is not None and model.get('fail') == 'Zig.Error.' + PANICS[native['fail']]: return Status.PANIC_MATCH
    if mkind == Kind.BOUNDED_NO_RESULT or (search and search['saw_no_result']): return Status.BOUNDED_NO_RESULT
    if host: return Status.HOST
    return Status.MISMATCH

def pins(path):
    result = {}
    if path.exists():
        for raw in path.read_text().splitlines():
            raw = raw.split('#',1)[0].strip()
            if not raw: continue
            parts = raw.split()
            if len(parts) != 2 or not IDENT.fullmatch(parts[0]) or parts[0] in result or not re.fullmatch(r'[0-9]+(?:-[0-9]+)?',parts[1]):
                raise Invalid('invalid count pin')
            vals = list(map(int,parts[1].split('-')))
            lo,hi = vals[0],vals[-1]
            if lo > hi: raise Invalid('reversed count pin')
            result[parts[0]] = (lo,hi)
    return result

def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd,name = tempfile.mkstemp(prefix='.diff-report-',dir=path.parent)
    try:
        with os.fdopen(fd,'w') as out: json.dump(value,out,sort_keys=True);out.write('\n')
        os.replace(name,path)
    finally:
        if os.path.exists(name): os.unlink(name)

def summary_failure(path, phase, reason, category=Failure.SETUP, observations=None):
    atomic_json(path, {'schema':SCHEMA,'complete':False,'phase':phase,'failure':category.value, 'observations':observations or [],
                       'reason':reason,'mutation_eligible':0,'qualified':False})

def selection(root, examples, version, host):
    rows=[]
    for directory in sorted((root/'examples').iterdir()):
        if not directory.is_dir() or directory.name in examples: continue
        reason='not_requested'
        if directory.name=='asm' and not host.endswith('-x86_64'): reason='host_excluded'
        versions=directory/'zig-versions'
        if versions.exists() and version not in versions.read_text().splitlines(): reason='version_excluded'
        rows.append({'schema':SCHEMA,'status':Status.SKIPPED.value,'example':directory.name,'reason':reason})
    return rows

def source_hashes(root):
    paths=[root/name for name in ('scripts/diff.sh','scripts/diff-report.py','tests/diff/Diff.lean','tests/diff/Outcome.lean','tests/diff/common.zig')]
    paths+=sorted((root/'ZigLean').rglob('*.lean'))
    paths+=sorted((root/'Proofs').rglob('*.lean'))
    paths+=sorted((root/'tests/diff').rglob('*.zig'))
    paths+=sorted((root/'examples').rglob('*.zig'))
    paths+=[root/name for name in ('scripts/example-selection.sh','scripts/mutate.sh','lakefile.toml','lean-toolchain','tests/diff/lakefile.toml')]
    if len(paths)>4096:raise Invalid('source inventory bound exceeded')
    result={}
    for path in paths:
        if not path.is_file():continue  # Isolated offline mocks deliberately omit runtime sources.
        digest=hashlib.sha256();total=0
        with path.open('rb') as stream:
            while chunk:=stream.read(65536):
                total+=len(chunk)
                if total>MAX_LINE:raise Invalid('source byte bound exceeded')
                digest.update(chunk)
        result[str(path.relative_to(root))]=digest.hexdigest()
    return result

def compare(root, examples, version, host, summary):
    if not examples or len(set(examples))!=len(examples) or any(not IDENT.fullmatch(ex) for ex in examples):
        raise Invalid('invalid selected examples')
    report_path=Path(str(summary)+'.jsonl')
    report_path.parent.mkdir(parents=True,exist_ok=True)
    totals=Counter();legacy_totals=Counter();violations=[];eligible=0;case_count=0;written=0
    with report_path.open('w') as out:
        def emit(row):
            nonlocal written
            encoded=json.dumps(row,sort_keys=True,separators=(',',':'))+'\n'
            written+=len(encoded.encode())
            if written>MAX_REPORT: raise Invalid('report byte bound exceeded')
            out.write(encoded)
        skipped=selection(root,examples,version,host)
        for row in skipped: emit(row)
        for ex in examples:
            inputs=root/'tests/diff'/ex/'inputs'
            if not inputs.is_dir(): raise Invalid('missing example inputs')
            allowed_host=set()
            host_file=root/'tests/diff'/ex/'host.txt'
            if host!='Linux-x86_64' and host_file.exists():allowed_host=set(host_file.read_text().splitlines())
            fn_pins={bucket:pins(root/'tests/diff'/ex/(bucket+'.txt')) for bucket in ('unspecified','capped')}
            files=sorted(inputs.glob('*.jsonl'))
            if not files: raise Invalid('no function inputs')
            for infile in files:
                fn=infile.stem
                if not IDENT.fullmatch(fn):raise Invalid('invalid function name')
                zpath=root/'tests/diff/out/zig'/ex/infile.name;lpath=root/'tests/diff/out/lean'/ex/infile.name
                generators=[iter(lines(path)) for path in (infile,zpath,lpath,Path(str(zpath)+'.outcomes'),Path(str(lpath)+'.outcomes'))]
                local=Counter();statuses=Counter();count=0
                while True:
                    values=[next(g,None) for g in generators]
                    if all(v is None for v in values):break
                    if any(v is None for v in values):raise Invalid('input/result/metadata row count mismatch')
                    raw,zline,lline,zmeta,lmeta=values;decode(raw)
                    native=wire(zline);model=wire(lline)
                    nkind,_=observation(zmeta,native,'native');mkind,search=observation(lmeta,model,'model')
                    status=classify(native,model,nkind,mkind,search,fn in allowed_host)
                    bucket=legacy_bucket(native,model,fn in allowed_host)
                    count+=1;case_count+=1
                    if case_count>MAX_CASES:raise Invalid('case bound exceeded')
                    totals[status.value]+=1;statuses[status]+=1;local[bucket]+=1;legacy_totals[bucket]+=1
                    eligible+=status==Status.MISMATCH
                    row={'schema':SCHEMA,'example':ex,'function':fn,'input_index':count,
                         'input_sha256':hashlib.sha256(raw.encode()).hexdigest(),'native_kind':nkind.value,'model_kind':mkind.value,
                         'native_sha256':hashlib.sha256(zline.encode()).hexdigest(),'model_sha256':hashlib.sha256(lline.encode()).hexdigest(),
                         'status':status.value,'legacy_bucket':bucket}
                    if search:row['schedule']=search
                    emit(row)
                if count==0:raise Invalid('empty function inputs')
                for bucket,specs in fn_pins.items():
                    lo,hi=specs.get(fn,(0,0))
                    if not lo<=local[bucket]<=hi:
                        violation={'example':ex,'function':fn,'counter':bucket,'actual':local[bucket],'min':lo,'max':hi}
                        violations.append(violation)
                        # Search-cap changes are budget evidence, not semantic mutation detections.
                        if bucket=='unspecified' and not any(statuses[s] for s in (Status.SEARCH_CAP,Status.BOUNDED_NO_RESULT,Status.HOST,Status.INPUT_FAILURE,Status.NATIVE_HARNESS_FAILURE)):eligible+=1
    setup_failures=totals[Status.INPUT_FAILURE.value]+totals[Status.NATIVE_HARNESS_FAILURE.value]
    atomic_json(summary,{'schema':SCHEMA,'complete':True,'qualified':False,'profile':{'zig_version':version,'host':host},
                         'case_count':case_count,'skipped_examples':len(skipped),'counts':dict(totals),'legacy_counts':dict(legacy_totals),
                         'pin_violations':violations,'mutation_eligible':0 if setup_failures else eligible,
                         'setup_failures':setup_failures,'cases_path':str(report_path),'runner_runtime_sources':source_hashes(root)})
    return 1 if setup_failures or totals[Status.MISMATCH.value] or legacy_totals['mismatch'] or violations else 0

def failure_observations(root, examples):
    observations=[];seen=0
    for ex in examples:
        if not IDENT.fullmatch(ex): raise Invalid('invalid selected example')
        for side in ('zig','lean'):
            directory=root/'tests/diff/out'/side/ex
            for path in sorted(directory.glob('*.jsonl.outcomes')):
                for index,line in enumerate(lines(path),1):
                    seen+=1
                    if seen>MAX_CASES:raise Invalid('failure observation bound exceeded')
                    record=decode(line)
                    if not isinstance(record,dict):raise Invalid('invalid failure observation')
                    if type(record.get('schema')) is int and record.get('schema')==SCHEMA and record.get('kind')==Kind.INPUT_FAILURE.value:
                        observations.append({'schema':SCHEMA,'status':Status.INPUT_FAILURE.value,
                                             'example':ex,'producer':side,'function':path.name.removesuffix('.jsonl.outcomes'),
                                             'input_index':index})
                    if len(observations)>MAX_CASES:raise Invalid('failure observation bound exceeded')
    return observations

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=('init','failure','compare','eligible'))
    parser.add_argument('--summary',type=Path,required=True)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--examples',default='')
    parser.add_argument('--version',default='unavailable')
    parser.add_argument('--host',default='unavailable')
    parser.add_argument('--phase',default='setup')
    args=parser.parse_args()
    try:
        if args.action=='init':
            Path(str(args.summary)+'.jsonl').unlink(missing_ok=True)
            for ex in args.examples.split():
                if not IDENT.fullmatch(ex): raise Invalid('invalid selected example')
                for side in ('zig','lean'):
                    for path in (args.root/'tests/diff/out'/side/ex).glob('*.jsonl.outcomes'):
                        path.unlink()
            summary_failure(args.summary,args.phase,'not completed');return 0
        if args.action=='failure':
            # Keep completed comparison evidence when its failing exit is intentional.
            if args.summary.exists() and read_summary(args.summary).get('complete') is True:return 0
            observed=failure_observations(args.root,args.examples.split())
            summary_failure(args.summary,args.phase,'runner phase failed',
                            Failure.INPUT if observed else Failure.SETUP,observed);return 0
        if args.action=='eligible':
            result=read_summary(args.summary)
            if type(result.get('schema')) is not int or result.get('schema')!=SCHEMA or result.get('complete') is not True or type(result.get('setup_failures')) is not int or result.get('setup_failures')!=0:
                raise Invalid('mutation runner setup/metadata failed')
            value=result.get('mutation_eligible')
            if type(value) is not int or value<0:raise Invalid('invalid mutation accounting')
            print(value);return 0
        return compare(args.root,args.examples.split(),args.version,args.host,args.summary)
    except (Invalid,OSError,UnicodeError,RecursionError) as exc:
        if args.action!='eligible':summary_failure(args.summary,args.phase,str(exc),Failure.UNSUPPORTED if isinstance(exc,Unsupported) else Failure.SETUP)
        parser.exit(2,str(exc)+'\n')

if __name__=='__main__':raise SystemExit(main())
