#!/usr/bin/env python3
"""Typed differential accounting. Legacy counters remain a compatibility projection."""
import argparse
from collections import Counter
from enum import Enum
import math
import functools
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
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
    NATIVE_SIGNAL = 'native_signal'
    ILLEGAL = 'illegal'
    UNSPECIFIED = 'unspecified'
    # `Zig.Error.unsupportedTimer`: a clock/timed-wait call the model has no semantics for.
    UNSPECIFIED_TIMER = 'unspecified_timer'
    DEADLOCK = 'deadlock'
    TRAP = 'trap'
    STACK_OVERFLOW = 'stack_overflow'
    BOUNDED_NO_RESULT = 'bounded_no_result'
    SEARCH_CAP = 'search_cap'
    INPUT_FAILURE = 'input_failure'
    NATIVE_HARNESS_FAILURE = 'native_harness_failure'

class Status(str, Enum):
    VALUE_MATCH = 'value_match'
    ERROR_RETURN_MATCH = 'error_return_match'
    PANIC_MATCH = 'panic_match'
    TRAP_MATCH = 'trap_match'
    ILLEGAL = 'illegal_exclusion'
    UNSPECIFIED = 'unspecified_exclusion'
    UNSPECIFIED_TIMER = 'unspecified_timer_exclusion'
    STACK_OVERFLOW = 'stack_overflow_exclusion'
    SEARCH_CAP = 'search_cap'
    BOUNDED_NO_RESULT = 'bounded_no_result'
    HOST = 'host_difference'
    MISMATCH = 'mismatch'
    INPUT_FAILURE = 'input_failure'
    NATIVE_HARNESS_FAILURE = 'native_harness_failure'
    SKIPPED = 'skipped'
    # ReleaseFast/ReleaseSmall only: the model throws on the input, so the build has illegal behavior.
    UB_EXCLUDED = 'ub_excluded'

ERRORS = {'overflow', 'outOfBounds', 'divByZero', 'unreachable', 'panic', 'illegal', 'unspecified', 'deadlock',
          'unsupportedTimer', 'trap', 'stackOverflow'}
# Model constructors with their own observation kind; every other `Zig.Error` is a model panic.
MODEL_ERROR_KINDS = {'illegal': Kind.ILLEGAL, 'unspecified': Kind.UNSPECIFIED,
                     'unsupportedTimer': Kind.UNSPECIFIED_TIMER, 'deadlock': Kind.DEADLOCK, 'trap': Kind.TRAP,
                     'stackOverflow': Kind.STACK_OVERFLOW}
# Legacy compatibility projection: these model errors count in the legacy `unspecified` bucket.
LEGACY_UNSPECIFIED = {'Zig.Error.illegal', 'Zig.Error.unspecified', 'Zig.Error.unsupportedTimer',
                      'Zig.Error.stackOverflow'}
IDENT = re.compile(r'[a-zA-Z0-9_-]+\Z')
# The synchronous fault signals tests/diff/common.zig reports by name (`native_signal`).
SIGNALS = frozenset({'SIGFPE', 'SIGILL', 'SIGSEGV', 'SIGBUS'})
SHA256 = re.compile(r'[0-9a-f]{64}\Z')

class Invalid(ValueError):
    pass

class Unsupported(Invalid):
    pass

def load_panic_policy(path):
    result={}
    for line in path.read_text().splitlines():
        fields=line.split('\t')
        if len(fields)!=2 or not IDENT.fullmatch(fields[0]) or fields[0] in result or fields[1] not in ERRORS:
            raise Invalid('invalid panic policy')
        result[fields[0]]=fields[1]
    if not result:raise Invalid('empty panic policy')
    return result

PANICS=load_panic_policy(Path(__file__).with_name('panic-policy.tsv'))

def no_duplicates(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise Invalid('duplicate JSON key')
        out[key] = value
    return out

def parse_finite_float(token):
    value=float(token)
    if not math.isfinite(value):raise Invalid('non-finite JSON number')
    return value

def decode(line):
    try:
        return json.loads(line, object_pairs_hook=no_duplicates, parse_float=parse_finite_float, parse_constant=lambda _: (_ for _ in ()).throw(Invalid('non-finite JSON')))
    except (ValueError, RecursionError) as exc:
        raise Invalid('invalid JSON record') from exc

def read_summary(path):
    with path.open('rb') as stream:
        content=stream.read(MAX_LINE+1)
    if len(content)>MAX_LINE:raise Invalid('summary byte bound exceeded')
    result=decode(content.decode('utf-8'))
    if not isinstance(result,dict):raise Invalid('summary must be an object')
    return result

def lines(path, *, max_records=None, max_bytes=None):
    if max_records is None:max_records=MAX_CASES
    with path.open('rb') as stream:
        count = 0
        total = 0
        while True:
            line = stream.readline(MAX_LINE + 1)
            if not line:
                break
            count += 1
            total += len(line)
            if len(line) > MAX_LINE or count > max_records or (max_bytes is not None and total > max_bytes):
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

def json_equal(left, right):
    """Exact decoded types/values, with object order ignored and float zero sign kept."""
    if type(left) is not type(right):return False
    if isinstance(left,dict):
        return left.keys()==right.keys() and all(json_equal(left[k],right[k]) for k in left)
    if isinstance(left,list):
        return len(left)==len(right) and all(json_equal(x,y) for x,y in zip(left,right))
    if isinstance(left,float) and left==right==0:
        return math.copysign(1,left)==math.copysign(1,right)
    return left==right

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
    if not json_equal(wire(record.get('legacy', record.get('legacy_line'))),legacy):
        raise Invalid('stale/misaligned observation')
    allowed = {Kind.VALUE, Kind.ERROR_RETURN, Kind.NATIVE_PANIC, Kind.NATIVE_SIGNAL, Kind.NATIVE_HARNESS_FAILURE, Kind.INPUT_FAILURE} if side == 'native' else set(Kind) - {Kind.NATIVE_PANIC, Kind.NATIVE_SIGNAL}
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
    elif kind == Kind.NATIVE_SIGNAL:
        if set(legacy) != {'fail'} or legacy['fail'] not in SIGNALS:
            raise Invalid('native signal requires a fault signal name')
    elif kind == Kind.NATIVE_HARNESS_FAILURE:
        if set(legacy) != {'fail'} or not isinstance(legacy['fail'],str):
            raise Invalid('native failure lacks failure marker')
    elif kind == Kind.NATIVE_PANIC:
        if set(legacy) != {'fail'} or not isinstance(legacy['fail'],str) or not IDENT.fullmatch(legacy['fail']):
            raise Invalid('invalid reported native panic tag')
    elif kind != Kind.INPUT_FAILURE:
        error = legacy.get('fail', '').removeprefix('Zig.Error.')
        expected = MODEL_ERROR_KINDS.get(error, Kind.MODEL_PANIC)
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
        if search['status'] == 'capped' and search['runs'] != search['cap']:
            raise Invalid('capped search did not exhaust its run cap')
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

def buffer_match(native, model):
    # Pointer fragments ('pp') are unresolved, so they cannot establish byte equality.
    if len(native)!=len(model) or len(native)%2:return False
    if not re.fullmatch(r'[0-9a-f]*',native) or not re.fullmatch(r'[0-9a-f?]*',model):return False
    return all(y=='?' or x==y for x,y in zip(native,model))

def same_extras(native, model):
    """The live allocation counts and the buffers after the call agree."""
    if native.get('live') != model.get('live') or ('bufs' in native) != ('bufs' in model):
        return False
    return len(native.get('bufs', [])) == len(model.get('bufs', [])) and all(
        buffer_match(z,l) for z,l in zip(native.get('bufs', []), model.get('bufs', [])))

def same_value(native, model):
    if 'ok' not in native or 'ok' not in model or not json_equal(normalized(native['ok']),normalized(model['ok'])):
        return False
    return same_extras(native, model)

MATCHES = (Status.VALUE_MATCH, Status.ERROR_RETURN_MATCH, Status.PANIC_MATCH, Status.TRAP_MATCH)

# Typed host differences (tests/diff/<ex>/host.txt, F3). Off the reference host (x86_64-linux,
# docs/floats.md) a native/model disagreement of two returned values is a `host_difference`
# only if every differing float leaf satisfies one of the kinds listed for the function:
#   nan_payload    both NaN of one format (sign and payload bits differ)
#   zero_sign      both zero of one format, opposite signs
#   libm_ulp       both finite of one format, at most LIBM_ULPS ulps apart; an f80/f128 pair whose
#                  values are both f64 values (the transcendental routines compute in f64) is
#                  measured in f64 ulps
# Anything else, including a model panic, error or exclusion against a native value, is a mismatch.
# An f80 rounding difference is no host kind: an aarch64-macos translation models the soft-float
# routines bit for bit (docs/floats.md §Targets).
HOST_KINDS = ('nan_payload', 'zero_sign', 'libm_ulp')
LIBM_ULPS = 2
# Hex digits of a "0x<bits>" float leaf -> (exponent bits, mantissa bits, explicit integer bit).
FLOAT_FORMATS = {4: (5, 10, False), 8: (8, 23, False), 16: (11, 52, False), 20: (15, 64, True), 32: (15, 112, False)}
HEX_FLOAT = re.compile(r'0x[0-9a-f]+\Z')

def float_leaf(leaf):
    """(hex digits, class, signed ordinal) of a "0x<bits>" float leaf, else None. Class is
    'nan', 'inf', 'zero', 'finite' or 'invalid' (an f80 encoding without a valid integer bit).
    Adjacent finite values of one format have ordinals one apart."""
    if not isinstance(leaf, str) or not HEX_FLOAT.fullmatch(leaf) or len(leaf) - 2 not in FLOAT_FORMATS:
        return None
    digits = len(leaf) - 2
    exp_bits, man_bits, explicit = FLOAT_FORMATS[digits]
    bits = int(leaf, 16)
    man = bits & ((1 << man_bits) - 1)
    exp = (bits >> man_bits) & ((1 << exp_bits) - 1)
    negative = bits >> (man_bits + exp_bits)
    top = exp == (1 << exp_bits) - 1
    if explicit:
        # f80: the integer bit must be 1 for a normal, infinity or NaN and 0 for a zero or denormal.
        integer, man_bits = man >> (man_bits - 1), man_bits - 1
        man &= (1 << man_bits) - 1
        if integer != (exp != 0):
            cls = 'invalid'
        elif top:
            cls = 'inf' if man == 0 else 'nan'
        else:
            cls = 'zero' if exp == 0 and man == 0 else 'finite'
    else:
        cls = ('inf' if man == 0 else 'nan') if top else ('zero' if exp == 0 and man == 0 else 'finite')
    magnitude = (exp << man_bits) | man
    return digits, cls, -magnitude if negative else magnitude

def leaf_host_kinds(native, model):
    """The host-difference kinds that explain one differing leaf pair."""
    n, m = float_leaf(native), float_leaf(model)
    if n is None or m is None or n[0] != m[0]:
        return frozenset()
    if n[1] == m[1] == 'nan':
        return frozenset({'nan_payload'})
    if n[1] == m[1] == 'zero':
        return frozenset({'zero_sign'})
    if {n[1], m[1]} <= {'finite', 'zero'}:
        ulps = abs(n[2] - m[2])
        wide = {20: 63, 32: 112}.get(n[0])  # mantissa bits of f80 (integer bit dropped), f128
        if wide is not None:
            shift = wide - 52
            if n[2] % (1 << shift) == 0 and m[2] % (1 << shift) == 0:
                ulps >>= shift
        return frozenset({'libm_ulp'} if ulps <= LIBM_ULPS else set())
    return frozenset()

def differing_leaves(native, model):
    """The differing scalar leaf pairs of two returned values, or None if their shapes differ."""
    if isinstance(native, list) and isinstance(model, list):
        if len(native) != len(model):
            return None
        pairs = []
        for a, b in zip(native, model):
            sub = differing_leaves(a, b)
            if sub is None:
                return None
            pairs += sub
        return pairs
    if json_equal(normalized(native), normalized(model)):
        return []
    return None if isinstance(native, (list, dict)) or isinstance(model, (list, dict)) else [(native, model)]

def host_difference(native, model, allowed):
    """The sorted typed kinds that explain a native/model disagreement off the reference host,
    or None. Only two returned values with the same buffers and live count can differ by host."""
    if not allowed or 'ok' not in native or 'ok' not in model or not same_extras(native, model):
        return None
    pairs = differing_leaves(native['ok'], model['ok'])
    if not pairs:
        return None
    used = set()
    for pair in pairs:
        kinds = leaf_host_kinds(*pair) & allowed
        if not kinds:
            return None
        used |= kinds
    return sorted(used)

def capped_search(search):
    return bool(search) and search['status'] == 'capped'

def legacy_bucket(native, model, host, values_match=None, search=None, ub_kinds=False):
    """The scripts/diff.sh bucket. `host`: the function is in host.txt off the reference host
    and both sides returned a value (the shell does not type the difference)."""
    bucket=_legacy_bucket(native,model,host,values_match,ub_kinds)
    # A capped search never contributes a legacy agreement counter.
    return 'capped' if capped_search(search) and bucket in {'ok','fail_match'} else bucket

def _legacy_bucket(native, model, host, values_match=None, ub_model=False):
    if values_match is None:values_match=same_value(native,model)
    if values_match: return 'ok'
    if model.get('fail') in LEGACY_UNSPECIFIED: return 'unspecified'
    if model.get('fail') == 'Zig.Error.capped': return 'capped'
    if ub_model and model.get('fail','').startswith('Zig.Error.') and model['fail'] not in ('Zig.Error.deadlock','Zig.Error.trap'): return 'ub_excluded'
    if 'fail' in native and PANICS.get(native['fail']) is not None and model.get('fail') == 'Zig.Error.' + PANICS[native['fail']]: return 'fail_match'
    return 'host' if host and 'ok' in native and 'ok' in model else 'mismatch'

def classify(native, model, nkind, mkind, search, host=False, values_match=None, exclude_ub=False, pinned=False):
    """Typed status of one case. `host`: a typed host difference was found (`host_difference`);
    `exclude_ub`: a ReleaseFast/ReleaseSmall run (a model panic is the build's illegal behavior);
    `pinned`: the input is a pinned exclusion of the function (unspecified.txt)."""
    status=_classify(native,model,nkind,mkind,search,host,values_match,exclude_ub,pinned)
    # Truncated exploration is never demonstrated correspondence, whatever it observed.
    return Status.SEARCH_CAP if status in MATCHES and capped_search(search) else status

def _classify(native, model, nkind, mkind, search, host=False, values_match=None, exclude_ub=False, pinned=False):
    if Kind.INPUT_FAILURE in (nkind,mkind): return Status.INPUT_FAILURE
    # Without safety checks the returned value of an illegal call can be garbage that the harness
    # cannot even render (a wild pointer, a missing sentinel): that is the exclusion, not a harness bug.
    if exclude_ub and mkind == Kind.MODEL_PANIC and nkind == Kind.NATIVE_HARNESS_FAILURE and not same_value(native,model):return Status.UB_EXCLUDED
    if Kind.NATIVE_HARNESS_FAILURE in (nkind,mkind): return Status.NATIVE_HARNESS_FAILURE
    if values_match is None:values_match=same_value(native,model)
    if values_match:
        if nkind != mkind:return Status.MISMATCH
        return Status.ERROR_RETURN_MATCH if mkind == Kind.ERROR_RETURN else Status.VALUE_MATCH
    # An exclusion only on an input pinned for it (F3): elsewhere a model illegal/unspecified
    # result is a mismatch, whatever the native side did, unless an incomplete schedule search
    # makes the case inconclusive (its pin violation still fails the run).
    if mkind in (Kind.ILLEGAL, Kind.UNSPECIFIED):
        if pinned or (search and (search['status'] == 'capped' or search['saw_no_result'])):
            return Status.ILLEGAL if mkind == Kind.ILLEGAL else Status.UNSPECIFIED
        return Status.MISMATCH
    if mkind == Kind.UNSPECIFIED_TIMER: return Status.UNSPECIFIED_TIMER
    # The model's stack budget is chosen by the environment (MM-5), not the native stack size.
    if mkind == Kind.STACK_OVERFLOW: return Status.STACK_OVERFLOW
    if mkind == Kind.SEARCH_CAP: return Status.SEARCH_CAP
    if exclude_ub and mkind == Kind.MODEL_PANIC: return Status.UB_EXCLUDED
    expected = 'Zig.Error.' + PANICS.get(native.get('fail'), '')
    if nkind == Kind.NATIVE_PANIC and mkind == Kind.MODEL_PANIC and model.get('fail') == expected: return Status.PANIC_MATCH
    if nkind == Kind.NATIVE_SIGNAL and mkind == Kind.TRAP and model.get('fail') == expected: return Status.TRAP_MATCH
    if mkind == Kind.BOUNDED_NO_RESULT or (search and search['saw_no_result']): return Status.BOUNDED_NO_RESULT
    if host and nkind == mkind == Kind.VALUE: return Status.HOST
    return Status.MISMATCH

SEARCH_STATUSES = ('witness','exhausted','bounded','capped')
REDUCTION = {'technique':'none','soundness':'not_proved',
             'note':'every explored schedule is executed; partial-order/symmetry reduction proofs are out of scope (research)'}

class Exploration:
    """Schedule coverage accounting. Observed-result matching (per-case search metadata) and
    bounded enumeration (schedules.py receipts) are kept in separate counters."""
    def __init__(self):
        self.observed={'searched_cases':0,'unsearched_cases':0,'schedules_explored':0,'max_runs':0,
                       'status_counts':{s:0 for s in SEARCH_STATUSES},'saw_no_result_cases':0,
                       'replayable_witnesses':0,'fuel':set(),'cap':set()}
        self.enumeration={'receipts':0,'schedules_explored':0,'complete':0,'truncated':0,
                          'node_cap_reached':0,'prefix_cap_reached':0,'saw_no_result':0,
                          'replay_seeds':0,'replays':0,'fuel':set(),'node_cap':set(),'prefix_cap':set()}
        self.scopes={};self.capped_cases=[];self.receipts=[]

    def scope(self, ex, fn):
        return self.scopes.setdefault((ex,fn),{'example':ex,'function':fn,'cases':0,'exact_matches':0,
            'observed':{'searched_cases':0,'schedules_explored':0,'capped':0,'bounded':0},
            'enumeration':{'receipts':0,'schedules_explored':0,'complete':0,'truncated':0,'saw_no_result':0}})

    def case(self, ex, fn, index, status, search):
        scope=self.scope(ex,fn);scope['cases']+=1;scope['exact_matches']+=status in MATCHES
        if not search:
            self.observed['unsearched_cases']+=1;return
        o=self.observed;o['searched_cases']+=1;o['schedules_explored']+=search['runs']
        o['max_runs']=max(o['max_runs'],search['runs']);o['status_counts'][search['status']]+=1
        o['saw_no_result_cases']+=search['saw_no_result'];o['replayable_witnesses']+=search['status']=='witness'
        o['fuel'].add(search['fuel']);o['cap'].add(search['cap'])
        s=scope['observed'];s['searched_cases']+=1;s['schedules_explored']+=search['runs']
        s['capped']+=search['status']=='capped';s['bounded']+=search['saw_no_result']  # bounded implies saw_no_result
        if search['status']=='capped':
            self.capped_cases.append({'example':ex,'function':fn,'input_index':index,'status':status.value,
                                      'runs':search['runs'],'cap':search['cap'],'fuel':search['fuel']})

    def receipt(self, path, receipt, digest):
        request,result=receipt['request'],receipt['result']
        if request['mode']=='replay':
            self.enumeration['replays']+=1;return
        e=self.enumeration;e['receipts']+=1;e['schedules_explored']+=result['runs']
        for key in ('node_cap_reached','prefix_cap_reached','saw_no_result','truncated'):e[key]+=result[key]
        e['complete']+=result['exploration_complete']
        for key in ('fuel','node_cap','prefix_cap'):e[key].add(request[key])
        seeds=[i for i,entry in enumerate(result['executions']) if entry['trace_complete']]
        e['replay_seeds']+=len(seeds)
        s=self.scope(request['example'],request['function'])['enumeration']
        s['receipts']+=1;s['schedules_explored']+=result['runs']
        s['complete']+=result['exploration_complete'];s['truncated']+=result['truncated']
        s['saw_no_result']+=result['saw_no_result']
        self.receipts.append({'path':str(path),'sha256':digest,
            'example':request['example'],'function':request['function'],'input_index':receipt['input_index'],
            'fuel':request['fuel'],'node_cap':request['node_cap'],'prefix_cap':request['prefix_cap'],
            'runs':result['runs'],'truncated':result['truncated'],'node_cap_reached':result['node_cap_reached'],
            'prefix_cap_reached':result['prefix_cap_reached'],'exploration_complete':result['exploration_complete'],
            'distinct_outcomes':len(result['outcomes']),'replay_seed_indices':seeds})

    def summary(self):
        scopes=[]
        for key in sorted(self.scopes):
            scope=self.scopes[key];blockers=[]
            if scope['observed']['capped']:blockers.append('search_cap')
            if scope['enumeration']['truncated']:blockers.append('enumeration_truncated')
            if scope['observed']['bounded'] or scope['enumeration']['saw_no_result']:blockers.append('bounded_no_result')
            if scope['cases']==0 or scope['exact_matches']!=scope['cases']:blockers.append('non_matching_cases')
            capped=bool(scope['observed']['capped'] or scope['enumeration']['truncated'])
            scope.update(capped=capped,counts_as_correspondence=not blockers,qualified=False,
                         blockers=blockers+['proof_applicability_not_evaluated'])
            scopes.append(scope)
        sets=lambda d:{k:sorted(v) if isinstance(v,set) else v for k,v in d.items()}
        return {'qualified':False,'reduction':REDUCTION,
                'observed_matching':sets(self.observed),'bounded_enumeration':sets(self.enumeration),
                'correspondence_scopes':sum(s['counts_as_correspondence'] for s in scopes),
                'capped_scopes':sum(s['capped'] for s in scopes),'capped_cases':self.capped_cases,
                'enumeration_receipts':self.receipts,'scopes':scopes}

@functools.cache
def load_schedule_cli():
    # Share this module (and its Invalid class) with schedules.py instead of loading a second copy.
    this=sys.modules.get(__name__)
    if this is not None and getattr(this,'Exploration',None) is Exploration:sys.modules.setdefault('diff_report',this)
    spec=importlib.util.spec_from_file_location('air2lean_schedules',Path(__file__).with_name('schedules.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def schedule_receipt(root, path, examples, sources):
    """Validate one schedules.py receipt against the current source/input context.
    Returns the receipt and the SHA-256 of the exact bytes that were validated."""
    try:
        receipt,raw_bytes=load_schedule_cli().load_receipt(root,path,sources,examples)
    except (KeyError,TypeError,ValueError) as exc:  # Invalid is a ValueError
        raise Invalid(f'schedule receipt {path}: {exc}') from exc
    return receipt,hashlib.sha256(raw_bytes).hexdigest()

def headline(summary):
    x=summary['schedule_exploration'];o=x['observed_matching'];e=x['bounded_enumeration'];c=o['status_counts']
    return (f"SCHEDULES: observed searched={o['searched_cases']} unsearched={o['unsearched_cases']} runs={o['schedules_explored']}"
            f" witness={c['witness']} exhausted={c['exhausted']} bounded={c['bounded']} capped={c['capped']}"
            f" fuel={o['fuel']} cap={o['cap']}"
            f" | enumeration receipts={e['receipts']} runs={e['schedules_explored']} complete={e['complete']}"
            f" truncated={e['truncated']} replay_seeds={e['replay_seeds']} replays={e['replays']}"
            f" fuel={e['fuel']} node_cap={e['node_cap']} prefix_cap={e['prefix_cap']}"
            f" | correspondence_scopes={x['correspondence_scopes']} capped_scopes={x['capped_scopes']}"
            f" reduction={x['reduction']['technique']} qualified=false")

def config_rows(path):
    """The non-empty lines of an optional per-example config file, `#` comments removed."""
    if path.exists():
        for raw in path.read_text().splitlines():
            raw = raw.split('#',1)[0].strip()
            if raw: yield raw

def pins(path):
    """Per-input exclusion pins (F3): `<fn> <input_sha256> <count>|<min>-<max> <reason>` lines,
    `#` comments. The number of the function's cases on inputs with that SHA-256 (of the input
    line, newline included) in the pinned bucket must lie in the range; any other input expects
    0. Returns {fn: {sha256: (min, max, reason)}}."""
    result = {}
    for raw in config_rows(path):
        parts = raw.split(None, 3)
        if (len(parts) != 4 or not IDENT.fullmatch(parts[0]) or not SHA256.fullmatch(parts[1])
                or parts[1] in result.get(parts[0], {}) or not re.fullmatch(r'[0-9]+(?:-[0-9]+)?',parts[2])):
            raise Invalid('invalid exclusion pin')
        vals = list(map(int,parts[2].split('-')))
        lo,hi = vals[0],vals[-1]
        if lo > hi: raise Invalid('reversed exclusion pin')
        result.setdefault(parts[0], {})[parts[1]] = (lo,hi,parts[3])
    return result

def pin_file(directory, bucket, host):
    """`<bucket>.<host>.txt` (host: `uname -s`-`uname -m`, e.g. `Darwin-arm64`) if present, else
    `<bucket>.txt`. A host file replaces the shared one whole: on that host the diff test runs
    that host's translation, whose target profile makes other float cases unspecified
    (docs/floats.md §Targets)."""
    own = directory/f'{bucket}.{host}.txt'
    return own if own.exists() else directory/f'{bucket}.txt'

def host_allowances(path):
    """tests/diff/<ex>/host.txt: `<fn> <kind>[,<kind>...]` lines (HOST_KINDS), `#` comments."""
    result = {}
    for raw in config_rows(path):
        parts = raw.split()
        kinds = frozenset(parts[1].split(',')) if len(parts) == 2 else frozenset()
        if not kinds or not IDENT.fullmatch(parts[0]) or parts[0] in result or not kinds <= set(HOST_KINDS):
            raise Invalid('invalid host allowance')
        result[parts[0]] = kinds
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
        functions=sorted(p.stem for p in (root/'tests/diff'/directory.name/'inputs').glob('*.jsonl'))
        if any(not IDENT.fullmatch(fn) for fn in functions):raise Invalid('invalid skipped function name')
        rows.append({'schema':SCHEMA,'status':Status.SKIPPED.value,'example':directory.name,'reason':reason,'functions':functions})
    return rows

def source_hashes(root):
    paths=[root/name for name in ('scripts/diff.sh','scripts/diff-report.py','tests/diff/Diff.lean','tests/diff/Outcome.lean','tests/diff/common.zig','tests/diff/ScheduleSearch.lean','tests/diff/Concurrent.lean','tests/diff/Schedules.lean','scripts/schedules.py')]
    paths+=sorted((root/'ZigLean').rglob('*.lean'))
    paths+=sorted((root/'Proofs').rglob('*.lean'))
    paths+=sorted((root/'tests/diff').rglob('*.zig'))
    paths+=sorted((root/'examples').rglob('*.zig'))
    paths+=[root/name for name in ('scripts/example-selection.sh','scripts/panic-policy.tsv','scripts/mutate.sh','lakefile.toml','lean-toolchain','tests/diff/lakefile.toml')]
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

def compare(root, examples, version, host, summary, schedule_receipts=(), build=None):
    return compare_summary(root,examples,version,host,summary,schedule_receipts,build)[0]

def compare_summary(root, examples, version, host, summary, schedule_receipts=(), build=None):
    """Write the summary and return (exit code, summary dict).

    `build` is the (optimize mode, backend) of the native side when it is not the default
    ReleaseSafe/LLVM reference. ReleaseFast and ReleaseSmall remove the safety checks, so an
    input on which the model throws is illegal behavior there and is excluded, not compared."""
    exclude_ub=bool(build) and build[0] in ('ReleaseFast','ReleaseSmall')
    if not examples or len(set(examples))!=len(examples) or any(not IDENT.fullmatch(ex) for ex in examples):
        raise Invalid('invalid selected examples')
    sources=source_hashes(root);exploration=Exploration()
    if len(schedule_receipts)>MAX_CASES or len(set(schedule_receipts))!=len(schedule_receipts):raise Invalid('invalid schedule receipt list')
    seen=set()
    for path in schedule_receipts:
        receipt,digest=schedule_receipt(root,Path(path),examples,sources)
        keys={Path(path).resolve(),digest}
        if keys&seen:raise Invalid(f'duplicate schedule receipt {path}')
        seen|=keys;exploration.receipt(path,receipt,digest)
    report_path=Path(str(summary)+'.jsonl')
    report_path.parent.mkdir(parents=True,exist_ok=True)
    totals=Counter();legacy_totals=Counter();violations=[];eligible=0;case_count=0;written=0
    cases_digest=hashlib.sha256()  # Binds the case evidence to this summary (scripts/claims.py).
    with report_path.open('wb') as out:
        def emit(row):
            nonlocal written
            encoded=(json.dumps(row,sort_keys=True,separators=(',',':'))+'\n').encode()
            written+=len(encoded)
            if written>MAX_REPORT: raise Invalid('report byte bound exceeded')
            cases_digest.update(encoded);out.write(encoded)
        skipped=selection(root,examples,version,host)
        for row in skipped: emit(row)
        for ex in examples:
            inputs=root/'tests/diff'/ex/'inputs'
            if not inputs.is_dir(): raise Invalid('missing example inputs')
            allowances=host_allowances(root/'tests/diff'/ex/'host.txt')
            allowed_host=allowances if host!='Linux-x86_64' else {}
            fn_pins={bucket:pins(pin_file(root/'tests/diff'/ex,bucket,host)) for bucket in ('unspecified','capped')}
            files=sorted(inputs.glob('*.jsonl'))
            if not files: raise Invalid('no function inputs')
            for infile in files:
                fn=infile.stem
                if not IDENT.fullmatch(fn):raise Invalid('invalid function name')
                zpath=root/'tests/diff/out/zig'/ex/infile.name;lpath=root/'tests/diff/out/lean'/ex/infile.name
                generators=[iter(lines(path)) for path in (infile,zpath,lpath,Path(str(zpath)+'.outcomes'),Path(str(lpath)+'.outcomes'))]
                local=Counter();statuses=Counter();count=0;per_input={bucket:Counter() for bucket in fn_pins}
                excluded=fn_pins['unspecified'].get(fn,{})
                while True:
                    values=[next(g,None) for g in generators]
                    if all(v is None for v in values):break
                    if any(v is None for v in values):raise Invalid('input/result/metadata row count mismatch')
                    raw,zline,lline,zmeta,lmeta=values;decode(raw)
                    native=wire(zline);model=wire(lline)
                    nkind,_=observation(zmeta,native,'native');mkind,search=observation(lmeta,model,'model')
                    values_match=same_value(native,model)
                    input_sha=hashlib.sha256(raw.encode()).hexdigest()
                    host_kinds=None if values_match else host_difference(native,model,allowed_host.get(fn))
                    status=classify(native,model,nkind,mkind,search,host_kinds is not None,values_match,exclude_ub,
                                    input_sha in excluded)
                    bucket=legacy_bucket(native,model,fn in allowed_host,values_match,search,exclude_ub)
                    count+=1;case_count+=1
                    if case_count>MAX_CASES:raise Invalid('case bound exceeded')
                    totals[status.value]+=1;statuses[status]+=1;local[bucket]+=1;legacy_totals[bucket]+=1
                    if bucket in per_input:per_input[bucket][input_sha]+=1
                    eligible+=status==Status.MISMATCH
                    exploration.case(ex,fn,count,status,search)
                    row={'schema':SCHEMA,'example':ex,'function':fn,'input_index':count,
                         'input_sha256':input_sha,'native_kind':nkind.value,'model_kind':mkind.value,
                         'native_sha256':hashlib.sha256(zline.encode()).hexdigest(),'model_sha256':hashlib.sha256(lline.encode()).hexdigest(),
                         'status':status.value,'legacy_bucket':bucket}
                    if status==Status.HOST:row['host_kinds']=host_kinds
                    if status in (Status.ILLEGAL,Status.UNSPECIFIED) and input_sha in excluded:row['exclusion_reason']=excluded[input_sha][2]
                    if search:row['schedule']=search
                    if status==Status.MISMATCH:
                        print(f'MISMATCH (typed) {ex}.{fn} input#{count}: {raw.strip()}\n  zig:  {zline.strip()}\n  lean: {lline.strip()}',file=sys.stderr)
                    emit(row)
                if count==0:raise Invalid('empty function inputs')
                observed=exploration.scope(ex,fn)['observed'];incomplete_search=bool(observed['capped'] or observed['bounded'])
                for bucket,specs in fn_pins.items():
                    pinned=specs.get(fn,{})
                    for sha in sorted(set(pinned)|set(per_input[bucket])):
                        lo,hi,_=pinned.get(sha,(0,0,None));actual=per_input[bucket][sha]
                        if lo<=actual<=hi:continue
                        violations.append({'example':ex,'function':fn,'counter':bucket,'input_sha256':sha,'actual':actual,'min':lo,'max':hi})
                        print(f'EXCLUSION PIN {ex}.{fn} {bucket} input {sha}: {actual}, expected {lo}-{hi} ({pin_file(Path("tests/diff")/ex,bucket,host)})',file=sys.stderr)
                        # Search-cap changes are budget evidence, not semantic mutation detections.
                        if bucket=='unspecified' and not incomplete_search and not any(statuses[s] for s in (Status.SEARCH_CAP,Status.BOUNDED_NO_RESULT,Status.HOST,Status.INPUT_FAILURE,Status.NATIVE_HARNESS_FAILURE)):eligible+=1
    setup_failures=totals[Status.INPUT_FAILURE.value]+totals[Status.NATIVE_HARNESS_FAILURE.value]
    result={'schema':SCHEMA,'complete':True,'qualified':False,'profile':{'zig_version':version,'host':host,**({'optimize':build[0],'backend':build[1]} if build else {})},
                         'case_count':case_count,'skipped_examples':len(skipped),'skipped_functions':sum(len(row['functions']) for row in skipped),
                         'exact_matches':sum(totals[s.value] for s in MATCHES),
                         'proof_applicability':'not_evaluated_by_differential_runner',
                         'proof_exclusions':[{'example':ex,'reason':'proof_applicability_not_evaluated','sources':sorted(str(p.relative_to(root)) for p in (root/'Proofs'/(ex[0].upper()+ex[1:])).glob('*.lean'))} for ex in examples],
                         'counts':dict(totals),'legacy_counts':dict(legacy_totals),
                         'schedule_exploration':exploration.summary(),
                         'pin_violations':violations,'mutation_eligible':0 if setup_failures else eligible,
                         'setup_failures':setup_failures,'cases_path':str(report_path),'cases_sha256':cases_digest.hexdigest(),'runner_runtime_sources':sources}
    atomic_json(summary,result)
    return (1 if setup_failures or totals[Status.MISMATCH.value] or legacy_totals['mismatch'] or violations else 0),result

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
    parser.add_argument('--optimize',default='',help='native build mode when not the ReleaseSafe reference')
    parser.add_argument('--backend',default='',help='native backend (llvm or stage2_x86_64)')
    parser.add_argument('--schedule-receipts',default='',help='space-separated scripts/schedules.py receipts')
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
        code,result=compare_summary(args.root,args.examples.split(),args.version,args.host,args.summary,args.schedule_receipts.split(),(args.optimize,args.backend or 'llvm') if args.optimize else None)
        print(headline(result));return code
    except (Invalid,OSError,UnicodeError,RecursionError) as exc:
        if args.action!='eligible':summary_failure(args.summary,args.phase,str(exc),Failure.UNSUPPORTED if isinstance(exc,Unsupported) else Failure.SETUP)
        parser.exit(2,str(exc)+'\n')

if __name__=='__main__':raise SystemExit(main())
