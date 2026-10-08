#!/usr/bin/env python3
"""Counterexample bundles (P08): replayable failures versus unsolved automation outcomes.

A bundle holds the input, the full schedule prefix, the violated contract, AIR candidate
sites with approximate Zig lines, and a one-command replay. Only a failure that a fresh
replay reproduced is a `counterexample`. Timeouts, caps, fuel exhaustion, unspecified results
and unsupported inputs are `unsolved`, never a program bug.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 1


def load_schedules():
    """Reuse loaded modules so schedules.py, diff-report.py and this script share one Invalid class."""
    loaded = sys.modules.get('air2lean_schedules')
    if loaded is not None: return loaded
    spec = importlib.util.spec_from_file_location('air2lean_schedules', ROOT/'scripts/schedules.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    sys.modules['air2lean_schedules'] = module
    return module


CLI = load_schedules()
REPORT = CLI.REPORT
Invalid = REPORT.Invalid

# --- Verdicts -----------------------------------------------------------------------------

COUNTEREXAMPLE, CANDIDATE, UNSOLVED, NO_FAILURE, SETUP = 'counterexample', 'candidate', 'unsolved', 'no_failure', 'setup_failure'

CONTRACTS = {
    'illegal': ('no_illegal_behaviour', 'No illegal behaviour that ReleaseSafe does not check: data race, dead, '
                'out-of-bounds or misaligned access, double free, minInt @rem/@mod -1.'),
    'deadlock': ('no_deadlock', 'While a thread is unfinished, some thread can make progress.'),
    'model_panic': ('no_safety_panic', 'No ReleaseSafe safety check or explicit panic trips.'),
    'postcondition': ('postcondition', 'The stated postcondition holds for the generated function on this input.'),
    'mismatch': ('native_correspondence', 'The model outcome equals the native Zig outcome on this input.'),
}

# Automation limits: inconclusive by construction, never evidence of a program bug.
UNSOLVED_REASONS = {
    'timeout', 'replay_timeout', 'replay_not_reproduced', 'search_cap', 'enumeration_truncated',
    'prefix_cap', 'bounded_no_result', 'unspecified_result', 'unsupported_timer', 'host_difference',
    'unsupported', 'search_exhausted', 'no_input_satisfies_precondition',
}
SETUP_REASONS = {'input_failure', 'native_harness_failure', 'replay_error', 'lean_error'}
GOAL_UNSOLVED = {'bounded': 'search_exhausted', 'no_result': 'bounded_no_result', 'timeout': 'timeout',
                 'no_input': 'no_input_satisfies_precondition', 'unsupported': 'unsupported'}


def verdict(*, kind=None, status=None, automation=None, replay=None, tree=None, goal=None):
    """The one mapping from typed outcomes to a P08 verdict. Returns (classification, reason, contract).

    `kind` is a model observation kind (diff-report Kind values), `status` a differential Status
    value, `automation` an automation limit or setup failure, `tree` an enumeration result with
    no failing execution, `replay` a replay status (`verified`, `not_reproduced`, `timeout`,
    `error`, `not_run`, `unavailable`). Keep every outcome-to-verdict decision here so it can
    switch to the V06 outcome taxonomy in one place.
    """
    K, S = REPORT.Kind, REPORT.Status
    if tree is not None:
        # A failure-free tree is clean only when complete and every execution finished.
        if tree['truncated']: automation = 'enumeration_truncated'
        elif tree['saw_no_result']: automation = 'bounded_no_result'
        else: return NO_FAILURE, 'no_failing_execution_in_bounded_tree', None
    if automation is not None:
        if automation in SETUP_REASONS: return SETUP, automation, None
        if automation not in UNSOLVED_REASONS: raise Invalid(f'unknown automation outcome {automation}')
        return UNSOLVED, automation, None
    failure = None
    if goal is not None:
        # A Lean goal search: only a violating input is a failure; a bounded search that finds none proves nothing.
        if goal == 'violated': failure = 'postcondition'
        elif goal == 'exhaustive': return NO_FAILURE, 'exhaustive_domain_no_violation', None
        elif goal in GOAL_UNSOLVED: return UNSOLVED, GOAL_UNSOLVED[goal], None
        else: raise Invalid(f'unknown goal outcome {goal}')
    elif status is not None:
        status = S(status)
        if status in (S.INPUT_FAILURE, S.NATIVE_HARNESS_FAILURE): return SETUP, status.value, None
        if status == S.SKIPPED: raise Invalid('skipped rows carry no outcome')
        unsolved = {S.SEARCH_CAP: 'search_cap', S.BOUNDED_NO_RESULT: 'bounded_no_result',
                    S.UNSPECIFIED: 'unspecified_result', S.UNSPECIFIED_TIMER: 'unsupported_timer',
                    S.HOST: 'host_difference'}
        if status in unsolved: return UNSOLVED, unsolved[status], None
        if status == S.MISMATCH: failure = 'mismatch'
        elif status == S.ILLEGAL: failure = 'illegal'
        else: return NO_FAILURE, status.value, None
    elif kind is not None:
        kind = K(kind)
        unsolved = {K.SEARCH_CAP: 'search_cap', K.BOUNDED_NO_RESULT: 'bounded_no_result', K.UNSPECIFIED: 'unspecified_result',
                    K.UNSPECIFIED_TIMER: 'unsupported_timer'}
        if kind in unsolved: return UNSOLVED, unsolved[kind], None
        if kind in (K.INPUT_FAILURE, K.NATIVE_HARNESS_FAILURE): return SETUP, kind.value, None
        if kind in (K.ILLEGAL, K.DEADLOCK, K.MODEL_PANIC): failure = kind.value
        else: return NO_FAILURE, kind.value, None
    else:
        raise Invalid('verdict needs an outcome')
    contract = failure
    if replay == 'verified': return COUNTEREXAMPLE, 'replayed_failure', contract
    if replay == 'timeout': return UNSOLVED, 'replay_timeout', contract
    if replay == 'not_reproduced': return UNSOLVED, 'replay_not_reproduced', contract
    if replay == 'error': return SETUP, 'replay_error', contract
    return CANDIDATE, 'failure_not_replayed', contract


def is_failure_kind(kind):
    return verdict(kind=kind, replay='verified')[0] == COUNTEREXAMPLE

# --- Localization -------------------------------------------------------------------------

MEMORY_TAGS = re.compile(r'(load|store|store_safe|atomic_.*|cmpxchg_.*|memcpy|memmove|memset.*|ptr_elem_val|ret_load)\Z')
DEADLOCK_CALL = re.compile(r'\.(join|wait|timedWait|lock|lockShared)(__anon_\d+)?\Z')
FREE_CALL = re.compile(r'\.(free|destroy)(__anon_\d+)?\Z')
ARITH = {'overflow': {'add_safe', 'sub_safe', 'mul_safe', 'intcast_safe', 'int_from_float_safe'},
         'divByZero': {'div_trunc', 'div_floor', 'div_exact', 'rem', 'mod'},
         'unreachable': {'unreach'}}
SITE_FAILURES = ('illegal', 'deadlock', 'model_panic')
MAX_FUNCTIONS = 64
MAX_SITES = 200


def panic_ctor(func):
    """The `Zig.Error` constructor a noreturn panic-handler call raises (panic-policy.tsv)."""
    if func == 'debug.defaultPanic': return 'panic'
    if not func.startswith("debug.FullPanic((function 'defaultPanic'))."): return None
    return REPORT.PANICS.get(func.rsplit('.', 1)[-1].split('__anon_')[0])


def site_matches(inst, failure, ctor):
    tag = inst.get('tag', ''); callee = inst.get('callee') if isinstance(inst.get('callee'), dict) else {}
    func = callee.get('func', '') if isinstance(callee.get('func'), str) else ''
    if failure == 'illegal':
        return bool(MEMORY_TAGS.fullmatch(tag)) or tag in ('rem', 'mod') or (tag == 'call' and bool(FREE_CALL.search(func)))
    if failure == 'deadlock':
        return tag == 'call' and bool(DEADLOCK_CALL.search(func))
    if failure == 'model_panic':
        return (tag == 'call' and callee.get('noreturn') is True and panic_ctor(func) == ctor) or tag in ARITH.get(ctor, ())
    return False


def valid_src(src):
    return src if isinstance(src, dict) and isinstance(src.get('file'), str) and type(src.get('decl_line')) is int else None


def span_of(scope):
    """I05 source span (docs/diagnostics.md): statement, declaration, or unavailable_in_AIR."""
    src = scope['src']
    if src is None: return None, 'unavailable_in_AIR'
    module = src.get('module') if isinstance(src.get('module'), str) else None
    if scope['line'] is None:
        return dict(file=src['file'], module=module, line=src['decl_line'], column=None), 'declaration'
    return dict(file=src['file'], module=module, line=src['decl_line'] + scope['line'] - 1, column=scope['column']), 'statement'


def instructions(body, state, inlined=False, scope=None):
    """Lexical walk yielding (inst, legacy line, inlined, (span, status)).

    `state['line']` is the nearest preceding non-inlined dbg_stmt line (legacy, approximate). The span
    follows the exporter's `src`/`column`: the nearest preceding dbg_stmt in the instruction's own inline
    scope; branch bodies start from their parent's statement, an inlined body from its callee's `src`."""
    scope = scope if scope is not None else dict(src=None, line=None, column=None)
    for inst in body if isinstance(body, list) else ():
        if not isinstance(inst, dict): continue
        if inst.get('tag') == 'dbg_stmt' and type(inst.get('line')) is int:
            if not inlined: state['line'] = inst['line']
            scope['line'] = inst['line']; scope['column'] = inst['column'] if type(inst.get('column')) is int else None
        yield inst, state['line'], inlined, span_of(scope)
        if inst.get('tag') == 'dbg_inline_block':
            inner = dict(src=valid_src(inst.get('src')), line=None, column=None)
            yield from instructions(inst.get('body'), state, True, inner)
            continue
        for key in ('body', 'then', 'else'):
            yield from instructions(inst.get(key), state, inlined, dict(scope))
        for case in inst.get('cases', ()) if isinstance(inst.get('cases'), list) else ():
            if isinstance(case, dict): yield from instructions(case.get('body'), state, inlined, dict(scope))


def decl_line(root, example, name):
    """1-based line of `fn <short>(` in the example's own source, or None (std code, ambiguous)."""
    module, _, short = name.rpartition('.')
    if not module or not REPORT.IDENT.fullmatch(module) or not REPORT.IDENT.fullmatch(short): return None, None
    path = root/'examples'/example/f'{module}.zig'
    if not path.is_file(): return None, None
    pattern = re.compile(r'\s*(pub\s+)?(export\s+)?(inline\s+)?fn\s+' + re.escape(short) + r'\s*\(')
    hits = [i for i, text in enumerate(path.read_text().splitlines(), 1) if pattern.match(text)]
    return (str(path.relative_to(root)), hits[0]) if len(hits) == 1 else (None, None)


def localize(root, example, function, failure, ctor, air_dir=None):
    """Candidate AIR sites for a failure kind across the root and its callees/spawned workers.

    The model reports only the `Zig.Error` constructor, not the faulting instruction, and the
    generated Lean carries no per-instruction source map, so the result is a candidate set."""
    air_dir = Path(air_dir) if air_dir else root/'tests/golden'/example/'air'
    docs = {}
    if air_dir.is_dir():
        for path in sorted(air_dir.glob('*.json')):
            doc = REPORT.decode(CLI.read_bytes(path).decode('utf-8'))
            if isinstance(doc, dict) and isinstance(doc.get('name'), str): docs[doc['name']] = (path, doc)
    name = next((n for n in docs if n.rpartition('.')[2] == function and n.startswith(example + '.')), None) or \
        next((n for n in docs if n.rpartition('.')[2] == function), None)
    out = dict(function=name, air_dir=str(air_dir.relative_to(root)) if air_dir.is_relative_to(root) else str(air_dir),
               localization='candidate_sites' if failure in SITE_FAILURES else 'function_only',
               source_map='unavailable_in_AIR',
               zig_line_basis='source_span when the AIR carries src; else dbg_stmt line relative to the fn declaration (approximate)',
               functions=[], candidate_sites=[], sites_truncated=False)
    if name is None: return out
    queue, seen = [name], {name}
    while queue:
        current = queue.pop(0)
        if current not in docs: continue
        path, doc = docs[current]
        zig_file, decl = decl_line(root, example, current)
        top = dict(src=valid_src(doc.get('src')), line=None, column=None)
        fn_span = span_of(top)
        if fn_span[0] is not None: out['source_map'] = 'exact_statement'
        out['functions'].append(dict(name=current, air_file=str(path.relative_to(root)) if path.is_relative_to(root) else str(path),
                                     zig_file=zig_file, zig_decl_line=decl, source_span=fn_span[0], source_span_status=fn_span[1]))
        for inst, line, inlined, (span, status) in instructions(doc.get('body'), {'line': None}, scope=dict(top)):
            callee = inst.get('callee') if isinstance(inst.get('callee'), dict) else {}
            for target in (callee.get('func'), callee.get('comptime_fn')):
                if isinstance(target, str) and target in docs and target not in seen and len(seen) < MAX_FUNCTIONS:
                    seen.add(target); queue.append(target)
            if out['localization'] != 'candidate_sites' or not site_matches(inst, failure, ctor): continue
            if len(out['candidate_sites']) >= MAX_SITES: out['sites_truncated'] = True; continue
            site = dict(function=current, air_id=inst.get('id'), tag=inst.get('tag'), dbg_line=line, inlined=inlined,
                        zig_file=zig_file, zig_line=decl + line - 1 if decl and line else None,
                        source_span=span, source_span_status=status)
            if status == 'statement' and not inlined: site['zig_line'] = span['line']
            if callee.get('func'): site['callee'] = callee['func']
            out['candidate_sites'].append(site)
    out['functions_truncated'] = len(seen) >= MAX_FUNCTIONS
    return out

# --- Replay -------------------------------------------------------------------------------


def sources_digest(sources):
    return hashlib.sha256(json.dumps(sources, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def run_replay(root, request, expected, binary, timeout):
    """Run one replay request; the caller's `expected` is compared here, not in the model."""
    sources = REPORT.source_hashes(root)
    try:
        response = CLI.invoke(Path(binary).resolve(), request, timeout)
        CLI.validate_response(response, request)
    except CLI.Timeout as error: return dict(status='timeout', detail=str(error))
    except FileNotFoundError as error: return dict(status='unavailable', detail=str(error))
    except (Invalid, OSError, UnicodeError) as error: return dict(status='error', detail=str(error))
    if not REPORT.json_equal(sources, REPORT.source_hashes(root)): return dict(status='error', detail='sources changed during replay')
    entry = response['executions'][0]
    actual = dict(line=entry['observation']['legacy_line'], kind=entry['observation']['kind'], options=entry['options'])
    same = all(REPORT.json_equal(actual[k], expected[k]) for k in ('line', 'kind', 'options'))
    return dict(status='verified' if same else 'not_reproduced', observed=actual)


def replay_request(request, prefix):
    return dict(schema=1, mode='replay', example=request['example'], function=request['function'], input=request['input'],
                fuel=request['fuel'], node_cap=1, prefix_cap=request['prefix_cap'], prefix=prefix)

# --- Sequential Lean replay and goal search (no Zig) --------------------------------------


def load_eval():
    loaded = sys.modules.get('air2lean_lean_eval')
    if loaded is not None: return loaded
    spec = importlib.util.spec_from_file_location('air2lean_lean_eval', ROOT/'scripts/lean-eval.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    sys.modules['air2lean_lean_eval'] = module
    return module


EVAL = load_eval()


def gen_path(root, example, gen=None):
    return Path(gen) if gen else root/'Proofs'/(example[:1].upper() + example[1:])/'Gen.lean'


def air_signedness(root, example, function, air_dir=None):
    """(param signed flags, result signed) from the golden AIR, or None when it is unavailable."""
    base = Path(air_dir) if air_dir else root/'tests/golden'/example/'air'
    path = base/f'{example}.{function}.json'
    if not path.is_file(): return None
    doc = REPORT.decode(CLI.read_bytes(path).decode('utf-8'))
    types = doc.get('types') if isinstance(doc, dict) else None
    if not isinstance(types, list) or not isinstance(doc.get('params'), list): return None
    flag = lambda i: bool(types[i].get('signed')) if type(i) is int and 0 <= i < len(types) and isinstance(types[i], dict) else False
    return [flag(i) for i in doc['params']], flag(doc.get('ret'))


def lean_request(root, example, function, raw_input, expected_line, *, gen=None, spec=None, pre=None, air_dir=None):
    """A replay request for a plain Zig.Result function, or None when the shape is unsupported."""
    path = gen_path(root, example, gen)
    if not path.is_file() or not isinstance(raw_input, list): return None
    try: params, ret = EVAL.signature(path.read_text(), function)
    except EVAL.Unsupported: return None
    if len(params) != len(raw_input): return None
    args = []
    for (_, t), value in zip(params, raw_input):
        if type(value) is bool: value = int(value)
        if type(value) is not int: return None
        args.append(value % EVAL.domain_size(t))
    sign = air_signedness(root, example, function, air_dir)
    return dict(gen=str(path.relative_to(root)) if path.is_relative_to(root) else str(path), gen_sha256=EVAL.sha256(path),
                example=example, function=function, args=args, spec=spec, pre=pre,
                signed_result=bool(sign and sign[1]), signedness='air' if sign else 'assumed_unsigned',
                expected=dict(line=expected_line, violation=spec is not None))


def lean_block(request):
    return dict(status='not_run', kind='lean_sequential', request=request,
                command=['python3', 'scripts/counterexample.py', 'replay', '--bundle', '<this bundle>'])


def lean_confirm(root, request, timeout, runner=None):
    """Evaluate the request in a fresh Lean process and compare with the expectation."""
    path = Path(request['gen'])
    path = path if path.is_absolute() else root/path
    if not path.is_file() or EVAL.sha256(path) != request['gen_sha256']: return dict(status='error', detail='generated Lean changed or is missing')
    try:
        params, ret = EVAL.signature(path.read_text(), request['function'])
        text = EVAL.driver(EVAL.namespace_of(path.read_text()), request['function'], params, ret, [tuple(request['args'])],
                           signed_ret=request['signed_result'], spec=request['spec'], pre=request['pre'], print_all=True)
    except EVAL.Unsupported as error: return dict(status='error', detail=str(error))
    out = EVAL.run(root, path, text, timeout=timeout, **(dict(runner=runner) if runner else {}))
    if out['status'] == 'timeout': return dict(status='timeout', detail=out['detail'])
    if out['status'] != 'ok': return dict(status='error', detail=out['detail'])
    lines = {l[0]: l for l in out['lines']}
    if 'N' in lines: observed = dict(line='{"diverge":true}', kind='bounded_no_result')
    elif 'O' in lines: observed = dict(line=lines['O'][2], kind=EVAL.obs_kind(lines['O'][2]))
    else: return dict(status='error', detail='no observation')
    violated = 'V' in lines
    same = observed['line'] == request['expected']['line'] and violated == request['expected']['violation']
    return dict(status='verified' if same else 'not_reproduced', observed=observed, violated=violated)


def goal_bundle(root, example, function, spec, pre=None, *, gen=None, max_inputs=4096, seed=0, timeout=300,
                replay=True, air_dir=None, runner=None):
    """Search small inputs for a violation of `spec`; the violation is replayed in a fresh Lean process."""
    path = gen_path(root, example, gen)
    source = dict(kind='lean_goal_search', gen=str(path), spec=spec, pre=pre, max_inputs=max_inputs, seed=seed, timeout=timeout)
    common = dict(root=root, source=source, example=example, function=function, input_index=None, input_value=None,
                  input_sha256=None, observed=None, air_dir=air_dir, statement=spec)

    def unsolved(goal):
        return bundle(judgement=verdict(goal=goal), **common)
    try:
        text = path.read_text()
        params, ret = EVAL.signature(text, function)
        namespace = EVAL.namespace_of(text)
    except (EVAL.Unsupported, OSError) as error:
        source['detail'] = str(error)
        return unsolved('unsupported')
    sign = air_signedness(root, example, function, air_dir)
    signed = sign[0] if sign else [False] * len(params)
    source.update(gen_sha256=EVAL.sha256(path), signedness='air' if sign else 'assumed_unsigned', params=[n for n, _ in params])
    rows, exhaustive = EVAL.inputs([t for _, t in params], max_inputs, seed)
    source.update(candidate_inputs=len(rows), exhaustive_domain=exhaustive)
    driver = EVAL.driver(namespace, function, params, ret, rows, signed_ret=bool(sign and sign[1]), spec=spec, pre=pre)
    out = EVAL.run(root, path, driver, timeout=timeout, **(dict(runner=runner) if runner else {}))
    if out['status'] == 'timeout': return unsolved('timeout')
    if out['status'] != 'ok':
        source['detail'] = out['detail']
        return bundle(judgement=verdict(automation='lean_error'), **common)
    summary = next((l for l in out['lines'] if l[0] == 'S'), None)
    if summary is None:
        source['detail'] = 'driver printed no summary'
        return bundle(judgement=verdict(automation='lean_error'), **common)
    checked, skipped, no_result, violations = map(int, summary[1:5])
    source.update(checked=checked, skipped_by_precondition=skipped, no_result=no_result)
    hit = next((l for l in out['lines'] if l[0] == 'V'), None)
    if hit is None:
        if checked == 0: return unsolved('no_input')
        if no_result: return unsolved('no_result')
        return unsolved('exhaustive' if exhaustive else 'bounded')
    row = rows[int(hit[1])]
    raw = [bool(v) if t[0] == 'bool' else EVAL.to_signed(v, t, sg) for v, (_, t), sg in zip(row, params, signed)]
    request = dict(gen=str(path.relative_to(root)) if path.is_relative_to(root) else str(path), gen_sha256=source['gen_sha256'],
                   example=example, function=function, args=list(row), spec=spec, pre=pre,
                   signed_result=bool(sign and sign[1]), signedness=source['signedness'],
                   expected=dict(line=hit[2], violation=True))
    info = lean_block(request)
    if replay: info.update(lean_confirm(root, request, timeout, runner))
    common.update(input_value=raw, input_sha256=hashlib.sha256(json.dumps(raw, separators=(',', ':')).encode()).hexdigest(),
                  input_index=int(hit[1]), observed=dict(kind=EVAL.obs_kind(hit[2]), line=hit[2]))
    return bundle(replay=info, judgement=verdict(goal='violated', replay=info['status']), **common)


# --- Bundles ------------------------------------------------------------------------------


def bundle(root, *, source, example, function, input_index, input_value, input_sha256, observed, judgement,
           schedule=None, native=None, replay=None, air_dir=None, sources=None, statement=None):
    classification, reason, contract = judgement
    failure_kind = contract or (observed or {}).get('kind')
    ctor = (observed or {}).get('line', '')
    ctor = REPORT.decode(ctor).get('fail', '').removeprefix('Zig.Error.') if ctor.startswith('{') else None
    return dict(schema=SCHEMA, qualified=False, classification=classification, reason=reason,
                  is_program_bug_evidence=classification == COUNTEREXAMPLE,
                  source=source, example=example, function=function, input_index=input_index,
                  input=input_value, input_sha256=input_sha256, observed=observed, native=native, schedule=schedule,
                  contract=dict(id=CONTRACTS[contract][0], statement=statement or CONTRACTS[contract][1]) if contract else None,
                  location=localize(root, example, function, failure_kind, ctor, air_dir),
                  sources_sha256=sources_digest(sources if sources is not None else REPORT.source_hashes(root)),
                  replay=replay or dict(status='unavailable'))


def schedule_bundle(root, receipt_path, index=None, *, replay=False, binary=None, timeout=60, air_dir=None):
    receipt, raw = CLI.load_receipt(root, receipt_path, REPORT.source_hashes(root))
    request, result = receipt['request'], receipt['result']
    if request['mode'] != 'enumerate': raise Invalid('not an enumeration receipt')
    executions = result['executions']
    if index is None:
        index = next((i for i, e in enumerate(executions) if is_failure_kind(e['observation']['kind']) and e['trace_complete']),
                     next((i for i, e in enumerate(executions) if is_failure_kind(e['observation']['kind'])), None))
    source = dict(kind='schedule_receipt', path=str(receipt_path), sha256=hashlib.sha256(raw).hexdigest(),
                  runs=result['runs'], truncated=result['truncated'], exploration_complete=result['exploration_complete'],
                  fuel=request['fuel'], node_cap=request['node_cap'], prefix_cap=request['prefix_cap'])
    common = dict(source=source, example=request['example'], function=request['function'], input_index=receipt['input_index'],
                  input_value=request['input'], input_sha256=receipt['input_sha256'], air_dir=air_dir,
                  sources=receipt['runner_runtime_sources'])
    if index is None:
        return bundle(root, observed=None, judgement=verdict(tree=result), **common)
    CLI.nat(index, len(executions) - 1, 'execution index')
    entry = executions[index]
    observed = dict(kind=entry['observation']['kind'], line=entry['observation']['legacy_line'])
    expected = dict(observed, options=entry['options'])
    schedule = dict(execution_index=index, prefix=entry['prefix'], options=entry['options'],
                    choice_count=entry['choice_count'], trace_complete=entry['trace_complete'], fuel=request['fuel'])
    if not entry['trace_complete']:
        return bundle(root, observed=observed, schedule=schedule, judgement=verdict(automation='prefix_cap'), **common)
    replay_info = replay_block(replay_request(request, entry['prefix']), expected, binary)
    if replay:
        replay_info.update(run_replay(root, replay_info['request'], expected, binary, timeout))
    judgement = verdict(kind=observed['kind'], replay=replay_info['status'])
    return bundle(root, observed=observed, schedule=schedule, replay=replay_info, judgement=judgement, **common)


def replay_block(request, expected, binary):
    binary = Path(binary or ROOT/'tests/diff/.lake/build/bin/schedules')
    shown = binary.relative_to(ROOT) if binary.is_absolute() and binary.is_relative_to(ROOT) else binary
    return dict(status='not_run', request=request, expected=expected,
                command=['python3', 'scripts/counterexample.py', 'replay', '--bundle', '<this bundle>', '--binary', str(shown)])


def case_bundle(root, summary, example, function, index, *, replay=False, binary=None, timeout=60, air_dir=None):
    data = REPORT.read_summary(summary)
    if data.get('complete') is not True: raise Invalid('incomplete differential summary')
    # A replay must run the code that produced the summary, as `schedules.py replay --summary` requires.
    if replay: CLI.bound_context(data, REPORT.source_hashes(root))
    case = None
    for line in REPORT.lines(Path(str(summary)+'.jsonl'), max_bytes=REPORT.MAX_REPORT):
        row = REPORT.decode(line)
        if isinstance(row, dict) and row.get('example') == example and row.get('function') == function and row.get('input_index') == index and row.get('status') != 'skipped':
            if case is not None: raise Invalid('ambiguous differential case')
            case = row
    if case is None: raise Invalid('missing differential case')
    raw_input, digest = CLI.current_input(root, example, function, index)
    native_line = CLI.row(root/'tests/diff/out/zig'/example/f'{function}.jsonl', index).strip()
    model_line = CLI.row(root/'tests/diff/out/lean'/example/f'{function}.jsonl', index).strip()
    for value, key in ((digest, 'input_sha256'), (hashlib.sha256((native_line+'\n').encode()).hexdigest(), 'native_sha256'),
                       (hashlib.sha256((model_line+'\n').encode()).hexdigest(), 'model_sha256')):
        if value != case.get(key): raise Invalid(f'stale differential evidence: {key}')
    observed = dict(kind=case['model_kind'], line=model_line)
    native = dict(kind=case['native_kind'], line=native_line)
    source = dict(kind='differential_case', path=str(summary), status=case['status'],
                  sha256=hashlib.sha256(Path(str(summary)+'.jsonl').read_bytes()).hexdigest())
    search, schedule, replay_info = case.get('schedule'), None, None
    sources = data.get('runner_runtime_sources') if isinstance(data.get('runner_runtime_sources'), dict) else REPORT.source_hashes(root)
    if isinstance(search, dict) and search.get('status') == 'witness':
        options, sparse = search['options'], search['prefix']
        prefix = sparse + [0] * (len(options) - len(sparse))
        schedule = dict(prefix=prefix, options=options, fuel=search['fuel'], search_status='witness')
        request = replay_request(dict(example=example, function=function, input=raw_input, fuel=search['fuel'], prefix_cap=4096), prefix)
        expected = dict(observed, options=options)
        replay_info = replay_block(request, expected, binary)
        if replay: replay_info.update(run_replay(root, request, expected, binary, timeout))
    elif isinstance(search, dict):
        schedule = dict(search_status=search['status'], runs=search['runs'], cap=search['cap'], fuel=search['fuel'])
    if replay_info is None:
        request = lean_request(root, example, function, raw_input, model_line)
        if request is not None:
            replay_info = lean_block(request)
            if replay: replay_info.update(lean_confirm(root, request, timeout))
    if replay_info is None:
        # Unsupported shape or unmatched concurrent case: rerun the differential runner for this example.
        replay_info = dict(status='unavailable', command=['env', f'AIR2LEAN_EXAMPLES={example}', 'scripts/diff.sh'],
                           note=f'compare row {index} of tests/diff/out/{{zig,lean}}/{example}/{function}.jsonl; needs Zig')
    # A Lean replay re-evaluates the model side only; the native line stays recorded evidence from the diff run.
    judgement = verdict(status=case['status'], replay=replay_info['status'])
    return bundle(root, source=source, example=example, function=function, input_index=index, input_value=raw_input,
                  input_sha256=digest, observed=observed, native=native, schedule=schedule, replay=replay_info,
                  judgement=judgement, air_dir=air_dir, sources=sources)


def search_bundle(root, args):
    """Enumerate, then bundle the first replayable failing execution. A timeout is unsolved."""
    receipt = args.receipt_output or args.output.with_name(args.output.stem + '.receipt.json')
    enum = CLI.parser().parse_args(['enumerate', '--example', args.example, '--function', args.function,
                                    '--input-index', str(args.input_index), '--fuel', str(args.fuel),
                                    '--node-cap', str(args.node_cap), '--prefix-cap', str(args.prefix_cap),
                                    '--binary', str(args.binary), '--timeout', str(args.timeout), '--output', str(receipt)])
    try:
        CLI.execute(enum, root)
    except CLI.Timeout:
        raw_input, digest = CLI.current_input(root, args.example, args.function, args.input_index)
        source = dict(kind='schedule_search', fuel=args.fuel, node_cap=args.node_cap, prefix_cap=args.prefix_cap, timeout=args.timeout)
        return bundle(root, source=source, example=args.example, function=args.function, input_index=args.input_index,
                      input_value=raw_input, input_sha256=digest, observed=None, judgement=verdict(automation='timeout'),
                      air_dir=args.air_dir)
    return schedule_bundle(root, receipt, None, replay=not args.no_replay, binary=args.binary, timeout=args.timeout, air_dir=args.air_dir)


REPLAY_EXIT = {'verified': 0, 'not_reproduced': 1, 'timeout': 2, 'error': 3, 'unavailable': 3}


def replay_bundle(root, path, binary, timeout):
    """Re-run a bundle's embedded request. Exit: 0 reproduced, 1 not reproduced, 2 unsolved, 3 setup."""
    data = CLI.read_json(path)
    if type(data) is not dict or data.get('schema') != SCHEMA or data.get('qualified') is not False: raise Invalid('unsupported bundle')
    replay = data.get('replay') if isinstance(data.get('replay'), dict) else {}
    if 'request' not in replay:
        print(f"counterexample: nothing to replay ({data.get('classification')}: {data.get('reason')})", file=sys.stderr)
        return 2 if data.get('classification') == UNSOLVED else 3
    if data.get('sources_sha256') != sources_digest(REPORT.source_hashes(root)):
        print('counterexample: stale runner/runtime source fingerprints', file=sys.stderr); return 3
    if replay.get('kind') == 'lean_sequential':
        outcome = lean_confirm(root, replay['request'], timeout)
        print(f"REPLAY: status={outcome['status']} {data.get('example')}.{data.get('function')}#{data.get('input_index')} lean_sequential"
              f" observed={outcome.get('observed', {}).get('kind', '-')}")
        if outcome.get('detail'): print(f"counterexample: {outcome['detail']}", file=sys.stderr)
        return REPLAY_EXIT[outcome['status']]
    request, expected = replay['request'], replay['expected']
    if type(request) is not dict or request.get('mode') != 'replay' or 'expected' in request: raise Invalid('invalid replay request')
    outcome = run_replay(root, request, expected, binary, timeout)
    print(f"REPLAY: status={outcome['status']} {data.get('example')}.{data.get('function')}#{data.get('input_index')}"
          f" expected={expected['kind']} observed={outcome.get('observed', {}).get('kind', '-')}")
    if outcome.get('detail'): print(f"counterexample: {outcome['detail']}", file=sys.stderr)
    return REPLAY_EXIT[outcome['status']]


def headline(data):
    sites = data['location']['candidate_sites']
    lines = sorted({f"{s['zig_file'] or (s['source_span'] or {}).get('file')}:{s['zig_line']}" for s in sites if s['zig_line']})
    return (f"COUNTEREXAMPLE: classification={data['classification']} reason={data['reason']}"
            f" case={data['example']}.{data['function']}#{data['input_index']}"
            f" contract={(data['contract'] or {}).get('id', '-')} replay={data['replay']['status']}"
            f" sites={len(sites)} zig_lines={','.join(lines[:8]) or '-'} qualified=false")


def parser():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    subs = p.add_subparsers(dest='command', required=True)
    search = subs.add_parser('search', help='enumerate schedules, then bundle and replay the first failure')
    search.add_argument('--fuel', type=int, default=100000); search.add_argument('--node-cap', type=int, default=128)
    search.add_argument('--prefix-cap', type=int, default=4096); search.add_argument('--receipt-output', type=Path)
    search.add_argument('--no-replay', action='store_true')
    receipt = subs.add_parser('from-receipt', help='bundle an execution of a schedules.py enumeration receipt')
    receipt.add_argument('--receipt', type=Path, required=True); receipt.add_argument('--execution-index', type=int)
    case = subs.add_parser('from-case', help='bundle a differential case from a diff-report summary')
    case.add_argument('--summary', type=Path, required=True)
    for sub in (receipt, case): sub.add_argument('--replay', action='store_true')
    for sub in (search, case):
        sub.add_argument('--example', required=True); sub.add_argument('--function', required=True)
        sub.add_argument('--input-index', type=int, default=1)
    for sub in (search, receipt, case):
        sub.add_argument('--air-dir', type=Path); sub.add_argument('--output', type=Path, required=True)
    goal = subs.add_parser('goal-search', help='search small inputs for a violation of a stated postcondition (Lean, no Zig)')
    goal.add_argument('--example', required=True); goal.add_argument('--function', required=True)
    goal.add_argument('--spec', required=True, help='Lean Prop over the parameter names and r : Except Zig.Error T')
    goal.add_argument('--pre', help='Lean Prop over the parameters; inputs failing it are skipped')
    goal.add_argument('--gen', type=Path); goal.add_argument('--air-dir', type=Path); goal.add_argument('--output', type=Path, required=True)
    goal.add_argument('--max-inputs', type=int, default=4096); goal.add_argument('--seed', type=int, default=0)
    goal.add_argument('--no-replay', action='store_true'); goal.add_argument('--timeout', type=int, default=300)
    rep = subs.add_parser('replay', help='re-run a bundle; exit 0 reproduced, 1 not reproduced, 2 unsolved, 3 setup')
    rep.add_argument('--bundle', type=Path, required=True)
    for sub in (search, receipt, case, rep):
        sub.add_argument('--interpret', action='store_true', help='run schedules through the Lean interpreter (no native build)')
        sub.add_argument('--binary', type=Path, default=ROOT/'tests/diff/.lake/build/bin/schedules')
        sub.add_argument('--timeout', type=int, default=60)
    return p


def execute(args, root=ROOT):
    CLI.nat(args.timeout, 900, 'timeout')
    if args.timeout == 0: raise Invalid('timeout must be positive')
    if getattr(args, 'interpret', False): args.binary = root/'scripts/schedules-interpreted.sh'
    if args.command == 'replay': return replay_bundle(root, args.bundle, args.binary, args.timeout)
    if args.command == 'goal-search':
        if not 0 < args.max_inputs <= EVAL.MAX_CASES: raise Invalid(f'max-inputs must be in 1..{EVAL.MAX_CASES}')
        data = goal_bundle(root, args.example, args.function, args.spec, args.pre, gen=args.gen, max_inputs=args.max_inputs,
                           seed=args.seed, timeout=args.timeout, replay=not args.no_replay, air_dir=args.air_dir)
        if 'command' in data['replay']:
            data['replay']['command'] = [str(args.output) if c == '<this bundle>' else c for c in data['replay']['command']]
        REPORT.atomic_json(args.output, data)
        print(headline(data))
        return 0
    if args.command == 'search': data = search_bundle(root, args)
    elif args.command == 'from-receipt':
        data = schedule_bundle(root, args.receipt, args.execution_index, replay=args.replay, binary=args.binary,
                               timeout=args.timeout, air_dir=args.air_dir)
    else:
        data = case_bundle(root, args.summary, args.example, args.function, args.input_index, replay=args.replay,
                           binary=args.binary, timeout=args.timeout, air_dir=args.air_dir)
    if 'command' in data['replay']:
        data['replay']['command'] = [str(args.output) if c == '<this bundle>' else c for c in data['replay']['command']]
    REPORT.atomic_json(args.output, data)
    print(headline(data))
    return 0


def main():
    args = parser().parse_args()
    try: return execute(args)
    except (Invalid, OSError, UnicodeError, KeyError, TypeError, ValueError) as error:
        print(f'counterexample: {error}', file=sys.stderr)
        return 3


if __name__ == '__main__': raise SystemExit(main())
