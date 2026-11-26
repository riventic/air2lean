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
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

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
    'stack_overflow': ('stack_sufficient', 'Every call chain fits in the selected stack budget (STK-01).'),
    'model_panic': ('no_safety_panic', 'No ReleaseSafe safety check or explicit panic trips.'),
    'postcondition': ('postcondition', 'The stated postcondition holds for the generated function on this input.'),
    'trap': ('no_hardware_trap', 'No allowlisted inline-asm instruction faults (its AsmFault condition, ASM-04).'),
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
        elif status == S.STACK_OVERFLOW: failure = 'stack_overflow'
        else: return NO_FAILURE, status.value, None
    elif kind is not None:
        kind = K(kind)
        unsolved = {K.SEARCH_CAP: 'search_cap', K.BOUNDED_NO_RESULT: 'bounded_no_result', K.UNSPECIFIED: 'unspecified_result',
                    K.UNSPECIFIED_TIMER: 'unsupported_timer'}
        if kind in unsolved: return UNSOLVED, unsolved[kind], None
        if kind in (K.INPUT_FAILURE, K.NATIVE_HARNESS_FAILURE): return SETUP, kind.value, None
        if kind in (K.ILLEGAL, K.DEADLOCK, K.MODEL_PANIC, K.TRAP, K.STACK_OVERFLOW): failure = kind.value
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
    if failure == 'trap':
        return tag == 'assembly'
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
    scope; branch bodies start from their parent's statement, an inlined body from its callee's `src`.
    `state['chain']` holds the enclosing inline blocks' call sites (outermost first) at each yield."""
    scope = scope if scope is not None else dict(src=None, line=None, column=None)
    for inst in body if isinstance(body, list) else ():
        if not isinstance(inst, dict): continue
        if inst.get('tag') == 'dbg_stmt' and type(inst.get('line')) is int:
            if not inlined: state['line'] = inst['line']
            scope['line'] = inst['line']; scope['column'] = inst['column'] if type(inst.get('column')) is int else None
        yield inst, state['line'], inlined, span_of(scope)
        if inst.get('tag') == 'dbg_inline_block':
            inner = dict(src=valid_src(inst.get('src')), line=None, column=None)
            # The call site is the statement that holds the inlined call; `state['chain']` is the stack of
            # call sites from the outermost inline block to the innermost one, read by the consumer while
            # it handles a yielded instruction.
            chain = state.setdefault('chain', [])
            span, status = span_of(scope)
            chain.append(dict(call_site=span, call_site_status=status, callee_span=span_of(dict(inner))[0]))
            try: yield from instructions(inst.get('body'), state, True, inner)
            finally: chain.pop()
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
        walk_state = {'line': None}
        for inst, line, inlined, (span, status) in instructions(doc.get('body'), walk_state, scope=dict(top)):
            callee = inst.get('callee') if isinstance(inst.get('callee'), dict) else {}
            for target in (callee.get('func'), callee.get('comptime_fn')):
                if isinstance(target, str) and target in docs and target not in seen and len(seen) < MAX_FUNCTIONS:
                    seen.add(target); queue.append(target)
            if out['localization'] != 'candidate_sites' or not site_matches(inst, failure, ctor): continue
            if len(out['candidate_sites']) >= MAX_SITES: out['sites_truncated'] = True; continue
            site = dict(function=current, air_id=inst.get('id'), tag=inst.get('tag'), dbg_line=line, inlined=inlined,
                        zig_file=zig_file, zig_line=decl + line - 1 if decl and line else None,
                        source_span=span, source_span_status=status)
            if status == 'statement':
                # Exact when the span is the instruction's own statement; inside an inlined body it is the
                # callee's statement, in the callee's file.
                site['zig_line'] = span['line']
                if inlined: site['zig_file'] = span['file']
            if inlined:
                # Where the inlined code is reached from: every enclosing call site, outermost first. A body
                # whose callee exports no `src` keeps only these (`source_span` stays unavailable_in_AIR).
                site['inline_chain'] = [dict(c) for c in walk_state.get('chain', ())]
                site['call_site_span'] = site['inline_chain'][-1]['call_site'] if site['inline_chain'] else None
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


def shown(root, path):
    return str(path.relative_to(root)) if path.is_relative_to(root) else str(path)


def air_path(root, example, function, air_dir=None):
    """The function's exported AIR document (its type table resolves the value kinds), or None."""
    path = (Path(air_dir) if air_dir else root/'tests/golden'/example/'air')/f'{example}.{function}.json'
    return path if path.is_file() else None


def read_signature(gen, function, air):
    """(generated Lean text, EVAL.Signature) of `function`, resolved against the AIR document at `air` (or None)."""
    text = Path(gen).read_text()
    doc = REPORT.decode(CLI.read_bytes(air).decode('utf-8')) if air is not None else None
    return text, EVAL.signature(text, function, doc)


def eval_request(root, path, air, example, function, sig, args, spec, pre, expected):
    return dict(gen=shown(root, path), gen_sha256=EVAL.sha256(path), air=shown(root, air) if air else None,
                air_sha256=EVAL.sha256(air) if air else None, example=example, function=function, args=list(args),
                spec=spec, pre=pre, signedness='air' if sig.typed else 'assumed_unsigned', expected=expected)


def lean_request(root, example, function, raw_input, expected_line, *, gen=None, spec=None, pre=None, air_dir=None):
    """A replay request for a function the Lean evaluator covers. Raises EVAL.Unsupported with the reason
    when the function or the input row is outside it."""
    path = gen_path(root, example, gen)
    if not path.is_file(): raise EVAL.Unsupported(f'no generated Lean at {path}')
    air = air_path(root, example, function, air_dir)
    _, sig = read_signature(path, function, air)
    return eval_request(root, path, air, example, function, sig, sig.parse_args(raw_input), spec, pre,
                        dict(line=expected_line, violation=spec is not None))


def lean_block(request):
    return dict(status='not_run', kind='lean_sequential', request=request,
                command=['python3', 'scripts/counterexample.py', 'replay', '--bundle', '<this bundle>'])


def request_signature(root, request):
    """(Gen.lean path, its text, the signature, the argument values) of a stored request. The request is
    untrusted input: the generated Lean and the AIR document must be the hashed ones. Raises EVAL.Unsupported."""
    resolve = lambda p: Path(p) if Path(p).is_absolute() else root/p
    path, air = resolve(request['gen']), resolve(request['air']) if request.get('air') else None
    if not path.is_file() or EVAL.sha256(path) != request['gen_sha256']: raise EVAL.Unsupported('generated Lean changed or is missing')
    if air is not None and (not air.is_file() or EVAL.sha256(air) != request.get('air_sha256')):
        raise EVAL.Unsupported('the AIR document changed or is missing')
    text, sig = read_signature(path, request['function'], air)
    return path, text, sig, sig.parse_args(request['args'])


def lean_evaluate(root, request, timeout, runner=None, given=None):
    """One fresh Lean process on the request's input: `status='ok'` with the observation and whether the
    postcondition is violated, else `timeout`/`error`. With `given` (a recorded outcome) the function is not
    called and the postcondition is decided on that outcome."""
    try:
        path, text, sig, args = request_signature(root, request)
        driver = EVAL.driver(EVAL.namespace_of(text), sig, [tuple(args)], spec=request['spec'], pre=request['pre'], print_all=True,
                             given=[given] if given is not None else None)
    except EVAL.Unsupported as error: return dict(status='error', detail=str(error))
    out = EVAL.run(root, path, driver, timeout=timeout, **(dict(runner=runner) if runner else {}))
    if out['status'] == 'timeout': return dict(status='timeout', detail=out['detail'])
    if out['status'] != 'ok': return dict(status='error', detail=out['detail'])
    lines = {l[0]: l for l in out['lines']}
    if 'N' in lines: observed = dict(line='{"diverge":true}', kind='bounded_no_result')
    elif 'O' in lines: observed = dict(line=lines['O'][2], kind=EVAL.obs_kind(lines['O'][2]))
    else: return dict(status='error', detail='no observation (the input does not satisfy the precondition)')
    return dict(status='ok', observed=observed, violated='V' in lines)


def lean_confirm(root, request, timeout, runner=None):
    """Evaluate the request in a fresh Lean process and compare with the expectation."""
    out = lean_evaluate(root, request, timeout, runner)
    if out['status'] != 'ok': return out
    same = out['observed']['line'] == request['expected']['line'] and out['violated'] == request['expected']['violation']
    return dict(out, status='verified' if same else 'not_reproduced')


# --- Zig-side replay ----------------------------------------------------------------------
# The Lean replay re-evaluates the model only. This one also runs the native Zig program on the
# same input through the production differential harness (tests/diff/common.zig: fork per call,
# panic kinds, JSON rendering) and compares the two outcome lines the way diff-report does. A
# stated postcondition is then decided on the outcome the native program returned.

HARNESS = '''const std = @import("std");
const common = @import("common");
const target = @import("target");
comptime {{ _ = target; }} // analyze the target's `export fn`s
pub const panic = common.panic;
{decl}
const Args = std.meta.ArgsTuple(@TypeOf({ref}));
const args: Args = .{{ {args} }};
pub fn main() !void {{
    var gpa_state = std.heap.DebugAllocator(.{{}}){{}};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();
    try common.makePath("tests/diff/out/zig/target");
    try common.forEachLine(gpa, "target", "{function}", struct {{
        fn call(_: std.mem.Allocator, _: []std.json.Value, writer: anytype) !void {{
            const outcome = try common.forkCall(Args, args, {ref}, {quote});
            try common.writeResult(writer, outcome);
        }}
    }}.call);
}}
'''
ZIG_IDENT = re.compile(r'[A-Za-z_][A-Za-z0-9_]*\Z')


def native_request(root, source, function):
    """A Zig-side replay request for the `export fn`/`pub fn` `function` of `source`. Raises EVAL.Unsupported."""
    source = Path(source)
    source = source if source.is_absolute() else root/source
    if not source.is_file() or not ZIG_IDENT.fullmatch(function): raise EVAL.Unsupported(f'no Zig function {function} in {source}')
    text = source.read_text()
    exported = re.search(r'^\s*export\s+fn\s+' + re.escape(function) + r'\s*\(', text, re.M)
    public = re.search(r'^\s*pub\s+fn\s+' + re.escape(function) + r'\s*\(', text, re.M)
    if bool(exported) == bool(public): raise EVAL.Unsupported(f'{function} is not exactly one `export fn` or `pub fn` of {source}')
    return dict(source=shown(root, source), source_sha256=EVAL.sha256(source), function=function, decl='export' if exported else 'pub')


def harness_text(request, sig, args):
    """The harness that calls the function on `args`: each value is a Zig literal of its kind, typed by the
    function's own parameter types (`std.meta.ArgsTuple`)."""
    function = request['function']
    if request['decl'] == 'export':
        # An `export fn` of another module is reached through its C-ABI declaration.
        ref, params = function, ', '.join(f'p{k}: {t.extern()}' for k, t in enumerate(sig.types))
        decl = f'extern fn {function}({params}) {sig.ret.extern()};'
    else:
        ref, decl = 'target.' + function, ''
    return HARNESS.format(decl=decl, function=function, ref=ref, args=', '.join(t.zig(v) for t, v in zip(sig.types, args)),
                          quote=str(sig.wide).lower())


def native_matches(native_line, model_line):
    """The differential comparison: equal values, or a native panic kind and its model constructor."""
    try: native, model = REPORT.decode(native_line), REPORT.decode(model_line)
    except Invalid: return False
    return isinstance(native, dict) and isinstance(model, dict) and REPORT.legacy_bucket(native, model, False) in ('ok', 'fail_match')


def native_confirm(root, request, lean, zig, model_line, timeout):
    """Build and run the harness with a stock `zig` on the input of the Lean request `lean`; compare its
    outcome line with the model's."""
    source = Path(request['source'])
    source = source if source.is_absolute() else root/source
    if not source.is_file() or EVAL.sha256(source) != request['source_sha256']: return dict(status='error', detail='Zig source changed or is missing')
    try:
        _, _, sig, args = request_signature(root, lean)
        harness = harness_text(request, sig, args)
    except EVAL.Unsupported as error: return dict(status='error', detail=str(error))
    try: version = subprocess.run([zig, 'version'], capture_output=True, text=True, timeout=timeout).stdout.strip()
    except subprocess.TimeoutExpired: return dict(status='timeout', detail='zig version timed out')
    except OSError as error: return dict(status='unavailable', detail=str(error))
    with tempfile.TemporaryDirectory(prefix='air2lean-native-') as temp:
        temp = Path(temp)
        (temp/'harness.zig').write_text(harness)
        inputs = temp/'tests/diff/target/inputs'; inputs.mkdir(parents=True)
        (inputs/f"{request['function']}.jsonl").write_text('[]\n')    # one call; the arguments are in the harness
        cmd = [zig, 'build-exe', *os.environ.get('AIR2LEAN_ROSETTA_LINK_FLAGS', '').split(),  # scripts/rosetta.sh
               '-OReleaseSafe', '-mcpu=baseline', f'-femit-bin={temp/"harness"}', '--cache-dir', str(temp/'cache'),
               '--dep', 'target', '--dep', 'common', '-Mroot=harness.zig', f'-Mtarget={source}', f'-Mcommon={root/"tests/diff/common.zig"}']
        try:
            built = subprocess.run(cmd, cwd=temp, capture_output=True, text=True, timeout=timeout)
            if built.returncode != 0: return dict(status='error', zig_version=version, detail='native build failed: ' + built.stderr.strip()[-400:])
            ran = subprocess.run([str(temp/'harness')], cwd=temp, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired: return dict(status='timeout', zig_version=version, detail='native build or run timed out')
        except OSError as error: return dict(status='error', zig_version=version, detail=str(error))
        out = temp/'tests/diff/out/zig/target'/f"{request['function']}.jsonl"
        lines = out.read_text().splitlines() if ran.returncode == 0 and out.is_file() else []
    if len(lines) != 1: return dict(status='error', zig_version=version, detail=f'native harness exit {ran.returncode}: {len(lines)} output lines')
    same = native_matches(lines[0], model_line)
    return dict(status='verified' if same else 'not_reproduced', zig_version=version, observed=dict(line=lines[0]), model_line=model_line)


def native_postcondition(root, lean, native_line, timeout, runner=None):
    """Decide the request's postcondition on the outcome the native program returned: the line is read as a
    value of the result type (or as the `Zig.Error` of its panic kind) and bound to `r` in a fresh Lean
    process, which does not call the model. `status`: violated, holds, undecided, timeout or error."""
    try:
        _, _, sig, _ = request_signature(root, lean)
        native = REPORT.decode(native_line)
        if isinstance(native, dict) and list(native) == ['ok']: given = ('ok', sig.ret.parse(native['ok'], sig.wide))
        elif isinstance(native, dict) and REPORT.PANICS.get(native.get('fail')) in EVAL.ERRORS: given = ('error', REPORT.PANICS[native['fail']])
        else: return dict(status='undecided', detail=f'the native outcome {native_line} is no outcome of the model')
    except EVAL.Mismatch as error: return dict(status='undecided', detail=f'the native outcome is no value of the result type: {error}')
    except (EVAL.Unsupported, Invalid) as error: return dict(status='error', detail=str(error))
    out = lean_evaluate(root, lean, timeout, runner, given=given)
    if out['status'] != 'ok': return out
    return dict(status='violated' if out['violated'] else 'holds', outcome=out['observed']['line'])


def confirm(root, replay, timeout, zig=None, runner=None):
    """Lean replay of `replay['request']`, then the native Zig run when the block carries one. Both must reproduce.

    A native outcome that differs from the Lean model line is not a program bug but a model or host
    disagreement: the replay is `not_reproduced`, so the case stays unsolved. With a stated postcondition
    the native outcome itself must also violate it (or satisfy it, when the model does)."""
    request = replay['request']
    outcome = lean_confirm(root, request, timeout, runner)
    native = replay.get('zig_native')
    if native is None: return outcome
    if outcome['status'] != 'verified': return dict(outcome, zig_native=dict(native, status='not_run'))
    result = native_confirm(root, native['request'], request, zig or default_zig(), outcome['observed']['line'], timeout)
    if result['status'] == 'verified' and request.get('spec') is not None:
        post = result['postcondition'] = native_postcondition(root, request, result['observed']['line'], timeout, runner)
        if post['status'] != ('violated' if request['expected']['violation'] else 'holds'):
            result['status'] = post['status'] if post['status'] in ('timeout', 'error') else 'not_reproduced'
    status = {'verified': 'verified', 'not_reproduced': 'not_reproduced', 'timeout': 'timeout'}.get(result['status'], 'error')
    return dict(outcome, status=status, zig_native=dict(native, **result))


def with_native(root, info, zig_source, function):
    """Attach the Zig-side replay request of `zig_source` to a lean_sequential block."""
    if zig_source is None: return info
    try:
        request = native_request(root, zig_source, function)
        _, _, sig, args = request_signature(root, info['request'])
        harness_text(request, sig, args)                  # an `export fn` takes C-ABI kinds only
    except EVAL.Unsupported as error: raise Invalid(f'{zig_source}: {error}') from None
    info['zig_native'] = dict(request=request, status='not_run')
    return info


# --- Differential-row replay (any shape the production harnesses cover) -------------------
# A sequential case of any example whose production harness (tests/diff/<ex>/harness.zig and
# tests/diff/Diff.lean) handles the function: structs, slices, memory buffers, optionals, error
# unions, floats, allocators. Both production runners are rerun on exactly the recorded input row
# in a scratch directory (every other function of the example gets an empty input file), and each
# fresh output line must equal the line the differential run recorded. Nothing is generated or
# re-derived: the shapes are exactly those the differential test supports, and a host difference
# (float bits, libm) is `not_reproduced`, never a program bug.

DIFF_SHARED = ('tests/diff/common.zig', 'tests/diff/compat.zig')


def diff_row_sources(root, example):
    """SHA-256 over the Zig sources a row replay builds: the example, its harness, the shared runner."""
    files = sorted(p for p in (root/'examples'/example).rglob('*.zig') if p.is_file() and not p.is_symlink())
    files += [root/'tests/diff'/example/'harness.zig', *(root/p for p in DIFF_SHARED)]
    return hashlib.sha256(json.dumps([[str(p.relative_to(root)), EVAL.sha256(p)] for p in files if p.is_file()]).encode()).hexdigest()


def diff_row_request(root, example, function, index, native_line, model_line):
    """A row-replay request, or None when the example has no production harness here."""
    if not REPORT.IDENT.fullmatch(example) or not REPORT.IDENT.fullmatch(function): return None
    if not (root/'tests/diff'/example/'harness.zig').is_file() or not (root/'examples'/example/f'{example}.zig').is_file(): return None
    inputs = root/'tests/diff'/example/'inputs'
    if not (inputs/f'{function}.jsonl').is_file(): return None
    row = CLI.row(inputs/f'{function}.jsonl', index)
    return dict(example=example, function=function, input_index=index, row=row.rstrip('\n'),
                row_sha256=hashlib.sha256(row.encode()).hexdigest(),
                sources_sha256=diff_row_sources(root, example), native_line=native_line, model_line=model_line)


def diff_row_block(request):
    return dict(status='not_run', kind='diff_row', request=request,
                command=['python3', 'scripts/counterexample.py', 'replay', '--bundle', '<this bundle>'])


def run_row(root, request, zig, difftest, timeout):
    """Run both production runners on the request's row. Returns (status, detail, zig_line, lean_line)."""
    example, function = request['example'], request['function']
    difftest = Path(difftest)
    if not difftest.is_file(): return 'unavailable', f'missing Lean runner {difftest}; run `(cd tests/diff && lake build difftest)`', None, None
    try: version = subprocess.run([zig, 'version'], capture_output=True, text=True, timeout=timeout).stdout.strip()
    except subprocess.TimeoutExpired: return 'timeout', 'zig version timed out', None, None
    except OSError as error: return 'unavailable', str(error), None, None
    with tempfile.TemporaryDirectory(prefix='air2lean-row-') as temp:
        temp = Path(temp)
        inputs = temp/'tests/diff'/example/'inputs'; inputs.mkdir(parents=True)
        for path in (root/'tests/diff'/example/'inputs').glob('*.jsonl'):
            (inputs/path.name).write_text(request['row'] + '\n' if path.stem == function else '')
        cmd = [zig, 'build-exe', *os.environ.get('AIR2LEAN_ROSETTA_LINK_FLAGS', '').split(),  # scripts/rosetta.sh
               '-OReleaseSafe', '-mcpu=baseline', f'-femit-bin={temp/"zigharness"}',
               '--dep', example, '--dep', 'common', f'-Mroot={root/"tests/diff"/example/"harness.zig"}',
               f'-M{example}={root/"examples"/example/f"{example}.zig"}', f'-Mcommon={root/"tests/diff/common.zig"}']
        try:
            built = subprocess.run(cmd, cwd=temp, capture_output=True, text=True, timeout=timeout)
            if built.returncode != 0: return 'error', 'native build failed: ' + built.stderr.strip()[-400:], None, None
            native = subprocess.run([str(temp/'zigharness')], cwd=temp, capture_output=True, text=True, timeout=timeout)
            lean = subprocess.run([str(difftest)], cwd=temp, env=dict(os.environ, AIR2LEAN_EXAMPLES=example),
                                  capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired: return 'timeout', 'native build, native run or Lean run timed out', None, None
        except OSError as error: return 'error', str(error), None, None
        def read(side):
            path = temp/'tests/diff/out'/side/example/f'{function}.jsonl'
            return path.read_text().splitlines() if path.is_file() else []
        zig_lines, lean_lines = (read('zig') if native.returncode == 0 else []), (read('lean') if lean.returncode == 0 else [])
    if len(zig_lines) != 1 or len(lean_lines) != 1:
        return 'error', f'runners exit {native.returncode}/{lean.returncode} with {len(zig_lines)}/{len(lean_lines)} output lines', None, None
    return 'ok', version, zig_lines[0].strip(), lean_lines[0].strip()


def diff_row_confirm(root, replay, zig, difftest, timeout):
    """Replay the recorded row; `verified` only when both fresh lines equal the recorded ones."""
    request = replay['request']
    # A bundle is untrusted input: names must be identifiers and the row must be the hashed one.
    if not (isinstance(request, dict) and all(isinstance(request.get(k), str) for k in ('example', 'function', 'row', 'row_sha256'))
            and REPORT.IDENT.fullmatch(request['example']) and REPORT.IDENT.fullmatch(request['function'])
            and hashlib.sha256((request['row'] + '\n').encode()).hexdigest() == request['row_sha256']):
        return dict(status='error', detail='malformed row-replay request')
    if diff_row_sources(root, request['example']) != request['sources_sha256']:
        return dict(status='error', detail='harness, example or runner sources changed since the bundle was written')
    try: current = CLI.row(root/'tests/diff'/request['example']/'inputs'/f"{request['function']}.jsonl", request['input_index'])
    except (Invalid, OSError): return dict(status='error', detail='the input row is missing')
    if hashlib.sha256(current.encode()).hexdigest() != request['row_sha256']: return dict(status='error', detail='the input row changed')
    status, detail, zig_line, lean_line = run_row(root, request, zig, difftest, timeout)
    if status != 'ok': return dict(status=status, detail=detail)
    same = zig_line == request['native_line'] and lean_line == request['model_line']
    return dict(status='verified' if same else 'not_reproduced', zig_version=detail,
                observed=dict(native_line=zig_line, model_line=lean_line))


MINIMIZE_ROUNDS = 64


def minimize(evaluate, types, row, line):
    """Shrink a violating row. Each round evaluates the rows one shrink step below the current one
    (`EVAL.shrinks`, smallest first) and moves to the first that violates too. Returns (row, its
    observation line, info): `locally_minimal` when no such row violates; a round cap or an evaluation
    that fails stops early, and the row reached so far is still a violation the search observed."""
    progress = 0
    for rounds in range(MINIMIZE_ROUNDS):
        candidates = EVAL.shrinks(types, row)
        out = evaluate(candidates) if candidates else dict(status='ok', lines=[])
        if out['status'] != 'ok': return row, line, dict(status='stopped_' + out['status'], rounds=rounds, rounds_with_progress=progress)
        hit = next((l for l in out['lines'] if l[0] == 'V'), None)
        if hit is None: return row, line, dict(status='locally_minimal', rounds=rounds, rounds_with_progress=progress)
        if not hit[1].isdigit() or int(hit[1]) >= len(candidates):
            return row, line, dict(status='stopped_error', rounds=rounds, rounds_with_progress=progress)
        row, line, progress = candidates[int(hit[1])], hit[2], progress + 1
    return row, line, dict(status='round_cap', rounds=MINIMIZE_ROUNDS, rounds_with_progress=progress)


def goal_bundle(root, example, function, spec, pre=None, *, gen=None, max_inputs=4096, seed=0, timeout=300,
                replay=True, air_dir=None, runner=None, zig_source=None, zig=None):
    """Search small inputs for a violation of `spec`; the violation is replayed in a fresh Lean process."""
    path = gen_path(root, example, gen)
    source = dict(kind='lean_goal_search', gen=str(path), spec=spec, pre=pre, max_inputs=max_inputs, seed=seed, timeout=timeout)
    common = dict(root=root, source=source, example=example, function=function, input_index=None, input_value=None,
                  input_sha256=None, observed=None, air_dir=air_dir, statement=spec)

    def without_violation(goal):
        return bundle(judgement=verdict(goal=goal), **common)
    air = air_path(root, example, function, air_dir)
    try:
        text, sig = read_signature(path, function, air)
        namespace = EVAL.namespace_of(text)
    except (EVAL.Unsupported, Invalid, OSError) as error:
        source['detail'] = str(error)
        return without_violation('unsupported')
    source.update(gen_sha256=EVAL.sha256(path), signedness='air' if sig.typed else 'assumed_unsigned', params=[n for n, _ in sig.params],
                  param_types=[t.lean for t in sig.types], result_type=sig.ret.lean)
    rows, exhaustive = EVAL.inputs(sig.types, max_inputs, seed)
    source.update(candidate_inputs=len(rows), exhaustive_domain=exhaustive)
    driver = EVAL.driver(namespace, sig, rows, spec=spec, pre=pre)
    out = EVAL.run(root, path, driver, timeout=timeout, **(dict(runner=runner) if runner else {}))
    if out['status'] == 'timeout': return without_violation('timeout')
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
        if checked == 0: return without_violation('no_input')
        if no_result: return without_violation('no_result')
        return without_violation('exhaustive' if exhaustive else 'bounded')
    index, row, line = int(hit[1]), rows[int(hit[1])], hit[2]   # the first violation in the order of EVAL.row_key
    if exhaustive: source['minimization'] = dict(status='smallest_of_domain', rounds=0)
    else:
        # A bounded search tried a sample: shrink its violation until no one-step simpler input violates.
        row, line, source['minimization'] = minimize(lambda cands: EVAL.run(
            root, path, EVAL.driver(namespace, sig, cands, spec=spec, pre=pre), timeout=timeout, **(dict(runner=runner) if runner else {})),
            sig.types, row, line)
        if source['minimization']['rounds_with_progress']: index = None
    raw = list(row)
    request = eval_request(root, path, air, example, function, sig, raw, spec, pre, dict(line=line, violation=True))
    info = with_native(root, lean_block(request), zig_source, function)
    if replay: info.update(confirm(root, info, timeout, zig, runner))
    common.update(input_value=raw, input_sha256=hashlib.sha256(json.dumps(raw, separators=(',', ':')).encode()).hexdigest(),
                  input_index=index, observed=dict(kind=EVAL.obs_kind(line), line=line))
    return bundle(replay=info, judgement=verdict(goal='violated', replay=info['status']), **common)


# --- Bundles ------------------------------------------------------------------------------


def bundle(root, *, source, example, function, input_index, input_value, input_sha256, observed, judgement,
           schedule=None, native=None, replay=None, air_dir=None, sources=None, statement=None):
    classification, reason, contract = judgement
    failure_kind = contract or (observed or {}).get('kind')
    # A postcondition violated by a safety panic or illegal behaviour is localized like that failure.
    if failure_kind == 'postcondition' and (observed or {}).get('kind') in SITE_FAILURES: failure_kind = observed['kind']
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


DIFFTEST = 'tests/diff/.lake/build/bin/difftest'


def default_zig():
    return os.environ.get('AIR2LEAN_ZIG', 'zig')


def replay_block(request, expected, binary):
    binary = Path(binary or ROOT/'tests/diff/.lake/build/bin/schedules')
    shown = binary.relative_to(ROOT) if binary.is_absolute() and binary.is_relative_to(ROOT) else binary
    return dict(status='not_run', request=request, expected=expected,
                command=['python3', 'scripts/counterexample.py', 'replay', '--bundle', '<this bundle>', '--binary', str(shown)])


def case_bundle(root, summary, example, function, index, *, replay=False, binary=None, timeout=60, air_dir=None,
                zig_source=None, zig=None, difftest=None, spec=None, pre=None, runner=None):
    difftest = difftest or root/DIFFTEST
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
    violated = None
    if spec is not None and replay_info is not None: raise Invalid('--spec needs a sequential case')
    if replay_info is None:
        try: request = lean_request(root, example, function, raw_input, model_line, spec=spec, pre=pre, air_dir=air_dir)
        except EVAL.Unsupported as error:
            # A stated postcondition is decided by the Lean evaluator; outside its value kinds nothing is guessed.
            if spec is not None: raise Invalid(f'--spec: {error}') from None
            request = None
        if request is not None and spec is not None:
            # Decide the postcondition on this row; the replay below repeats it in fresh processes.
            probe = lean_evaluate(root, request, timeout, runner)
            if probe['status'] == 'error': raise Invalid(f"--spec: {probe['detail']}")
            violated = probe['violated'] if probe['status'] == 'ok' else 'timeout'
            request['expected']['violation'] = violated is True
            source.update(spec=spec, pre=pre, postcondition={True: 'violated', False: 'holds'}.get(violated, 'undecided'))
        if request is not None:
            replay_info = with_native(root, lean_block(request), zig_source, function)
            if replay and violated != 'timeout': replay_info.update(confirm(root, replay_info, timeout, zig, runner))
        elif search is None and zig_source is None:
            # Any other sequential shape: rerun the example's production runners on this row.
            row_request = diff_row_request(root, example, function, index, native_line, model_line)
            if row_request is not None:
                replay_info = diff_row_block(row_request)
                if replay: replay_info.update(diff_row_confirm(root, replay_info, zig or default_zig(), difftest, timeout))
    if zig_source is not None and 'zig_native' not in (replay_info or {}):
        raise Invalid('--zig-source needs a sequential case whose function the Lean replay supports')
    if replay_info is None:
        # Unsupported shape or unmatched concurrent case: rerun the differential runner for this example.
        replay_info = dict(status='unavailable', command=['env', f'AIR2LEAN_EXAMPLES={example}', 'scripts/diff.sh'],
                           note=f'compare row {index} of tests/diff/out/{{zig,lean}}/{example}/{function}.jsonl; needs Zig')
    # A Lean replay re-evaluates the model side only; the native line stays recorded evidence from the diff run.
    # A violated stated postcondition is the failure of the case; one that holds leaves the differential verdict.
    if violated == 'timeout': judgement = verdict(automation='timeout')
    elif violated: judgement = verdict(goal='violated', replay=replay_info['status'])
    else: judgement = verdict(status=case['status'], replay=replay_info['status'])
    return bundle(root, source=source, example=example, function=function, input_index=index, input_value=raw_input,
                  input_sha256=digest, observed=observed, native=native, schedule=schedule, replay=replay_info,
                  judgement=judgement, air_dir=air_dir, sources=sources, statement=spec if violated is True else None)


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


def replay_bundle(root, path, binary, timeout, zig=None, difftest=None):
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
        outcome = confirm(root, replay, timeout, zig or default_zig())
        native = outcome.get('zig_native')
        print(f"REPLAY: status={outcome['status']} {data.get('example')}.{data.get('function')}#{data.get('input_index')} lean_sequential"
              f" observed={outcome.get('observed', {}).get('kind', '-')}"
              + (f" zig_native={native['status']} native_observed={native.get('observed', {}).get('line', '-')}" if native else '')
              + (f" native_postcondition={native['postcondition']['status']}" if native and 'postcondition' in native else ''))
        if native and native.get('postcondition', {}).get('detail'): print(f"counterexample: {native['postcondition']['detail']}", file=sys.stderr)
        if native and native.get('detail'): print(f"counterexample: {native['detail']}", file=sys.stderr)
        if outcome.get('detail'): print(f"counterexample: {outcome['detail']}", file=sys.stderr)
        return REPLAY_EXIT[outcome['status']]
    if replay.get('kind') == 'diff_row':
        outcome = diff_row_confirm(root, replay, zig or default_zig(), difftest or root/DIFFTEST, timeout)
        observed = outcome.get('observed', {})
        print(f"REPLAY: status={outcome['status']} {data.get('example')}.{data.get('function')}#{data.get('input_index')} diff_row"
              f" native={observed.get('native_line', '-')} model={observed.get('model_line', '-')}")
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
    case.add_argument('--spec', help='postcondition (as for goal-search) decided on this row; a violation is the failure of the case')
    case.add_argument('--pre', help='Lean Prop over the parameters that the row must satisfy')
    goal.add_argument('--gen', type=Path); goal.add_argument('--air-dir', type=Path); goal.add_argument('--output', type=Path, required=True)
    goal.add_argument('--max-inputs', type=int, default=4096); goal.add_argument('--seed', type=int, default=0)
    goal.add_argument('--no-replay', action='store_true'); goal.add_argument('--timeout', type=int, default=300)
    for sub in (case, goal):
        sub.add_argument('--zig-source', type=Path, help='Zig file defining --function: also replay the native program on the input')
    rep = subs.add_parser('replay', help='re-run a bundle; exit 0 reproduced, 1 not reproduced, 2 unsolved, 3 setup')
    rep.add_argument('--bundle', type=Path, required=True)
    for sub in (case, rep):
        sub.add_argument('--difftest', type=Path, default=None, help='Lean differential runner for row replays (default tests/diff/.lake/build/bin/difftest)')
    for sub in (case, goal, rep):
        sub.add_argument('--native-zig', default=default_zig(), help='stock zig for the native replay (default $AIR2LEAN_ZIG or zig)')
    for sub in (search, receipt, case, rep):
        sub.add_argument('--interpret', action='store_true', help='run schedules through the Lean interpreter (no native build)')
        sub.add_argument('--binary', type=Path, default=ROOT/'tests/diff/.lake/build/bin/schedules')
        sub.add_argument('--timeout', type=int, default=60)
    return p


def execute(args, root=ROOT):
    CLI.nat(args.timeout, 900, 'timeout')
    if args.timeout == 0: raise Invalid('timeout must be positive')
    if getattr(args, 'interpret', False): args.binary = root/'scripts/schedules-interpreted.sh'
    if args.command == 'replay':
        return replay_bundle(root, args.bundle, args.binary, args.timeout, args.native_zig, args.difftest)
    if args.command == 'goal-search':
        if not 0 < args.max_inputs <= EVAL.MAX_CASES: raise Invalid(f'max-inputs must be in 1..{EVAL.MAX_CASES}')
        data = goal_bundle(root, args.example, args.function, args.spec, args.pre, gen=args.gen, max_inputs=args.max_inputs,
                           seed=args.seed, timeout=args.timeout, replay=not args.no_replay, air_dir=args.air_dir,
                           zig_source=args.zig_source, zig=args.native_zig)
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
                           binary=args.binary, timeout=args.timeout, air_dir=args.air_dir,
                           zig_source=args.zig_source, zig=args.native_zig, difftest=args.difftest, spec=args.spec, pre=args.pre)
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
