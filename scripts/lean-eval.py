#!/usr/bin/env python3
"""Evaluate a generated Lean function on concrete inputs without Zig (P08).

Appends a small driver to a copy of a `Gen.lean` and runs it with `lake env lean --run`, so the
generated model is interpreted directly: no native toolchain, no libm archive. Supports
`Zig.Result` functions whose parameters and result are `BitVec n` or `Bool`; anything else is
`unsupported`, which callers report as unsolved. An optional precondition and postcondition
(Lean text over the parameter names and `r : Except Zig.Error T`) are decided per input.

Output protocol of the driver (tab separated): `O idx obs` an observation, `V idx obs` a
postcondition violation, `N idx` no result within fuel, `S checked skipped none violations`.
"""
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import re
import signal
import subprocess
import tempfile

SIG = r'^def\s+{fn}\s+((?:\([^()]*\)\s*)*):\s*Zig\.Result\s+\(?([^:=]+?)\)?\s*:=\s*do'
TYPE = re.compile(r'(?:BitVec\s+(\d+)|(Bool))\Z')
MAX_CASES = 20000


class Unsupported(Exception):
    pass


def parse_type(text):
    m = TYPE.fullmatch(text.strip().strip('()').strip())
    if not m: raise Unsupported(f'unsupported type {text.strip()}')
    return ('bool', 1) if m.group(2) else ('bv', int(m.group(1)))


def signature(gen_text, function):
    """([(name, type)], ret type) of `def function ... : Zig.Result T := do` or Unsupported."""
    m = re.search(SIG.format(fn=re.escape(function)), gen_text, re.M)
    if not m: raise Unsupported(f'{function} is not a plain Zig.Result function (memory, concurrent or missing)')
    params = [(n, parse_type(t)) for n, t in re.findall(r'\((\w+)\s*:\s*([^()]+)\)', m.group(1))]
    return params, parse_type(m.group(2))


def namespace_of(gen_text):
    m = re.search(r'^namespace\s+(\S+)', gen_text, re.M)
    if not m: raise Unsupported('no namespace in Gen.lean')
    return m.group(1)


def lean_type(t):
    return 'Bool' if t[0] == 'bool' else f'BitVec {t[1]}'


def domain_size(t):
    return 2 if t[0] == 'bool' else 2 ** t[1]


def boundary(t):
    if t[0] == 'bool': return [0, 1]
    n = t[1]; top = 2 ** n
    vals = list(range(0, min(top, 9))) + [top - 1, top - 2, top // 2, top // 2 - 1, top // 2 + 1]
    return sorted({v % top for v in vals})


def to_signed(v, t, signed):
    return v - 2 ** t[1] if signed and t[0] == 'bv' and v >= 2 ** (t[1] - 1) else v


def inputs(types, max_inputs, seed, randoms=256):
    """(rows of unsigned ints, exhaustive?). Rows are ordered smallest first."""
    total = 1
    for t in types: total *= domain_size(t)
    if total <= max_inputs:
        return sorted(itertools.product(*[range(domain_size(t)) for t in types]), key=lambda r: (sum(r), r)), True
    rng = random.Random(seed)
    rows = set()
    cross = [boundary(t) for t in types]
    size = 1
    for c in cross: size *= len(c)
    if size <= max_inputs: rows.update(itertools.product(*cross))
    else:
        while len(rows) < max_inputs // 2: rows.add(tuple(rng.choice(c) for c in cross))
    for _ in range(min(randoms, max_inputs - len(rows))):
        rows.add(tuple(rng.randrange(domain_size(t)) for t in types))
    return sorted(rows, key=lambda r: (sum(r), r))[:max_inputs], False


def render_expr(ret, signed):
    if ret[0] == 'bool': return 'if v then "1" else "0"'
    body = 'toString v.toInt' if signed else 'toString v.toNat'
    return f'"\\"" ++ {body} ++ "\\""' if ret[1] >= 64 else body


def driver(namespace, function, params, ret, rows, *, signed_ret=False, spec=None, pre=None, print_all=False, max_violations=1):
    names = [n for n, _ in params]
    data = ';'.join(','.join(map(str, (i, *row))) for i, row in enumerate(rows))
    lets = ''.join(f'      let {n} : {lean_type(t)} := ' + (f'(a{k} != 0)' if t[0] == 'bool' else f'BitVec.ofNat {t[1]} a{k}') + '\n'
                   for k, (n, t) in enumerate(params))
    pat = ', '.join(['i'] + [f'a{k}' for k in range(len(params))])
    call = ' '.join([f'{namespace}.{function}', *names])
    pre_guard = f'decide ({pre})' if pre else 'true'
    spec_ok = f'decide ({spec})' if spec else 'true'
    return f'''
namespace A2LEval
def obs (r : Except Zig.Error ({lean_type(ret)})) : String :=
  match r with
  | .ok v => "{{\\"ok\\":" ++ ({render_expr(ret, signed_ret)}) ++ "}}"
  | .error e => "{{\\"fail\\":\\"" ++ reprStr e ++ "\\"}}"

def rows : List (List Nat) :=
  ("{data}".splitOn ";").filterMap fun row =>
    if row.isEmpty then none else some (row.splitOn "," |>.map String.toNat!)

def main : IO UInt32 := do
  let mut checked := 0
  let mut skipped := 0
  let mut none_ := 0
  let mut bad := 0
  for row in rows do
    match row with
    | [{pat}] =>
{lets}      if !({pre_guard}) then
        skipped := skipped + 1
      else
        checked := checked + 1
        match ({call}).run with
        | none =>
          none_ := none_ + 1
          IO.println s!"N\\t{{i}}"
        | some r =>
          if {str(print_all).lower()} then IO.println s!"O\\t{{i}}\\t{{obs r}}"
          if !({spec_ok}) then
            bad := bad + 1
            IO.println s!"V\\t{{i}}\\t{{obs r}}"
    | _ => throw (IO.userError "malformed row")
    if bad >= {max_violations} then break
  IO.println s!"S\\t{{checked}}\\t{{skipped}}\\t{{none_}}\\t{{bad}}"
  return 0
end A2LEval

def main : IO UInt32 := A2LEval.main
'''


def run(root, gen_path, text, *, timeout, runner=('lake', 'env', 'lean', '--run')):
    """Run Gen.lean + driver. Returns dict(status=ok|timeout|error, lines, detail)."""
    with tempfile.TemporaryDirectory(prefix='air2lean-eval-') as temp:
        path = Path(temp)/'Eval.lean'
        path.write_text(Path(gen_path).read_text() + text)
        # Own session: `lake` forks `lean`, and a timeout must end the whole group, not orphan the evaluator.
        try:
            proc = subprocess.Popen([*runner, str(path)], cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                    start_new_session=True)
        except OSError as error:
            return dict(status='error', lines=[], detail=str(error))
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            try: os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            proc.communicate()
            return dict(status='timeout', lines=[], detail='lean evaluation timed out')
    if proc.returncode != 0:
        return dict(status='error', lines=[], detail=(stdout + stderr)[-2000:])
    return dict(status='ok', lines=[l.split('\t') for l in stdout.splitlines() if l[:2] in ('O\t', 'V\t', 'N\t', 'S\t')], detail='')


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def obs_kind(line):
    """Diff-report Kind of a legacy observation line."""
    d = json.loads(line)
    if 'ok' in d: return 'value'
    if d.get('diverge'): return 'bounded_no_result'
    e = d.get('fail', '').removeprefix('Zig.Error.')
    return e if e in ('illegal', 'unspecified', 'deadlock') else 'model_panic'
