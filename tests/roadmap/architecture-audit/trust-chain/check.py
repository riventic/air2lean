#!/usr/bin/env python3
"""Trust-chain audit counterexamples (docs/architecture-audit/trust-chain.md).

Each case is an AIR export (real, from the patched 0.16.0 compiler, unless the case name says
`handedit`) that the translator should reject or translate differently. The script runs the
already-built translator on each case and reports `vulnerable` (the unsound behaviour is still
present) or `fixed`. It never builds anything: pass the binary with --bin (default
.lake/build/bin/air2lean).

  python3 tests/roadmap/architecture-audit/trust-chain/check.py [--bin PATH] [--require-fixed]

Exit 0 after reporting (audit mode). With --require-fixed, exit 1 if any case is vulnerable:
a fix agent flips its case(s) to fixed and adds --require-fixed coverage for them.
`std-name-spoof` and `std-type-spoof` (findings 1 and 9) are fixed; CI requires them fixed.

Three Lean witnesses state the wrong model facts as checked theorems over the generated text
as of the audit base (they need ZigLean.Basic built; a fix makes the first two fail to
elaborate, which is the intended signal, and the files are then deleted or inverted):

  lake env lean tests/roadmap/architecture-audit/trust-chain/volatile-asm/SameTick.lean
  lake env lean tests/roadmap/architecture-audit/trust-chain/comptime-field/ComptimeField.lean
  lake env lean tests/roadmap/architecture-audit/trust-chain/reduce-bool-handedit/PanicDefault.lean
"""
import argparse
import importlib.util
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def translate(binary, air_dir, out, prefix, extra=()):
    proc = subprocess.run([str(binary), str(air_dir), '-o', str(out), '--namespace', 'Audit',
                           '--prefix', prefix, *extra],
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=600)
    text = out.read_text() if proc.returncode == 0 and out.exists() else ''
    return proc.returncode, proc.stdout, text


def body(text, name):
    """The `def <name>` block of a generated file."""
    m = re.search(rf'^def {re.escape(name)}\b.*?(?=^def |^structure |^inductive |^opaque |^end |\Z)',
                  text, re.S | re.M)
    return m.group(0) if m else ''


def case_std_name_spoof(binary, tmp):
    # A user file `atomic.zig` defines `spinLoopHint`, which always panics. Its AIR is not in
    # the input (the default `<ex>.` filter), so a call resolved by FQN binds std's model.
    # Fixed by module identity (docs/air-json.md §Identity): the AIR, re-exported by the B1
    # exporter, names the callee's module `root`.
    rc, log, text = translate(binary, HERE / 'std-name-spoof/air', tmp / 'spoof.lean', 'spoof.')
    vulnerable = rc == 0 and 'spinLoopHintC' in body(text, 'answer')
    return vulnerable, f'rc={rc}; answer uses std model spinLoopHintC: {vulnerable}; {log.strip()[:300]}'


def case_std_type_spoof(binary, tmp):
    # A user file `Thread.zig` is a struct named `Thread`, the name of the std thread handle type
    # (finding 9). Read by name, it becomes the model handle type, whose fields are not translated.
    rc, log, text = translate(binary, HERE / 'std-type-spoof/air', tmp / 'tspoof.lean', 'tspoof.')
    user_struct = rc == 0 and re.search(r'^structure \w*Thread where', text, re.M) is not None
    return not user_struct, f'rc={rc}; user Thread is a translated struct: {user_struct}; {log.strip()[:300]}'


def case_addrspace(binary, tmp):
    # `*addrspace(.gs) const u64` and `*const u64` export identical type tables.
    gs = json.loads((HERE / 'addrspace/air/addr.readGs.json').read_text())
    gen = json.loads((HERE / 'addrspace/air/addr.readGen.json').read_text())
    identical = all(gs[k] == gen[k] for k in ('types', 'params', 'ret', 'body'))
    rc, log, text = translate(binary, HERE / 'addrspace/air', tmp / 'addr.lean', 'addr.')
    same = rc == 0 and body(text, 'readGs').replace('readGs', 'X') == body(text, 'readGen').replace('readGen', 'X')
    return identical and rc == 0, (f'export identical: {identical}; rc={rc}; '
                                   f'readGs/readGen bodies equal: {same}; {log.strip()[:300]}')


def case_unchecked_memcpy(binary, tmp):
    # @setRuntimeSafety(false) (and ReleaseFast) drop Sema's memcpy alias/length checks; the
    # model still copies like memmove (ZigLean/Mem/Basic.lean `memmove`).
    results = []
    for sub in ('air', 'air-releasefast'):
        rc, log, text = translate(binary, HERE / 'unchecked-memcpy' / sub, tmp / f'mc-{sub}.lean', 'mc.')
        results.append((sub, rc, 'Zig.memmove' in text, log.strip()[:200]))
    vulnerable = any(rc == 0 and mm for _, rc, mm, _ in results)
    return vulnerable, '; '.join(f'{s}: rc={rc} memmove={mm} {l}' for s, rc, mm, l in results)


def case_volatile_asm(binary, tmp):
    # `asm volatile ("rdtsc")` becomes a pure `opaque` constant: both reads are the same term.
    rc, log, text = translate(binary, HERE / 'volatile-asm/air', tmp / 'tsc.lean', 'tsc.')
    pure_opaque = re.search(r'^opaque airAsm_\w+ : BitVec 32$', text, re.M) is not None
    return rc == 0 and pure_opaque, f'rc={rc}; pure 0-ary opaque: {pure_opaque}; {log.strip()[:300]}'


def case_reduce_bool_handedit(binary, tmp):
    # Hand-edited `reduce` op Or -> Add on a bool vector: Check has no `reduce` rule and Emit
    # writes `panic!`, whose kernel value is `default`: in the Zig monads a successful return
    # of the default value (PanicDefault.lean).
    rc, log, text = translate(binary, HERE / 'reduce-bool-handedit/air', tmp / 'red.lean', 'red.')
    marker = 'panic! "air2lean:' in text
    return rc == 0 and marker, f'rc={rc}; panic! marker emitted: {marker}; {log.strip()[:300]}'


def case_comptime_field(binary, tmp):
    # A `comptime` struct field is exported as a runtime field at offset 0, overlapping `v`.
    d = json.loads((HERE / 'comptime-field/air/ct.go.json').read_text())
    s = next(t for t in d['types'] if t.get('name') == 'ct.S')
    overlap = [f['offset'] for f in s['fields']] == [0, 0] and s['abi_size'] == 4
    rc, log, text = translate(binary, HERE / 'comptime-field/air', tmp / 'ct.lean', 'ct.')
    has_k = re.search(r'^\s+k : BitVec 32', text, re.M) is not None
    return overlap and rc == 0 and has_k, (f'overlapping offsets exported: {overlap}; rc={rc}; '
                                           f'k is a Lean runtime field: {has_k}; {log.strip()[:300]}')


def case_claims_unbound(binary, tmp):
    # A goal's theorem is not tied to its root's generated function: any total triple, here
    # about `pure v`, satisfies a `total_correctness` goal of any root.
    spec = importlib.util.spec_from_file_location('claims', ROOT / 'scripts/claims.py')
    claims = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(claims)
    report = json.loads((ROOT / 'tests/roadmap/claims/fixture-report.json').read_text())
    theorems = {t['name']: t for t in claims.classify(report)['theorems']}
    goal = {'theorem': 'ClaimFixture.ret_total', 'strength': 'total_correctness',
            'domain': 'all pairs of unsigned 32-bit inputs (root basic.tardiness)'}
    result = claims.check_goal(goal, theorems)
    return result['status'] == 'accepted', f'goal for root basic.tardiness backed by `pure v` theorem: {result["status"]}'


CASES = {
    'std-name-spoof': case_std_name_spoof,
    'std-type-spoof': case_std_type_spoof,
    'addrspace': case_addrspace,
    'unchecked-memcpy': case_unchecked_memcpy,
    'volatile-asm': case_volatile_asm,
    'reduce-bool-handedit': case_reduce_bool_handedit,
    'comptime-field': case_comptime_field,
    'claims-unbound': case_claims_unbound,
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--bin', default=str(ROOT / '.lake/build/bin/air2lean'))
    ap.add_argument('--require-fixed', action='store_true')
    ap.add_argument('cases', nargs='*', default=list(CASES))
    a = ap.parse_args()
    binary = Path(a.bin)
    if not binary.is_file():
        print(f'error: translator binary {binary} not found (build it with lake build air2lean)', file=sys.stderr)
        return 2
    vulnerable = []
    with tempfile.TemporaryDirectory() as tmp:
        for name in a.cases:
            vuln, detail = CASES[name](binary, Path(tmp))
            print(f'{name}: {"vulnerable" if vuln else "fixed"} -- {detail}')
            if vuln:
                vulnerable.append(name)
    return 1 if a.require_fixed and vulnerable else 0


if __name__ == '__main__':
    sys.exit(main())
