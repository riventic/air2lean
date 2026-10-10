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

Lean witnesses state the wrong model facts as checked theorems over the generated text as of
the audit base (they need ZigLean.Basic built; a fix makes them fail to elaborate, which is
the intended signal, and the files are then deleted or inverted). The comptime-field witness
was deleted when the translator started rejecting comptime fields:

  lake env lean tests/roadmap/architecture-audit/trust-chain/volatile-asm/SameTick.lean
  lake env lean tests/roadmap/architecture-audit/trust-chain/reduce-bool-handedit/PanicDefault.lean

Every case is fixed; CI runs all of them with --require-fixed (merged-tags: finding 12,
generated-binding: finding 13).
"""
import argparse
import dataclasses
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
    # `*addrspace(.gs) const u64` and `*const u64` exported identical type tables before the
    # exporter wrote `address_space`; the translator emitted the same generic load for both.
    gs = json.loads((HERE / 'addrspace/air/addr.readGs.json').read_text())
    gen = json.loads((HERE / 'addrspace/air/addr.readGen.json').read_text())
    identical = all(gs[k] == gen[k] for k in ('types', 'params', 'ret', 'body'))
    rc, log, text = translate(binary, HERE / 'addrspace/air', tmp / 'addr.lean', 'addr.')
    same = rc == 0 and body(text, 'readGs').replace('readGs', 'X') == body(text, 'readGen').replace('readGen', 'X')
    return rc == 0, (f'export identical: {identical}; rc={rc}; '
                     f'readGs/readGen bodies equal: {same}; {log.strip()[:300]}')


def case_unchecked_memcpy(binary, tmp):
    # @setRuntimeSafety(false) (and ReleaseFast) drop Sema's memcpy alias/length checks. Fixed:
    # `memcpy` lowers to `Zig.memcpy`, which checks the overlap and the counts itself and throws
    # `.illegal` (ZigLean/Mem/Basic.lean); only `memmove` lowers to `Zig.memmove`.
    results = []
    for sub in ('air', 'air-releasefast'):
        rc, log, text = translate(binary, HERE / 'unchecked-memcpy' / sub, tmp / f'mc-{sub}.lean', 'mc.')
        results.append((sub, rc, 'Zig.memmove' in text, 'Zig.memcpy' in text, log.strip()[:200]))
    vulnerable = any(rc == 0 and (mm or not mc) for _, rc, mm, mc, _ in results)
    return vulnerable, '; '.join(f'{s}: rc={rc} memmove={mm} memcpy={mc} {l}'
                                 for s, rc, mm, mc, l in results)


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


def case_build_mode(binary, tmp):
    # Finding 8: ReleaseFast AIR (no Sema safety checks) is translated without an opt-in.
    rc, log, text = translate(binary, HERE / 'unchecked-memcpy/air-releasefast', tmp / 'fast.lean', 'mc.')
    vulnerable = rc == 0 and '"admission"' not in text.partition('\n')[0]
    return vulnerable, f'rc={rc}; accepted without a recorded opt-in: {vulnerable}; {log.strip()[:300]}'


def edited_air(tmp, name, source, edit):
    """A hand edit of a real export, in its own directory."""
    doc = json.loads(source.read_text())
    edit(doc)
    out = tmp / name
    out.mkdir()
    (out / source.name).write_text(json.dumps(doc, indent=1))
    return out


def case_legacy_default(binary, tmp):
    # Finding 10: drop the profile and claim schema 11. The legacy reader assumes a 64-bit
    # little-endian target without checking it; that needs an explicit opt-in.
    def edit(doc):
        del doc['profile']
        doc['schema'] = 11
    air = edited_air(tmp, 'legacy', HERE / 'addrspace/air/addr.readGen.json', edit)
    rc, log, _ = translate(binary, air, tmp / 'legacy.lean', 'addr.')
    return rc == 0, f'rc={rc} without --profile legacy-abi64-le; {log.strip()[:300]}'


def case_unknown_key(binary, tmp):
    # Finding 11: a key the decoder does not know (a future pointer attribute) is ignored.
    def edit(doc):
        next(t for t in doc['types'] if t['k'] == 'ptr')['is_far'] = True
    air = edited_air(tmp, 'unknown', HERE / 'addrspace/air/addr.readGen.json', edit)
    rc, log, _ = translate(binary, air, tmp / 'unknown.lean', 'addr.')
    return rc == 0, f'rc={rc} with an unknown pointer key; {log.strip()[:300]}'


def case_missing_flag(binary, tmp):
    # Finding 11: an absent `volatile` flag defaults to false under schema 12.
    def edit(doc):
        del next(t for t in doc['types'] if t['k'] == 'ptr')['volatile']
    air = edited_air(tmp, 'missing', HERE / 'addrspace/air/addr.readGen.json', edit)
    rc, log, _ = translate(binary, air, tmp / 'missing.lean', 'addr.')
    return rc == 0, f'rc={rc} without the pointer volatile flag; {log.strip()[:300]}'


def case_claims_unbound(binary, tmp):
    # A goal's theorem is not tied to its root's generated function: any total triple, here
    # about `pure v`, satisfies a `total_correctness` goal of any root.
    spec = importlib.util.spec_from_file_location('claims', ROOT / 'scripts/claims.py')
    claims = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(claims)
    report = json.loads((ROOT / 'tests/roadmap/claims/fixture-report.json').read_text())
    goal = {'theorem': 'ClaimFixture.ret_total', 'strength': 'total_correctness',
            'domain': 'all pairs of unsigned 32-bit inputs (root basic.tardiness)'}
    # Fixed by claim binding (S5): the conclusion must be about the root's generated definition.
    result = claims.check_goal(goal, claims.audited_theorems(report), definition='Basic.tardiness',
                               nodes=claims.nodes_of(report))
    return result['status'] == 'accepted', f'goal for root basic.tardiness backed by `pure v` theorem: {result["status"]}'


def case_merged_tags(binary, tmp):
    # Finding 12: Normalize merged tags whose illegal input differs (`add` is illegal behaviour on
    # overflow, `add_safe` a panic; likewise `intcast`), so a model change for one silently applied
    # to the other. Fixed: those keep their safety in the op, and every remaining merge is a
    # reviewed group with a reason (`sharedOpTags`, checked at build time by OpTable.lean).
    proc = subprocess.run([str(binary), '--print-op-table'], capture_output=True, text=True, timeout=600)
    if proc.returncode:
        return True, f'--print-op-table exited {proc.returncode}'
    rows = {row['tag']: row for row in json.loads(proc.stdout)['tags']}
    merged = [t for t in ('add', 'sub', 'mul', 'intcast')
              if t + '_safe' in ((rows[t].get('shared_op') or {}).get('tags') or ())]
    unreviewed = sorted(t for t, row in rows.items() if 'shared_op' not in row)
    groups = sorted({tuple(row['shared_op']['tags']) for row in rows.values() if row.get('shared_op')})
    return bool(merged or unreviewed), (f'safety merged: {merged}; rows without a reviewed sharing record: '
                                        f'{len(unreviewed)}; reviewed groups: {len(groups)}')


def case_generated_binding(binary, tmp):
    # Finding 13: the Gen.lean header records only the profile and float semantics, and receipts
    # and manifests recorded only the module's identity. Fixed by retranslation rather than by a
    # header claim (AIR digests or a translator revision in the header would make the output
    # depend on storage names and on AIR edits that change no semantics, docs/stable-generation.md):
    # every evidence consumer requires the module to equal a fresh translation of its committed
    # AIR with its own check's arguments (gen-integrity.py attest), as proof receipts
    # (proof-receipts/check.sh) and theorem inventory records do and `project.py check` does by
    # retranslating. A translation with another semantic option must not attest.
    spec = importlib.util.spec_from_file_location('gen_integrity', ROOT / 'scripts/gen-integrity.py')
    gi = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gi)
    target = 'tests/roadmap/global-init/GlobalInit/Gen.lean'
    index, case = next((i, c) for i, c in enumerate(gi.all_cases()) if c.path == target)
    (tmp / 'gi').mkdir()
    (tmp / 'gi-other').mkdir()
    translator = gi.Translator(str(binary), tmp / 'gi')
    attested = translator.matches(index, case, target) is None
    other = dataclasses.replace(case, args=[*case.args, '--proof-api'])
    altered = tmp / 'Altered.lean'
    altered.write_bytes(gi.Translator(str(binary), tmp / 'gi-other').output(index, other))
    refused = translator.matches(index, case, str(altered)) is not None
    consumers = {'proof receipts': 'gen-integrity.py" attest' in (ROOT / 'tests/roadmap/proof-receipts/check.sh').read_text(),
                 'theorem inventory': 'attest_generated(' in (ROOT / 'scripts/theorem-inventory.py').read_text()}
    fixed = attested and refused and all(consumers.values())
    return not fixed, (f'committed module attests: {attested}; --proof-api translation refused: {refused}; '
                       f'consumers attesting: {consumers}')


CASES = {
    'std-name-spoof': case_std_name_spoof,
    'std-type-spoof': case_std_type_spoof,
    'addrspace': case_addrspace,
    'unchecked-memcpy': case_unchecked_memcpy,
    'volatile-asm': case_volatile_asm,
    'reduce-bool-handedit': case_reduce_bool_handedit,
    'comptime-field': case_comptime_field,
    'build-mode': case_build_mode,
    'legacy-default': case_legacy_default,
    'unknown-key': case_unknown_key,
    'missing-flag': case_missing_flag,
    'claims-unbound': case_claims_unbound,
    'merged-tags': case_merged_tags,
    'generated-binding': case_generated_binding,
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
