#!/usr/bin/env python3
"""Mutants of the AIR interpreter's arms (V01) and of the trusted Canon rewrites (V02); Q02,
docs/mutation-map.md.

    python3 -B tests/roadmap/air-semantics/mutations.py [--list] [--only NAME]... [--jobs N]

Needs `lake build Air2Lean.Main Proofs.<Ex>.AirCert` (the committed certificates) first.

Each mutant is one well-typed change of a source file of the translator, applied in a check tree
(scripts/check-tree.py; one tree per worker), never in the checkout. The mutated module must
still build there (else the mutant is invalid and the run aborts). Then the group's fixture, run
on the mutated module, must complete and fail every check the mutant names (`kills`).

- `sem`: an arm of `Air2Lean/Sem.lean` (an operation of `evalPure`, `evalMem` or `execInst`, or a
  table or helper an arm reads: `arithFn`, `divFn`, `bitFn`, `cmpFn`, `panicOf?`, the operand,
  cell and frame helpers). `SemArms.lean` states the meaning of each instruction kind on concrete
  inputs. Where the mutant has a `cert`, `Air2Lean.SemView` must still build and the committed
  certificate `Proofs/<Ex>/AirCert.lean` must fail in the named theorems and nowhere outside the
  certificate (scripts/lean_mutant.py `reject`): the generated code of that function no longer
  agrees with the interpreter.
- `canon`: the condition of one rewrite of `Air2Lean/Air/Canon.lean` that has no preservation
  theorem (every rewrite but `renumber`). `CanonRewrites.lean` holds, per rewrite, a raw function
  on which that condition decides the result.

A mutant that passes a check, or fails it for another reason, aborts the run: a survivor is a
finding. Both fixtures pass on the unmutated sources (the control, run first).
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import queue
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
import lean_mutant  # noqa: E402
from mutation_kill_log import killed as log_kill  # noqa: E402

SELF = 'tests/roadmap/air-semantics/mutations.py'
VIEW = 'Air2Lean/SemView.lean'
# group -> (the mutated source, its fixture)
GROUPS = {
    'sem': ('Air2Lean/Sem.lean', 'tests/roadmap/air-semantics/SemArms.lean'),
    'canon': ('Air2Lean/Air/Canon.lean', 'tests/roadmap/air-semantics/CanonRewrites.lean'),
}
# The modules a run compiles in a tree: restored from the tree's own outputs after each mutant.
COMPILED = [source for source, _ in GROUPS.values()] + [VIEW]
TREES = ROOT / '.lake/check-tree'


def one(old, new, kills, cert=None):
    return dict(edits=[(old, new)], kills=kills.split(), cert=cert)


def arith(op, mode, new, kills, cert=None):
    """The arm of `arithFn` for `op` in `mode`, replaced by `new`."""
    old = {'checked': f'Zig.{op} s a b', 'unchecked': f'Zig.{op} s a b (safe := false)',
           'wrap': f'pure (Zig.{op}Wrap a b)', 'sat': f'pure (Zig.{op}Sat s a b)'}[mode]
    return one(f'  | .{op}, .{mode} => {old}\n', f'  | .{op}, .{mode} => {new}\n', kills, cert)


def table(arm, old, new, kills, cert=None):
    """The arm `arm` of a one-line table (`divFn`, `bitFn`, `cmpFn`: `old` tells them apart)."""
    return one(f'  | .{arm} => {old}\n', f'  | .{arm} => {new}\n', kills, cert)


def panic(member, old, new, kills, cert=None):
    name = member if member == 'debug.defaultPanic' else f"debug.FullPanic((function 'defaultPanic')).{member}"
    return one(f'  | "{name}" => some .{old}\n', f'  | "{name}" => some .{new}\n', kills, cert)


def guarded(arm, guard, kills):
    """The type guard of a one-line arm of `evalPure` dropped."""
    return one(f'  | .{arm} a => if {guard} then do', f'  | .{arm} a => if true then do', kills)


# name -> edits of Sem.lean (each anchor occurs once), the SemArms checks that must fail, and for
# some the committed certificate theorems that must fail too. The names are the designated
# mutants of assurance/mutation-map.json (V01).
SEM = {
    # Integer arithmetic: each arm of `arithFn` (operation x overflow mode) and `intBin`.
    'arith-add-checked-wraps': arith('add', 'checked', 'pure (Zig.addWrap a b)', 'arith.add.checked.overflow',
                                     ('Pointers', ['addTo_step', 'delay_step'])),
    'arith-add-unchecked-panics': arith('add', 'unchecked', 'Zig.add s a b', 'arith.add.unchecked.overflow'),
    'arith-add-wrap-saturates': arith('add', 'wrap', 'pure (Zig.addSat s a b)', 'arith.add.wrap'),
    'arith-add-sat-wraps': arith('add', 'sat', 'pure (Zig.addWrap a b)', 'arith.add.sat',
                                 ('Basic', ['clampAdd_step'])),
    'arith-sub-checked-wraps': arith('sub', 'checked', 'pure (Zig.subWrap a b)', 'arith.sub.checked.overflow'),
    'arith-sub-unchecked-panics': arith('sub', 'unchecked', 'Zig.sub s a b', 'arith.sub.unchecked.overflow'),
    'arith-sub-wrap-saturates': arith('sub', 'wrap', 'pure (Zig.subSat s a b)', 'arith.sub.wrap'),
    'arith-sub-sat-wraps': arith('sub', 'sat', 'pure (Zig.subWrap a b)', 'arith.sub.sat'),
    'arith-mul-checked-wraps': arith('mul', 'checked', 'pure (Zig.mulWrap a b)', 'arith.mul.checked.overflow',
                                     ('Basic', ['scale_step'])),
    'arith-mul-unchecked-panics': arith('mul', 'unchecked', 'Zig.mul s a b', 'arith.mul.unchecked.overflow'),
    'arith-mul-wrap-saturates': arith('mul', 'wrap', 'pure (Zig.mulSat s a b)', 'arith.mul.wrap'),
    'arith-mul-sat-wraps': arith('mul', 'sat', 'pure (Zig.mulWrap a b)', 'arith.mul.sat'),
    'intbin-operands-swapped': one('    let r ← k s w x y\n', '    let r ← k s w y x\n',
                                   'arith.sub.checked arith.sub.wrap div.trunc div.rem',
                                   ('Basic', ['absDiff_step', 'tardiness_step'])),
    'intbin-signedness-flipped': one('    let r ← k s w x y\n', '    let r ← k (!s) w x y\n',
                                     'arith.add.signed arith.add.signed.overflow div.trunc.unsigned '
                                     'minmax.max.signed'),
    # Division and remainder: each arm of `divFn`; `min`/`max`.
    'div-trunc-floors': table('divTrunc', 'Zig.divTrunc s a b', 'Zig.divFloor s a b', 'div.trunc.neg'),
    'div-floor-truncates': table('divFloor', 'Zig.divFloor s a b', 'Zig.divTrunc s a b', 'div.floor.neg'),
    'div-exact-truncates': table('divExact', 'Zig.divExact s a b', 'Zig.divTrunc s a b', 'div.exact.remainder'),
    'div-rem-as-mod': table('rem', 'Zig.rem s a b', 'Zig.mod s a b', 'div.rem.neg', ('Vectors', ['sRem_step'])),
    'div-mod-as-rem': table('mod', 'Zig.mod s a b', 'Zig.rem s a b', 'div.mod.neg', ('Vectors', ['sMod_step'])),
    'div-ceil-floors': table('divCeil', 'Zig.divCeil s a b', 'Zig.divFloor s a b', 'div.ceil div.ceil.neg'),
    'minmax-swapped': one('pure (if isMax then Zig.max s x y else Zig.min s x y)',
                          'pure (if isMax then Zig.min s x y else Zig.max s x y)', 'minmax.max minmax.min'),
    # Bit and boolean operations.
    'bit-and-as-or': table('and', 'a &&& b', 'a ||| b', 'bit.and'),
    'bit-or-as-xor': table('or', 'a ||| b', 'a ^^^ b', 'bit.or'),
    'bit-xor-as-or': table('xor', 'a ^^^ b', 'a ||| b', 'bit.xor'),
    'bit-bool-and-as-or': one('| .and => x && y | .or', '| .and => x || y | .or', 'bit.and.bool'),
    'bit-bool-or-as-and': one('| .or => x || y | .xor', '| .or => x && y | .xor', 'bit.or.bool'),
    'bit-bool-xor-as-or': one('| .xor => x ^^ y))', '| .xor => x || y))', 'bit.xor.bool'),
    'not-bool-identity': one('    | .bool => do pure (.bool (!(← (← operand f env a).asBool)))',
                             '    | .bool => do pure (.bool (← (← operand f env a).asBool))', 'not.bool'),
    'not-int-identity': one('pure (.int s w (~~~(← (← operand f env a).asInt w)))',
                            'pure (.int s w (← (← operand f env a).asInt w))', 'not.int'),
    'bool-and-as-or': one('    pure (.bool (x && y))\n', '    pure (.bool (x || y))\n', 'bool.and'),
    'bool-or-as-and': one('    pure (.bool (x || y))\n', '    pure (.bool (x && y))\n', 'bool.or'),
    # Comparisons: each arm of `cmpFn`, the `bool` arms and the pointer arms of `evalMem`.
    'cmp-lt-as-le': table('lt', 'Zig.lt s a b', 'Zig.le s a b', 'cmp.lt.equal', ('Basic', ['sum_loop7_body'])),
    'cmp-le-as-lt': table('le', 'Zig.le s a b', 'Zig.lt s a b', 'cmp.le.equal'),
    'cmp-gt-as-ge': table('gt', 'Zig.gt s a b', 'Zig.ge s a b', 'cmp.gt.equal'),
    'cmp-ge-as-gt': table('ge', 'Zig.ge s a b', 'Zig.gt s a b', 'cmp.ge.equal'),
    'cmp-eq-as-ne': table('eq', 'a == b', 'a != b', 'cmp.eq.equal cmp.eq.less',
                          ('Recursion', ['fact_step', 'isEven_step'])),
    'cmp-ne-as-eq': table('ne', 'a != b', 'a == b', 'cmp.ne.equal cmp.ne.less'),
    'cmp-bool-eq-as-ne': one('      | .eq => do pure (.bool (x == (← (← operand f env b).asBool)))',
                             '      | .eq => do pure (.bool (x != (← (← operand f env b).asBool)))',
                             'cmp.bool.eq cmp.bool.eq.differ'),
    'cmp-bool-ne-as-eq': one('      | .ne => do pure (.bool (x != (← (← operand f env b).asBool)))',
                             '      | .ne => do pure (.bool (x == (← (← operand f env b).asBool)))',
                             'cmp.bool.ne cmp.bool.ne.same'),
    'cmp-ptr-eq-as-ne': one('      | .eq => do pure (.bool (← Zig.ptrEqAddr p q))',
                            '      | .eq => do pure (.bool (!(← Zig.ptrEqAddr p q)))',
                            'cmp.ptr.eq.same cmp.ptr.eq.differ', ('Pointers', ['same_step'])),
    'cmp-ptr-ne-as-eq': one('      | .ne => do pure (.bool (!(← Zig.ptrEqAddr p q)))',
                            '      | .ne => do pure (.bool (← Zig.ptrEqAddr p q))',
                            'cmp.ptr.ne.same cmp.ptr.ne.differ'),
    'cmp-ptr-lt-as-le': one('      | .lt => do pure (.bool (← Zig.ptrLt p q))',
                            '      | .lt => do pure (.bool (← Zig.ptrLe p q))', 'cmp.ptr.lt.equal'),
    'cmp-ptr-le-as-lt': one('      | .le => do pure (.bool (← Zig.ptrLe p q))',
                            '      | .le => do pure (.bool (← Zig.ptrLt p q))', 'cmp.ptr.le.equal'),
    'cmp-ptr-gt-operands-swapped': one('      | .gt => do pure (.bool (← Zig.ptrLt q p))',
                                       '      | .gt => do pure (.bool (← Zig.ptrLt p q))',
                                       'cmp.ptr.gt.less cmp.ptr.gt.greater'),
    'cmp-ptr-ge-operands-swapped': one('      | .ge => do pure (.bool (← Zig.ptrLe q p))',
                                       '      | .ge => do pure (.bool (← Zig.ptrLe p q))',
                                       'cmp.ptr.ge.less cmp.ptr.ge.greater'),
    # Casts.
    'intcast-unchecked': one('pure (.int s₂ m (← Zig.intCast s₁ s₂ m x safe))', 'pure (.int s₂ m (Zig.trunc m x))',
                             'cast.int.overflow cast.int.unsafe.overflow cast.int.negative',
                             ('Basic', ['scale_step'])),
    'intcast-always-safe': one('pure (.int s₂ m (← Zig.intCast s₁ s₂ m x safe))',
                               'pure (.int s₂ m (← Zig.intCast s₁ s₂ m x true))', 'cast.int.unsafe.overflow'),
    'intcast-signedness-swapped': one('pure (.int s₂ m (← Zig.intCast s₁ s₂ m x safe))',
                                      'pure (.int s₂ m (← Zig.intCast s₂ s₁ m x safe))',
                                      'cast.int.negative.widen'),
    'trunc-result-signedness': one('      | .int _ _ x => pure (.int s₂ m (Zig.trunc m x))',
                                   '      | .int _ _ x => pure (.int (!s₂) m (Zig.trunc m x))',
                                   'cast.trunc cast.trunc.signed'),
    'bitcast-result-signedness': one('    | some (s, w) => do pure (.int s w (← (← operand f env a).asInt w))',
                                     '    | some (s, w) => do pure (.int (!s) w (← (← operand f env a).asInt w))',
                                     'cast.bitcast cast.bitcast.unsigned'),
    'ptr-bitcast-untyped': one('    if f.plainPtr i.ty then do\n      let (q, _) ← StateT.lift (ptrOperand f env a)',
                               '    if true then do\n      let (q, _) ← StateT.lift (ptrOperand f env a)',
                               'cast.bitcast cast.bitcast.unsigned'),
    # Optionals and error unions.
    'opt-nonnull-negated': one('pure (.bool (← (← operand f env a).optIsSome)) else stuck',
                               'pure (.bool (!(← (← operand f env a).optIsSome))) else stuck',
                               'opt.nonnull.some opt.nonnull.none'),
    'opt-null-not-negated': one('pure (.bool (!(← (← operand f env a).optIsSome))) else stuck',
                                'pure (.bool (← (← operand f env a).optIsSome)) else stuck',
                                'opt.null.some opt.null.none'),
    'opt-payload-identity': one('      (← operand f env a).optGet else stuck',
                                '      pure (← operand f env a) else stuck', 'opt.payload'),
    'opt-wrap-untyped': guarded('wrapOptional', 'plainOpt f i.ty', 'opt.wrap.type'),
    'err-iserr-negated': one('pure (.bool (← (← operand f env a).errIsErr)) else stuck',
                             'pure (.bool (!(← (← operand f env a).errIsErr))) else stuck',
                             'err.iserr.ok err.iserr.err'),
    'err-isnonerr-not-negated': one('pure (.bool (!(← (← operand f env a).errIsErr))) else stuck',
                                    'pure (.bool (← (← operand f env a).errIsErr)) else stuck',
                                    'err.isnonerr.ok err.isnonerr.err', ('Errors', ['digitOrZero_step'])),
    'err-payload-as-code': one('      (← operand f env a).errGet else stuck',
                               '      (← operand f env a).errGetErr else stuck', 'err.payload'),
    'err-code-as-payload': one('      (← operand f env a).errGetErr else stuck',
                               '      (← operand f env a).errGet else stuck', 'err.code'),
    'err-wrap-payload-untyped': guarded('wrapErrPayload', 'isErrorUnion f i.ty', 'err.wrap.type'),
    'err-wrap-as-payload': one('then do (← operand f env a).errWrap else stuck',
                               'then do pure (.errOk (← operand f env a)) else stuck', 'err.wrap.err'),
    'const-error-unchecked': one('  | .errUnionErr t n => if errUnionIn f t n then pure (.errErr n) else stuck',
                                 '  | .errUnionErr _ n => if true then pure (.errErr n) else stuck',
                                 'const.errunion.unknown'),
    # Memory: loads and stores of blocks and register locals, fields, items.
    'store-dropped': one('    storeAs f env q a v\n    pure .void', '    pure .void',
                         'mem.block mem.block.last.store mem.field.b', ('Pointers', ['swap_step'])),
    'store-undef-keeps-bytes': one('    | .int _ w => Zig.storeUndef (BitVec w) align p', '    | .int _ _ => pure ()',
                                   'mem.block.store.undef'),
    'load-address-off-by-one': one('    loadAs f i.ty q a\n  | .store p v', '    loadAs f i.ty (q.add 1) a\n  | .store p v',
                                   'mem.block mem.field.a', ('Pointers', ['addTo_step'])),
    'field-offset-zero': one('    | some off, true => do pure (.ptr (← Zig.ptrProject q (·.add off)))',
                             '    | some _, true => do pure (.ptr (← Zig.ptrProject q (·.add 0)))',
                             'mem.field.a mem.field.b', ('Pointers', ['dueOf_step'])),
    'ptr-add-sub-swapped': one('(if sub then (·.elemSub size k) else (·.elem size k))',
                               '(if sub then (·.elem size k) else (·.elemSub size k))', 'mem.ptr.add mem.ptr.sub'),
    'ptr-add-item-size-one': one('    | some (size, _), true =>\n      do pure (.ptr (← Zig.ptrProject q '
                                 '(if sub then (·.elemSub size k) else (·.elem size k))))',
                                 '    | some (_, _), true =>\n      do pure (.ptr (← Zig.ptrProject q '
                                 '(if sub then (·.elemSub 1 k) else (·.elem 1 k))))', 'mem.ptr.add.wide'),
    'elem-ptr-item-size-one': one('    | some (size, _), true => do pure (.ptr (← Zig.ptrProject base (·.elem size k)))',
                                  '    | some (_, _), true => do pure (.ptr (← Zig.ptrProject base (·.elem 1 k)))',
                                  'mem.elem.ptr.wide'),
    'elem-ptr-slice-bounds-dropped': one('      Zig.checkIndex s.len k\n      pure s.ptr', '      pure s.ptr',
                                         'mem.elem.ptr.slice.bounds'),
    'elem-ptr-array-bounds-dropped': one('      checkCount f t k\n      pure q', '      pure q',
                                         'mem.elem.ptr.array.bounds'),
    'elem-val-item-size-one': one('    | some (size, align) => do\n      checkCount f ((operandTy env p).getD 0) k\n'
                                  '      loadAs f i.ty (q.elem size k) align',
                                  '    | some (_, align) => do\n      checkCount f ((operandTy env p).getD 0) k\n'
                                  '      loadAs f i.ty (q.elem 1 k) align', 'mem.elem.val.wide'),
    'elem-val-array-bounds-dropped': one('      checkCount f ((operandTy env p).getD 0) k\n', '',
                                         'mem.elem.val.array.bounds mem.elem.val.sentinel.bounds'),
    'array-sentinel-not-an-item': one(
        'if sentinel then Zig.checkSentinelIndex (BitVec.ofNat 64 n) k else Zig.checkIndex (BitVec.ofNat 64 n) k',
        'if sentinel then Zig.checkIndex (BitVec.ofNat 64 n) k else Zig.checkSentinelIndex (BitVec.ofNat 64 n) k',
        'mem.elem.val.sentinel mem.elem.val.array.bounds'),
    'slice-elem-bounds-dropped': one('      Zig.checkIndex s.len k\n      loadAs f i.ty (s.ptr.elem size k) align',
                                     '      loadAs f i.ty (s.ptr.elem size k) align', 'mem.slice.elem.len'),
    'slice-len-untyped': one('    if intTy? f i.ty == some (false, 64) then do', '    if true then do',
                             'mem.slice.len.type'),
    'slice-ptr-untyped': one('    if f.plainPtr i.ty then do pure (.ptr (← StateT.lift (sliceOperand f env sv)).1.ptr)',
                             '    if true then do pure (.ptr (← StateT.lift (sliceOperand f env sv)).1.ptr)',
                             'mem.slice.ptr.type'),
    'slice-view-ignored': one('    match c.view k with\n', '    match (none : Option (Array Value)) with\n',
                              'mem.slice.view'),
    'cell-undefined-reads-void': one('  | none => throw .unspecified\n', '  | none => pure .void\n',
                                     'mem.cell.undefined mem.cell.store.undef'),
    'cell-store-undef-stores-void': one('  | .undef _ => pure none\n  | v => some <$> operand f env v',
                                        '  | .undef _ => pure (some .void)\n  | v => some <$> operand f env v',
                                        'mem.cell.store.undef'),
    'cell-read-untyped': one('  | some v => if valOk t v then pure v else stuck\n', '  | some v => pure v\n',
                             'mem.cell.type'),
    'alloc-all-register': one('    if regAlloc c.func i.id then do', '    if true then do',
                              'mem.block mem.field.a mem.frame.two'),
    'alloc-block-size-zero': one('        let p ← liftMem (Zig.allocStack size align)',
                                 '        let p ← liftMem (Zig.allocStack 0 align)', 'mem.block mem.field.c'),
    'frame-not-freed': one('\n    frame.blocks.forM Zig.free\n', '\n', 'mem.frame.freed'),
    # Control flow.
    'arg-index-ignored': one('    match c.args[index]? with', '    match c.args[0]? with', 'flow.arg.second'),
    'br-value-dropped': one('  | .br t v => do pure (.br t (← liftR (operand c.func env v)))',
                            '  | .br t _ => do pure (.br t .void)', 'flow.block flow.block.outer'),
    'cond-branches-swapped': one('asBool) then execBody c th.toList env\n    else execBody c el.toList env',
                                 'asBool) then execBody c el.toList env\n    else execBody c th.toList env',
                                 'flow.cond.then flow.cond.else'),
    'switch-item-negated': one('pure (x == (← (← operand f env it).asInt w))',
                               'pure (x != (← (← operand f env it).asInt w))',
                               'flow.switch.item flow.switch.else', ('Basic', ['classify_step'])),
    'switch-range-exclusive': one('    pure (Zig.le s l x && Zig.le s x h)', '    pure (Zig.le s l x && Zig.lt s x h)',
                                  'flow.switch.range.high'),
    'switch-range-unsigned': one('    pure (Zig.le s l x && Zig.le s x h)',
                                 '    pure (Zig.le false l x && Zig.le false x h)', 'flow.switch.range.signed'),
    'loop-tick-dropped': one('  if c.prog.ticked c.func.name then liftMem Zig.tick\n', '  if false then liftMem Zig.tick\n',
                             'flow.loop.ticks', ('Pointers', ['sumTo_loop6_body'])),
    'loop-tick-always': one('  if c.prog.ticked c.func.name then liftMem Zig.tick\n', '  if true then liftMem Zig.tick\n',
                            'flow.loop.ticks.pure'),
    'entry-tick-dropped': one('    if prog.entryTicked f.name then Zig.tick\n', '    if false then Zig.tick\n',
                              'flow.entry.tick'),
    'unreach-as-panic': one('  | .unreach => liftR (throw .unreachable)', '  | .unreach => liftR (throw .panic)',
                            'flow.unreachable'),
    'trap-as-unreachable': one('  | .trap => liftR (throw .panic)', '  | .trap => liftR (throw .unreachable)', 'flow.trap'),
    'try-payload-runs-error-body': one(
        '    | .errOk x => execBody c rest (env.set i.id i.ty x)\n    | .errErr _ => execBody c errBody.toList env',
        '    | .errOk _ => execBody c errBody.toList env\n    | .errErr _ => execBody c errBody.toList env',
        'flow.try.payload'),
    # Calls.
    'call-args-reversed': one('      let vs ← liftR (args.toList.mapM (operand c.func env))',
                              '      let vs ← liftR (args.toList.reverse.mapM (operand c.func env))',
                              'call.args', ('Recursion', ['gcd_step'])),
    'call-arg-error-set-unchecked': one('    | some (.errorUnion s _), .errErr name => errIn f s name\n',
                                        '    | some (.errorUnion _ _), .errErr _ => true\n',
                                        'call.arg.error.unknown'),
    'panic-default-as-overflow': panic('debug.defaultPanic', 'panic', 'overflow', 'call.panic.default'),
    'panic-overflow-as-panic': panic('integerOverflow', 'overflow', 'panic', 'call.panic.overflow'),
    'panic-bounds-as-panic': panic('outOfBounds', 'outOfBounds', 'panic', 'call.panic.bounds'),
    'panic-start-as-panic': panic('startGreaterThanEnd', 'outOfBounds', 'panic', 'call.panic.start'),
    'panic-zero-as-panic': panic('divideByZero', 'divByZero', 'panic', 'call.panic.zero',
                                 ('Vectors', ['callee_0'])),
    'panic-unreachable-as-panic': panic('reachedUnreachable', 'unreachable', 'panic', 'call.panic.unreachable'),
    'panic-null-as-illegal': panic('unwrapNull', 'panic', 'illegal', 'call.panic.null'),
}

# name -> the edit of Canon.lean that drops one rewrite's condition, and the CanonRewrites check
# that must fail. The designated mutants of assurance/mutation-map.json (V02), one per rewrite
# that a certificate still lists as trusted.
CANON = {
    # versionTags: an integer `bit_and` of Zig 0.17.1 renamed to `bool_and`.
    'version-tags-int-and-as-bool': one(
        '    | none, "bit_and" => if boolTyped i.ty then { i with tag := "bool_and" } else i',
        '    | none, "bit_and" => if true then { i with tag := "bool_and" } else i', 'versionTags.int.bit_and'),
    # argRanks: an `arg` takes its rank among the args, not the runtime slot of that rank.
    'arg-ranks-rank-as-slot': one(
        '  let rank (p : Nat) : Nat := slots[(ranks.idxOf? p).getD slots.size]!\n  let body := rewriteBody',
        '  let rank (p : Nat) : Nat := (ranks.idxOf? p).getD slots.size\n  let body := rewriteBody', 'argRanks.slot'),
    # errTraces: a call whose callee takes the error return trace does not pass it.
    'err-traces-call-without-trace': one('          i := { i with args := i.args.push v, errTrace := none }',
                                         '          i := { i with args := i.args, errTrace := none }', 'errTraces.call'),
    # dropDeadAllocPlaceholders: a placeholder that is read is dropped.
    'alloc-placeholder-read-dropped': one('  if read then return f\n', '  if false then return f\n',
                                          'dropDeadAllocPlaceholders.read'),
    # dropDeadRuntimeLanePtrs: a runtime lane pointer that is read is dropped.
    'lane-ptr-read-dropped': one('(i.ty.bind (f.layouts[·]?)).any (·.runtimeLane) && !read.contains i.id',
                                 '(i.ty.bind (f.layouts[·]?)).any (·.runtimeLane)', 'dropDeadRuntimeLanePtrs.read'),
    # forwardReadOnlyCopies: a read that can run before the copy's store is forwarded the value.
    'copy-read-before-store-forwarded': one('              runsAfter pos s.id u.id) then', '              true) then',
                                            'forwardReadOnlyCopies.read.before.store'),
    # itemReads: an item of a loaded array is read from memory after a later write.
    'item-read-past-write': one('u.args[0]? == some (.inst x.id) &&\n          next[x.id]? == some u.id then',
                                'u.args[0]? == some (.inst x.id) then', 'itemReads.write.between'),
    # dropTrueChecks: `0 <= x` counts as always true for a signed `x`.
    'true-check-signed-dropped': one('        | ("cmp_lte", #[.int t 0, _]) => unsigned (some t)',
                                     '        | ("cmp_lte", #[.int _ 0, _]) => true', 'dropTrueChecks.signed'),
    # sinkPastChecks: any instruction on a nullable pointer moves past the checks, not only a
    # pointer formation.
    'sink-any-nullable-operand': one('  formation && ((i.args[0]?).bind tyOf).any (nullablePtrTy f.types f.layouts)',
                                     '  ((i.args[0]?).bind tyOf).any (nullablePtrTy f.types f.layouts)',
                                     'sinkPastChecks.load'),
}

MUTANTS = {name: (group, mutant) for group, mutants in (('sem', SEM), ('canon', CANON))
           for name, mutant in mutants.items()}
assert len(MUTANTS) == len(SEM) + len(CANON), 'a mutant name occurs in both groups'


def lean(cwd, *args):
    """`lake env lean ARGS` in the tree CWD: (returncode, stdout and stderr)."""
    done = subprocess.run(['lake', 'env', 'lean', *map(str, args)], cwd=cwd, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1800, check=False)
    return done.returncode, done.stdout


def fixture(cwd, path):
    """The fixture PATH in the tree CWD: (returncode, the checks that passed, the checks that failed)."""
    rc, out = lean(cwd, '--run', path)
    summary = re.search(r'^checks: (\d+), failed: (\d+)$', out, re.M)
    passed, failed = (set(re.findall(rf'^check {word} (\S+)$', out, re.M)) for word in ('ok', 'FAILED'))
    if not summary or (int(summary[1]), int(summary[2])) != (len(passed) + len(failed), len(failed)):
        sys.stderr.write(out[-4000:])
        raise SystemExit(f'{path}: the run did not complete')
    return rc, passed, failed


def olean(source):
    return Path('.lake/build/lib/lean') / Path(source).with_suffix('.olean')


def build(tree, name, source):
    """Compile the tree's SOURCE over the tree's build outputs; a failure is an invalid mutant."""
    rc, out = lean(tree, '-o', olean(source), source)
    if rc != 0:
        sys.stderr.write(out[-4000:])
        raise SystemExit(f'{name}: {source} does not build with the mutant (an invalid mutant)')


def control():
    """Both fixtures pass on the checkout, and every check a mutant names exists."""
    for group, (_, path) in GROUPS.items():
        rc, passed, failed = fixture(ROOT, path)
        if rc != 0 or failed:
            raise SystemExit(f'{path}: the unmutated source fails {sorted(failed)}')
        named = {check for owner, mutant in MUTANTS.values() if owner == group for check in mutant['kills']}
        if named - passed:
            raise SystemExit(f'{SELF}: no such check in {path}: {sorted(named - passed)}')
        print(f'{path}: {len(passed)} checks pass on the unmutated source')


def create(tree, work):
    """A check tree whose replaced files are the sources the mutants edit (their own text)."""
    replace = []
    for source in COMPILED:
        shutil.copy(ROOT / source, Path(work) / Path(source).name)
        replace += ['--replace', f'{source}={Path(work) / Path(source).name}']
    subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/check-tree.py'), 'create', str(tree), *replace],
                   cwd=ROOT, check=True)
    for source in COMPILED:
        shutil.copy(tree / olean(source), Path(work) / f'{tree.name}-{Path(source).stem}.olean')


def kill(tree, work, name):
    """Apply the mutant NAME in TREE; exits unless each of its checks rejects it."""
    group, mutant = MUTANTS[name]
    source, path = GROUPS[group]
    try:
        text = lean_mutant.edit((ROOT / source).read_text(encoding='utf-8'), mutant['edits'], name)
        (tree / source).write_text(text, encoding='utf-8')
        build(tree, name, source)
        rc, _, failed = fixture(tree, path)
        missing = sorted(set(mutant['kills']) - failed)
        if rc == 0 or missing:
            raise SystemExit(f'{name}: SURVIVED {path}: no failure of {missing} (failed: {sorted(failed)})')
        killers = f'{len(failed)} checks of {Path(path).name} ({", ".join(mutant["kills"])})'
        if mutant['cert']:
            example, theorems = mutant['cert']
            cert = f'Proofs/{example}/AirCert.lean'
            build(tree, name, VIEW)
            rc, out = lean(tree, cert)
            lean_mutant.reject(name, rc, out, tree / cert, theorems)
            killers += f'; {cert} ({", ".join(theorems)})'
    finally:
        # The next mutant of this tree starts from the unmutated sources and their outputs.
        for compiled in COMPILED:
            shutil.copy(ROOT / compiled, tree / compiled)
            shutil.copy(Path(work) / f'{tree.name}-{Path(compiled).stem}.olean', tree / olean(compiled))
    # This file both defines the mutant and is the CI check that kills it.
    log_kill(SELF, name, SELF)
    print(f'{name}: killed by {killers}', flush=True)


def run(names, jobs):
    control()
    with tempfile.TemporaryDirectory() as work:
        trees = queue.SimpleQueue()
        for index in range(min(jobs, len(names))):
            tree = TREES / f'air-semantics-mutants-{index}'
            create(tree, work)
            trees.put(tree)

        def job(name):
            tree = trees.get()
            try:
                kill(tree, work, name)
            finally:
                trees.put(tree)

        with ThreadPoolExecutor(max_workers=jobs) as pool:
            results = [pool.submit(job, name) for name in names]
            try:
                for result in results:
                    result.result()
            except BaseException:
                # A survivor or an invalid mutant ends the run: the mutants not started stay so.
                pool.shutdown(cancel_futures=True)
                raise
    print(f'air-semantics mutants: {len(names)} killed')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n', 1)[0])
    parser.add_argument('--list', action='store_true', help='print the mutant names')
    parser.add_argument('--only', action='append', default=[], metavar='NAME')
    parser.add_argument('--jobs', type=int, default=int(os.environ.get('AIR2LEAN_JOBS') or 1),
                        help='check trees used at once (default: AIR2LEAN_JOBS, else 1)')
    args = parser.parse_args(argv)
    unknown = sorted(set(args.only) - set(MUTANTS))
    if unknown or args.jobs < 1:
        parser.error(f'unknown mutants: {unknown}' if unknown else '--jobs needs a positive number')
    if args.list:
        print('\n'.join(MUTANTS))
        return 0
    run(args.only or list(MUTANTS), args.jobs)
    return 0


if __name__ == '__main__':
    sys.exit(main())
