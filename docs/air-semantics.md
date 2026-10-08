# Formal AIR semantics and translation certificates (V01 slice)

Status: research, first verified slice. This page states what is defined, what is proved and
checked, and what is not. Roadmap rows V01 (formal AIR semantics) and V02 (normalization and
emission preservation) remain open; [§Gap](#gap-to-v01-and-v02) lists what is missing.

## Acceptance evidence for this slice

Stated before the implementation, checked by CI:

1. A Lean semantics of *canonical* AIR, over the translator's own decoded datatypes
   (`Air2Lean.Func`, `Air2Lean.Inst`, `Air2Lean.Op`, `Air2Lean.Val`), for a named fragment, with
   locals in ZigLean's one memory model (`Zig.Mem`, `Zig.MemM`).
2. A translator flag that writes, beside the generated `Gen.lean`, a certificate file. The
   ordinary translation output stays byte-identical with and without the flag.
3. For the committed examples `basic` and `recursion`: every function in the fragment has a
   kernel-checked theorem relating its generated definition to the semantics of its decoded
   AIR; every other function is listed with a reason. The certificate file is committed and
   compared with the translator's output in CI.
4. The certificates are not vacuous: changing one operator in a certificate's embedded AIR
   makes that function's theorem fail (mutation check), and the embedded AIR is the decoded
   golden AIR (round-trip check).
5. No `sorry`, `admit` or `native_decide`.

## The semantics (`Air2Lean/Sem.lean`)

`Air2Lean.Sem` is a definitional interpreter over `Air2Lean.Func`, the output of
`Air2Lean.normalize` (that is, *after* canonicalization, [§Gap](#gap-to-v01-and-v02)).

| Piece | Definition |
|---|---|
| Values | `Value.int (signed) (w) (BitVec w)`, `Value.bool`, `Value.void`, `Value.ptr (Zig.Ptr) (align)` |
| Memory | `Zig.MemM` (= `StateT Zig.Mem Zig.Result`); a body runs in `Zig.MM Frame` (the stack blocks it allocated) |
| Body | `execBody`/`execInst`/`execSwitch`: well-founded recursion over the nested instruction arrays |
| Function | `execFunc call f args`: arguments must match `f.params` (`argsOk`); empty SSA environment; frees the frame at `ret` |
| Program | `run (p : Prog)`: the least fixpoint (`partial_fixpoint`) of `execFunc` over the call oracle |
| Bottom | `stuck` = `Option.none`: non-termination and every out-of-fragment or ill-typed step |

The fragment:

* integers of any width: `add`/`sub`/`mul` checked (`*_safe` and plain: overflow panics),
  wrapping and saturating; `div_trunc`/`div_floor`/`div_exact`/`rem`/`mod`; `min`/`max`;
  bitwise `and`/`or`/`xor`/`not` (and their `bool` forms); comparisons; `bool_and`/`bool_or`;
  `intcast` and `trunc`;
* control flow: `block`/`br` (with or without a value), `cond_br`, `switch_br` on an integer
  (items and ranges, first match, else), `loop`/`repeat` (as `Zig.loop`: the least fixpoint of
  iteration), `ret`, `unreach`, `trap`, and a call to a safety-panic handler (`Sem.panicOf?`,
  the literal table of `docs/generated-code.md` §Panics);
* locals: `alloc` is `Zig.allocStack` with the export's size and alignment, `load`/`store` of
  an integer or `bool` are `Zig.load`/`Zig.store` at the pointer type's `align(N)`, a store of
  `undefined` is `Zig.storeUndef`; the function's stack blocks are freed at its `ret`;
* direct calls by fully qualified name through an oracle; `run` ties the oracle to the
  program;
* `dbg_*` and `dbg_stmt` have no effect.

The arithmetic primitives are ZigLean's (`Zig.add`, `Zig.intCast`, `Zig.rem`, …): the semantics
fixes the meaning of the AIR *program structure* (SSA dataflow, operand typing, signedness
from the AIR types, control flow, locals, calls, panics) over them.

Proved once, in `Air2Lean/Sem.lean`:

* `execBody_mono`, `execFunc_mono`: a body is monotone in its call oracle;
* `run_le_of_fixpoint`, `run_le_of_table`: any oracle that satisfies every function's equation
  on well-typed arguments is above `run` — every terminating AIR behaviour (a value or a panic)
  is that oracle's behaviour (`Result.eq_of_le`);
* `run_of_lookup`: one unfolding of `run`;
* `adm_app0`…`adm_app4`, `execFunc_le`: the admissibility and monotonicity facts that a
  completeness proof by fixpoint induction over a generated clique needs.

## Certificates (`--air-certificate`)

```
air2lean tests/golden/basic/air -o Proofs/Basic/Gen.lean --namespace Basic --prefix basic. \
  --air-certificate Proofs/Basic/AirCert.lean --air-certificate-import Proofs.Basic.Gen
```

`Air2Lean/Certificate.lean` writes `<Ns>.AirCert`, containing for each fragment function `f`:

* `air_f : Func` — the decoded canonical AIR, printed as a Lean term (`printFunc`, every
  field);
* `f_step` — the per-translation certificate:

  ```lean
  theorem scale_step (call : Oracle) (p0 : BitVec 32) (p1 : BitVec 8) (m : Zig.Mem) :
      (execFunc call air_scale [(Value.int false 32 p0), (Value.int false 8 p1)]).run m =
        (fun v => ((Value.int false 32 v), m)) <$> Basic.scale p0 p1
  ```

  for any call oracle when `f` makes no certified call, otherwise with `gen` (the generated
  definitions as an oracle) answering its calls;
* `f_fix` — the same equation for every well-typed argument list; `gen_fixpoint`, `run_le_gen`:
  the generated program is a fixpoint of the AIR program's equations, so `run ⊑ gen`;
* `f_run` (no certified calls): **equality** of the program semantics and the generated
  definition, `(run (progOf table) "basic.scale" [...]).run m = ... <$> Basic.scale p0 p1`;
* with certified calls: `f_sound` (`run ⊑ gen`: every terminating AIR behaviour, value or
  panic, is the generated definition's), `f_complete` (`gen ⊑ run`: the generated definition
  is defined only where the AIR program is) and `f_eq`, **equality**, by antisymmetry:

  ```lean
  theorem gcd_eq (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
      (run (progOf table) "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m =
        (fun v => ((Value.int false 32 v), m)) <$> Recursion.gcd p0 p1
  ```

  `f_complete` is fixpoint induction over the generated `partial_fixpoint` clique
  (`Recursion.gcd.fixpoint_induct`; for `isEven`/`isOdd` the two-motive mutual principle):
  each step relates the clique body, with its recursive calls abstracted as `g`, to
  `execFunc (calls_f g)` (the AIR semantics with `f`'s callees answered by `g`) by the same
  normalization, and `calls_f g ⊑ run` by the induction hypothesis. A non-recursive caller uses
  its callees' `_complete` theorems the same way, without induction.

The `_step` proofs are one `simp only` with the `air_sem` simp set (`Air2Lean/SemAttr.lean`)
after one unfolding of the generated definition. A panic handler's name is evaluated by `rfl`
(`callee_<k>`).

### Results on the committed examples

| Example | Certified (equality with `run`) | Outside the fragment |
|---|---|---|
| `basic` | `scale`, `clampAdd`, `absDiff`, `tardiness`, `classify` (`_run`) | `weightedTardiness` (struct parameter), `sum`, `totalWeightedTardiness` (slice parameters) |
| `recursion` | `gcd`, `fact` (self-recursive), `isEven`, `isOdd` (mutually recursive) (`_eq`) | — |

The generator was also run on every other example's shared golden AIR (not committed): the
functions it admits in `layout` (`double`, `square`, `succ`) and `vectors` (`sMod`, `sRem`)
check as well; it admits `debug.assert` in `iogroup`, `sync` and `threadsync` (not checked
locally). Every other function of those examples is listed as outside the fragment.

### Emission strategies and fail-closed coverage

The generator admits a function only if every construct maps to an emission strategy whose
certificate the `air_sem` normalization covers:

| AIR construct | Emission strategy (`Air2Lean/Emit.lean`) | Certificate |
|---|---|---|
| function | `(do … : Zig.M L E).run' default`, then `match e with \| .ret v => pure v \| _ => throw .panic` | covered |
| `arg` | parameter `p<i>` | covered |
| integer/bool op | `let i<n> ← Zig.<op> s a b` or `pure (…)` (`emitScalar`) | covered |
| integer constant | `(n : BitVec w)` / `(-(n : BitVec w))` (`tagLit`) = `Sem.litBV` | covered |
| `block` | `match ← … with \| .br<n> [v] => rest \| e => pure e`, or continuation dropped | covered |
| `cond_br` | `if c then … else …` | covered |
| `switch_br` on an integer | `if x == a \|\| (Zig.le s lo x && Zig.le s x hi) then … else …` chain | covered |
| `switch_br` on an exhaustive enum | `match x with \| .A => …` | excluded (enum) |
| `ret`, `unreach`, `trap`, panic-handler call | `pure (.ret v)`, `throw .unreachable`, `throw .panic`, `throw .<ctor>` | covered |
| direct call | `Zig.call (f args)`; a recursion clique is `mutual … partial_fixpoint` | covered: unfolded once by its equation lemma; completeness by `fixpoint_induct` for parameters up to 4 (otherwise only `_sound`, noted in the file) |
| `loop`/`repeat` | extracted `f.loop<n>` definitions and `Zig.loop` | **excluded**: semantics only |
| `alloc`/`load`/`store` | struct-field locals, escaping `Zig.Mem` stack blocks, byte locals | **excluded**: semantics only |
| everything else (aggregates, slices, optionals, errors, floats, vectors, pointers, atomics, threads, models, indirect calls, asm) | — | excluded |

Excluded functions are listed in the certificate with the first reason found; a function that
calls an excluded function is excluded. If a covered construct were emitted in a way the
simp set does not normalize, that function's theorem would fail to check: `lake build Proofs`
fails, so the failure mode is closed, not silent.

### Cost

Measured on the committed certificates (Apple M-series laptop; median of three
`lake env lean` runs, with the import-only time of `Air2Lean.Sem` + the `Gen` module subtracted):

| Certificate | Functions | AIR instructions | Lines | Bytes (of which `Func` terms) | Theorems | Check time (imports) |
|---|---|---|---|---|---|---|
| `Proofs/Basic/AirCert.lean` | 5 | 53 | 310 | 19,806 (9,304) | 22 | 0.6 s (0.7 s) |
| `Proofs/Recursion/AirCert.lean` | 4 | 65 | 486 | 30,541 (10,063) | 27 | 4.4 s (0.6 s) |

A call-free function costs one normalization (`_step`); a function with calls costs a second,
oracle-abstracted normalization plus the argument inversions of its callees in `_complete`,
which is why the recursive example is slower per instruction. Both grow with the AIR body
(instructions and branches), not with the program: each theorem unfolds only its own function.

## Trusted base

A certificate is a statement about the decoded `Func`, so the following are trusted and not
checked by the certificates:

* the AIR exporter and the compiler (V03);
* JSON parsing and canonicalization (`Air2Lean/Air/Json.lean`, `Canon.lean`, `Normalize.lean`):
  the semantics starts at the canonical `Func` — [§Gap](#gap-to-v01-and-v02);
* `printFunc`: the printed term must be the decoded `Func`. `tests/roadmap/air-semantics/RoundTrip.lean`
  checks that the printed terms of the committed certificates print back to the decoded
  golden files (`printFunc` writes every field, so equal prints mean equal values);
* ZigLean's primitive operations (`Zig.add`, `Zig.intCast`, `Zig.load`, …) and memory model,
  shared by the semantics and the generated code; their fidelity to Zig is the subject of
  `docs/premises.md`, the differential tests and V03;
* `Sem.panicOf?`, the literal panic-handler table (the translator's `panicErrorFor?` for the
  same names).

## Gap to V01 and V02

What this slice does **not** establish:

* **V01 coverage.** The semantics covers the fragment above, not every operation the checker
  admits: aggregates, slices, optionals, error unions, floats, vectors, unions, enums,
  pointers beyond stack locals, globals, atomics, threads, external models and indirect calls
  are stuck (`⊥`). Target/profile parameters enter only through the export's layout table and
  the integer widths.
* **Canonicalization (V02).** The semantics is of canonical AIR. The rewrites in
  `Air2Lean/Air/Canon.lean` (read-only-copy forwarding, item reads, dropped true checks,
  argument ranks, renumbering) are not proved to preserve a raw-AIR semantics.
* **Loops and locals are not certified.** Their semantics is defined (`Zig.loop`,
  `Zig.allocStack`/`load`/`store`), but the generated code represents a non-escaping local as
  a field of the function's locals structure and a loop body as a separate definition; relating
  them needs a simulation lemma per strategy (`Zig.loop` under a state/exit encoding; the
  `Zig.Mem` store/load round trip against struct fields). Functions with loops or locals are
  excluded, so `basic.sum` would need both plus slices.
* **Completeness needs the scheme's shape.** `f_complete` assumes the generated clique's
  `fixpoint_induct` binds exactly the clique members a body calls, in the mutual block's
  order, and has an admissibility lemma only up to 4 parameters. A clique outside that shape
  gets only `_sound` (with a comment); a mismatch fails the check, it is not silently weakened.
* **Ill-formed AIR** is `⊥`, not a distinguished error; a certificate never relies on it
  (the certified functions are checked, well-typed AIR).

Proposed classification: V01 and V02 stay **research**; this page is partial evidence for both.
