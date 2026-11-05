# Verification conditions

Requirement P02 asks for compositional verification conditions (VCs) for safety, functional results,
memory effects and error returns. Unsolved obligations must be exposed, and no invariant may be
invented. The one proof framework (`docs/proof-framework.md`) provides them. There is no VC
engine, AST or command of its own. A contract is a total (or partial) triple in the full-state
separation logic (`docs/sep-full-state.md`). Its VCs are the goals that the walk of the
symbolic executor `fsym` (`docs/proof-automation.md`) leaves over the generated body.

## Contracts

* A **memory contract** of a generated `MemM` function is `FTotalTriple pre (f xs) post` (total)
  or `FTriple pre (f xs) post` (partial).
* A **`Result` contract** of a pure generated function is `∃ v, f xs = pure v ∧ post v`. It
  follows from the total triple of its lifted program,
  `FTotalTriple emp (StateT.lift (f xs)) (fun v => ⟪post v⟫)`, by `FTotalTriple.result_spec`
  (`ZigLean/Sep/Full/Init.lean`). `fsym` inlines a pure generated function under `StateT.lift`,
  so the walk is the same as for memory code.

A proof states the contract and runs `fsym`. The goals it leaves are the VCs, and closing them
proves the contract. Each closing step of the walk is a kernel-checked proof, so the goals left
are the complete open obligations. The walk discharges what its arithmetic and planner prove:
overflow from a hypothesis, ownership, frames and the heap postcondition. A wrong contract leaves a
goal that is false.

## Kinds of obligations

`set_option fsym.report true in fsym` emits one `fsym-report {json}` line (schema version 1,
`ZigLean/Sep/Full/AutoReport.lean`). It lists every residual goal with its origin: the judgment and
command at that point, the rule, and why the goal was left. The kinds of P02 are read from the
origin and, where two kinds share one, from the command (`program`) or the goal:

| kind | goal | origin (`condition`, `reason`) |
| --- | --- | --- |
| safety | a primitive's or a callee's precondition (overflow, a range, a checked unwrap) | `rule_premise`, `side_condition_not_proved` |
| safety | a reachable panic: the triple of its `throw` on its path, which no rule proves | `reachability`, `panic_not_refuted` |
| memory | ownership: a command no rule executes from the precondition | `program`, `no_rule` |
| memory | the heap postcondition (`EUpd P Q`) | `postcondition`, `postcondition_not_proved` |
| result | a fact of the postcondition at a return | `postcondition`, `postcondition_not_proved` |
| error | a returned Zig error (`Except.error e = …`) against the postcondition | `postcondition`, `postcondition_not_proved` |
| loop | the loop itself: an invariant and a variant are required | `program`, `no_rule` (the command is the `loop`) |
| recursion | the recursive call: its measured contract is required | `program`, `no_rule` (the command is the call) |

Other origins are stops of the walk itself rather than obligations of the contract
(`fuel_exhausted`, `match_without_discriminant`, `indirect_targets_not_literal`), or obligations
inside a supplied rule (`update_premise`, `rule_continuation`). Without the option the goals are
the same, and `fsym` prints a human stop message at a command no rule executes.

## Calls

A call of another generated function is compositional through its proved contract: `fsym [c]`
uses the contract `c` as a step rule before inlining the callee. The contract is the total triple
of the callee (its lifted program for a pure function), `∀ xs, FTotalTriple pre (g xs) post`
(`fsym [tardiness_total]` in `tests/roadmap/vcs/Extract.lean`). A `Result` contract
`pre → ∃ v, g xs = pure v ∧ post v` becomes one with `Zig.VC.result_step` (`ZigLean/VC/Rules.lean`):
its precondition is a side goal and its summary a fact. Without a contract, a non-recursive callee
is inlined, so its obligations appear in the caller's.

## Loops and recursion

`fsym` guesses no invariant. A generated loop that no supplied rule executes stops the walk. The
loop's triple is then the residual (`program`, `no_rule`): the request for its invariant and variant.
It is proved with the loop rules of `ZigLean/Sep/Full/Loop.lean` (`FTotalTriple.loop_ghost inv
post`, the measure carried by `inv s n`; `FTriple.loop inv post`) and then given to callers as a
contract. A recursive function is proved by `FTotalTriple.rec_group` with its measure
(`docs/proof-automation.md`). Without it, the walk stops at a command it cannot execute.

## Regressions

`tests/roadmap/vcs/Extract.lean` states contracts of the committed translations of
`examples/basic`, `examples/errors` and `examples/pointers` (`Proofs/*/Gen.lean`):

* `Basic.tardiness`, whose safety obligation (the `sub` precondition, from the branch condition)
  and result obligations the walk discharges (its pinned report is complete);
* `Basic.weightedTardiness` through the contract of `tardiness`: without bounds its open
  obligations (the overflow of its `add` and `mul`, its result) are pinned, and with them it gets
  the statement of `weightedTardiness_ok`;
* a wrong `tardiness` contract, which leaves exactly one goal, and that goal is refuted;
* `Errors.parseDigit`, whose error-return and result obligations are pinned and then closed, and
  `Errors.digitOrZero` (callee contract plus checked unwraps);
* the memory contracts of `Pointers.addTo` (framed), `Pointers.swap p q` (two cells),
  `Pointers.swap p p` and `Pointers.same`, each with its strength example in
  `tests/roadmap/strength-log/Vcs.lean`, and three mutated contracts (a dropped overflow bound,
  cells not swapped, a dropped provenance premise), each with its pinned open obligation;
* `Basic.sum` and `Pointers.sumTo`, which leave their loops as requests, and `Pointers.addDown`,
  which leaves its recursive call.

`tests/roadmap/vcs/Memory.lean` pins the kinds on small functions written as the translator
writes them:

* ownership is not assumed;
* a fabricated heap postcondition and an overflow are left;
* a returned error and a reachable panic are separate goals;
* a raw loop is left;
* signed arithmetic without runtime safety (`safe := false`) is walked by the same step rule, whose
  side condition is the overflow bound;
* stores of bytes (`docs/architecture-audit/nan-bits.md`) are walked.

Once `ZigLean.Sep.Full.AutoAll` and `Proofs.{Basic,Errors,Pointers}.Gen` are built, check each
file with `lake env lean tests/roadmap/vcs/<name>.lean`.
