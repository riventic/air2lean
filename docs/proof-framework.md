# One proof framework

Every proof about a translated program uses one logic and one automation:

* **The full-state separation logic** ([sep-full-state.md](sep-full-state.md)): `FTriple P c Q`
  (partial correctness), `FTotalTriple P c Q` (total: `FTriple` and `FReturns`) and `CTriple P x Q`
  (a concurrent function read in its thread), over full-state resources (`FAssn`: bytes with
  atomic-tag constraints, block knowledge, extents, ghost ledgers). Allocators meet `FAllocSpec`.
* **The symbolic executor `fsym`** (`ZigLean/Sep/Full/Auto.lean`,
  [proof-automation.md](proof-automation.md)): a proof supplies the statement and the invariants;
  `fsym` walks the generated code with the library's rules.

The library grows by **lemmas** (rules, entailments, arithmetic facts) and **`@[fsym]` rules**
(and the other registries of `fsym`, all in `ZigLean/Sep/Full/AutoAttr.lean`: `@[fsym_atom]`,
`@[fsym_facts]`, `@[fsym_provider]`, `@[fsym_plan]`, `@[fsym_drop]`, `@[fsym_view]`, `fsym_norm`,
`fsym_arith`). Nothing else: no new judgment, tactic, template, attribute, simp set or parallel
automation. When `fsym` cannot do something, the exact request (the goal, the missing step, the
rule it would need) goes to the coordinator, and the work stops there (CLAUDE.md, "One proof
framework").

## The ratchet

`scripts/proof-framework.py` (run by `scripts/preflight.sh`, so by CI) keeps
`assurance/proof-framework.json`:

* `judgments`: every definition of a program judgment in a tracked Lean file (a name ending in
  `Triple`, `TripleIn`, `Returns`, `Within`, `Stk`, `Stops`, `Turns`, `Halts`, `Template`, `Spec`,
  `WP`, …, or, whatever its name, a structural candidate: a Prop-valued `def`/`structure` over a
  program (`Result`, `MemM`, `ConcM`, `CoN`, `StateT`, `Proto`) and an assertion or postcondition;
  a structure with program and assertion fields (the `*Impl` contracts, `ResetLedger`); a
  Prop-valued structure relating two memories (`FStepIn`)), with its module and status;
* `tactics`: every tactic declaration (`syntax`/`macro`/`elab … : tactic`) and every extension of a
  tactic declared in another module (`macro_rules`), with module and status; likewise every
  command (`… : command`, kinds `command` and `command-rules`), because a command elaborator can
  add, hide or rewrite declarations (`if_decl … end_if` elaborates its theorems only when a
  constant exists);
* `registries`: every declaration of an attribute or a simp set, with its kind (`attribute`,
  `simp-set`, `rule-set`) and module: the commands `register_simp_attr`, `register_label_attr`, …
  and the calls of a registration function (`registerBuiltinAttribute`, `registerTagAttribute`, …),
  which stand in an `initialize` or `builtin_initialize`. A registry is a second way to add automation next to
  `@[fsym]` and `fsym_norm`, so a new attribute or simp set is a reviewed decision like a new tactic.
  Applying one (`@[fsym]`, `attribute [fsym] …`, `simp [fsym_norm]`, `simproc [fsym_norm] …`) is
  not a declaration and is not recorded;
* `legacy_users`: every Lean file that imports a module of the legacy logic or names a legacy
  triple.

Status is `target` (the framework above) or `legacy-to-retire`. The check fails on anything new
and on entries that no longer exist (delete them: the file is exact). Against the base branch the
file only shrinks; an addition carries `"approved": "<coordinator, date, PR>"`, which the review
of that change checks. A new `@[fsym_…]` attribute of `fsym` itself is such an addition.

## From the legacy judgments and tactics to the framework

| legacy | where | target |
| --- | --- | --- |
| `Triple` | `Sep/Triple` | `FTriple` over `up P`; the strength lemma `FTriple.toTriple_on` gives the legacy statement back on every `Mem.FSeqPlain` memory (`Mem.FSeq` without a stack budget, which the legacy logic does not have; Plan A, D1) |
| `TotalTriple`, `Returns` | `Sep/Total` | `FTotalTriple`, `FReturns` (`FTotalTriple.toTotal_on`) |
| `TotalTripleIn`, `TotalTripleStk` (#166) | `Sep/Total`, stack work | `FTotalTriple` whose precondition owns the room it needs (a stack-room resource) |
| `TotalTripleWithin`, `FailsWithin` (#166), `Sep/Cost` | `Sep/Bounded`, `Sep/Cost` | `FTotalTriple` with a cost resource (credits in the ghost state, spent by the step rules) |
| `TTriple`, `TTripleIn` | `Conc/Own`, `Conc/TlsLemmas` | `CTriple` (thread-local resources in `FAssn`; Plan A4) |
| `EventuallyReturns`, `EventuallyReturnsUnder`, `ReturnsWithin`, `Stops`, `Turns` (#178) | `Conc/Total` | a total `CTriple` with turn credits as a ghost resource |
| `MemM.Halts` (#178) | | a consequence of the total step rules (`FReturns`) |
| `LoopTemplate`, `DispatchTemplate`, `DispatchSpec`, `RecTemplate` | `Sep/LoopTemplate`, `Sep/DispatchTemplate`, `RecTemplate` | loop, dispatch and call rules for `fsym` (`Full/Loop`: `FTotalTriple.loop_ghost`, `FTriple.loop`; recursion by `FTriple.admissible_fun`) |
| `AllocSpec` | `Sep/AllocSpec` | `FAllocSpec` |
| `MutexSpec`, `CondSpec`, `FutexSpec`, `WaitGroupSpec`, `EventSpec`, `Sem.Spec`, `CancelSpec` | `Conc/Spec/*`, proofs | the same contracts stated with `CTriple` (Plan A4); `Conc/Spec/MutexToy` (a spin mutex meets `MutexSpec`, one with a monotonic `unlock` does not; imported by nothing) is deleted with `MutexSpec`, its counterexample restated against `MutexImpl` if still wanted |
| `Float.AllowedSpec`, `TimedBudget.Spec`/`WithinSpec`, test `Spec`s | pure results | propositions about a `Result` (no memory); they stay until a pure-result rule set replaces them |

| legacy tactic | where | target |
| --- | --- | --- |
| `sep_step`, `sep_steps`, `sep_unfold`, `sep_intro`, `sep_ret`, `sep_close`, `sep_split` | `Sep/Step` (deleted, L6) | `fsym` |
| `sep_normalize`, `sep_frame` | `Sep/Automation` | `fsym` (frame inference is the planner) |
| `sep_from`, `tame_prim`, `tame` | `Sep/AllocSpec/Wrappers`, `Full/Tame` | native `@[fsym]` rules (no lifting) |
| `conc_norm` | `Full/Conc` | `fsym_norm` (`gen_norm` of `Sep/AllocSpec/Norm` is deleted: its lemmas are in `fsym_norm`) |
| `loop_template(?)`, `dispatch_template(?)`, `rec_template(?)` | templates | `@[fsym]` loop, dispatch and call rules |
| `vc_gen(?)` | `VC/Extract` | retargeted onto `FTriple` (Plan A, D3) |
| `unroll_sched` | `Conc/Unroll` | `CTriple` rules for the scheduler (Plan A4) |
| `blkat_alloc`, `tomega`, `zig_range` | `Conc/Lemmas`, `Conc/Spec/Count`, `Range` | `fsym_arith` and `@[fsym_provider]` facts |
| module glue in `Proofs/`, `tests/`, `Air2Lean/Sem` (`fma_case`, `spec_case`, `bridge_*`, `pure_norm`, `mach_step`, `word_step`, `nn_step`, `mono_step`, `ok_step`) | modules | general library lemmas or `fsym` rules (CLAUDE.md, "General tactics over module-specific ones") |

A legacy entry leaves the list when its last user is migrated and the definition is deleted
([ROADMAP.md](../ROADMAP.md), architecture work). The lanes, blockers, deletion stages (D-a to D-e)
and decisions of that retirement are in [legacy-retirement.md](legacy-retirement.md).

## Deletion plans for transitional items

A transitional item needs a recorded deletion plan in the PR that adds it (CLAUDE.md, "One proof
framework"). There are two records, both in the repository:

* a legacy-layer item (`legacy-to-retire` in the ratchet): its lane in
  [legacy-retirement.md](legacy-retirement.md);
* a workaround for something `fsym` cannot do yet (a hand-written rule, an extra hypothesis, a manual case
  split): a row of the engine ledger ([engine-ledger.md](engine-ledger.md), data in
  `assurance/engine-ledger.json`) with the workaround's files and what is deleted when the row closes.
  `scripts/engine-ledger.py check` (preflight) fails on a citation of a row that does not exist and on a
  closed row that a workaround still cites.
