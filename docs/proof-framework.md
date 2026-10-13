# One proof framework

Every proof about a translated program uses one logic and one automation:

* **The full-state separation logic** ([sep-full-state.md](sep-full-state.md)): `FTriple P c Q`
  (partial correctness), `FTotalTriple P c Q` (total: `FTriple` and `FReturns`) and `CTriple P x Q`
  (a concurrent function read in its thread), over full-state resources (`FAssn`: bytes with
  atomic-tag constraints, block knowledge, extents, ghost ledgers). Allocators meet `FAllocSpec`.
* **The symbolic executor `fsym`** (`ZigLean/Sep/Full/Auto.lean` and `docs/proof-automation.md`,
  which arrive on `main` with the allocator work of `codex/alloc-arena-proof`): a proof supplies the
  statement and the invariants; `fsym` walks the generated code with the library's rules.

The library grows by **lemmas** (rules, entailments, arithmetic facts) and **`@[fsym]` rules**
(and the other registries of `fsym`: `@[fsym_atom]`, `@[fsym_facts]`, `@[fsym_provider]`,
`fsym_norm`, `fsym_arith`). Nothing else: no new judgment, tactic, template or parallel
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
* `legacy_users`: every Lean file that imports a module of the legacy logic or names a legacy
  triple.

Status is `target` (the framework above) or `legacy-to-retire`. The check fails on anything new
and on entries that no longer exist (delete them: the file is exact). Against the base branch the
file only shrinks; an addition carries `"approved": "<coordinator, date, PR>"`, which the review
of that change checks.

## From the legacy judgments and tactics to the framework

| legacy | where | target |
| --- | --- | --- |
| `Triple` | `Sep/Triple` | `FTriple` over `up P`; the strength lemma `FTriple.toTriple_on` gives the legacy statement back on every `Mem.FSeq` memory (Plan A, D1) |
| `TotalTriple`, `Returns` | `Sep/Total` | `FTotalTriple`, `FReturns` (`FTotalTriple.toTotal_on`) |
| `TotalTripleIn`, `TotalTripleStk` (#166) | `Sep/Total`, stack work | `FTotalTriple` whose precondition owns the room it needs (a stack-room resource) |
| `TotalTripleWithin`, `FailsWithin` (#166), `Sep/Cost` | `Sep/Bounded`, `Sep/Cost` | `FTotalTriple` with a cost resource (credits in the ghost state, spent by the step rules) |
| `TTriple`, `TTripleIn` | `Conc/Own`, `Conc/TlsLemmas` | `CTriple` (thread-local resources in `FAssn`; Plan A4) |
| `EventuallyReturns`, `EventuallyReturnsUnder`, `ReturnsWithin`, `Stops`, `Turns` (#178) | `Conc/Total` | a total `CTriple` with turn credits as a ghost resource |
| `MemM.Halts` (#178) | | a consequence of the total step rules (`FReturns`) |
| `LoopTemplate`, `DispatchTemplate`, `DispatchSpec`, `RecTemplate` | `Sep/LoopTemplate`, `Sep/DispatchTemplate`, `RecTemplate` | loop, dispatch and call rules for `fsym` (`Full/Loop`: `FTotalTriple.loop_ghost`, `FTriple.loop`; recursion by `FTriple.admissible_fun`) |
| `AllocSpec` | `Sep/AllocSpec` | `FAllocSpec` |
| `MutexSpec`, `CondSpec`, `FutexSpec`, `WaitGroupSpec`, `EventSpec`, `Sem.Spec`, `CancelSpec` | `Conc/Spec/*`, proofs | the same contracts stated with `CTriple` (Plan A4) |
| `Float.AllowedSpec`, `TimedBudget.Spec`/`WithinSpec`, test `Spec`s | pure results | propositions about a `Result` (no memory); they stay until a pure-result rule set replaces them |

| legacy tactic | where | target |
| --- | --- | --- |
| `sep_step`, `sep_steps`, `sep_unfold`, `sep_intro`, `sep_ret`, `sep_close`, `sep_split` | `Sep/Step` | `fsym` |
| `sep_normalize`, `sep_frame` | `Sep/Automation` | `fsym` (frame inference is the planner) |
| `sep_from`, `tame_prim`, `tame` | `Sep/AllocSpec/Wrappers`, `Full/Tame` | native `@[fsym]` rules (no lifting) |
| `gen_norm`, `conc_norm` | `Sep/AllocSpec/Norm`, `Full/Conc` | `fsym_norm` |
| `loop_template(?)`, `dispatch_template(?)`, `rec_template(?)` | templates | `@[fsym]` loop, dispatch and call rules |
| `vc_gen(?)` | `VC/Extract` | retargeted onto `FTriple` (Plan A, D3) |
| `unroll_sched` | `Conc/Unroll` | `CTriple` rules for the scheduler (Plan A4) |
| `blkat_alloc`, `tomega`, `zig_range` | `Conc/Lemmas`, `Conc/Spec/Count`, `Range` | `fsym_arith` and `@[fsym_provider]` facts |
| module glue in `Proofs/`, `tests/`, `Air2Lean/Sem` (`fma_case`, `spec_case`, `bridge_*`, `pure_norm`, `mach_step`, `word_step`, `nn_step`, `mono_step`, `ok_step`) | modules | general library lemmas or `fsym` rules (CLAUDE.md, "General tactics over module-specific ones") |

A legacy entry leaves the list when its last user is migrated and the definition is deleted
([ROADMAP.md](../ROADMAP.md), architecture work).
