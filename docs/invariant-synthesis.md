# Invariant synthesis (P09)

Status: design, approved as part of the end state by the maintainer on 2026-10-14. The first
generator slice (counted loops, stage S2) is implemented: see "Implemented: counted loops" below.
Register entry: `assurance/register/P09.md`. Spike:
`tests/roadmap/invariant-synthesis/Vacuity.lean` (kernel-checked, not in CI).

## Goal

A module proof states only its **specification**: the generic contract (written once, e.g.
`FAllocSpec`) instantiated for the module, plus the few client-visible choices that belong to the
contract instance (below). Everything else is **generated**: the implementation's invariant (its
shape, numeric facts and ghost state), its loop invariants and measures, and its range bounds.
`fsym` and the Lean kernel check the result. The generator is untrusted. A wrong guess fails to
check and is reported. It can never make a wrong proof.

This is the same split as everywhere else in the project (CLAUDE.md, "Build generic, prove
individual items against it"): the contract and the families of invariants are generic library
parts, and a module instantiates them. P09 moves the instantiation from hand-written code into a
generator.

P09 adds no judgment and no tactic. It adds an offline generator, which is a program and not a
tactic, plus two `fsym` registries and three engine outputs (stage S1, "Engine ledger rows").

## Where the proofs are today

Measured on `origin/main` at `d77a7b768`. "Lemmas" counts `theorem`/`lemma` declarations, and
"defs" counts `def`/`abbrev`/`structure`.

| Module | Lines | Lemmas | Defs | Macros | Shape of the proof |
|---|---|---|---|---|---|
| FBA `tests/roadmap/alloc-fba/AllocFba/Full.lean` | 166 | 6 | 14 | 0 | invariant `fown` by hand; the four entries are plain `fsym` |
| FBA with reset ledger (`codex/fba-reset-ledger`, then unmerged; merged later in [#337](https://github.com/riventic/air2lean/pull/337)) | 782 | 15 | 20 | 0 | adds six hand ghost updates (`alloc_upd` … `reset_upd`) and `FCov` lemmas, passed as `fsym [u]` |
| Arena `tests/roadmap/alloc-arena/AllocArena/Core.lean` | 2769 | 95 | 68 | 11 tactic + 1 command | invariant `own`/`OV`, ghost updates `free_last_upd` …, hand `CTriple` walks inside macros |
| Arena `AllocArena/Reset.lean` | 668 | 23 | 8 | 0 | chain split/join, coverage and release lemmas |
| Arena `ArenaSpec.lean`, `ArenaSpecFixed.lean`, `ArenaSpecMacos.lean` | 328 / 214 / 211 | 13 / 12 / 12 | 7 each | 0 | loop invariants `Inv9`, `Inv19`, `Lists9` by hand; `count_loop` by hand induction |
| Lists `Proofs/Lists/Linked.lean` | 269 | 15 | 7 | 0 | `revInv`, `sumInv` and their `*_step`/`*_loop` lemmas by hand (measured at S0; since S2d the loop invariants are generated, `Proofs/Lists/OpenInv.lean`, and since 2026-11-24 `sum_exact`'s too: the credit-mode invariant) |
| Lists `Proofs/Lists/Alloc.lean` | 377 | 22 | 11 | 0 | `freeInv`, `freePost`, `freeAll_loop` by hand (measured at S0; since 2026-11-24 the loop invariant is generated from `destroy`'s contract, `Proofs/Lists/AllocInv.lean`, and `freeAll_exact`'s too: the credit-mode invariant) |

Of the 95 arena lemmas, 11 are declared by the `arena_spec_statements` command. The 12 macros are
the `legacy-to-retire` entries of `assurance/proof-framework.json` for `AllocArena.Core`.

The FBA on main is close to the target: a hand invariant, and `fsym` for every entry. The ledger
version shows where the cost goes. Once ghost state enters, every entry needs hand-written
`EUpd` lemmas. These are the same families the arena writes again (free the last grant, free
another grant, shrink, grow, reset), each restated over the module's own invariant.

## What is specification and what is generated

**Specification (hand-written, reviewed, part of the claim):**

1. The generic contract, once: `FAllocSpec`/`CAllocSpec`, `ResetLedger`, the sync contracts, the
   container contracts.
2. Per instance, the theorem statements. These are one line each where the contract is generic
   over the implementation (`FAllocSpec L vt ctx I`, with `vt` the generated vtable).
3. Per instance, the **client-visible choices**:
   - the request bound `fits`. A client must establish it, so a stronger `fits` is a weaker
     contract.
   - the **creation triple's precondition**: the raw resources from which the instance is created
     (the FBA's buffer region and its struct bytes; the arena's struct and a child allocator that
     meets `CAllocSpec`).
   - the instance parameters that clients see. For the arena this is the child (`Child`, whose
     contract is an explicit premise).

**Generated (untrusted, kernel-checked, never read for soundness):** the invariant's body
(`FAllocInv.own`, the facts in `tok`, the variable record such as `OV`/`FW`), loop invariants and
measures, range facts, the dispatch tables of the closure (`tables` in `ArenaSpec.lean`), and
which library family the ghost state instantiates.

### Non-vacuity: why the creation triple is part of the specification

The kernel checks that the generated invariant makes the triples true. It does not check that the
invariant is ever reached. `Vacuity.lean` shows this:

* `vacuous_spec`: every vtable meets `FAllocSpec` (total logic included) for
  `falseInv := { own := ⟪False⟫, … }`. Each entry's precondition starts with `I.own`.
* `creation_admits`: a total triple from an admissible precondition (`FAdmit`,
  `docs/claim-strength.md`) ends in an admissible state.
* `no_creation_falseInv`: so a creation triple from an admissible precondition cannot end in
  `falseInv.own`.

Every instance therefore comes with (i) an ordinary total creation triple from its hand-stated
raw precondition, proved by `fsym`, and (ii) the existing `FAdmit` companion for that precondition.
`FAllocInv.creationPost` states the obligation once: an inhabited accepted request domain,
`I.own` and an available fee `I.fee φ` for some positive fraction `φ`. The fee excludes the audit's second
counterexample, whose state is `emp` but whose fee never holds; the request excludes `fits := False`.
This is an assertion over the existing judgment, not a new judgment or proof framework.

The contract theorem `T` names its total companion `T.creation`; `nonvacuity_witness T.creation`
provides its admissibility theorem. The claims extractor compares the post with the exact
invariant family of `T`. Plain `T.creationParameters` specification data distinguishes visible
instance parameters from fresh ghost parameters. Creation quantifies and preserves the visible
parameters (`ctx` and `B` for the FBA) and existentially binds only the fresh ones (its ledger and
epoch). The roles are hand-stated specification, not inferred ghostness; parameters captured by
the executable contract or request bound cannot be hidden as fresh. Unused impossible premises
cannot be erased. The extractor then audits both companion proofs. Claims fail closed on missing,
mismatched or unaudited
companion, including contracts used inside client proofs and anonymous inline instances.
The FBA starts from its initialized struct words, free buffer and raw claim (`fown_init`);
the page allocator starts from its null hint word. The arena follow-up is recorded as
`arena-creation` in the soundness audit.

Visible-parameter matching does not prove that every member's raw precondition is admissible.
The maintainer chose exact applied-argument admission on 2026-10-16
([PR400](https://github.com/riventic/air2lean/pull/400#issuecomment-6209913710)):
a parameterized client carries `FAdmit` of that same creation precondition, and the audit keeps
the actual contract application and its complete dependent context. An existing exact admission
hypothesis from the original theorem or a closed checked local proof supplies the evidence.
An exact local proof under unbound semantic Holds/False premises is insufficient; its context
must be bound to the root or actual initialization, not merely serialized. Unbound uses remain
`unbound_admissibility` (engine ledger #allocator-creation-admissibility). Actual creation
resources and arguments must follow translated initialization through general `fsym` and
start-memory rules; the FBA's manually built seed does not complete that obligation. No second
hand-stated domain is added, and one existential witness never stands for all capacities or
contexts. F2 remains open pending the real FBA/page proofs and negative controls.

For a parameterized instance, that existential companion alone does not bind admission to every
visible argument. `tests/roadmap/invariant-synthesis/CreationFamily.lean` proves total creation
from `⟪n = 0⟫` into the exact state and fee, with an accepted request. Its companion chooses zero;
the kernel also proves that the member at one cannot be admitted. Moving the condition into a
proof binder preserves the restriction. Engine ledger #allocator-creation-admissibility tracks
the chosen exact applied-argument protocol, whose implementation remains open. The mechanism must
automatically derive admission from translated initialization/program start using the general
full-state rules. A manually selected seed buffer or per-instance hand proof engine is not
acceptance, and Task10 has not closed F2 for FBA or page.

`fits` is the other way a contract can go vacuous: `fits := fun _ _ => False` makes `alloc`,
`resize` and `remap` vacuous, while `free` still has to be proved. That is why `fits` is
specification, not generated. A generator may *propose* a bound (from the overflow side
conditions that `fsym` reports), but the committed `fits` is hand-stated. A library lemma like
`FAllocInv.FitsUpTo` relates it to what clients and parent allocators need.

## Research, and what transfers

Our setting differs from most of the literature in three ways:

* The proof object is generated Lean (`MemM`/`CM` programs from Zig AIR), not source code.
* The checker is a proof-producing symbolic executor (`fsym`) whose failures are visible goals
  and planner messages, not an SMT verdict.
* The kernel check makes every inference engine untrusted.

The third point is the main lever. Any heuristic, solver or model may propose; nothing it
proposes needs to be sound.

### Bi-abduction and shape analysis

*Work.* Smallfoot-style symbolic execution with separation logic (Berdine, Calcagno, O'Hearn,
APLAS 2005). List-segment abstraction to a fixpoint (Distefano, O'Hearn, Yang, TACAS 2006).
SpaceInvader (Yang et al., CAV 2008). Bi-abduction, which infers the missing precondition (the
anti-frame) and the frame at once, so procedures get specs bottom-up (Calcagno, Distefano,
O'Hearn, Yang, POPL 2009 / JACM 2011; the Abductor tool, then Infer: Calcagno et al., NFM 2015).
SLAyer (Berdine, Cook, Ishtiaq, CAV 2011) for systems code with composite structures and
higher-order list predicates (Berdine et al., CAV 2007). Predicate inference: from data-structure
checkers or type declarations (Chang, Rival, Necula, SAS 2007; Chang and Rival, POPL 2008, Xisa),
and second-order bi-abduction that synthesizes the inductive predicates themselves (Le,
Gherghina, Qin, Chin, CAV 2014, S2). Infer's later Pulse engine is under-approximate
(incorrectness logic; Le et al., OOPSLA 2022), which answers a different question.

*Transfers.*

* **Frame inference is already `fsym`'s planner** (`EUpd P (P₀ ⋆ ?R)`).
* **Abduction maps onto `fsym`'s failures.** When a rule's precondition has an atom that the state
  lacks, the planner reports "no atom for X" and records the wanted atom (`viewStep`'s notes).
  This is the abduced anti-frame, so a bi-abduction loop can be built on `fsym` without a second
  engine:
  1. Start from the atoms the types give.
  2. Walk the entry.
  3. Add the missing atom with fresh existentials.
  4. Repeat.

  This needs the engine to report the missing atom in machine-readable form (row P09-E3).
* **List-segment abstraction with a fixpoint** is how loop invariants for list walks are found:
  run the body from a candidate, fold `lseg ⋆ node → lseg` with library lemmas (`lseg_snoc`;
  range laws `@[fsym_plan]`), and join until stable.
* **Predicates from types.** AIR types, as translated (structs with `Enc` field layouts,
  `?*Node` self-references, slices), give the candidate predicates. This is SLAyer's and Xisa's
  move, with the generated `Enc` instances in place of C declarations.

*Does not transfer.* Infer's procedure summaries are disjunctive and unchecked. We need one
invariant per module that the kernel accepts. Second-order predicate synthesis is not needed: the
library supplies the predicate families (list, segment, chain of headed nodes), and synthesis
only instantiates them.

### Abstract interpretation for ranges and relational numeric invariants

*Work.* Abstract interpretation (Cousot and Cousot, POPL 1977). Polyhedra (Cousot and Halbwachs,
POPL 1978). Octagons (Miné, HOSC 2006). Congruences (Granger, 1989). Wrapped intervals for
machine integers (Navas et al., APLAS 2012). Astrée (Blanchet et al., PLDI 2003): no false
alarms on its target family through domain specialization. IKOS (Brat, Navas, Shi, Venet, SEFM
2014). The Apron library (Jeannet and Miné, CAV 2009). Numeric abstraction of heap programs:
numeric variables for the sizes and fields of the shape abstraction (Magill, Tsai, Lee, Tsay,
POPL 2010).

*Transfers.* The facts that allocators need are octagonal or congruence facts over the values of
words and the sizes of regions:

* `ei ≤ cap`, `24 + ei ≤ sz`, `tail.size = sz - 24 - ei`;
* `sz % 2 = 0`, `(A + off) % 8 = 0`;
* `off + sz < 2 ^ 63`.

The checker is `fsym_arith` (`omega` over `x.toNat` facts, with literal moduli), so the domain only
has to propose facts in that fragment. Intervals, octagons and congruences, applied to the
numeric variables of the shape (Magill et al.), cover every fact of the FBA and the arena
invariants. Polyhedra are affordable at these sizes and are a fallback. Widening thresholds come
from the program's constants (24, `2 ^ 63`, alignments). Every word is read as its unsigned value
`x.toNat` (`docs/proof-automation.md`, "The arithmetic solver"), so the domain works on naturals
with explicit `< 2 ^ w` bounds, the wrapped-interval view.

*Does not transfer.* Astrée-style domain engineering for floating point and digital filters
is not needed for this scope. Soundness of the analysis is never needed: its results are
candidates (below, Houdini).

### Loop-invariant synthesis: templates, ICE, CHC, Houdini

*Work.* Template and constraint-based synthesis (Colón, Sankaranarayanan, Sipma, CAV 2003;
Gulwani, Srivastava, Venkatesan, PLDI 2008). Linear ranking functions (Podelski and Rybalchenko,
VMCAI 2004: complete for single-path linear loops). ICE learning from positive, negative and
implication examples (Garg, Löding, Madhusudan, Neider, CAV 2014; with decision trees, POPL 2016).
Constrained Horn clauses (Bjørner, Gurfinkel, McMillan, Rybalchenko, 2015), solved by Spacer in
Z3 (Komuravelli, Gurfinkel, Chaki, CAV 2014) or Eldarica (Hojjat and Rümmer, FMCAD 2018).
Houdini: candidate conjuncts pruned to the largest inductive subset (Flanagan and Leino, FME
2001). Daikon proposes candidates from runs (Ernst et al., 2001/2007).

*Transfers.*

* **Houdini fits `fsym` exactly.** Take a candidate invariant that is a conjunction of facts and
  atoms. Walk the body with it. Every conjunct that the post does not re-establish remains as its
  own residual goal (`fsym` leaves side conditions it cannot prove as visible goals). Drop those
  conjuncts and walk again. The fixpoint is the largest inductive subset, and its last walk is
  the proof. The checker is the oracle, so pruning is deterministic. This needs residual goals to
  name the conjunct they came from (row P09-E1).
* **Measures.** A list walk has the length of the ghost list under the cursor (what
  `Linked.lean` uses with `loop_ghost`). A counted loop has a linear ranking function
  (Podelski–Rybalchenko). A labelled-switch dispatch loop has `B * data + rank` (`loop_dispatch`).
  All three are template instances that the shape and the loop's exit test determine.
* **Positive examples** come from concrete runs that the project already has: the Lean interpreter
  over generated code (`goal-search`, P08) and the differential harness rows. Daikon-style
  candidates from them seed the template set. Negative and implication examples are weaker here:
  `omega` gives no models.
* **CHC solvers** are an optional hint source for the numeric layer once the shape is fixed: encode
  the loop over the numeric variables as Horn clauses, solve offline, and read the interpretation
  back as candidate facts. They never run in CI or in a build (layer 4).

*Does not transfer.* ICE's learner-teacher loop with an SMT teacher. Our teacher is `fsym`, and
it returns goals, not states.

### Ghost-state and ledger invariants

*Work.* Iris: ghost state from resource algebras and invariants (Jung et al., JFP 2018). Diaframe:
goal-directed proof search with bi-abduction hints as library lemmas; the user gives the
invariants (Mulder, Krebbers, Geuvers, PLDI 2022; linearizability, OOPSLA 2023). RefinedC:
refinement types annotate structs and loops, and Lithium search does the rest (Sammler et al.,
PLDI 2021). VeriFast: annotations, auto-open/close of predicates, "auto lemmas" (Jacobs et al.,
NFM 2011). Viper (Müller, Schwerhoff, Summers, VMCAI 2016). Permission inference (Ferrara and
Müller, VMCAI 2012; Dohrau, Summers, Urban, Müller, CAV 2018, arrays). Prusti derives the core
permission invariants from Rust's ownership types (Astrauskas et al., OOPSLA 2019).

*Transfers.*

* **Updates as registered library lemmas** (Diaframe's hints, VeriFast's auto lemmas) is the shape
  of row P09-E5: generic ghost updates (`ledger_return`, `ledger_shrink`, `ledger_regrow`, lend
  and return of shares, junk growth) registered once and tried at returns. Today a module passes
  them as `fsym [u]`.
* **Prusti's point carries over.** Ownership that a type system already tracks needs no
  inference. In Zig it is not in the types, but the interface contracts carry it: a pointer that
  the code got from `alloc` comes with `granted`, and a node that the code later `free`s must keep
  its token. That is abduction over the contract's pre/postconditions (layer 1).
* **What none of these systems infers is the ledger itself.** Iris, Diaframe and RefinedC all take
  the ghost invariant from the user. Our answer is the library: the ledger families are written
  once (`ResetLedger`, the grant map and receipts, claims, the pool of lent shares, coverage by
  junk), and synthesis picks and instantiates a family (layer 3). A new kind of allocator (a pool,
  a size-class allocator) means one new library family, not a new generator.

### LLM-based invariant generation with a checker in the loop

*Work.* Lemur: LLM proposals checked by a verifier, with a sound calculus around them (Wu,
Barrett, Narodytska, ICLR 2024). LaM4Inv: LLM proposals filtered by bounded model checking (Wu et
al., ASE 2024). Loopy (Kamath et al., 2023), and ranking of LLM candidates (Chakraborty et al.,
EMNLP Findings 2023). For Lean: LeanDojo/ReProver (Yang et al., NeurIPS 2023), Lean Copilot (Song,
Yang, Anandkumar, 2024), DeepSeek-Prover (2024, 2025), AlphaProof (Google DeepMind, 2024). For
verification-aware languages: AutoVerus (Yang et al., 2024).

*Transfers.* The common pattern, propose with a model and accept only what the checker accepts,
is exactly our trust model. The useful unit for us is a **candidate term** (an invariant, a fact,
a measure, a family choice) in the module's vocabulary, not a proof script. Ranking by the number
of residual goals after one `fsym` walk is cheap. A model never writes tactics: the proofs stay
`fsym`.

*Does not transfer.* Running a model in the build. Outputs are committed as hints (layer 4), so
builds are deterministic and need no network.

## Design

### (a) Where it sits in the framework

Options:

| | Engine feature (synthesis inside `fsym` at proof time) | Offline generator (definitions committed, like `Gen.lean`) |
|---|---|---|
| Module invariant | impossible as a definition: it occurs in the theorem's **statement** (`FAllocSpec … (inv …)`), so it must exist before the theorem. The only way around this is an existential package `∃ I, FAllocSpec … I ∧ creation`, which is a new judgment-like structure (rejected below) | a `def` in a committed file; the statement names it |
| Loop invariants | possible (the loop rule's `inv` is a metavariable) | possible |
| Cost | every elaboration repeats the search (Houdini is many walks); breaks the 200k heartbeat budget | search once at generation; a build pays only the final check |
| Determinism and review | invariants invisible in diffs; an engine change can silently change proofs | diffs show every invariant change; byte-identical regeneration is checked |
| Allow-list | the search has to live in a tactic or the engine | no tactic; the generator is a program |

**Recommendation: the offline generator for all synthesized content, plus small permanent engine
features that consume it and serve as its oracle.**

* The generator `air2lean-invgen` is a Lean executable (a `def main`, no `syntax`/`macro`/`elab`).
  It imports the generated module and the library, calls `fsym` through its single entry point
  for checking and pruning, and writes `<Module>/Inv.lean`. Engine row #14 (open) is to expose
  that entry point as `Zig.Full.Auto.run`.
  The file holds only `def`/`abbrev`/`structure` declarations and registry attributes: no
  theorems, no tactics, no commands. Its first line is a record
  `-- air2lean-invgen: {…}` with the generator revision, the hash of every input (the generated
  modules it reads, the spec header, the hints file) and the semantic fingerprints of the
  generated functions it covers (`docs/stable-generation.md`). Like a `Gen.lean`, it is never
  edited by hand.
* The proof file is the specification: theorem statements naming `Inv.*`, each proved by `fsym`
  with no module lemma arguments.
* Engine features (fsym lane; rows below):
  1. `@[fsym_inv]`: a registry from a generated loop (`body`/`again` constants) to its invariant and
     measure. At a `Zig.loop` with no rule, `fsym` applies its backend's generic loop rule
     (`FTotalTriple.loop_ghost`/`loop_measure`/`loop_dispatch`, `FTriple.loop`, `CTriple.loop`,
     `WP.loop`) with the registered invariant. The invariant's parameters are unknowns that the
     planner assigns at loop entry, and the frame is inferred. The body is a subgoal walked by
     `fsym`. This replaces the hand `*_loop` lemmas and `fsym [loop_ct]` arguments.
  2. `@[fsym_upd]`: a registry of library ghost updates (`EUpd` lemmas keyed by the heads they
     change), tried at a return that the planner does not close, as caller updates are today
     (`tryUpd`, row 9f).
  3. Oracle outputs for the generator: residual goals attributed to the conjunct they came from,
     strongest-post inference at returns for the sequential and thread backends (as the `WP`
     backend's `inferPost` already does for segments), and machine-readable stop reasons with the
     atom the planner missed.

  These are registries (data, like `@[fsym_plan]`) and outputs of the one engine. They are also
  useful without P09: a hand-written loop invariant gets registered instead of wrapped in a
  lemma.

**What the allow-list (`assurance/proof-framework.json`) sees.** No new `judgments`: invariants
are `FAssn`-valued; facts are `Prop`-valued over values, not over programs; the generator never
emits a structure with program and assertion fields. No new `tactics` or commands: the generator
is an executable, and the generated file uses only built-in commands. No new `legacy_users`. The
list **shrinks**: stage S4 deletes the 12 `AllocArena.Core` entries (11 tactics,
`arena_spec_statements`). `scripts/proof-framework.py` stays the gate. A generated file that
declared a tactic would fail it like any other file.

Rejected: an existential package `structure AllocInstance … : Prop := ∃ I, FAllocSpec … I ∧ …` is a
new judgment by shape. Two theorems (contract, creation) and the `FAdmit` companion give the same
guarantee with existing heads. A tactic such as `fsym_infer` is a new tactic and would repeat the
search on every build.

### The generator

Input: a generated module (one or more `Gen*.lean`), the **spec header** (the hand-stated
contract instance: which contract, the vtable, `fits`, the creation function and its precondition,
the visible parameters), and an optional hints file. Output: `Inv.lean`, or a report of the best
candidate's residual goals (the remaining premises, P03's acceptance wording). Phases:

1. **Read** the generated module at the meta level: structure types and their `Enc` field
   layouts (as `encFieldOf?` reads them), loops (`Zig.loop body again` and their locals
   structures), calls through vtables (`callIndirect`), atomic ops per field offset, constants.
   The generator works on the same terms `fsym` walks. It needs no second semantics of AIR.
2. **Propose** candidates per layer (below), cheapest first.
3. **Check and prune** with `fsym`. A Houdini fixpoint per entry and per loop: walk, drop the
   conjuncts whose goals remain, repeat. The bi-abduction loop adds missing atoms reported by the
   planner. Candidates are tried in a fixed order, and all limits are heartbeats, never wall
   time, so a run is deterministic.
4. **Emit** the surviving invariant, or report.

The arena's three modules (stock and patched x86_64-linux, aarch64-macos) read the same layout.
The generator writes one invariant module for them when the fingerprints of the types it read
agree, as `arena_spec_statements` shares statements today.

**Staleness and reproducibility.** `scripts/gen-integrity.py check` recomputes the input hashes in
the record. Equal hashes mean the file is current (the generator is deterministic). Different
hashes mean it is stale, and `scripts/regen.sh` reruns the generator (a new `pr`-scope step in
`scripts/regen.py`, cached through `AIR2LEAN_CAS_DIR`). The nightly unrestricted run regenerates
everything and requires byte-identical output. The build itself is the soundness gate: a stale
but still checking invariant is still a correct proof.

### (b) Layers, cheapest first

Each layer proposes candidates. Only the check decides.

**1. Data-structure predicates from Zig types and AIR.**
* A struct reached by a pointer gives `up (pts p a s)`. A field that the module accesses
  atomically gives `apts`/`aptsE` (access-mode scan per offset). Fields owned by different
  parties give one atom per field (`docs/proof-automation.md` §Parts).
* A slice field `[]T` gives a region `up (regionIn ptr A S K al bs)` with `bs.size = len * size`,
  the block's `known` address and an extent share up to its end (the FBA's `wBuf`, `ftail`,
  `bshare`).
* A self-referential `?*Node` gives an instance of the library's list family (`lseg`/`Chain`,
  parameterized by the node layout and by `X`, the rest of what each node's owner keeps, as in
  `Proofs/Lists/Linked.lean`). A node with a header and trailing bytes (the arena's
  `size`/`end_index`/`next` and its buffer) is the headed-chain instance. The length relation
  between the header word and the trailing region is a layer-2 fact.
* Memory obtained through an interface (`alloc` through a vtable) keeps what the contract's `free`
  will need: the child's token and fee (the arena's `Child.ntok`, `Child.cown`). This is abduction
  over the contract's pre- and postconditions.
* The closure's dispatch tables (`tables`) are read off the generated vtables.

The arena's `Chain`/`ChainH` and the lists' `lseg` become one library family. Its split, join,
snoc and owned-bytes lemmas (`chain_split`, `chain_join`, `lseg_snoc`, `chain_owns`,
`chain_ownsList`) are stated once.

**2. Numeric and range invariants and measures.** Intervals, octagons and congruences over the
numeric variables of the layer-1 shape (word values, region sizes, offsets, addresses mod
alignment), with constants from the program as widening thresholds. Candidates are facts in
`fsym_arith`'s fragment. Measures come from the loop's shape (layer-1 ghost list length, linear
ranking, dispatch rank). Bounds that hold because owned bytes fit in the address space come from
`OwnedBound` (`Holds.owned_length_le`), as for the arena's `countListCapacity` (`chain_capOf_le`),
and enter as candidate facts with their library lemma.

**3. Ghost and ledger invariants composed from the generic pieces.** The contract determines which
components the invariant needs. Grants need a token and a fee (`FAllocInv`). A reset contract
needs the epoch ledger (`ResetLedger`: `gauthP`, `LedgerRcpts`, `epFee`). Grants carved from
owned regions need coverage by junk (`JunkAt`, `Reclaim`) and byte-range claims. Shares lent to
grants need the pool accounting. The shape determines where grants come from: one region (FBA), a
chain of nodes with an active first node (arena), whole mappings (page allocator). P09 adds the
**bump-ledger family** to the library, written once: the variable record, the facts (grant map
bound, grants inside nodes, per-block fraction accounting, coverage) and the generic updates
(carve a grant, free the last grant or another, shrink, grow, reset). These are the updates the
FBA ledger branch and the arena write by hand today. FBA is the one-node instance and the arena
the chain instance. The generator picks the family and maps the shape's parts to its parameters,
from a finite set of candidates, each checked.

**4. Guess-and-check fallback.** When layers 1–3 leave goals, the hints file is consulted: a
committed `<Module>/Inv.hints.json` of candidate *terms* (invariants, facts, measures, family
choices) as Lean source text, each with its provenance (`heuristic`, `chc:<solver>@<version>`, or
`llm:<model>@<date>`, with the prompt's hash). Producers (heuristics, CHC solvers, LLMs) are
offline tools that write hints. They never run in `scripts/regen.sh`, in CI or in a build. The
generator treats hints like any other candidate: pruned by `fsym`, dropped and reported if they do
not check. Hints count as hand-written lines in the acceptance metrics.

### Fail closed

If no candidate checks, the generator emits no invariant for the item and prints the best
candidate's residual goals. The proof file then does not build: no `sorry`, no axiom
(`scripts/no-sorry.sh`), no admitted premise. A conservative invariant (too strong) cannot be
vacuous, because of the creation triple. It can only make an entry unprovable, and that is
reported.

## (c) Acceptance

Measured as in the table above. "Hand-written" means lines in files that are neither generated
(`Gen*.lean`, `Inv.lean`) nor library. Hints count as hand-written.

* **FBA** (`tests/roadmap/alloc-fba`): the invariant (`fown`/`finv` and, with the reset ledger,
  its variable record, facts and updates) is generated with no hints. The hand-written proof file
  is at most 60 lines: the statements of `fallocSpec`, the creation triple, `reset` when the
  ledger has landed, and `fits`. 0 module-specific lemmas. Every proof body is `fsym` with no
  arguments naming module lemmas. An `FAdmit` companion for the creation precondition.
* **Arena** (`tests/roadmap/alloc-arena`): `Core.lean` shrinks to the specification instance (the
  `Child` record, the creation precondition, `fits`, the statements), at most 150 lines, with 0
  module-specific lemmas (95 today). `Reset.lean` is deleted (its general lemmas go to the
  library families, the rest is generated). The three `ArenaSpec*.lean` files hold statements
  only, at most 40 lines each: no hand loop invariants (`Inv9`, `Inv19`, `Lists9`, `count_loop`).
  The 11 arena tactic macros and the `arena_spec_statements` command are deleted, and their 12
  entries leave `assurance/proof-framework.json`. A creation triple and its `FAdmit` companion are
  added (none exists today). No proof above the 4M heartbeat gate. 0 hints.
* **Lists and queue loops**: `Proofs/Lists/Linked.lean` (`revInv`, `revPost`, `sumInv`, `sumPost`
  and the `*_step`/`*_loop` lemmas), `Proofs/Lists/Alloc.lean` (`freeInv`, `freePost`,
  `freeAll_loop`): invariants and measures generated and registered, so these files hold the
  statements and `fsym`, and the queue instance `tests/roadmap/loop-tactics/Queue.lean` builds
  unchanged on top. 0 hints.
* **Upstream robustness**: retranslating the arena or the FBA for another Zig version, or a
  fixture with permuted struct fields, needs a regeneration and no hand edit to build.
* **Mutants fail closed**: seeded bugs in the translated FBA and arena entries (in the style of
  `tests/roadmap/alloc-arena/mutant.sh`: an `alloc` that reserves nothing, a `free` that moves
  `end_index` back for a slice that is not the last one) get no invariant that checks. The generator reports residual goals and the
  build fails.
* **Determinism**: `scripts/regen.sh` twice gives byte-identical `Inv.lean` files, with the
  network disabled.
* **Cost**: generation at most 15 minutes per module on the development Mac with a warm cache;
  proofs within their current heartbeat budgets.

## (d) Staging

Each stage is a permanent part of the end state, and none adds a shim.

| Stage | Content | Removes |
|---|---|---|
| S0 (this PR) | design, register P09, vacuity spike | — |
| S1 (fsym lane) | engine oracle outputs: residual-goal attribution and machine-readable stop reasons (P09-E1, extends #14/#15), strongest post at returns for the sequential and thread backends (P09-E2), the missed atom of a failed plan (P09-E3) | — (also improves diagnostics of hand proofs) |
| S2 | `@[fsym_inv]` (P09-E4); generator skeleton with layers 1–2 for loops; the `invgen` regen step and the gen-integrity record | hand invariants and step/loop lemmas of `Linked.lean`, `Alloc.lean` (`freeAll`), `loop-tactics/Queue.lean` |
| S3 | library list/chain family (lists' `lseg` and the arena's `Chain` in one); struct, slice and access-mode atoms; the numeric domain; FBA invariant generated (main's version, no ledger) | FBA hand `fown`; the duplicate chain lemmas of `Reset.lean` |
| S4 | `@[fsym_upd]` (P09-E5); the bump-ledger family with its generic updates; FBA ledger and arena invariants generated; creation triples and companions | FBA ledger hand updates (`alloc_upd` … `reset_upd`, `FCov.*`); arena `OV`/`FV`, updates (`free_last_upd` …), `Reset.lean`; the 12 arena macros and their allow-list entries (with the arena lane's move of macro steps into general rules, row #9) |
| S5 | layer 4: hints file format, provenance, offline producers | — |
| S6 | acceptance measured; P09 complete; P03's "invariants and measures are not inferred" closed | — |

P09-E1 is implemented: `Auto.runReport` returns residual attribution, and `fsym.report` emits
the documented JSON schema. P09-E2 and P09-E3 are implemented
(`docs/proof-automation.md`, §Inferred posts and §Machine-readable residual reports), so S1 is
complete:

* **P09-E2.** An unknown postcondition is inferred as the strongest post of the walk's returns,
  in the sequential, thread and concurrent backends. This includes an unknown applied to computed
  arguments, such as a loop step's exit `(label, s)`, whose returns are joined when its walk
  ends. A loop with a registered invariant and no registered `B.post` continues from the
  strongest post of its step's exits. The report's `posts` lists each inferred post (`return`,
  `loop_exit`).
* **P09-E3.** A stop with no rule, or an invariant that does not hold at a loop's entry, lists in
  its origin's `plans` the rules whose precondition had no plan. Each comes with the atoms it
  missed and their unknowns: the abduced anti-frame.

The generator does not read either output yet. It still emits `B.post` from its reading, which
the callers' walks check. Reading the inferred exit post instead, and the bi-abduction loop over
`plans`, are generator work of S2 and later, not engine work.

P09-E4 is implemented (`docs/proof-automation.md`, §Loops): `@[fsym_inv]` registers `B.inv`,
`B.meas` and the exit post `B.post` of a loop body `B`, and `air2lean-invgen` emits all three
with the attribute. The exit post was registered because the invariant alone forgets the exit's
label and test, which a translated caller matches on. Since P09-E2, `fsym` infers the strongest
post at a loop's exits when no `B.post` is registered. Since 2026-11-24 the registry is keyed by
the body and the walk's mode: a body also registers `B.credits.inv` and `B.credits.post` for a
walk that pays its steps with credits ("Implemented: the credit mode" below).

### Implemented: counted loops (S2, first slice)

`air2lean-invgen` (`Air2Lean/InvGen.lean`, executable `Air2Lean/InvGenMain.lean`, lake target
`air2lean-invgen`) is the generator of decision 5: a compiled Lean program in this package, with
no `syntax`, `macro`, `elab`, tactic or command. `air2lean-invgen MODULE NAMESPACE --source SRC -o FILE`, run
under `lake env`, imports the translated module (and `ZigLean.Sep.Full.AutoAll`, for the
pruning walks of S2f), finds every `Zig.loop body again` in its
definitions and reads the body as the elaborated term that `fsym` walks: a symbolic run over
`bind`, `pure`, `get`, `modify`, `ite`, the lifted `Zig.load`/`Zig.store`/`Zig.add`/`Zig.sub`/
`Zig.intCast`, the unsigned comparisons and `!=`, `Zig.tick` and a `match` on a known exit gives
each path of one iteration with its guard, its result, the adds and subtractions it ran and its
changes to the locals and to the cells behind pointer parameters. This reading only proposes; it
is not a semantics anything relies on, and `fsym` decides inside the generator which of its
candidate facts stay (Houdini pruning, S2f below). It writes `Inv.lean`: a first line
`-- air2lean-invgen: {…}` recording the generator's revision (its Lean version and the SHA-256 of
each of its modules, as `translator_revision%` records the translator's), the inputs it read (the
translated module's source, `--source`, with its SHA-256), the module, its namespace and, per
loop, the family or why the loop has none; then the `def`s, registered with `@[fsym_inv]`. A module with no loop, or a loop
body outside the given namespace, is an error. `scripts/invgen.py check|write` regenerates every
committed `Inv.lean` (its `TARGETS` table); it is the `invgen` step of `scripts/regen.py`, right
after `gen`, so a retranslation regenerates the invariants with it.
Each loop's entry in the record names the function that runs the loop and that function's
**semantic fingerprint** (S2b, `docs/stable-generation.md`): `scripts/invgen.py` translates the
module's committed AIR again (its case of `scripts/gen-integrity.py`) with `--source-map-json`,
computes the fingerprints of its functions (`scripts/semantic-fingerprints.py`) and passes them to
the generator (`--fingerprints`). The fingerprint is the documented one without the translator's
and the runtime's revisions: those change every fingerprint at every translator or runtime
change, and would make every `Inv.lean` change with them, while the input hash already covers a
change of what the translator emits and `scripts/invgen.py check` a change of the library's
pruning. So a recorded fingerprint changes when the function's translated AIR, a callee's, the
target profile or the translation options change, for example on a retranslation for another
Zig version. When a file is stale, `scripts/invgen.py check` names the functions whose
fingerprints changed and their loops.
The record also holds the SHA-256 of the rest of the file. `scripts/gen-integrity.py invgen`
(preflight, also without a translator) checks each target's record against the checkout without
running Lean: a changed generator module, toolchain or input makes the file stale, a hand edit
below the record or a record of another module (or of another generator) fails, and so does a
record outside the targets. (The record's `loops` summary, with the pruning decisions, is not
hashed: an edit there changes no definition.) The `invgen` regen step still always runs the
generator: a runtime (`ZigLean`) change can change how an unchanged translation elaborates and
which candidates `fsym` prunes, which the record does not hash (hashing the runtime would mark
every `Inv.lean` stale at every runtime change). So a library change can make a committed
`Inv.lean` stale without `gen-integrity.py invgen` noticing; `scripts/invgen.py check` (the
`invgen` regen step, and each fixture's `check.sh`) finds it.

The slice's family is the **counted loop** (widened in S2c, below): one repeating path, guarded by an unsigned `x < b`
(`b` a local the loop does not write, a loop parameter or a literal), that adds 1 to the local
`x`, adds a constant `cₖ` to each cell `*pₖ` it writes (an unsigned word behind a loop
parameter), writes no other local and runs no add other than partial sums of these; and exit
paths, guarded by `¬ x < b`, that touch no memory and no local. For the loop body `F.loopN` the
generator writes `F.loopN.inv params s0 v₀ … s` (the other locals pinned to the entry locals
`s0`, `s0.x ≤ x ≤ b`, each cell `vₖ + cₖ * (x - s0.x)` and the no-overflow fact
`vₖ + cₖ * (b - s0.x) < 2 ^ w` of its checked adds, and `plain` when the body ticks) and
`F.loopN.meas params s := b - x`, and the exit post `F.loopN.post params s0 v₀ … r` (the exit's
label, the other locals at their entry values, the counter at its exit value `b` and each cell at
`vₖ + cₖ * (b - s0.x)`).
`fsym` applies `FTotalTriple.loop_measure` with the three at the loop (P09-E4), so a caller's walk
needs no loop lemma. The invariant needs `s0.x ≤ b` at entry: the client
establishes it (a loop entered past its bound is not an instance). Every other loop gets no definition and the reason (a nested
loop, a call, a signed test, a second test, a cell at an offset, an increment that is not a
constant, an uncovered add, a literal that wraps, a parameter named like a generated binder, …): a
proof that needs it does not build.

First client: the inner loop `pairs.loop14` of `tests/roadmap/loop-tactics/nested` (the
translated `while (j < i) : (j += 1) acc.* += 1`). Its hand-written `innerI` and measure are
deleted; `Proof.lean` imports the committed `Nested/Inv.lean`, and the walk of the outer body
(`outer_step`, by `fsym`) applies the inner loop's registered invariant, measure and exit post:
no inner step or loop lemma (P09-E4 deleted `inner_step` and `inner_loop`), and `pairs_total` is
unchanged. `nested/check.sh`:

* regenerates `Inv.lean` from the committed translation and compares it byte for byte
  (`lake exe air2lean-invgen`, as `scripts/invgen.py check` does);
* checks the proof against it;
* checks three seeded mutants of the generated file (a wrong cell relation, a dropped bound `x ≤ b`,
  a measure that does not decrease): each still elaborates, and the proof then fails with an
  elaboration error inside `pairs_total`, the theorem whose walk runs the inner loop (until S2c′,
  the hand-written `outer_step`).

The outer loop `pairs.loop5` runs a loop in its body. Since S2c′ (below) its invariant is generated
too, from the inner loop's exit post; the hand `outerI` is deleted, and so are `outer_step` and
`outer_loop`: `pairs_total` is a bare `fsym`, whose walk of each outer iteration applies the inner
loop's definitions, so the mutants above now fail inside `pairs_total`.

### Implemented: the counted family widened (S2c)

The counter may go up or down by 1 (`Zig.add`/`Zig.sub`), under any unsigned test of it that
moves towards the bound: `x < b` and `x <= b` going up, `x > b` and `x >= b` going down, and
`x != b` either way, with the counter on either side of the test and either branch of an order
test repeating (`¬ x < b` repeating is `x >= b`; `==` is outside the family, as are a `>= 0` and a
`<= maxInt` test, which hold until the step wraps). As in S2, the invariant holds at entry only for
a counter that starts on the repeating side of its exit value or at it; the client proves that.
The bound may also be the length of a slice parameter (`p.len`) or a cell the loop only reads
(`*p`, read in every iteration); a read-only cell is owned at its entry value `vₖ`, and a measure
with it as bound takes `vₖ`. The invariant bounds the counter between its entry value and the
value it exits at; for `<=` and `>=` that value is one past the bound, so the invariant carries the
fact that the counter's step there does not wrap (`b + 1 < 2 ^ w`, resp. `1 ≤ b`): `upLe(n)` with
`n` the largest `u32` panics, and its proof must exclude it. Each written cell is
`vₖ + cₖ * d` (`d` the iterations so far: `x - x₀` going up, `x₀ - x` going down) with the
no-overflow fact `vₖ + cₖ * n < 2 ^ w` (`n` all iterations); the measure is the iterations left.

Client: `tests/roadmap/loop-tactics/counted`, the retained Zig 0.17.1 AIR of `counted.zig`, one
exported function per shape (`down`: `i > 0`, `i -= 1`, `acc.* += 3`; `upNe`; `upLe`; `lenCount`
over `xs.len`; `readBound` over `lim.*`). `Proof.lean` proves each function's total triple
(`F_total`) by `fsym` alone, with the generated invariant, measure and exit post: no hand
invariant and no step or loop lemma. No other loop in the corpus has these shapes in the full-state logic: the translated
counted loops of `Proofs/` (`sum`, `find`, `sumDigits`, `advance`, `totalWeightedTardiness`,
`dot`) are pure-layer loops (`Zig.loop_spec` over `M`, not `MM` over memory) whose invariants are
prefix sums over array items, and `Proofs/Slices/Sep.lean`'s `reverse` swaps items (S2e).
`check.sh` (shared with `nested` through `../invgen-fixture.sh`) regenerates and compares the
translation and `Inv.lean`, checks the proof, and runs the seeded mutants of `mutants.json`
(`../invgen_mutants.py`): a wrong down-counting relation, a dropped `x ≤ b` under `!=`, a dropped
`x ≤ b + 1` of a `<=` counter, a measure that does not decrease over a slice length, a
dropped read-only cell and an exit post that is too strong (`down`'s counter at `1`, which its
caller does not need, so only the loop rule's exit obligation rejects it) each fail inside their
function's theorem. (A dropped no-wrap fact of the
`<=` counter is not among them: the walk runs in `upLe_total`'s context, whose premise
`n + 1 < 2 ^ 32` restores it.)

### Implemented: array items, counter-dependent sums, inner loops (S2c′)

Three more shapes of the counted family, each a general reading (no per-loop case):

* **Items of an array parameter.** A body that indexes a parameter `p` with a literal index
  (`Zig.ptrProject p (·.elem size k)`; `p` itself is item `0`) accesses an array (`arraysOf`
  finds such parameters before the reading; every access through `p` is then an item). The
  invariant owns it as one atom, `up (arr p (x₀ :: … :: xₘ :: tₚ))`: the items up to the last one
  the body reaches, each written item `xₖ = wₖ` an existential with its facts (as a written cell:
  `wₖ = vₖ + cₖ * d`), each item it only reads at its entry value `vₖ`, and the rest `tₚ` (a
  parameter of any length, so the invariant fits every array at least that long). `fsym` walks
  the items by `FTotalTriple.arr_load`/`arr_store` (item `0` by `arr_load_zero`/`arr_store_zero`)
  and matches the stored list against the invariant's constructors (closed ledger row
  #atom-args-normal-form). Client: `counted.pairAt` (`acc[0] += 1; acc[1] += 2`), `pairAt_total`.
* **A cell that goes up by a value of the counter.** In a loop that counts up, an increment may be
  a value `g u` of the counter's value `u` at the iteration's start (also of the parameters, the
  locals the body does not write and the cells it only reads; the constant part joins `g`). With
  the library sum `tsum n g` (`ZigLean/Sep/Full/TSum.lean`, `g u` over `u < n`) the invariant is
  linear: `v + (tsum e g - tsum x g) = vₖ + (tsum e g - tsum x₀ g)` (`e` the counter's exit
  value: the increments still to come plus the cell stay at the entry value plus all of them),
  with the no-overflow fact `vₖ + (tsum e g - tsum x₀ g) < 2 ^ w`, and the exit post
  `v = vₖ + (tsum e g - tsum x₀ g)`. `fsym` walks the step: the counter's step relates
  `tsum x.toNat g` to `tsum (i.toNat + 1) g` by the congruence of atoms (closed ledger row
  #arith-atom-congruence), and `tsum_sub_of_lt` under the loop test bounds the add. Client:
  `counted.tri` (`acc.* += i`), `tri_total`. A loop that counts down with such an increment is
  outside (recorded): its sum runs over the values above the counter, a form the arithmetic has
  no regression for.
* **An inner counted loop** (`execInner`). A body that runs `Zig.loop inner again` reads the inner
  body as a counted loop over the same locals and continues after it with the inner loop's exit
  post as values: the inner counter at its exit value, each cell it writes up by its constant
  increment times the distance its counter goes. A cell that the inner loop moves by a distance
  that depends on the outer counter is then a counter-dependent sum (above). The inner counter is
  a **scratch local**: the body sets it before it reads it, so no path reads its value at an
  iteration's start, and the invariant and the exit post do not state it. The generator
  generates the inner loop first (`generate` orders the loops by the loops their bodies run) and
  puts its generated definitions in front of every walk of the outer loop's step (`Cand.deps`),
  which applies them at the inner loop as a client's walk does. Client: `nested.pairs.loop5`; its
  hand invariant `outerI`, `outerPost`, `outer_step` and `outer_loop` are deleted and
  `pairs_total` (unchanged statement) is a bare `fsym`. An inner loop with an increment that is not
  a constant, with a loop of its own or with several exits is outside (recorded).

An outer body that runs an inner loop which takes steps gets no credit-mode definitions (the record
says why): one run of it takes more than the one step that the counted loop rule pays with one
credit, so its exact count is not the outer measure.

A file whose definitions name `arr` or `tsum` imports `ZigLean.Sep.Full.Arr` or
`ZigLean.Sep.Full.TSum` (`Cand.imports`), and only then.

### Implemented: Houdini pruning (S2f)

The reading proposes candidate facts, and `fsym` decides which of them stay (`houdini` in
`Air2Lean/InvGen.lean`). Every candidate holds at loop entry (`s = s0`, each cell at its entry
value) or is an entry obligation of the family that the client discharges:

* the pinned locals;
* the counter on either side of its entry value (`x₀ ≤ x` and `x ≤ x₀`);
* the counter on the repeating side of its exit value (the family's entry condition);
* the no-wrap and no-overflow facts (constraints on the entry values only, so no walk can drop
  them);
* each written cell counted both up and down from its entry value (`v = vₖ + cₖ * (x - x₀)`
  and `v = vₖ + cₖ * (x₀ - x)`; a cell that goes up by `0` keeps both, so it gets only the one
  of the reading's direction).

So the reading no longer chooses the side of the counter or the direction of a cell's count;
the checker does. Pruning works in four steps:

1. The generator writes a check (`Cand.check`): each kept candidate as a definition
   `F.loopN.candᵢ`, the invariant over them, the measure, and one iteration's step triple. From
   the invariant, a repeating iteration ends in the invariant with a smaller measure, and an
   exiting one ends in the invariant (in the counted family, an exit changes no local and no
   memory).
2. It elaborates the check with `Lean.Elab.process` in its own environment, with the opens of
   the generated file. `InvGenMain` imports the translated module and
   `ZigLean.Sep.Full.AutoAll`, so the step's proof is `unfold …; fsym` with `fsym.report` on:
   `Auto.runReport`, the single entry point.
3. It reads the report (P09-E1). A residual whose origin is the postcondition and whose goal is
   a candidate's definition names that candidate: a candidate named as a definition stays folded
   when `fsym` cannot prove it, while an inlined conjunct comes back split, over fresh names, and
   could not be traced to its candidate. The walk drops those candidates.
4. It repeats until a walk leaves no residual. That walk is a proof of the step with the kept
   candidates, kernel-checked inside the generator.

The following mean no invariant (fail closed), and the loop is recorded with the reason:

* a residual that no candidate explains (the measure, an overflow, a missed atom);
* any error besides those residuals' unsolved goals (an ill-typed candidate is such an error,
  never a pruned fact);
* a walk that does not give exactly one report.

Each walk drops at least one candidate, so the fixpoint takes at most one walk per candidate,
plus one. Each loop runs with its own heartbeat budget.

The output is the definitions with the kept facts written out, in the S2c text, registered
with `@[fsym_inv]` beside the exit post `F.loopN.post` (P09-E4). The post is no candidate: after
the fixpoint the generator walks the output once more, with the post at the exit as the loop rule's
step has it, and a residual there means no invariant (fail closed, at generation). The callers'
proofs check the post again. The proofs of the
fixtures, which are the kernel checks that count, are bare `fsym` walks of the callers. Every pruning decision is
in the record: each loop's entry in `loops` lists, under `pruned`, the dropped fact, the walk
that dropped it and its residual goal there. On every loop of `counted` and on `nested`'s inner
loop, the first walk drops the wrong side of the counter and the wrong direction of the cell's
count, and the second walk proves the step: about 20 s for both targets, with `fsym` in Lean's
interpreter. Two seeded mutants of `counted/mutants.json` check the pruning against the proof:

* `houdini-pruned-kept` puts the pruned `s0.i ≤ s.i` back into `down`'s invariant;
* `houdini-kept-dropped` drops the kept `s.i ≤ s0.i`, which the proof needs.

Each fails inside `down_total`, whose walk applies `down`'s registered invariant. A generated invariant is only as strong as the candidates. A loop
whose proof needs a fact that is not a candidate gets an invariant that is too weak, and its
proof fails.

### Implemented: a list walk with a call, by the call's contract (S2d, layer 3 for one call)

A walk may hand each node to a call: `while (p) |n| { p = n.next; a.destroy(n); }`
(`freeAll.loop5` of `Proofs/Lists/Open.lean`, a `CM` body). Its invariant needs what the call
takes and leaves, which only the call's contract says. So the generator takes contracts:

    air2lean-invgen MODULE NAMESPACE --source FILE --spec SPEC SPECFILE --contract RULE -o FILE

`SPEC` is a hand-written specification module (it is imported, and its source is an input of the
record), and `RULE` a theorem of it about the function that the loop calls,
`∀ ys, T P (f as) (fun _ => Q)`. This is the first piece of the design's **spec header**: the
contract is specification, the invariant between the contracts is generated. `scripts/invgen.py`
lists such a target's module and rules in `CONTRACTS`; `scripts/gen-integrity.py invgen` checks
them and the specification's hash in the record. A file generated with contracts holds the loops
that call by one of them; the module's other loops stay in its file without contracts.

The generator reads the body as before (now also a body of `CM Tgt σ ε`, checked as a `CTriple`
step; an instance parameter `[Ext]` of the body is an explicit parameter `inst0` of the
definitions, as `@[fsym_inv]` wants them). At a call `callC (f as)`, `callM` or `callMC` of a
function with a given contract it reads the contract (`readContract`, in order, the first that
fits):

* The call fixes the rule's variables: one is the node's pointer (the cursor's payload), the
  others are terms over the loop's parameters (`ctx := p0.ptr`, `vtp := p0.vtable` for the rule's
  `⟨ctx, vtp⟩` at the loop's `p0`), found by unifying the rule's command with the call.
* The precondition's atoms (through reducible definitions, so a node may be written by its
  layout's name) that name the node's pointer or the value of one of its fields
  (`up (pts (p.add k) a y)`) are **the node** (`F.loopN.node`); the others are **the frame**.
* The postcondition must return the frame atom for atom. What it holds besides is **what the
  call leaves of a node** (`F.loopN.done`): the fee and `I.freed p` for `destroy`, the node
  itself for a call that only reads it.

The invariant of the walk `w` with the contract is then, with `xs` the list's items:

    ∃ ys zs, ⟪xs = ys.reverse ++ zs ∧ zs.length = n ∧ …⟫ ⋆
      listSegRev (F.loopN.done …) s0.cur s.cur ys ⋆ listSeg (F.loopN.node …) s.cur none zs ⋆
      frame ⋆ plain

and the exit post `listSegRev (F.loopN.done …) s0.cur none xs.reverse ⋆ frame ⋆ plain`. Its
parameters are the loop's, then the contract's variables that the node, the frame or a node
passed names (`fns`, `I`, `φ`), which the plan at the loop's entry determines; a variable that only
a node passed names is rejected (nothing at the entry determines it). The contract's other
variables (its hypotheses, here `h : CAllocSpec …` and the `e` it names) are binders of the step's
check only, and the check walks the call by the contract (`fsym [fun p v q => @RULE … p v q h]`).
A client's walk passes the contract itself, as for any call.

**Why `listSegRev`.** The nodes passed are the segment at the `done` layout *told from its end*
(`ZigLean/Sep/Full/ListSeg.lean`: `listSegRev N hd tl (v :: vs) = ∃ p, N p v tl ⋆ listSegRev N hd
(some p) vs`, and `listSeg_of_listSegRev`: it is `listSeg N hd tl vs.reverse`). A visit without a
call joins a node to `listSeg` at its end by the update `listSeg_snoc_upd`, whose arguments (the
item `v`, the next pointer `q`) `fsym` reads from the node's atoms. What `destroy` leaves of a
node names neither, and the update is then rejected (`tryUpd`: an argument that its precondition
does not determine; kernel-checked in experiments on `freeAll`, 2026-11-24: with the nodes passed
as `listSeg done s0.p s.p ys` the walk reaches the repetition and stops there, also with the item
given). Told from its end, the node joins by the *constructor*, as the prefix of a reversal does:
the planner's constructor fold takes the next pointer from the goal's own index and the item from
the list's equation. So this needs neither a fold over an unknown `Nat` (the count of fees, the
obstruction recorded for the hand-written attempt of 2026-11-07) nor the updates registry
(P09-E5).

Outside this slice, each recorded with its reason (fail closed): two calls in one iteration, a
call before the body's last access to the node or with a store to the node, a call on another
node or that takes a value of the body, a contract that does not return its frame, that owns
more than one value of the node besides `next`, whose postcondition reads the result or that
returns a value.

Client: `Proofs/Lists/AllocInv.lean` (target of `scripts/invgen.py`; specification
`Proofs/Lists/AllocNode.lean`, contract `Lists.Alloc.destroy_fields`, for every allocator that
meets `CAllocSpec`). `Proofs/Lists/Alloc.lean`'s `freeAll_done` is a bare
`fsym [destroy_fields …]` over the generated invariant; `freeInv`, `freeAll_step_nil`,
`freeAll_step_cons`, `freeAll_step` and `freeAll_loop` are deleted, and `freeAll_freed` and
`freeAll_spec` are unchanged statements (the nodes passed are the fees and `freedSeg`,
`fees_freed_of_done`).

### Implemented: the credit mode (a second invariant per loop body)

A statement with an exact step count (`sum_exact`, `freeAll_exact`) walks its loop while paying
each body run with a credit. Its invariant is the plain-mode one without `plain`, at the exact
count of the body runs left. `@[fsym_inv]` held one invariant per loop body, the plain-mode one,
so these loops stayed hand-written (`sumInv`, `freeInvExact`, hand-applied `loop_exact`).

**Maintainer decision (2026-11-24): a loop body registers a second invariant, selected by mode.**
Rejected: one mode-generic invariant with a higher-order parameter `K : Nat → FAssn` for the
mode's resources (the planner cannot assign a higher-order unknown at the loop's entry), and
keeping the hand-written loops. This is an extension of the `@[fsym_inv]` registry only: no new
attribute, tactic or judgment, and the updates registry (P09-E5) is not needed.

* **The registry's key** is the loop body and the mode (`LoopMode`: `plain`, `credits`), read off
  the registered name: `B.inv`, `B.meas`, `B.post` are the plain mode's, `B.credits.inv` and
  `B.credits.post` the credit mode's (`ZigLean/Sep/Full/AutoAttr.lean`).
* **Selection** (`docs/proof-automation.md`, §Loops): the walk is in the credit mode at a loop
  when its state holds `credits n` and neither `plain` nor `unmetered`. `fsym` then applies the
  counted loop rule (`FTotalTriple.loop_exact`, `CTriple.loop_exact`) with the credit parts; the
  rule adds `credits (n + 1)` and returns `spent (n + 1)`, so the invariant names neither.
* **One mode registered.** Plain walks are unchanged. A credit walk at a body with only a
  plain-mode invariant is an error that names the missing definition. `fsym` never falls back to
  the plain-mode invariant, which would change what the walk means.
* **The generator derives the credit parts from the plain ones**, for every family alike
  (`Cand.creditOutput`, `creditOf` in `Air2Lean/InvGen.lean`). After the Houdini fixpoint and the
  check of the exit post:
  1. the credit candidate is the plain one's kept facts and resources without `plain`, with the
     count `n` as last parameter. The count is the family's measure read exactly: a list walk's
     ghost measure is the count already (`zs.length = n`, the nodes left), and a counted loop's
     measure `B.meas` (the iterations left) becomes the fact `n = meas`;
  2. the generator walks the counted rule's step with it (`Cand.creditCheck`): from the invariant
     at `n` and one credit, a body run returns one receipt and repeats at exactly `n - 1` or
     exits at `n = 0` with the exit post;
  3. a walk with no residual gives `B.credits.inv` and `B.credits.post` (registered), and the
     record's loop entry gets `"credits": {"count": …}`. Any residual or error gives no credit
     parts and `"credits": {"none": why}` (a body that takes no step has nothing to count). The
     plain parts are emitted either way.

  The measure is exact for both families because each body run moves it by exactly one and the
  exit is at zero: a counted loop's counter moves by 1 towards its exit value, and a list walk
  passes one node. A family whose measure is only an upper bound would fail step 2 and get no
  credit parts.

The counted fixture proves two of its functions with their exact step counts too (`down_exact`,
`upNe_exact` in `tests/roadmap/loop-tactics/counted/Proof.lean`: `n + 1` credits in, `n + 1`
receipts out, by `fsym` alone), and three seeded mutants of the credit-mode definitions fail
inside them: a wrong count (`n = 2 * meas`), a dropped count, and a credit-mode invariant that
keeps `plain`. Because a loop's two invariants repeat their facts, a mutant of `mutants.json`
may name the definition it changes (`def`); `old` then occurs exactly once in that definition.

Clients (instances, not special cases): `Proofs/Lists/OpenInv.lean` (`sum.loop6`,
`reverse.loop6`), `Proofs/Lists/AllocInv.lean` (`freeAll.loop5`, a `CM` body with a call),
`tests/roadmap/loop-tactics/counted` and `nested` (the counted family). `sum_exact`,
`sum_loop_exact` and `freeAll_exact` are unchanged statements proved by `fsym` over them;
`sumInv`, `sumPost`, `sum_step`, `freeInvExact`, `freePost`, `freeAll_step_nil_exact`,
`freeAll_step_cons_exact`, `freeAll_step_exact` and `freeAll_loop_exact` are deleted.

### Implemented: retranslation needs a regeneration only

The acceptance sentence "retranslation for another Zig version or with permuted struct fields
needs regeneration only" is checked mechanically for every client of the generator
(`tests/roadmap/loop-tactics/check-variants.sh`, CI step "Retranslated loop-invariant clients").

A **variant** of a client is a fixture root that holds another translation of the same program
under the module names of the first one, and the `Inv.lean` files generated from it
(`scripts/invgen.py` `VARIANTS`; the translations are rows of `scripts/gen-integrity.py`
`FIXTURES`, the invariants targets of `scripts/invgen.py`, so `scripts/regen.sh` regenerates both
and preflight checks their records like the first translation's). The hand-written files, the
specifications and the proofs, exist once. For each variant `invgen_variants.py`

1. checks that the translation is the translator's output for the variant's committed AIR and
   that each `Inv.lean` is the generator's output for that translation: the two regenerations;
2. elaborates the client's hand-written files against the variant, unchanged
   (`scripts/lean_overlay.py`: the variant's modules replace the first translation's, each
   module that imports a replaced one is compiled again, and Lean's search path has the
   replacements in front of the Lake package's own library);
3. applies each seeded mutant of the client's `mutants.json` to the variant's generated
   invariants and requires the proof to fail inside the mutant's theorems.

| Client | First translation | Variants |
|---|---|---|
| `tests/roadmap/loop-tactics/counted` (`Proof.lean`, 14 mutants) | Zig 0.17.1 | 0.16.0, 0.15.2, 0.14.1 |
| `tests/roadmap/loop-tactics/nested` (`Proof.lean`) | Zig 0.16.0 | 0.17.1, 0.15.2, 0.14.1 |
| the linked list of `Proofs/Lists` (`Linked.lean`, `AllocNode.lean`, `Alloc.lean`, `Bounded.lean`, `loop-tactics/Queue.lean`; mutants `loop-tactics/lists/mutants.json`) | Zig 0.17.1 | 0.16.0, 0.15.2, 0.14.1 (the AIR of `tests/roadmap/interfaces`), `permuted`, `layout` |

The list's `permuted` variant is `examples/lists/lists.zig` with the fields of `Node` in the other
order (`tests/roadmap/loop-tactics/lists/permuted/lists.zig`; the check requires that the two
sources differ in nothing else).

What the slices do not have yet (next slices, sizes S < M < L):

| Next | Content | Size |
|---|---|---|
| S2b | **Done** (2026-11-25): each loop's entry in the record names its function and that function's semantic fingerprint, and `scripts/invgen.py check` names the functions that changed (above) | S |
| S2c′ | **Done** (2026-11-25): array items, counter-dependent sums and inner counted loops ("Implemented: array items, counter-dependent sums, inner loops"). Still outside: a counter-dependent increment in a loop that counts down, an inner loop whose increments are not constants, loops nested three deep | M |
| S2d | the list-walk family on the library list family (layer 1, measure the ghost list's length): `revInv`, `sumInv` (`Proofs/Lists/Linked.lean`), `freeInv` (`Proofs/Lists/Alloc.lean`), `loop-tactics/Queue.lean` unchanged on top. Not covered yet (checked 2026-11-06 by running `air2lean-invgen Proofs.Lists.Gen Lists`): `reverse.loop6` and `sum.loop6` give "an unsupported term: i8.isSome", and `freeAll.loop5` gives "an unsupported term: i7.isSome". The loop test is on an optional node pointer (`?*Node`), not on a counter. The engine side is done (ledger #list-walk-step, `docs/proof-automation.md`): `fsym` splits the ghost list at the cursor's test, folds the node back constructor by constructor at a repetition (a node at a segment's end by the caller's update `lseg_snoc_upd`), and applies an `@[fsym_inv]` invariant with a ghost measure (`B.inv … s n`, the nodes left, which the locals do not determine; `loop_ghost_ex`). `Proofs/Lists/Linked.lean`'s `reverse` and `sum` are bare `fsym` walks; their step and loop lemmas are deleted. **Generator done (PR #725)**: `air2lean-invgen` reads `Option.isSome`/`some`/`Zig.optPayload` on an optional-pointer cursor and the loads and stores of a node's fields (`Zig.ptrProject` offsets), recognizes a list walk (a visit, or a reversal that points each node back to a prefix local; accumulators that add the item or a constant), and emits the invariant, with a ghost measure, over the library list family `listSeg` (`ZigLean/Sep/Full/ListSeg.lean`, the S3 list family) at the node layout read off the body (`F.loopN.node`: `next`, the item field if read, the rest as a parameter); the facts are Houdini candidates, the step's walk with the exit post decides. `Proofs/Lists/OpenInv.lean` (target of `scripts/invgen.py`) replaces the hand invariants of `Linked.lean`, whose `node`/`lseg`/`list` are the family's instance; `reverse` is proved for every node with a `next` field. **`freeAll.loop5` done** (2026-11-24, "a list walk with a call" above): the generator reads `CM` bodies and the contract of the call (`--spec`/`--contract`), and states the nodes passed over `listSegRev` at what the contract leaves of a node, so no fold over an unknown `Nat` is needed; `Proofs/Lists/AllocInv.lean` replaces `freeInv` and the hand step and loop lemmas of `Proofs/Lists/Alloc.lean`. **Exact step counts done** (2026-11-24, "the credit mode" above): `sum_exact` and `freeAll_exact` walk their loops from generated credit-mode invariants, the second registration of the body | L |
| S2e | loops over array contents (`Proofs/Slices/Sep.lean`'s `revInv`: quantified item facts from a permutation template) | L |

S3 to S6 follow the staging table above.

The arena lane does not rewrite the arena invariant by hand in the meantime (coordinator,
2026-10-14). Its work after #337, moving the macro steps into general `fsym` rules, is a
prerequisite of S4, not a parallel invariant.

### Engine ledger rows

New rows. Numbers are assigned when the fsym lane records them in its ledger.

* **P09-E1** residual-goal attribution: each goal `fsym` leaves names its origin (the
  postcondition conjunct, the side condition of which rule). Stop reasons are returned in
  machine-readable form by `Auto.runReport`, using the shared `Auto.run` entry (extends #14, #15).
* **P09-E2** strongest-postcondition inference at returns for `FTotalTriple`/`FTriple` and the
  thread backends, as `inferPost` does for `WP` segments.
* **P09-E3** abduction report: at "no plan for its precondition", return the missing atom with its
  unknowns.
* **P09-E4** `@[fsym_inv]` loop-invariant registry: apply the backend's loop rule with the
  registered invariant and measure; parameters by the planner, frame inferred.
* **P09-E5** `@[fsym_upd]` ghost-update registry, keyed by heads, tried at returns. It generalizes
  the caller updates of 9f.

Existing open rows on the path: #55 and #60 (cost in large states: generation runs many
walks over the arena's state), #58, #59, #61 (arena planning), #62 (struct ownership in a thread),
#64–#67 (the FBA updates' workarounds, which E5 and the bump-ledger family replace).

## Maintainer decisions (2026-10-15)

1. **Placement: approved.** The offline generator plus the registries `@[fsym_inv]` and
   `@[fsym_upd]` and the oracle outputs E1–E3. Engine requests P09-E1 to E5 are approved.
2. **The specification boundary: approved.** `fits`, the creation precondition and the visible
   parameters are hand-stated. A creation triple with an `FAdmit` companion is mandatory for every
   instance, including an arena creation theorem that does not exist today.
3. **Register status: `open`** (no new `planned` status).
4. **External hint producers: open.** Whether LLMs or CHC solvers (Z3/Spacer, Eldarica) may produce
   hints, and what source may be sent to an external service, is not decided. Until it is, the
   generator uses no external producer; the acceptance targets need none.
5. **Generator home: the `Air2Lean` package**, a Lean executable importing `ZigLean.Sep.Full.Auto`.
