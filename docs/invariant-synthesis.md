# Invariant synthesis (P09)

Status: design, approved as part of the end state by the maintainer on 2026-10-14. Nothing here is
implemented yet. Register entry: `assurance/register/P09.md`. Spike:
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
| FBA with reset ledger (`codex/fba-reset-ledger`, unmerged) | 782 | 15 | 20 | 0 | adds six hand ghost updates (`alloc_upd` … `reset_upd`) and `FCov` lemmas, passed as `fsym [u]` |
| Arena `tests/roadmap/alloc-arena/AllocArena/Core.lean` | 2769 | 95 | 68 | 11 tactic + 1 command | invariant `own`/`OV`, ghost updates `free_last_upd` …, hand `CTriple` walks inside macros |
| Arena `AllocArena/Reset.lean` | 668 | 23 | 8 | 0 | chain split/join, coverage and release lemmas |
| Arena `ArenaSpec.lean`, `ArenaSpecFixed.lean`, `ArenaSpecMacos.lean` | 328 / 214 / 211 | 13 / 12 / 12 | 7 each | 0 | loop invariants `Inv9`, `Inv19`, `Lists9` by hand; `count_loop` by hand induction |
| Lists `Proofs/Lists/Linked.lean` | 269 | 15 | 7 | 0 | `revInv`, `sumInv` and their `*_step`/`*_loop` lemmas by hand |
| Lists `Proofs/Lists/Alloc.lean` | 377 | 22 | 11 | 0 | `freeInv`, `freePost`, `freeAll_loop` by hand |

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

The arena lane does not rewrite the arena invariant by hand in the meantime (coordinator,
2026-10-14). Its work after #337, moving the macro steps into general `fsym` rules, is a
prerequisite of S4, not a parallel invariant.

### Engine ledger rows

New rows. Numbers are assigned when the fsym lane records them in its ledger.

* **P09-E1** residual-goal attribution: each goal `fsym` leaves names its origin (the
  postcondition conjunct, the side condition of which rule). Stop reasons are returned in
  machine-readable form by `Auto.run` (extends #14, #15).
* **P09-E2** strongest-postcondition inference at returns for `FTotalTriple`/`FTriple` and the
  thread backends, as `inferPost` does for `WP` segments.
* **P09-E3** abduction report: at "no plan for its precondition", return the missing atom with its
  unknowns.
* **P09-E4** `@[fsym_inv]` loop-invariant registry: apply the backend's loop rule with the
  registered invariant and measure; parameters by the planner, frame inferred.
* **P09-E5** `@[fsym_upd]` ghost-update registry, keyed by heads, tried at returns. It generalizes
  the caller updates of 9f.

Existing open rows on the path: #9 (arena macros), #14, #15, #21 (disjunctions in `fsym_arith`:
Houdini candidates with case splits), #55 and #60 (cost in large states: generation runs many
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
