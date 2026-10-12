# Proof automation: the symbolic executor `fsym`

`fsym` proves a triple about generated code in the full-state logic (`FTotalTriple P c Q`,
`FTriple P c Q` or `L.T P c Q` for any `FLogic`, [sep-full-state.md](sep-full-state.md)), or
about a concurrent function read in the caller's thread (`CTriple P x Q`), by walking the
program. A proof about a module supplies its invariant and the statement, and
nothing else: the generated code is walked by general rules from the library (CLAUDE.md,
"General tactics over module-specific ones").

```lean
import ZigLean.Sep.Full.AutoAll

theorem ffree_spec (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s.ptr k bs) (impl.free ctx s k ra)
      (fun _ => (finv ctx B).own) := by
  fsym
```

`ZigLean.Sep.Full.AutoAll` is the one import of a proof: `fsym` with every rule of the library
(arrays, typed values, error unions and optionals through pointers, regions, blocks, the
allocator wrappers, the mapping primitives), the loop rules, the start memory and the claim
witnesses. `tests/roadmap/one-logic/check.sh` fails when a library module that declares an `fsym`
rule is not reached from it.

The users are the translated `FixedBufferAllocator` (`tests/roadmap/alloc-fba/AllocFba/Full.lean`:
all four `FAllocSpec` fields, including the refined `resize` field) and the translated
`PageAllocator` (`tests/roadmap/alloc-translated/PageSpec.lean` for x86_64-linux and
`PageSpecMacos.lean` for aarch64-macos: `free`, refined `resize`, `remap`; the invariant is
`PageTok.lean`; `PageAlloc.lean` proves the concurrent `alloc` with the `CTriple` backend). The page
proofs walk the generated code down to the OS mapping primitives (`mmap`, `munmap`, `mremap`,
premise OSM-01) with the library rules of `ZigLean/Sep/Full/Mmap.lean`. Small library-only
examples are in `tests/roadmap/sep-auto/` (CI: the `lean` part, step "Full-state separation
logic"; `Conc.lean` for the concurrent backend: atomics, an indirect call through a table, a loop
with its invariant).

| Proof | heartbeats (default budget 200k) |
| --- | --- |
| FBA `alloc` | 64k |
| FBA `resize` (refined) | 57k |
| FBA `remap` | 70k |
| FBA `free` | 21k |
| page (linux) `free` / `resize` / `remap` | 13k / 78k / 85k |
| page (macOS) `free` / `resize` / `remap` | 13k / 78k / 55k |
| page `alloc` (concurrent, `CTriple`) | 141k |

FBA `Full.lean` is 139 lines, of which the proofs are four `fsym` calls (the handwritten version
was 1025 lines); the page specs are 80 lines each (the legacy proofs were 582 and 501). Elaboration
on a loaded machine (load average about 17): FBA 66 s, each page spec 17 s, one theorem at a time
(`-j1`). The cost is `omega`: about 870 calls per page spec, a third of them case-split probes for
truncated subtractions; failed probes are cheap (about 90 heartbeats each), the cost is spread over
many successful calls with 20 to 30 facts.

## Modules

* `ZigLean/Sep/Full/AutoAttr.lean`: the registries. `@[fsym]` marks a step rule (a triple about
  one command); `@[fsym_atom]` marks an assertion that `fsym` keeps opaque (also for imported
  constants, such as the library's `Junk`); the simp sets `fsym_norm` (programs) and `fsym_arith`
  (arithmetic side goals); `@[fsym_plan]` registers a **range law**
  `X … lo m … ⋆ X … m hi … = X … lo hi …` (checked when the attribute is added; the planner's
  table is data, never code `fsym` evaluates: no `evalConst`), `@[fsym_drop]` a drop lemma
  `EUpd (X ⋆ R) R` for atoms left over (knowledge, claims).
* `ZigLean/Sep/Full/AutoClaims.lean`: byte-range claims (`docs/sep-full-state.md` §Byte-range
  claims): `bclaim_split` is their range law, and claims left over are dropped (`claim_drop`).
  Import it (not just `Auto`) to prove allocator specifications: grants carry claims.
* `ZigLean/Sep/Full/AutoRules.lean`: the rule library. Structural steps over any `FLogic`, step
  rules (loads, stores, pointer operations, the fields of a stored slice, checked `+ - % /`),
  providers (`AddrOf`, `Reaches`, `Live`, `Active`; §Providers), pointer `==` across live blocks
  (`ptrEqAddr_live`), the planner's local updates (region
  split/join/weaken, share halves/join/weaken/raise), entailment combinators, and the arithmetic
  lemmas (masks, overflow bits, shifts, no-wrap rewrites, atoms for `omega`).
* `ZigLean/Sep/Full/AutoConc.lean`: the concurrent backend's rules (`C.step` & co., the oracle
  pick, indirect calls), the `fsym_norm` lemmas of concurrent bodies, the atomic rules as
  `@[fsym]` rules, and sequential rules that concurrent code reaches (`@ptrFromInt`, `@divExact`).
* `ZigLean/Sep/Full/Region.lean`: the region library (`up (regionIn …)`): `@memset(_, undefined)`,
  item stores and the read-back of a stored item, `@memcpy` between separate regions, the
  pointer order `ptrLe`/`ptrLt`, and the memory fact `MemFacts.regions_apart` (two separately
  owned regions lie at disjoint address ranges; `@[fsym_facts]`: `fsym` adds it for a pair of
  regions when it needs more facts, `MemFacts.pre` puts it in the context by hand).
* `ZigLean/Sep/Full/Auto.lean`: the tactic.

### Range laws

For an atom of `Q` whose head `X` has a range law, the planner carves it out of a state atom of
`X` with the same other arguments that covers it (the law twice, backwards:
`X lo hi ⟶ X lo a ⋆ X a c ⋆ X c hi`); when none covers it, adjacent state atoms (the second from
the first's end) are joined first (the law forwards). The law's hypotheses are side goals of the
arithmetic solver. A head with a law is an atom (never unfolded). Regression:
`tests/roadmap/sep-auto/Plan.lean` (claims and a user's own range assertion).

### Providers

A rule takes what it needs of the memory from a **provider**, a property of every memory that
holds the precondition `P`: `AddrOf b A P` (block `b` at address `A`), `Reaches b k P` (at least
`k` bytes), `Live b k P` (live, at least `k` bytes), `Active t P` (the tag `t` of a share is
active). A provider kind `K` is a constant with a lemma `K.of_within : K … X → Within X P → K … P`.
`fsym` proves a provider goal by

* an **atom lemma** (`@[fsym_provider]`, conclusion `K … X` of an atom `X`: a region, a typed
  value, `known`, an untagged share, an allocator's own state) on one of the parts of `P`, or
* a **lemma about the whole precondition** (`@[fsym_provider]`, conclusion `K … P` of a variable
  `P`), whose hypotheses are goals again: `Within X P` (a part of `P` that unifies with `X`),
  other providers (up to `providerDepth`), blocks, arithmetic. `Reaches.of_live`; `Live.share`: a
  share whose tag is active (`Within (bshare b q k t) P`, `Active t P`); `Active.root`;
  `Active.gauthP`: a ledger's authority at its epoch under an active parent.

The candidates are tried in order, with backtracking over the rule's later side goals; the goals a
candidate leaves must all be proved. So a node pointer reaches its node's end through a share
tagged with the arena's epoch while the tail region may be empty, and pointer `==` of two
pointers into blocks that may differ (`ptrEqAddr_live`: both in bounds, or both past their
blocks' starts) gives `decide (b = b' ∧ p.off = q.off)`; the Boolean test becomes facts
(`b = b'` substitutes the block). `fsym_entail` closes a goal `Within X P` the same way, through
definitions of `P`. Regression: `tests/roadmap/sep-auto/Providers.lean`.

## How it works

* **Preconditions** are a flat list of atoms. Definitions that build assertions from `⋆`, `⟪φ⟫`
  and `FAssn.ex` (an invariant, a token, `pshare`, a projection of an `FAllocInv`) are unfolded;
  existentials and facts move into the context (conjunctions split, equations of a variable
  substituted, user definitions of facts unfolded; a term `t` that is not a variable, such as a
  field of the locals, equated to a constructor application `C …` or to a closed value of a type
  that is not arithmetic (`w.M = GMap.empty`) is replaced by it in the goal and the facts, so a
  `match` on `t` reduces: `substCtor`; a test `o.isSome`/`o.isNone` of an optional adds its
  constructor equation, `o = none` or `o = some a`: `opt_*`). An assertion-level `if c then X else Y`
  (`relBytes`, `newBytes`) takes the branch the facts decide; an undecided one stays an atom and
  is split at the next return.
* **Programs** are normalized with `fsym_norm` (the `MM`/`StateT` layer of generated code,
  binds, trivial results, field accessors of structure values), **at the head only**
  (`lazyMethods`): at `x >>= f` only `x` is simplified and the node rewritten (`bind_assoc`,
  `pure_bind`, `ite_bind`), the continuation `f` is not visited; at an `if` only the condition. A
  continuation is normalized once it is the head, so a step costs the same on a 900-line
  generated body as on a small one (normalizing the whole body pushes every continuation into
  both branches of each `if` before it). A call of a generated function is inlined; a vtable
  projection is reduced.
* **Facts of atoms** (`@[fsym_facts]`, `AtomFacts X φ`): an atom that owns memory at a pointer
  implies the pointer's block, a nonnegative offset and, for a region, its alignment
  (`facts_region`, `facts_bytes`, `facts_pts`, `facts_apts`, `facts_aptsE`). When the walk needs
  more facts (a rule whose side goals fail, an undecided `if`, a reachable panic, a return the
  planner cannot close), the facts of the precondition's atoms that the context lacks are added
  (`pre_fact`) and the step is retried; so a pointer whose block the context does not know
  (a field of a node, an argument) gets one from what the precondition owns at it. A facts
  lemma may need the memory, or be about an ordered pair of atoms (`MemFacts X φ` with `X` an atom
  or `X₁ ⋆ X₂`, `pre_mfact`): a token names a grant of its authority's map (`facts_gfrag`:
  `gauthP γ e M t ⋆ gfrag γ e i g` gives `M i = some g`); two owned regions lie apart (by
  addresses, `MemFacts.regions_apart`; by offsets in one block, `facts_regions_block`). A facts
  lemma's premises are proved from the context (blocks `p.block = some b`) or by the arithmetic
  solver (`0 < bs.size`); a lemma gives one fact per unordered pair (disjunctive facts cost `omega`
  case splits). Block
  variables of pointers derived by `Ptr.add`/`elem` are identified (`unifyBlocks`). A Boolean
  test (`(!decide (b = b' ∧ x = y)) = false`, of a pointer `==`) becomes the proposition.
* **Commands** are executed by the first rule (the caller's `fsym [r]` first, then the `@[fsym]`
  rules) whose command unifies. Commands of one head are unified argument by argument: a
  mismatch never unfolds `load`/`store`. A rule about a part of the precondition is framed (the
  part is matched structurally, the rest is the frame). Its hypotheses are side goals: blocks
  (from the context), providers (§Providers, with backtracking) and arithmetic.
* **Word results are opaque** (symbolic execution in SSA form): a checked `a + b` gives a fresh
  `r` with the fact `r.toNat = a.toNat + b.toNat` (subtraction is stated additively), so later
  terms mention `r`, not the growing expression that computed it.
* **Branches**: an `if` whose condition (or its negation) the facts prove takes one side; else
  both are walked with the condition as a fact. A `match` on a variable is split by cases. A
  `throw` must be unreachable (the facts are contradictory).
* **A rule's precondition that is not literally in the state** is planned: the planner closes
  `EUpd P (P₀ ⋆ ?R)` (`?R` is the frame: what is left), so a rule may ask for the full extent of a
  block (`bext`) and one region of its bytes while the state holds the authority, shares and
  several regions. Among the rules whose command unifies, the first whose side goals are all
  proved is taken; a side condition that the facts decide neither way is split on (the cases of
  `mremap`: shrink or grow).
* **A condition that matches on a variable** (an error union's tag) splits the variable; a
  `match` on a constructor in the precondition reduces. A `match`/`Option.elim` on a term (a
  field of the locals) generalizes the term with its equation and splits it.
* **Returns** `pure v`: the goal becomes the update `EUpd P (Q v)`, which the planner closes:
  `Q`'s existentials become metavariables, assigned by unification; regions are matched exactly,
  or carved out of a state region (split at the start with `Q`'s alignment and at the end by a
  size fact), joining adjacent regions where needed (a region that a part of `Q` has claimed is
  not joined again); shares of one block are joined, split and weakened, and a share with a
  determined fraction is raised to a higher bound with another share of its block
  (`share_raise`), or with the authority of its block (`auth_raise`, up to the block's size);
  **authorities** (`bauth`, `bext`): a share of a block of which the state has none is lent out of
  the authority (`auth_lend`; the authority's fraction is `x + q` syntactically, by an equation of
  the context, or `q` takes half of it), and an authority with a determined fraction takes the
  block's shares back (`auth_unlend`) until the fractions are equal (equations of the context, also
  under an arithmetic premise); a region's size label and kind are relabelled (`EUpd.relabel`);
  **knowledge** `known b A` comes from the state's or from an owned region of the block
  (`known_of_region`); **range laws** (`@[fsym_plan]`, claims) are planned after the shares; atoms left over that a drop lemma (`@[fsym_drop]`) forgets are dropped (knowledge,
  claims); an assertion-level `if` of `Q` that
  the facts do not decide is split on; `up` atoms left over go into `Junk`; `Q`'s facts go to the
  arithmetic solver. Unproved side goals are left to the caller. `fsym_entail` is the planner on
  an `EUpd P Q` goal.

## The concurrent backend (`CTriple`)

A goal `CTriple P x Q` (a concurrent function read in one thread, `ZigLean/Sep/Full/Conc.lean`)
is walked like a sequential one, by the `C.*` counterparts of the structural steps:

* the body monad `CM` is normalized (`CNorm`, the atomic ops of `CM` as an oracle pick and a
  `MemM` op), and `ConcM.liftMem` is pushed through the `MemM` layer (`liftMem_bind`), so a
  generated `MemM` callee is walked command by command;
* a `ConcM.liftMem c` command is executed by a sequential rule about `c`: total (`@[fsym]`) or
  partial (`FTriple`: the atomic rules, `CTriple` being partial correctness); an oracle pick
  takes the choice `0` (`C.pick`);
* a concurrent command (a call through a table, a loop) is executed by a `CTriple` rule given
  to `fsym [h]`: its command may be a definition that unfolds to the program's (`t.call f a` or
  `(CVTable.dispatch t fns).alloc …` to the generated chain): `CTriple.tableCall`'s reading;
  a loop is `CTriple.loop` with its invariant, whose body `∀ s, CTriple (inv s) (body.run s) …`
  is again `fsym`;
* a generated indirect call `if f == c₁ then x₁ else … else d` (`d` is `throw .illegal`, or the
  environment's call `callC (extCall …)` of an open interface, `docs/interfaces.md`) is folded
  into `callIndirect f [(c₁, x₁), …] d` at its `if`, before its tests are rewritten
  (`callIndirect_fold_one`/`_ext`/`_cons`) and its arms' common continuation is pulled out
  (`pullIndirect`), so it is one command; with no rule for it, the arm that the facts select is
  walked (`C.callIndirect_pos`/`_neg`), else both cases, and with no arm left the last arm
  (`C.callIndirect_nil`);
* a `CTriple` rule's command is unfolded to the program's head and its projections of structure
  values are reduced (`(env e).alloc f (c, n, k, ra)` to the generated `Ext.call0 f c n …`), so
  the program's literal arguments unify as written; a raw natural literal that unification
  assigns (`BitVec.ofNat 6 ?k =?= 3`) is a numeral again in the rule's pre- and postcondition
  (`normNatLits`).

Partial rules (`FTriple`) also apply in `FLogic.partial` (`P.step`).

## The arithmetic solver

Side goals are about words, pointer offsets and sizes. The solver (`arithCore`, also the tactic
`fsym_arith`):

1. turns the hypotheses into **facts in normal form**, each once per run and each normalized with
   the facts before it: values of words and pointers as natural numbers, user definitions of
   values unfolded, overflow bits and shifts as values, low and high masks as remainders by
   `2 ^ x`; and **no wrap-around** where it cannot happen (`Zig.toNat_add_of_lt` and friends: the
   side condition by the discharger);
2. normalizes the target the same way;
3. adds facts about symbolic powers of two (`0 < 2 ^ x`, `2 ^ x < 2 ^ c` from `x < c`), masks of
   opaque words (`a &&& b` with `b = 2 ^ x - 1` or `b = 2 ^ w - 2 ^ x`, checked by `omega`),
   remainders by `2 ^ x` (bounds, multiples, `z % M = z` or `0` where `omega` shows so);
4. adds `z % 2 ^ x = z % L % 2 ^ x` for a literal power of two `L = 2 ^ c` of the problem with
   `x ≤ c` (`mod_pow_of_le`: `omega` reads `z % L`, not `z % 2 ^ x`), and runs `omega` on the facts. `omega` case-splits on every truncated subtraction, `Int.toNat`,
   `min` and `max`; a term whose case the split-free (linear) facts decide becomes an opaque
   atom with a linear defining fact (`subAtom`, also a subtraction truncated to `0`, `toNatAtom`,
   `minAtom`, `maxAtom`), so no split is explored for it;
5. unless the call is a probe (`quick`), `t % M = c` follows from a fact `u % M = c` with `t = u`.

`omega` is given only the facts **relevant** to the target: those connected to it by shared
atoms (its variables: words' values, offsets, fields), transitively (`relevantFacts`); a target
without atoms (`False`: a refutation) gets all facts. Irrelevant facts (another object's
alignment `% 8`) cost `omega` case splits on a problem that fails.

Results of the discharger and of the probes are cached per run; a cached proof is reused only
where its free variables are in scope. The caches belong to one run (theorems are elaborated in
parallel; a run is identified by the option `fsym.run`).

## Extending it

* A new command: a step rule `@[fsym] theorem … : FTotalTriple P c Q` in a library module, with
  its side conditions as hypotheses (blocks `p.block = some b`, providers `AddrOf`/`Reaches`,
  arithmetic). Prefer a postcondition that states a word result by a fact about `r.toNat`.
* A new opaque assertion: `attribute [fsym_atom] myPred`; its pure facts (the block of the
  pointer it owns memory at, its alignment): `@[fsym_facts] theorem … : AtomFacts (myPred p …) φ`;
  facts that need the memory or two atoms: `@[fsym_facts] theorem … : MemFacts (X ⋆ Y) φ`.
* A provider for a new atom: `@[fsym_provider] theorem … : Reaches b k (myPred …)` (or `AddrOf`,
  `Live`, `Active`); one from the whole precondition: `@[fsym_provider] theorem … (hw : Within X P)
  … : Live b k P`. A new provider kind `K` needs `K.of_within`.
* A new range resource to plan (split, join): its range law tagged `@[fsym_plan]`, and
  `@[fsym_drop]` for its atoms that may be forgotten. Another kind of planning (lending, a
  different algebra) is an engine change in `Auto.lean` (the fsym lane), not a user extension.
* Normalization: `attribute [fsym_norm] …` for programs, `attribute [fsym_arith] …` for
  arithmetic. A simp lemma must match the child-normalized form of terms (`0#1`, not the literal
  `(0 : BitVec 1)`).
* Library facts that are not arithmetic (`keepsPrefix`, fractions): `macro_rules | `(tactic| fsym_fact) => …`.
* Generated code computes constants at run time (`alignment - 1`): `+ - *` of two word literals
  are folded by proof-producing simprocs (`add_lit`, `sub_lit`, `mul_lit`). `~~~` of a literal is
  not folded in programs (the kernel would check the folded program by a deep unfolding); the
  arithmetic solver reads literal high masks (`2 ^ w - 2 ^ j`) directly.

## Debugging and budget

`set_option trace.fsym true in fsym` traces the walk, rule and provider failures, carving and
joining, failed arithmetic and entailment errors; `trace.fsym.arith` prints each `omega` problem;
`trace.fsym.prof` prints heartbeats per arithmetic call, rule and entailment, and
`trace.fsym.total` the total of the run. Every proof must stay under the default heartbeat budget. Lessons:

* A failed definitional unification of two programs unfolds them: compare heads and arguments.
* `omega`'s cost is its case splits: state facts without truncated subtraction, and let
  `omegaFacts` turn determined split terms into atoms.
* Normalize each hypothesis once; never re-simplify the whole context per call.
* Never normalize the whole program per step (`lazyMethods`).
* A generated helper with heavy arithmetic (`alignForward` of masks modulo `2 ^ 64`) is inlined
  and its failing `omega` probes dominate (one problem can take 90k heartbeats; `omega` has no
  heartbeat checkpoints): prove a rule for the helper once and pass it as `fsym [rule]`.

## Limits and next steps

* Backends: the full-state triples (`FTotalTriple`, `FTriple`, `FLogic`) and the concurrent
  `CTriple`; `@[fsym]` takes `FTotalTriple` conclusions (every backend) and `FTriple` conclusions
  (the partial ones). The legacy `TotalTriple` layer is not a target (it is being phased out).
* Whole-mapping steps (`mmap`, `munmap` of a whole mapping, `mremap` that may move) are lifted
  inside the library from the legacy rules with the pinned bridge (`FTotalTriple.ofTotal`);
  partial-mapping steps are native.
* Time: the `fsym` proofs are slower than the handwritten ones; the largest cost is `omega`
  (results are cached per run: a proof where its variables are in scope, a failure in the same
  context).
