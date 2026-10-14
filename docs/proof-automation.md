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
| FBA `alloc` | 61k |
| FBA `resize` (refined) | 65k |
| FBA `remap` | 80k |
| FBA `free` | 22k |
| page (linux) `free` / `resize` / `remap` | 9k / 72k / 89k |
| page (macOS) `free` / `resize` / `remap` | 9k / 73k / 59k |
| page `alloc` (concurrent, `CTriple`) | 89k |

FBA `Full.lean` is 139 lines, of which the proofs are four `fsym` calls (the handwritten version
was 1025 lines); the page specs are 80 lines each (the legacy proofs were 582 and 501). Elaboration
on a loaded machine (load average about 17): FBA 66 s, each page spec 17 s, one theorem at a time
(`-j1`). The largest single cost is `omega` (`trace.fsym.prof`, 2026-10-12): the three linux page
specs make 986 `omega` calls (80k of their 170k heartbeats), 235 of them fail (17k: probes of
rules, providers and cases that do not apply, about 70 heartbeats each); FBA's four entries make
788 calls (75k of 228k), 364 failed (13k). The rest of the cost is spread over many successful
calls with 20 to 30 facts.

## Modules

* `ZigLean/Sep/Full/AutoAttr.lean`: the registries. `@[fsym]` marks a step rule (a triple about
  one command); `@[fsym_atom]` marks an assertion that `fsym` keeps opaque (also for imported
  constants, such as the library's `Junk`); the simp sets `fsym_norm` (programs) and `fsym_arith`
  (arithmetic side goals); `@[fsym_plan]` registers a **range law**
  `X … lo m … ⋆ X … m hi … = X … lo hi …` (checked when the attribute is added; the planner's
  table is data, never code `fsym` evaluates: no `evalConst`), `@[fsym_drop]` a drop lemma
  `EUpd (X ⋆ R) R` for atoms left over (knowledge, claims), `@[fsym_view]` a view lemma
  `EUpd X Y` of one atom (§Views).
* `ZigLean/Sep/Full/AutoClaims.lean`: byte-range claims (`docs/sep-full-state.md` §Byte-range
  claims): `bclaim_split` is their range law, and claims left over are dropped (`claim_drop`).
  Import it (not just `Auto`) to prove allocator specifications: grants carry claims.
* `ZigLean/Sep/Full/AutoRules.lean`: the rule library. Structural steps over any `FLogic`, step
  rules (loads, stores, pointer operations, checked `+ - % /`), the fields of typed values
  (`EncField`, §Fields),
  providers (`AddrOf`, `Reaches`, `Live`, `Active`; §Providers), pointer `==` across live blocks
  (`ptrEqAddr_live`), the planner's local updates (region
  split/join/weaken, share halves/join/weaken/raise), entailment combinators, and the arithmetic
  lemmas (masks, overflow bits, shifts, no-wrap rewrites, atoms for `omega`).
* `ZigLean/Sep/Full/AutoConc.lean`: the concurrent backend's rules (`C.step` & co., the oracle
  pick, indirect calls), the `fsym_norm` lemmas of concurrent bodies, the atomic rules as
  `@[fsym]` rules, and sequential rules that concurrent code reaches (`@ptrFromInt`, `@divExact`).
* `ZigLean/Sep/Full/AutoThread.lean`: the thread backend (`TLogic`, `Th.step` & co.), the
  locality providers that make a sequential rule a thread rule (`ofSeq`), and the native thread
  rules as `@[fsym]` rules (§Threads).
* `ZigLean/Sep/Full/AutoWP.lean`: the library's rules of a thread's run in a protocol
  (`Proto.WP`: `MemM` segments of a thread that owns its part, `spawn`, `join`; §A thread's run
  in a protocol).
* `ZigLean/Sep/Full/AtomicPlain.lean`: plain loads and stores of atomic words that keep their
  tag (§Atomic words).
* `ZigLean/Sep/Full/Parts.lean`: loads and stores of a struct whose fields several parts own
  (`ReadsAt`, `AlignedAt`, `load_reads`, `storeBytes_parts`; §Parts).
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
  other providers (up to `providerDepth`), blocks, arithmetic. `Reaches.of_live`;
  `Reaches.shareW`: a share whose tag is active (`Within (bshare b q k t) P`, `Active t P`);
  `Active.root`; `Active.gauthP`: a ledger's authority at its epoch under an active parent.
  `Live b l k` (live bytes from `l` to below `k`) comes only from owned bytes: a share bounds
  no first live offset (MM-19). A rule that needs a live block up to a bound takes `Live b l k₀`
  and `Reaches b k` apart (`Live.reach`, not a provider: with `Reaches.of_live` it would cycle),
  so the first live offset comes from owned bytes and the bound from any part (a node's share).

The candidates are tried in order, with backtracking over the rule's later side goals; the goals a
candidate leaves must all be proved. So a node pointer reaches its node's end through a share
tagged with the arena's epoch while the tail region may be empty, and pointer `==` of two
pointers into blocks that may differ (`ptrEqAddr_live`: both at live bytes in bounds, or both
past a live byte; one past a full node is past its header and within its share) gives
`decide (b = b' ∧ p.off = q.off)`; the Boolean test becomes facts
(`b = b'` substitutes the block). `fsym_entail` closes a goal `Within X P` the same way, through
definitions of `P`. Regression: `tests/roadmap/sep-auto/Providers.lean`.

### Fields

A struct of generated code is one typed value `up (pts p a s)`, read and written whole (the
`pts` rules) and by field: `EncField T U o get set` (`AutoRules.lean`) says that the bytes
`[o, o + size U)` of every encoding of `s : T` decode to `get s`, and that bytes decoding to `v`
written there make an encoding of `set s v`. The `@[fsym]` rules `FTotalTriple.encField_load`/
`_store` (`Typed.lean`, also at byte 0) load `get s` and store into `set s w`; their side goal
`EncField T U o ?get ?set` is solved by `encFieldOf?` (`Auto.lean`): it reads the fields off the
struct's decoding (`do pure { f := ← Enc.decodeAt bs o, … }`, as the translator writes it and as
`Slice` decodes), finds the field that holds byte `o`, proves its `EncField` from the decoding
(`result_bind_eq_pure`, `decode_write_*`) and descends into a field of a field by
`EncField.comp` (a slice's `len` in a list header: `get := fun s => s.items.len`). A decoding of
another shape, or an access that straddles fields, gives no field: the rules do not apply.
Equations of such values (`{ h with capacity := c }` against a module's `hdr ptr len cap`) are
proved field by field up to arithmetic (`proveEq` unfolds a user definition of a value; a fact
`p.elem 4 i = p.elem 4 j` by `congrEq`). Regression: `tests/roadmap/sep-auto/Fields.lean`.

### Atomic words

A word that atomic ops use (`apts p v`, `aptsE p v`: owned bytes `abytesAt` with the atomic tag
`(p.off, 8)`) is also read and written by plain loads and stores: the arena's `reset` stores
its list heads, `allocatedSliceUnsafe` loads a node's packed size word. A plain access checks no
tag, and a write keeps every cell's tag (`Holds.write`), so the `@[fsym]` rules of
`ZigLean/Sep/Full/AtomicPlain.lean` keep the word's tag and the atomic ops still apply afterwards:
`aptsE_load`/`_store`/`_storeBytes` (a value of any 8-byte type, or bytes that decode to one),
`apts_load`/`_store` (the word) and `apts_loadPacked`/`_storePacked` (a packed struct over the
word, whose generated `Enc` is its bits' encoding). They are the byte rules
`load_abytesAt`/`storeBytes_abytesAt` (the analogues of `Ops.lean`'s `…_bytesAt` rules) with the
word's facts. Regression: `tests/roadmap/sep-auto/AtomicPlain.lean`. In a thread the same rules
apply through `FTTotalTriple.ofSeq`: the word's 8 bytes are owned (`@[fsym_provider]`
`OwnsPtr.apts`/`OwnsPtr.aptsE`), so the access is local. A struct over several parts needs its
whole range owned: `fsym` splits the range where a part of the precondition starts and joins
the parts' own ranges (`ownsJoin` in `solveSides`, `OwnsPtr.join_at`), as it composes the
struct's `ReadsAt` from its fields. Regression: the `…_thread` theorems of
`tests/roadmap/sep-auto/Parts.lean`.

### Parts

A struct whose bytes several parts of the precondition own (the arena's header: its child
allocator's bytes as a region, its list heads as atomic words; a list header as one atom per
field) is loaded and stored whole by the parts' own rules (`ZigLean/Sep/Full/Parts.lean`), so each
part keeps its view and an atomic word its tag:

* **Loads** read. The provider kind `ReadsAt q n D P` says that the `n` bytes at `q` are in a
  live block and satisfy `D` in every memory that holds `P`; `AlignedAt q al P` that `q`'s
  address is aligned. The parts provide them for their bytes (`@[fsym_provider]`
  `ReadsAt.pts`/`.ptsField` (a field of a typed value, by its `EncField`)/`.aptsE`/`.apts`/
  `.regionIn` (bytes that decode to a value), `.regionInEnc` (a region that holds a value's
  encoding), `AlignedAt.pts`/`.aptsE`/`.regionIn`/`.addr`). For
  a struct that decodes its fields one after the other, `fsym` composes its bytes from its
  fields' (`readsStruct` in `Auto.lean`: each field a provider goal again, `ReadsAt.base` and a
  `Reaches` bound for the extent, `ReadsAt.field`, and the struct's decoding of the fields'
  values). `FTotalTriple.load_reads` loads the value; `fsym` tries it after every other rule, for
  every load (a node's `next` pointer from a region that holds its encoding).
* **Stores** write. `FTotalTriple.storeBytes_parts` executes a write by pieces (`Parts`,
  `storeParts`): one write and the writes of its pieces leave the same blocks and atomic layout
  (`storeBytes_two_run`; only the record of accesses differs, which no assertion reads). When no
  rule stores a struct, `fsym` cuts its encoding (`Enc.fields N [(o, Enc.encode x), …]`, as the
  translator writes a struct's `Enc`) at its fields (`fields_extract`, sizes by `LawfulEnc` or a
  struct's layout, `LayoutOk` checked on numbers), stores each field as a typed value by the rule
  of the part that owns it (a struct-valued field again by its pieces) and the padding as bytes
  (`storeSplitRule?`).

Regression: `tests/roadmap/sep-auto/Parts.lean` (the arena header loaded whole and its list heads
stored by `reset`, a list header held as one atom per field).

### Views

An atom may stand for another assertion over the same bytes: a **view lemma** `EUpd X Y`
(`@[fsym_view]`, one atom `X`) shows `X` as `Y`. Registered: an atomic word as the region of its 8
bytes (`apts_view`, `aptsE_view`, `AtomicPlain.lean`; one way, the region does not keep the
bytes' tag), a region as its owned bytes with its alignment and kind (`regionIn_view`) and owned
bytes with those facts as a region again (`regionIn_fold`, `AutoRules.lean`). The planner notes
each atom it did not find in the state (a rule's precondition, a return's postcondition); when
the step is stuck (no rule applies with more facts either; a return that neither the planner nor
the caller's updates close), `fsym` views every state atom of that atom's block whose view
provides its head (`viewStep`: `Y`'s atoms of the head unify with the wanted atom where they can,
which fixes a fold's alignment; the lemma's hypotheses must all be proved), and tries the step
again on the new state, whose facts and existentials open as usual. A view is kept only if the
walk gets past the step. So the arena's `deinit` gives a free-list node back to its child
allocator: the node's header words become regions, two regions of one block get the same labels
(`facts_regions_labels`), the planner relabels and joins adjacent regions (`joinOnce`) and carves
the granted region, whose size the grant's token names (`tok p bs.size …`, `atomSize?`).
Regression: `tests/roadmap/sep-auto/Views.lean` (a node given back, a load of a value's encoding,
a refund joined with a reservoir: two atoms of one head with unknown fractions take two state
atoms, a region viewed as bytes for a rule and folded back at the return).

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
  projection is reduced. Every rewrite carries its proof, a `rfl` lemma too (`StateT.run_bind`):
  as a definitional step it would leave the kernel to unfold `StateT.run`/`bind` against the
  rest of the program at a join of simp's proof (arena `resize` ran out of 10 GB there).
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
  rules) whose command unifies. The caller's terms are elaborated in the goal's context (its
  `have`s); their unknowns become leading binders (fresh at each use), and a local that the walk
  replaced (a substitution reintroduces the hypotheses after the variable it eliminates) is the
  current local of the same name and type, else a binder of the term (`refreshUser`). Commands of one head are unified argument by argument: a
  mismatch never unfolds `load`/`store`. A rule about a part of the precondition is framed (the
  part is matched structurally, the rest is the frame). Its hypotheses are side goals: blocks
  (from the context), providers (§Providers, with backtracking) and arithmetic; a side goal that
  is not arithmetic is closed by a hypothesis equal to it **up to arithmetic** in its arguments
  (`I.fits x.toNat 0` by `I.fits (n + 1) 0` with `x.toNat = n + 1`: `congrEq`, function by
  function down to numbers and words) or up to projections of structure values and unfolding
  (`{ names := ns, .. }.names.contains e = true` by `Option.all domain.names.contains (some e)`):
  `assumptionEq`.
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
  not joined again). **Planning order**: the unknown bytes of a
  region of `Q` with a size fact are assigned by the region planner from the state's current
  bytes, so an atom of `Q` that mentions them (the token `I.tok p bs.size …` of a grant whose bytes
  were written after the allocation) is matched only after the regions, with its arguments equal
  up to arithmetic (`(replicate x.toNat b).size = bs.size`); atoms of `Q` that differ from the
  state's only in such arguments (`replicate x.toNat b` against `replicate (n + 1) b` with
  `x.toNat = n + 1`) are matched argument by argument, the differing ones proved equal
  (`proveEq`; regression `tests/roadmap/sep-auto/Unify.lean`). Shares of one block and tag are joined, split and weakened (an
  allocator's own share and its grants' tagged shares of the same block stay apart; regression
  `Walk.tags_apart`), and a share with a
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
  the facts do not decide is split on, and one whose condition names an existential of `Q`
  (`if bs.size = 0 then … else …` of an `∃ bs`) is tried branch by branch with its condition as a
  fact of `Q`, proved once the planner has assigned the existential (`imp_ite_pos`/`_neg`); a
  region of `Q` whose unknown bytes' size another atom of `Q` names (the token `tok p bs.size …`)
  is carved to the size of the state's atom of that head; `up` atoms left over go into `Junk`; `Q`'s facts go to the
  arithmetic solver. Unproved side goals are left to the caller. `fsym_entail` is the planner on
  an `EUpd P Q` goal.
* **The caller's updates** `fsym [u]` with `u : ∀ …, EUpd P₀ Q₀` (a module's step of its
  invariant that the planner cannot take: a ghost update, junk that grows, a pool push; the arena's
  `free_last_upd`): at a return that the planner does not close, `EUpd P (P₀ ⋆ ?R)` is planned,
  `u`'s hypotheses are side goals, and `EUpd (Q₀ ⋆ R) (Q v)` closes the return (`tryUpd`; an
  update that closes it is preferred, else the first that applies with its arithmetic goals
  left). A variable of `u` of a structure type that no local has (the bundle `v : FV` of the
  arena's variables) is expanded into its fields (`etaStructArgs`), so `v.N` unifies with the
  state's pointer; a block fact of `P₀` is read only for a known pointer. Side goals that are user
  definitions are proved by the hypothesis of their unfolded form, or by the case of a `match` that
  a hypothesis `d = C …` selects (`matchCase?`); a fact of a user structure (`NodeFacts N A sz`)
  adds its fields next to it; two owned nonempty regions of one block have the same address and
  kind labels (`facts_regions_labels`). A postcondition atom whose head (a user definition) an
  update produces stays folded for the update to close; only a return's last attempt, after the
  updates, unfolds it like any other atom. Regression `tests/roadmap/sep-auto/Updates.lean`.

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

## Threads (`FTTotalTriple`, `FTTriple`)

A thread's step (`ZigLean/Sep/Full/Thread.lean`) is walked like a sequential program, in the
logic record `TLogic` (`TLogic.total`: `FTTotalTriple`, `TLogic.partial`: `FTTriple`;
`ZigLean/Sep/Full/AutoThread.lean`) by the `Th.*` counterparts of the structural steps. A thread
logic has no `ofTotal`: a sequential rule reads its part of the state without a race check.

* **Sequential rules in a thread.** A sequential `@[fsym]` rule `FTotalTriple P₀ c Q₀` (in the
  partial logic also `FTriple`) executes `c` when `c` is local to the thread that owns `P₀`: the
  rule becomes `FTTotalTriple.ofSeq r hl` (`ThreadStep.lean`), with the side goal
  `hl : ThreadLocal P₀ c` proved last by the providers. So each sequential rule is a thread rule;
  nothing is copied by hand.
* **Locality providers** (`@[fsym_provider]`, kinds `ThreadLocal` and `OwnsPtr`, each with
  `of_within`): an owned access (`ThreadLocal.load`, `store`, `store_lawful`, `loadBytes`,
  `storeBytes`, `memset_of`, `memmove`, `memcpy`) is local when `P₀` owns its bytes
  (`OwnsPtr` of `bytesAt`, `regionIn`, `region`, `pts`, `arr`: a pointer of the same block
  inside the view, arithmetic side goals; an array item `arr_elem`; an error union's payload
  `errPayload`); `alloc`, `pure`, `throw` and pure steps (`liftR`, `StateT.lift`) always are, and
  so is `mmap` (`ThreadLocal.mmap`); `munmap` and the `mremap` shrink are local when `P₀` owns the
  bytes they remove and holds the block's extent (`ThreadLocal.munmap_of`, `mremapShrink_of`;
  the provider kind `BlockIs` of `Full/Mmap`: size and kind from `bext`). A
  provider goal's assertion is its last argument of type `FAssn` (`ThreadLocal P c`), and a
  provider lemma about another command is not tried.
* **Native thread rules**: a rule with an `FTTotalTriple`/`FTTriple` conclusion applies directly
  in a thread goal (the pointer operations and bounds checks of `Full/Ops` and `Full/Region`,
  which read only the blocks, and the `const` read `FTTotalTriple.cload` of `Full/Const`, which
  records nothing (MM-20), are `@[fsym]` this way). Sequential goals do not use them (they have
  their sequential rules).
* **Fail closed.** A command that no provider shows local gets no rule from its sequential one: a
  plain access the thread does not own. The atomic ops keep their own thread rules
  (`docs/sep-threads.md` step 5).

Regressions: `tests/roadmap/sep-auto/Threads.lean` (the former hand-written thread rules of
`Full/Ops`, `Full/Region`, `Full/Typed`, `Full/Arr` and `Full/Mmap`, each one `fsym` call; programs in both
thread logics; `const` reads; the rejected store to unowned bytes).

## A thread's run in a protocol (`Proto.WP`)

`fsym` also walks `P.WP t x Q G m n` (`ZigLean/Conc/Logic.lean`, the one concurrent logic of
`docs/sep-threads.md`): thread `t` runs `x` from the memory `m` with the ghost values `G` and
keeps the protocol `P`. The goal has no assertion: the walk's state is the context (the
invariant `P.inv (upd G t g) m`, the thread's part `FOwned own rO m` and an assertion about it,
facts of the memory). It is the same walk (program normal form, results, `if`/`match` decided
by the facts or split, each command by a rule), with these differences (Auto.lean, §The `WP`
backend):

* **Rules** are `@[fsym]` theorems (or the caller's terms `fsym [r]`) whose conclusion is a `WP`
  of one command, keyed by its head through `StateT.run`. They are tried only in a `WP` walk.
  The library's (`ZigLean/Sep/Full/AutoWP.lean`): the `MemM` segments of a thread that owns its
  part (`WP.liftMem_fowned`, partial, and `WP.liftMem_fownedT`, total), a pure step
  (`WP.liftMem_liftR`; a checked `+`/`-` without overflow, `WP.liftMem_add`/`_sub`, with its
  value as a fact, as `add_step`/`sub_step` of a thread's walk) and `spawn`/`join`. A protocol's own rules are passed with its arguments:
  the steps of a lock's code (`Full/LockRules.lean`: `wp_casOn hP S hS`, …), a contract
  (`MutexImpl.lock_wp`), a loop with its invariant (`WP.loop _ _ inv meas post step`), a step whose
  run a protocol lemma gives (`WP.liftMem_pure h`).
* **One form for memory steps.** A memory step of generated code (`(callMC x).run s`,
  `(liftM x).run s`, `callRC`, `liftR`) is `ConcM.liftMem x >>= fun a => pure (a, s)` in the
  normal form, consecutive steps one `ConcM.liftMem`. A rule for a memory step (the library's, a
  protocol's: a read of a shared object, a holder's step on the lock's resource) is stated on
  `ConcM.liftMem x` with a post over the value; the step-form lemmas of hand proofs
  (`WP.liftM_fowned`, `WP.callMC_ptrProject`) do not apply. Stops (atomics, `sync`, `spawn`,
  `join`) keep their step form.
* **A rule's hypotheses** are of three kinds. A *continuation* names the rule's post, which is
  the goal's (the rest of the program after `WP.bind`); its binders are introduced (a pair by its
  components; a fact normalized and split: `∧`, `∃`, `∨` by cases, an equation substituted), an
  `∃` gets an unknown witness, an `∧` is proved part by part, and the walk goes on. A rule with a
  fixed post (a contract, `WP.loop`) goes through `WP.mono` with its post as the continuation's
  hypothesis. A *segment* (`FTTriple Pa x Qa`) is walked by the thread backend, its precondition
  from the context and its post **inferred**: at the segment's return the walk sets `Qa` to the
  strongest post `fun r => ∃ xs, ⟪φs⟫ ⋆ (⟪r = v⟫ ⋆ state)` over the locals the walk introduced
  (`inferPost`). A segment whose walk splits (an `if`, the cases of a variable, a side
  condition) gets one unknown post per branch, and `Qa` is their join `fun r => ∃ b : Bool, if b
  then Q₁ r else Q₂ r` (`joinPosts`, `join_l`/`join_r`): branches may end in different states,
  and the continuation splits on `b`. The continuation's hypothesis `Qa a r'` is split into its
  facts and the assertion that the next segment starts from. A goal `A ∨ B` (a post over
  branches) is proved by one side, else by the solver. *Side goals* are solved with their unknowns (a
  ghost value at a stop, a segment's precondition): a goal with unknowns takes a hypothesis that
  unifies with it, with backtracking over the choices until all side goals are proved, or waits
  until the others fix its unknowns; a determined goal goes to assumption, arithmetic and the
  providers after rewriting by the caller's simp terms, `upd_self`/`upd_upd`, the Boolean tests
  as propositions and the memory's equations of the context (`m'.threads = m.threads`); a user
  definition is unfolded. An automatic argument (`(h : T := by tac)`) runs its tactic.
* **The program normal form** is `fsym_norm` with the steps of a concurrent body (`CNorm`), but
  without the unfoldings of concurrent commands (`atomicRmwAsC` as an oracle pick and a `MemM` op
  is the solo reading of the `CTriple` backend; in a run it is a stop that a protocol's rule
  takes). A generated function with no rule is inlined.
* The caller's terms are related to each step's context: a local that a substitution eliminated
  (`m'.current = t` substitutes `t`) is replaced by its value (`refreshUser`).

```lean
theorem lock_wp (hP : L.FitsOn P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hS : L.c = mutexS.c) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Io_Mutex_lockUncancelable p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  have hS : mutexS.c = L.c := hS.symm
  fsym [wp_casOn hP mutexS hS, wp_waitOn hP mutexS hS,
    WP.loop _ _ (lockInv P L t g d) (fun _ => 0) (lockPost P L t g d)
      (loop23_body hP hcost hS t g hok d io),
    L.ph_set, L.set_set, hP.ok_set, mutexS]
```

Regressions: `tests/roadmap/sep-auto/WP.lean` (two segments of any protocol, the second's
precondition the first's inferred post) and `WPMutex.lean` (the generated `Io.Mutex` of
`examples/iogroup`: `lock`, `unlock` and the lock loop's body for every protocol with the lock,
the statements of `Proofs/Iogroup/Lock.lean`; 3 `fsym` calls for the 25 hand steps of the
hand walk). Limits: a segment's post is inferred at its first return (a segment with branches
whose states differ needs the caller's rule for it); a protocol's ghost update at a stop is
the protocol's rule (its `Fits` lemmas), not inferred.

## The arithmetic solver

Side goals are about words, pointer offsets and sizes. The solver (`arithCore`, also the tactic
`fsym_arith`; its normal forms and lemmas are `ZigLean/Sep/Full/AutoArith.lean`):

1. turns the hypotheses into **facts in normal form**, each once per run and each normalized with
   the facts before it: values of words and pointers as natural numbers, user definitions of
   values unfolded, overflow bits and shifts as values, low and high masks as remainders by
   `2 ^ x`; and **no wrap-around** where it cannot happen (`Zig.toNat_add_of_lt` and friends: the
   side condition by the discharger). Every reading of a word goes through its unsigned value
   `x.toNat`, for any width: a signed value `x.toInt` is `x.toNat - 2 ^ w * (2 * x.toNat / 2 ^ w)`
   (`toInt_eq_div`; a division by a literal for a literal width, which `omega` reads without a
   case split), and so are `Zig.val`, signed comparisons and signed overflow bits; `setWidth`
   (widening, `@truncate`) and `BitVec.ofInt` are remainders by `2 ^ m`, removed where the value
   fits. `@intCast` of either signedness steps by `intCast_step` (`r.toNat` is that
   of `BitVec.ofInt m v`: `r.toNat = a.toNat` where an unsigned value fits);
2. normalizes the target the same way;
3. adds facts about symbolic powers of two (`0 < 2 ^ x`, `2 ^ x < 2 ^ c` from `x < c`), masks of
   opaque words (`a &&& b` with `b = 2 ^ x - 1` or `b = 2 ^ w - 2 ^ x`, checked by `omega`),
   remainders by `2 ^ x` (bounds, multiples, `z % M = z` or `0` where `omega` shows so);
4. adds `z % 2 ^ x = z % L % 2 ^ x` for a literal power of two `L = 2 ^ c` of the problem with
   `x ≤ c` (`mod_pow_of_le`: `omega` reads `z % L`, not `z % 2 ^ x`), and runs `omega` on the facts. `omega` case-splits on every truncated subtraction, `Int.toNat`,
   `min` and `max`; a term whose case the split-free (linear) facts decide becomes an opaque
   atom with a linear defining fact (`subAtom`, also a subtraction truncated to `0`, `toNatAtom`,
   `minAtom`, `maxAtom`), so no split is explored for it. A case probe is not retried with a
   subset of the facts it failed with (`detProbe`; an undecided `min 4096 (2 ^ k)` of the page
   allocator's `alloc` was probed again for every side goal: 100k heartbeats, now 89k);
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
  A rule on a view of owned bytes (a region, a typed value: labels and facts over `bytesAt`) is
  the rule of owned bytes (`Full/Ops`: `load_bytesAt`, `storeBytes_bytesAt`, …) through
  `FTotalTriple.up_view`/`up_view'`, not a proof of its own.
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
`trace.fsym.total` the total of the run. A heartbeat or recursion limit hit while a rule or a
caller's update is tried is reported with the rule and the command (`reportLimit`) and ends the
run. Every proof must stay under the default heartbeat budget. Lessons:

* A failed definitional unification of two programs unfolds them: compare heads and arguments.
* `omega`'s cost is its case splits: state facts without truncated subtraction, and let
  `omegaFacts` turn determined split terms into atoms.
* Normalize each hypothesis once; never re-simplify the whole context per call.
* Never normalize the whole program per step (`lazyMethods`).
* Never elaborate a step's proof against the goal: `refine C.ex_sep _ …` checks the expected type
  `CTriple P prog Q`, whose `whnf` evaluates the program (6M heartbeats per step after a case
  split); `normPre` builds `lift_sep`/`ex_sep` from the goal's parts (`mkAppM`).
* A generated helper with heavy arithmetic (`alignForward` of masks modulo `2 ^ 64`) is inlined
  and its failing `omega` probes dominate (one problem can take 90k heartbeats; `omega` has no
  heartbeat checkpoints): prove a rule for the helper once and pass it as `fsym [rule]`.

## Limits and next steps

* Backends: the full-state triples (`FTotalTriple`, `FTriple`, `FLogic`) and the concurrent
  `CTriple`; `@[fsym]` takes `FTotalTriple` conclusions (every backend) and `FTriple` conclusions
  (the partial ones). The legacy `TotalTriple` layer is not a target (it is being phased out).
* Whole-mapping steps (`mmap`, `munmap` of a whole mapping, `mremap` that may move) are native
  like the partial-mapping steps: they are the block steps `Holds.push` and `Holds.free`.
* Time: the `fsym` proofs are slower than the handwritten ones; the largest cost is `omega`
  (results are cached per run: a proof where its variables are in scope, a failure in the same
  context).
