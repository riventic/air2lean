# Loop-free verification conditions

`import ZigLean.VC` provides verification conditions (VCs) for loop-free generated functions and a
per-function report (`scripts/vc-report.py`). It does not add a translation-preservation theorem.
There are two kinds of contracts, and one engine for each:

* a **`Result` contract** `∃ v, f xs = pure v ∧ post v` of a pure function: `f`'s body is
  reflected into the typed proof AST `ResultProgram` (`ZigLean/VC/Result.lean`), whose `vc`
  computes the obligations and whose `sound` theorem proves the contract from them;
* a **memory contract** `FTotalTriple pre (f xs) post` or `FTriple pre (f xs) post` of a `MemM`
  function, in the full-state separation logic (`docs/sep-full-state.md`): its obligations are
  the goals that the walk of the symbolic executor `fsym` (`docs/proof-automation.md`) leaves.

## Memory VCs are the walk of `fsym` (decision)

The one proof framework (`docs/proof-framework.md`) has one automation for memory programs,
`fsym`. A memory VC generator of its own (the earlier `MemProgram` AST over the legacy `Triple`,
with its own load/store/call rules and its own soundness theorem) would be a second engine with
a second rule set, and it could not split the heap: a load or store needed ownership of the whole
current heap. So `vc_gen` on a full-state triple is a mode of `fsym`, not a parallel engine:

1. it makes the checks of extraction (below): a generated loop yields its invariant request and
   recursion is refused, with the same messages as `#vc_extract`;
2. it runs `fsym`'s walk (`Zig.Full.Auto.walk`) with the library's `@[fsym]` rules, plus every
   `@[vc_contract]` theorem as a user step rule (a memory contract `∀ xs, FTotalTriple pre (g xs)
   post` directly, a `Result` contract through `result_step`, `ZigLean/VC/Rules.lean`);
3. it tags each goal the walk leaves by where it sits in the proof term that the walk built:
   a fact of the postcondition at a return (`imp_lift`) is `result_i`, or `error_i` when the
   returned value is a Zig error; a side condition of a step rule or contract is `memory_i` when
   the rule consumes a resource (its precondition is not a variable) or the contract is a
   memory contract, otherwise `safety_i`; an entailment `EUpd` that the planner did not close is
   `memory_i` (the heap postcondition); a reachable `throw` becomes the goal `False` (`safety_i`).
   A side condition `φ` that the walk split on (`hc : ¬φ ⊢ φ`) is reported without `hc`, which
   is equivalent.

A command that no rule executes is refused (`vc_gen: no @[fsym] rule or @[vc_contract] theorem
for the command …`); nothing is assumed. Every closing step is a kernel-checked proof, so the
goals left are the complete open obligations: closing them proves the contract. The walk
discharges what its arithmetic and planner prove (overflow from a hypothesis, ownership, frames,
the heap postcondition); a wrong contract leaves a goal that is false. Memory VCs are total with
`FTotalTriple` and partial with `FTriple`.

`ensures result heap` (`ZigLean/VC/Rules.lean`) is the postcondition `⟪result v⟫ ⋆ heap v`:
`vc_gen` unfolds it, so the result is a fact and the heap an assertion.

The memory programs that the earlier AST refused are now walked by the rule library: two cells
(`swap p q`, the planner splits the heap), pointer formation, pointer `==` without provenance
(`ptrEqAddr_raw`), and stores of bytes. A NaN constant is stored as its exact bytes with
`Zig.storeBytes` (`docs/architecture-audit/nan-bits.md`) and a float vector's store writes its
bytes, whatever a NaN lane's bits are, so neither has a typed `pts` result: `storeBytes_region`
and `storeEnc_region` (`ZigLean/Sep/Full/AutoPrim.lean`) write the bytes into an owned
`region` (`writeBytes`), the latter for any encoding, without `LawfulEnc`.

The theorems of the removed AST (`MemProgram.sound`, `verify`, `sound_of`, `triple_intro`,
`annotatedLoop`) have no successor: each memory contract is now proved by `fsym`'s rules. A loop
is proved with the loop rules of `ZigLean/Sep/Full/Loop.lean` (`FTotalTriple.loop_ghost`,
`FTriple.loop`) and registered as a contract.

## `Result` VCs

`ResultProgram` accepts return, unsigned checked addition, unsigned widening, safety
guards/panics, bind, Boolean branches, and checked modular calls. Its VC computes a proposition
from the requested postcondition. Primitive safety requirements remain visible even when that
postcondition is `True`. The soundness theorem supplies a successful result equality with `pure`
and the requested result property. Returned Zig errors are ordinary error-union values.

Bind generates the first program's VC with the continuation's VC as its postcondition. It
therefore keeps every accepted operation's requirements, without guessing intermediate values or
user invariants. `obligation pre program post` is the implication from the user precondition to
this generated condition. An unsolved condition is a proof obligation, not a counterexample or a
verified result.

## Automatic extraction

`#vc_extract Ns.f` reflects a generated loop-free `Zig.Result` function into this AST, without
changing the translator or its output. It unfolds `f` once through its `eq_def`, normalizes the
generated locals/exit plumbing with a fixed `simp only` set (`Zig.VC.Extract.normLemmas`), and
maps the result constructor by constructor: `pure`, bind, `if b then` on a `Bool`, `throw`,
unsigned `Zig.add`, unsigned widening `Zig.intCast`. Every other operation, including a call to
another generated function, becomes a checked modular call only through a theorem tagged
`@[vc_contract]` (`∀ xs, pre → ∃ v, g xs = pure v ∧ post v`, `pre →` optional; the first
registered matching contract is used). `ZigLean/VC/Rules.lean` tags primitive contracts for
unsigned `sub`/`mul`/`divTrunc`, signed `add`/`sub`/`mul`, ranged `intCast`, `index`,
`optPayload`, `unwrapPayload` and `unwrapErr`; their preconditions are exactly the non-failure
conditions, and those that `fsym`'s library lacks are also `@[fsym]` step rules (`result_step`).
It adds three declarations:

- `Ns.vc_f : ∀ xs, ResultProgram α`;
- `Ns.vc_f_source : ∀ xs, (vc_f xs).eval = f xs`, the `simp` normalization proof composed with
  definitional unfolding of `eval`, checked by the kernel;
- `Ns.vc_f_sound`, the unchanged `ResultProgram.sound` transported along that equality
  (`sound_of`).

For a loop-free `Zig.MemM` function, `#vc_extract` makes the same checks and reports `walk`: its
VCs come from a contract (above).

Extraction fails closed. A generated loop body `Ns.f.loop<i>` (AIR instruction `%i`, nested
loops included) yields the request "invariant + variant required for loop `Ns.f.loop<i>` at AIR
instruction %i", which points at `FTotalTriple.loop_ghost inv post` (the measure carried by
`inv s n`) or `FTriple.loop inv post` for a memory loop and `Zig.loop_spec` for a `Result` loop;
no invariant is guessed. A self-recursive function, an unrecognized operation, an unreduced exit
`match`, or a call without a contract is refused with its reason. A proved loop or recursive
function becomes usable by callers once its contract is tagged `@[vc_contract]`.
`#vc_extract_all Ns` reports every generated function of `Ns` (extracted, walk, loop request or
refused) without failing on one of them.

## Obligations

`vc_gen` applies to `∃ v, f xs = pure v ∧ post v`, `FTotalTriple pre (f xs) post` or
`FTriple pre (f xs) post`. For a `Result` contract it uses `vc_f_source` when present and
otherwise extracts on the fly, then splits the generated VC with one introduction rule per
constructor (`ZigLean/VC/Rules.lean`); for a memory contract it walks (above). Each remaining
goal is tagged by kind: `safety_i` (overflow, widening, guards, reachable panics, primitive and
callee preconditions), `memory_i` (ownership, memory callee preconditions, heap
postconditions), `result_i` (functional result) or `error_i` (a returned `Except.error`). In a
`Result` VC, path conditions (`branch<k>`) and call results (`value<k>`, `summary<k>`) are
hypotheses; in a memory VC, the facts the walk collected are. Nothing else is solved in a `Result`
VC, so its goals are the complete obligations of the contract; closing them proves it through
`sound`. A wrong contract leaves a false goal. `Result` VCs give total correctness (an actual
`pure` result).

`vc_gen?` also logs the obligations with their hypotheses and one `vc-report {json}` line.
`scripts/vc-report.py` collects those lines:

```sh
python3 scripts/vc-report.py --import Proofs.Basic.Gen --namespace Basic
python3 scripts/vc-report.py tests/roadmap/vcs/Extract.lean      # vc_gen? reports
python3 scripts/vc-report.py --json ...                           # machine-readable
```

The first form runs `#vc_extract_all` in a temporary file; the second checks a contract file.
Both need the imported modules built and return Lean's exit status.

`tests/roadmap/vcs/Extract.lean` extracts committed translations of `examples/basic`,
`examples/errors` and `examples/pointers`. It proves `Basic.tardiness` (safety and result
obligations) and, through its tagged contract, `Basic.weightedTardiness` (the statement of
`weightedTardiness_ok`); `Errors.parseDigit` (error-return obligations) and `Errors.digitOrZero`
(callee contract plus checked unwraps); and the memory contracts of `Pointers.addTo` (framed),
`Pointers.swap p q` (two cells), `Pointers.swap p p` and `Pointers.same` (with `ensures`), each
with its strength example: the legacy statement on every `Mem.FSeq` memory, from
`FTotalTriple.toTotal_on` (`ZigLean/Sep/Full/Strength.lean`). A wrong `tardiness` contract leaves
exactly one goal, which is refuted. `Basic.sum` and `Pointers.sumTo` produce loop requests and
`Pointers.addDown` is refused as recursive. `tests/roadmap/vcs/report.json` is the expected
`--json` report for these namespaces and that file.

Limits: a memory command needs an `@[fsym]` rule or a `@[vc_contract]`; generated `match`
dispatch on tagged unions, stack allocation, packed fields, `memset`/`memmove` and allocator calls
are walked only as far as the rule library covers them (`docs/proof-automation.md`).

## Regressions

Regressions distinguish generated condition rejection from a concrete modeled overflow execution.
They check boundary arithmetic, wrong results, both branch paths, heap postconditions, ownership,
returned errors versus safety panics, stores of bytes, and refusal of unproved call summaries
and raw loops. Once the modules and `Proofs.Pointers.Gen`, `Proofs.Basic.Gen` and
`Proofs.Errors.Gen` are built, check each file with `lake env lean tests/roadmap/vcs/<name>.lean`
(`Result`, `Memory`, `Extract`).
