# Loop-free verification conditions

`import ZigLean.VC` provides a typed proof AST and compositional `eval`/`vc`
functions, automatic extraction of that AST from loop-free generated functions
(`ZigLean/VC/Extract.lean`, below) and a per-function report
(`scripts/vc-report.py`). It does not add a translation-preservation theorem.
It has no dependency on the earlier proof-tools modules.

`ResultProgram` accepts return, unsigned checked addition, unsigned widening,
safety guards/panics, bind, Boolean branches, and checked modular calls. Its VC
computes a proposition from the requested postcondition. Primitive safety
requirements remain visible even when that postcondition is `True`. The
soundness theorem supplies a successful result equality with `pure` and the
requested result property. Returned Zig errors are ordinary error-union values.

`MemProgram` accepts return, typed load/store (annotated `read`/`write` with
ghost old values, or ghost-free `load`/`store` whose VC asks for some owned cell
value), lifted `ResultProgram`, bind, Boolean branches, and checked modular calls. It generates positive-size and
ownership conditions, arithmetic conditions for lifted operations, and explicit
entailments from changed-heap assertions to the requested postcondition. Read
and write annotations include logical old values; `eval` ignores those ghost
values. A call requires a proved `Triple`, rather than an unchecked declaration
of what an external action is supposed to do.

Bind generates the first program's VC with the continuation's VC as its
postcondition. It therefore keeps every accepted operation's requirements,
without guessing intermediate memories or user invariants. `obligation pre
program post` is the implication from the user precondition to this generated
condition. `verify` still requires a proof of that implication. An unsolved
condition is a proof obligation, not a counterexample or a verified result.

`MemProgram.sound` yields the existing framed `Triple`: memory ownership and
`Mem.Seq` are preserved, safety errors are excluded, and the result property
holds if the action returns. A checked modular memory call may be partial, so
this interface does not claim termination for every memory AST. The unchanged
`Triple.frame` rule preserves additional client resources.

Raw loops and recursion have no constructor and are outside generated VCs.
`MemProgram.annotatedLoop` requires an explicit invariant, a natural-number
variant, and a proved iteration contract; it builds a checked call through the
existing `loop_sep_spec` theorem. Each repeat must strictly decrease the variant.
No annotation or iteration proof is synthesized. The generated client VC then
uses the loop's summary. Other loops/recursion require a separately proved
modular-call contract. Arbitrary AIR operations, general heap splitting, and automatic
contract discovery are also outside this accepted fragment.

`tests/roadmap/vcs/Clients.lean` proves denotation equalities with the committed
`Pointers.addTo` and `Pointers.swap p p` translations in
`Proofs/Pointers/Gen.lean`, generated from `examples/pointers/pointers.zig`.
The mutable add client exposes its widening and overflow obligations. The
self-swap client discharges a computed VC in two proof steps and applies
`verify`, replacing the explicit intermediate-memory/footprint proof in
`Proofs/Pointers/Sep.lean`. AST declarations and source-link proofs are explicit
setup, not automatically generated compiler output. These equalities link these
proof ASTs to those translated functions only; they do not prove Zig/AIR/compiler
preservation.

## Automatic extraction

`#vc_extract Ns.f` reflects a generated loop-free `Zig.Result`/`Zig.MemM`
function into this AST, without changing the translator or its output. It unfolds
`f` once through its `eq_def`, normalizes the generated locals/exit plumbing with
a fixed `simp only` set (`Zig.VC.normLemmas`), and maps the result constructor by
constructor: `pure`, bind, `if b then` on a `Bool`, `throw`, unsigned `Zig.add`,
unsigned widening `Zig.intCast`, `Zig.load`, `Zig.store` (needs `LawfulEnc`), and
lifted `Result` code. Every other operation, including a call to another generated
function, becomes a checked modular call only through a theorem tagged
`@[vc_contract]` (`∀ xs, pre → ∃ v, g xs = pure v ∧ post v`, `pre →` optional, or
`∀ xs, Triple pre (g xs) post`; a memory contract with hypotheses outside its
`Triple` is rejected with that reason, and the first registered matching contract is
used). `ZigLean/VC/Rules.lean` tags primitive contracts
for unsigned `sub`/`mul`/`divTrunc`, signed `add`/`sub`/`mul`, ranged `intCast`,
`index`, `optPayload`, `unwrapPayload` and `unwrapErr`; their preconditions are
exactly the non-failure conditions. It adds three declarations:

- `Ns.vc_f : ∀ xs, ResultProgram α` (or `MemProgram α`);
- `Ns.vc_f_source : ∀ xs, (vc_f xs).eval = f xs`, the `simp` normalization proof
  composed with definitional unfolding of `eval`, checked by the kernel;
- `Ns.vc_f_sound`, the unchanged `ResultProgram.sound`/`MemProgram.sound`
  transported along that equality (`sound_of`).

Extraction fails closed. A generated loop body `Ns.f.loop<i>` (AIR instruction
`%i`, nested loops included) yields the request "invariant + variant required for
loop `Ns.f.loop<i>` at AIR instruction %i", which points at `loop_template inv post`
(`step`/`entry`/`exit` goals, the measure carried by `inv s n`),
`MemProgram.annotatedLoop` or `Zig.loop_spec`; no invariant is guessed. A
self-recursive function, an unrecognized operation, an unreduced exit `match`, or a
call without a contract is refused with its reason. A proved loop or recursive
function becomes usable by callers once its contract is tagged `@[vc_contract]`.
`#vc_extract_all Ns` reports every generated function of `Ns` (extracted, loop
request or refused) without failing on one of them.

## Obligations

`vc_gen` applies to `∃ v, f xs = pure v ∧ post v` or `Triple pre (f xs) post`. It
uses `vc_f_source` when present and otherwise extracts on the fly, then splits the
generated VC with one introduction rule per constructor (`ZigLean/VC/Rules.lean`).
Each remaining goal is tagged by kind: `safety_i` (overflow, widening, guards,
reachable panics, primitive and `Result` callee preconditions), `memory_i` (positive
access size, cell ownership, memory callee preconditions, heap postconditions), `result_i` (functional result) or
`error_i` (a returned `Except.error`). Path conditions (`branch<k>`) and call
results (`value<k>`, `summary<k>`, `heap<k>`, `stored<k>`) are hypotheses. A
`Triple` precondition is introduced as `pre`; for a load or store, a hypothesis
`pts p a v heap` (also inside conjunctions) supplies the owned cell, and such a
store ownership goal is reported as closed by that hypothesis. Otherwise the
goal stays open. `ensures result heap` splits a memory postcondition into a
`result` and a `memory` goal; any other memory postcondition is one `memory` goal.
Nothing else is solved, so the goals are the complete obligations of the
contract, and closing them proves it through `sound`. A wrong contract leaves a
false goal. `Result` VCs give total correctness (an actual `pure` result); memory
VCs give the partial `Triple`.

`vc_gen?` also logs the obligations with their hypotheses and one
`vc-report {json}` line. `scripts/vc-report.py` collects those lines:

```sh
python3 scripts/vc-report.py --import Proofs.Basic.Gen --namespace Basic
python3 scripts/vc-report.py tests/roadmap/vcs/Extract.lean      # vc_gen? reports
python3 scripts/vc-report.py --json ...                           # machine-readable
```

The first form runs `#vc_extract_all` in a temporary file; the second checks a
contract file. Both need the imported modules built and return Lean's exit status.

`tests/roadmap/vcs/Extract.lean` extracts committed translations of
`examples/basic`, `examples/errors` and `examples/pointers`. It proves
`Basic.tardiness` (safety and result obligations) and, through its tagged
contract, `Basic.weightedTardiness` (the statement of `weightedTardiness_ok`);
`Errors.parseDigit` (error-return obligations) and `Errors.digitOrZero` (callee
contract plus checked unwraps); `Pointers.addTo` (memory obligations, framed);
and `Pointers.same` with `ensures`. A wrong `tardiness` contract leaves exactly one
goal, which is refuted. `Basic.sum` and `Pointers.sumTo` produce loop requests and
`Pointers.addDown` is refused as recursive. `tests/roadmap/vcs/report.json` is the
expected `--json` report for these namespaces and that file.

Limits: the memory AST has no heap splitting, so a load or store needs ownership of
the whole current heap (`pts p a v heap`); two-cell functions such as
`Pointers.swap p q` leave the ownership goal open. Generated `match` dispatch on
tagged unions, stack allocation, packed fields, vectors, `memset`/`memmove` and
allocator calls are refused unless a contract is supplied.

## Regressions

Regressions distinguish generated condition rejection from a concrete modeled
overflow execution. They check boundary arithmetic, wrong results, both branch
paths, memory postconditions, ownership, returned errors versus safety panics,
and refusal of unproved call summaries and raw loops. Once the modules and
`Proofs.Pointers.Gen`, `Proofs.Basic.Gen` and `Proofs.Errors.Gen` are built, check
each file with `lake env lean tests/roadmap/vcs/<name>.lean` (`Result`, `Memory`,
`Clients`, `Extract`).
