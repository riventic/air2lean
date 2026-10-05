# Loop-free verification conditions

`import ZigLean.VC` provides a typed proof AST and compositional `eval`/`vc`
functions. This is a bounded P02 interface for Lean contracts. It does not add
automatic AIR extraction, a CLI VC report, or a translation-preservation theorem.
It has no dependency on the earlier proof-tools modules.

`ResultProgram` accepts return, unsigned checked addition, unsigned widening,
safety guards/panics, bind, Boolean branches, and checked modular calls. Its VC
computes a proposition from the requested postcondition. Primitive safety
requirements remain visible even when that postcondition is `True`. The
soundness theorem supplies a successful result equality with `pure` and the
requested result property. Returned Zig errors are ordinary error-union values.

`MemProgram` accepts return, typed load/store, lifted `ResultProgram`, bind,
Boolean branches, and checked modular calls. It generates positive-size and
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

Regressions distinguish generated condition rejection from a concrete modeled
overflow execution. They check boundary arithmetic, wrong results, both branch
paths, memory postconditions, ownership, returned errors versus safety panics,
and refusal of unproved call summaries and raw loops. Once the modules and
`Proofs.Pointers.Gen` are built, check each file with `lake env lean
tests/roadmap/vcs/<name>.lean` (`Result`, `Memory`, `Clients`).
