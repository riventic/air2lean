# User external models and contracts

`--model-registry registry.json` binds selected direct external calls to project-supplied
Lean models. This first API admits acyclic, fully checked signatures in sequential programs
and uses `Zig.MemM` for every external model, including models that preserve memory. Unknown
calls still fail. Indirect callbacks, noreturn calls, comptime worker targets and concurrent
programs are outside this extension fragment. Historical allocator/thread recognition stays
in its existing centralized tables; this API cannot override those models or translated AIR.

Generate an authoring template from checked AIR first:

```sh
air2lean AIR_DIR -o registry.json --namespace My.Program --model-registry-template
```

The template records each missing direct symbol, its complete normalized profile, and
canonical argument/return shapes. Shapes include signedness, recursive child types, named
aggregate fields, error sets, ABI sizes/alignments/offsets, pointer alignment and pointer
flags. Local type IDs do not determine identity. The `type` string is the normalized Lean
`Ty` representation in registry schema 1; regenerate templates after changing that format.
No accepted implementation or contract is supplied by a template: fill every missing field.

Registry JSON uses the shared strict parser: duplicate decoded keys, oversized numbers or
exponents, more than 528 nested registry JSON containers and inputs over 64 MiB are rejected. AIR retains
its 128-container default. The CLI
bounds registry-file reads before constructing a UTF-8 string.

Schema 1 deliberately retains expanded tree-shaped JSON. Completed type memoization avoids
revisiting shared children, while expanded-cost accounting rejects more than 65,536 JSON
nodes or 1,048,576 UTF-8 bytes and nesting beyond 256 type nodes along any expanded path. Repeated DAG edges count
again toward serialized cost. Registry/template inputs preflight the entire type table before
normalization and recursive subset checking; consequently every type in those tables must
be acyclic and fit these limits, including types outside an external signature. The same
limits apply to all argument/return roots of each binding. Failure reports a budget/cycle
diagnostic before output. This is a bounded extension interface, not a general V05 fix for
unregistered inputs or all translator traversals.

Each entry must add these fields:

```json
{
  "import": "My.Models",
  "implementation": "My.Models.identity",
  "contract": "My.Models.identityContract",
  "trust": "proved",
  "proof": "My.Models.identityEvidence",
  "termination": "total",
  "errors": [],
  "effects": "preserves",
  "dependencies": []
}
```

Keep the template's `symbol`, `signature` and `profile`. Profiles use the AIR parser and must
match all input facts and the Zig version exactly. Legacy AIR requires the complete explicit
`legacy-abi64-le` normalized record; a legacy binding is only qualified for that reference
model, with its unavailable target facts still unverified. No wildcard names, versions,
layouts or profiles exist. Duplicate/unused bindings, missing fields, invalid Lean identifiers,
unknown policy values and incompatible same-name signatures are rejected before writing output.

Models receive a right-associated tuple of arguments (one argument stays its own type;
zero arguments use `Unit`) and return `Zig.MemM Result`. The imported contract has type
`Zig.External.Contract Args Result`. Generated aliases check those types; generated evidence
checks `contract.Holds termination errors effects implementation`. `errors` names allowed
`Zig.Error` safety failures. Returned Zig errors are values (`Except Zig.ErrName Payload`) and
must be constrained by `post`; divergence is separate. `total` excludes divergence within
`pre`; `partial` requires the contract's divergence predicate. Every successful step proves
`post`, the declared state frame, preservation of the existing access log, and permission for
every new `FootprintEntry`. `preserves` additionally requires equality of the entire before
and after state. `tracked` requires the explicit access and frame predicates; it never
manufactures empty effects. The frame predicate must state allocation/lifetime and other
observable state requirements for the chosen model.

Memory on failure is erased by the existing `StateT Mem Result` runtime. Failure predicates
therefore see the initial memory and safety error, not a fabricated final state. Contracts
cannot use this interface to claim failure-state mutation/ownership preservation. Models of
real foreign libraries, devices, clocks or operating systems need separate correspondence
and environment premises; no shipping-binary theorem follows from registering a Lean model.

`trust: "proved"` requires an imported proof identifier and emits a theorem obligation.
`trust: "assumed"` forbids a proof field and emits a named explicit axiom with the same complete
typed obligation. When bindings are present, the generated `-- air2lean-models:` JSON marker reports these assumptions
separately from selected runtime semantics and preserves semantic dependencies, profile and
signature. Without bindings, output has only the existing profile header before the Lean body. A proved entry is reported as `proved-obligation` until the generated source is
kernel checked. Kernel elaboration checks the obligation's type; imported axioms/dependencies
must still be audited (for example with `#print axioms`) before claiming implementation
verification. `dependencies` is the project's explicit semantic dependency inventory, not an
automatically inferred proof-dependency closure.

Compile project model modules and the generated output before treating the translation as
usable proof evidence. Clients use `Contract.success` under the declared precondition and
`Contract.terminates` for total contracts. Changing a binding/profile requires regeneration
and checking again. Contracts do not automatically prove a client's preconditions or loops.

The focused regression example defines a proved identity model and proves a generated
client's returned value from its declared postcondition, plus a tuple-and-scalar client that
checks argument grouping. Under the serialized compiler guard:

```sh
AIR2LEAN_MODEL_EVIDENCE="$RUNNER_TEMP/model-contracts" scripts/model-contracts.sh
```

The CLI driver exercises exact signature/layout/profile checks, proved versus assumed
obligations, mandatory fields, missing models and preservation of existing output on errors.
Template mode produces JSON authoring data and intentionally does not certify program calls.

The gate explicitly builds the `ZigLean` umbrella imported by generated source, compiles the
fixture model into an isolated module search path, and retains generated source, the binding
manifest and all compiler/CLI logs in the evidence directory. CI runs it once on its 0.16.0
non-mutation row. Without `RUNNER_TEMP`, local runs use the temporary directory; override
`AIR2LEAN_MODEL_EVIDENCE` to retain a separate run. No new CI artifact upload is introduced.
