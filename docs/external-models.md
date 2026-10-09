# User external models and contracts

`--model-registry registry.json` binds selected direct external calls to project-supplied
Lean models. This first API admits acyclic, fully checked signatures in sequential programs
and uses `Zig.MemM` for every external model, including models that preserve memory. Unknown
calls still fail. Indirect callbacks, noreturn calls, comptime worker targets and concurrent
programs are outside this extension fragment. Callbacks have a separate Lean-level interface,
described in "Callback contracts (E02)" below. Built-in allocator/thread/clock recognition is
one typed table, `stdModels` in `Air2Lean/StdModels.lean`: each row is a qualified std name,
its typed model (or rejection reason), its Zig-version qualification and its semantic
dependencies (the `ZigLean` declarations its emitted term may use). The checker, emitter,
memory/concurrency analysis, diagnostics and this registry all consult that table; adding a
built-in model is one row plus its typed signature and emission cases, not a new name test.
This API cannot override those models or translated AIR, and a translated AIR function that
reuses a built-in std model name is rejected.

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

A known byte sentinel is part of the exact signature layout (`sentinel_byte` as a JSON
number). A binding for `[:0]u8` cannot be reused for `[:42]u8` or missing byte metadata.
Legacy signatures with no byte value retain their old serialized shape; newly exported
known values require a fresh checked template. Runtime pointer/slice representations remain
shared, so imported contracts still supply the actual memory and sentinel invariants.

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
automatically inferred proof-dependency closure. Each entry must be unique and name another
binding in the same registry, a modelled built-in std model qualified for the binding's Zig
version (for example `mem.Allocator.create`; `mem.Allocator.allocSentinel` needs 0.16.0 or 0.17.0), or
a Lean identifier. A rejected std name (`Io.futexWaitTimeout`) and any cycle between bindings,
including a self-dependency, are rejected before output is written.

## Memory footprints (E01)

An entry may add an optional `footprint`, bound to the same exact symbol and signature:

```json
"footprint": {"reads": [], "writes": [0]}
```

Each list holds zero-based parameter indices; every listed parameter must be a pointer or
slice at every call site. Indices must be in range, unique, and not both read and written.
`preserves` bindings cannot list any index. Unknown footprint keys are rejected. A declared
footprint becomes part of the generated obligation:

```lean
def air2lean_model_0_footprint : Zig.External.Footprint (Args) where
  reads := fun _ => []
  writes := fun args => [Zig.External.Region.block args.1]
theorem air2lean_model_0_evidence :
    air2lean_model_0_contract.Holds ... ∧ air2lean_model_0_contract.Respects air2lean_model_0_footprint
```

`Contract.Respects` (in `ZigLean.External`) requires two things. Every access the contract
permits must fall in a written region, or be a non-write access to a read region. The
contract's frame must also leave every block outside the written regions unchanged. A
footprint therefore excludes allocating or freeing other blocks; models that allocate or
free declare no footprint. Clients use `Contract.frame_outside` (blocks outside the writes
stay unchanged) and `Contract.accesses_within`. A `proof` must prove the conjunction.
`assumed` bindings emit it as one axiom. The report's `footprint` field is `null` when
none is declared.

**Volatile parameters (L13).** A binding is the only declared contract for a device access
([volatile-effects.md](volatile-effects.md)). Every direct volatile pointer parameter must be
listed in `footprint.writes`, because a device read can change device state. A volatile pointer
nested inside a parameter (a field, a payload or a pointee) is rejected. Volatile pointers in the
return type are allowed; the caller's accesses through them are checked.

`tests/roadmap/models/Fill.lean` defines `fill(buf: []u8, value: u8)` with footprint
`writes: [0]`, together with its proved evidence. Its client `client_fills_both` calls fill on
two separate buffers. Using only the contract and footprint, it proves both buffers are
filled: the first stays filled because the second call writes only its own block. The
registry test generates `fillClient` from a registered binding and proves the same fact
through the generated obligation (`FillGenerated.lean`). An assumed variant
(`FillAssumedGenerated.lean`) also checks, but its theorem rests on the binding axiom.

## Callback contracts (E02)

`ZigLean.External.Callback` extends the contract layer to function-pointer parameters. A
callback is the model `Ptr × Args → MemM Result`. The first component is the captured context
pointer, which is always passed explicitly. A `CallbackContract Args Result` holds these fields:

- `contract`: a `Contract (Ptr × Args) Result` with pre/post, frame, access, failure and
  divergence over the context and the arguments, plus `termination`, `errors` and `effects`.
- `reads`: blocks the callback may read but not write.
- `reentrancy` and `reentry`. A `.forbidden` callback never calls back into its caller. An
  `.allowed` one lists in `reentry` the caller-owned blocks that a nested call may write.
- `cancellation` and `stop`. `stop` marks the results that ask the caller to stop, for example
  `false` or a returned Zig error. A `.never` callback returns no such result.

Its footprint is fixed: it writes the context block and the `reentry` blocks, and reads `reads`.
`CallbackContract.WellFormed` checks the rules that do not depend on an implementation:

- a forbidden callback lists no re-entry blocks;
- a never-cancelling callback's postcondition excludes every `stop` result;
- the context is borrowed: a call that starts with the context live leaves it live;
- `contract.Respects footprint` holds.

`CallbackContract.Holds cc impl` adds `contract.Holds` for the implementation. Clients use
`CallbackContract.call`, which gives the postcondition, a context that stays live, and every
block outside the context and the re-entry blocks unchanged. `call_forbidden` and
`call_continues` are the non-re-entrant and never-cancelling special cases.
`Contract.comap` adapts an E01 contract to a callback's argument shape.

A call through a function pointer is modelled by `dispatch`. It tries the known targets in
order and throws `.illegal` for any other pointer. This mirrors the emitted indirect call, whose
fallback arm is the same throw (`applyTwice_illegal` in `Proofs/Layout/Proofs.lean`); the
correspondence is by inspection in general, not a theorem about the emitter. By `dispatch_ok`, a
successful call ran a known target. `dispatch_unknown` shows that a pointer with no known
target and no contract never succeeds, so no effects can be assumed for it, empty ones
included. `resolve table s impl` selects the targets of signature `s` from the program's
callable-address table; `resolve_complete`, `resolve_incompatible` and `resolve_unknown` show
that every declared target of `s` is reachable and that a target of another signature or an
unknown address throws `.illegal`. `tests/roadmap/indirect-calls/Bridge.lean` proves that a
fresh emitted indirect call equals `dispatchIn (resolve …)` for every pointer. The registry still rejects address-taken bindings: a callback contract is a Lean-level
interface for model clients. It is not a registry entry, and the translator does not bind it to
an emitted indirect call.

`tests/roadmap/models/Callback.lean` proves two clients from the contract alone:

- the observer `forEach(xs, ctx, cb)` (`forEach_spec`, `forEach_frame`);
- the evaluator `evaluate(cb, ctx, x)` (`evaluate_spec`).

`forEach_spec` takes a caller invariant. It proves that the invariant holds at the end, a live
context stays live, and every block outside the context and the re-entry blocks is unchanged,
which includes the caller's own buffer. A never-cancelling callback runs to the end. The concrete
callback `mark` stores a byte at its context through the E01 `fill` model. Its contract
`markCallback` is checked (`mark_evidence`), and `forEach_mark` proves that the context holds
the last element and that every other block is unchanged.

Negative tests:

- `uncontracted_not_effect_free`: no theorem makes every callback effect-free.
- `uncontracted_forEach_frame_fails`: an uncontracted callback that frees memory breaks the
  observer's context-liveness fact.
- `havoc_not_empty`, `clobber_havoc`: a contract whose frame allows any change does not respect
  the empty footprint, and that freeing callback satisfies it.
- `havoc_not_callback`: such a contract is not a well-formed non-re-entrant callback contract.
- `unknown_call_fails`: a dispatch with no known target always fails.

The model gate checks this file after the Fill model (`callback.log`).

## Contract assumption report

```sh
lake env python3 scripts/external-contracts.py --check Generated.lean [...]
```

The script reads each file's `-- air2lean-models:` marker. It kernel checks the file with
`#print axioms` on every `air2lean_model_<i>_evidence` and lists each used contract. A
contract is `verified` only if its trust is `proved-obligation`, the file checks, and its
evidence uses only `propext`, `Classical.choice` and `Quot.sound`. Every other contract is
listed under `assumptions`, with a reason. That covers assumed axioms, unchecked runs
(no `--check`), failed checks, and proofs that reach `sorryAx` or a project axiom.
`--expect-assumptions=a,b` fails unless the assumption set is exactly that list. The model
gate requires an empty list for the proved fill client and `project.fill` for the assumed one.
A verified status still covers only the Lean model. Correspondence to the real foreign
function remains EXT-01's environment premise.

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
`tests/roadmap/models/StdModels.lean` checks the built-in table (unique names, every typed
model has a row, anonymous-instance lookup), rejection of a std call with an incompatible
runtime signature, of an unqualified Zig version, of a translated function or project binding
reusing a std name, of a same-name project binding with a different second call site, and the
semantic dependency rules. `tests/roadmap/models/StdDependencies.lean` elaborates against the
`ZigLean` umbrella and fails if any row's dependency is not a declaration there.

The gate explicitly builds the `ZigLean` umbrella imported by generated source, compiles the
fixture model into an isolated module search path, and retains generated source, the binding
manifest and all compiler/CLI logs in the evidence directory. CI runs it once on its 0.16.0
non-mutation row. Without `RUNNER_TEMP`, local runs use the temporary directory; override
`AIR2LEAN_MODEL_EVIDENCE` to retain a separate run. No new CI artifact upload is introduced.
