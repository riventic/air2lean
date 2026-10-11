# Tutorial: external contracts

Give an external function a Lean model with a typed contract, prove the model meets it, and
reason about callers through the contract only. The registry workflow that binds such a model
to a direct external call is in [user external models and contracts](../../docs/external-models.md).

The Zig side is a direct call to an external function, for example:

```zig
extern fn clamp(x: u8, hi: u8) u8;
```

## Steps

1. Generate a registry template from checked AIR (needs the patched Zig; see
   [external models](../../docs/external-models.md)):

   ```sh
   air2lean AIR_DIR -o registry.json --namespace My.Program --model-registry-template
   ```

   [`tests/roadmap/models/client.json`](../../tests/roadmap/models/client.json) is a committed
   AIR input for this step; `tests/roadmap/models/test_cli.py` runs it.

2. Write the model, the contract and the evidence. [`Main.lean`](Main.lean) defines
   `ExternalContracts.clamp` (a `Zig.MemM` model), `clampContract` (`Zig.External.Contract`:
   the result is at most `hi`, memory and access log unchanged, no failure, no divergence) and
   `clampEvidence : clampContract.Holds .total [] .preserves clamp`.

3. Fill the template entry with these names:

   ```json
   {
     "import": "My.Models",
     "implementation": "My.Models.clamp",
     "contract": "My.Models.clampContract",
     "trust": "proved",
     "proof": "My.Models.clampEvidence",
     "termination": "total",
     "errors": [],
     "effects": "preserves",
     "dependencies": []
   }
   ```

   With `"trust": "assumed"` instead, the translator emits a named axiom for the obligation,
   which `scripts/assumptions.sh` reports ([EXT-02](../../docs/premises.md#ext-02)); prefer a
   proof.

4. Check the Lean side:

   ```sh
   lake build ZigLean.External
   lake env lean tutorials/external-contracts/Main.lean
   ```

   `clamp_le_hi` is a client consequence: it uses only `Contract.success`, the evidence and
   the precondition, never the model's body.

## Exercise

Use `Contract.terminates` to prove that every call of the model produces a result:

```lean
theorem clamp_terminates (args : BitVec 8 × BitVec 8) (before : Mem) :
    clamp args before ≠ none
```

A solution is in [`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) claims that the contract gives `result = x`. The contract
promises only `result ≤ hi`, so Lean must reject the client proof with a type mismatch:

```sh
lake env lean tutorials/external-contracts/Negative.lean   # must fail
```

## Assumptions and remaining obligations

[`docs/premise-index.md`](../../docs/premise-index.md) derives these premises for `Main.lean`
(definitions in [`docs/premises.md`](../../docs/premises.md)):

- [EXT-01](../../docs/premises.md#ext-01): a registered call runs the project-supplied model.
  Nothing proves that the real external function (a C library, the OS) behaves like the model;
  that correspondence is the user's obligation.
- [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02): value
  semantics and the memory model the contract talks about.
- [SEM-07](../../docs/premises.md#sem-07): block addresses are the environment's placement
  (`docs/address-placement.md`); the result holds for every placement.
- [TRU-01](../../docs/premises.md#tru-01): the Lean kernel.

Remaining obligations: the extension interface admits only sequential programs with direct
calls; concurrent programs, callbacks and noreturn calls are outside it. This tutorial uses
`"trust": "proved"`; an assumed binding adds a named axiom (see step 3).
