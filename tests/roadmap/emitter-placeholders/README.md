# Emitter placeholders fail closed (MM-6)

`docs/architecture-audit/memory-model.md` MM-6: an emitter arm that `Check.lean` was assumed to
exclude wrote `panic! "air2lean: …"` or `pure default`. In the kernel both are a successful
return of `default` with the memory unchanged, so an unsupported operation was proved to do
nothing. Now:

* every such arm writes `Emit.lean`'s `placeholder`, an unbound identifier
  (`air2lean_emitter_placeholder "…"`) that does not elaborate;
* the CLI emits through `emitWithNamesChecked`, which rejects output that contains one with
  `EMITTER_PLACEHOLDER` and writes nothing; `--diagnostics-json` runs the same gate;
* each arm that hand-made AIR could reach has a checker rule, so the gate is only a backstop.

`test_cli.py` builds 14 hand-made AIR inputs at run time (one per formerly reachable arm, among
them the trust-chain audit's hand-edited `@reduce(.Add)` of a bool vector) and requires a checker
rejection in both modes. All 14 were accepted, with a placeholder, before the fix. `Gate.lean`
bypasses the checker and requires the gate to reject the placeholder and to leave checked output
unchanged.

    python3 tests/roadmap/emitter-placeholders/test_cli.py .lake/build/bin/air2lean
    lake env lean --run tests/roadmap/emitter-placeholders/Gate.lean
