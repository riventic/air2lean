# Memory-model hardening regressions

Fixes of the memory-model audit ([docs/architecture-audit/memory-model.md][audit], fixtures
in `tests/roadmap/architecture-audit/memory-model/`).
Each Lean file here is run by CI (`lake env lean <file>`, after `lake build ZigLean.Mem.Lemmas`).

| Finding | Fix | Regression |
|---|---|---|
| MM-5 no stack bound | `Mem.stackLimit`/`stackUsed`, `Zig.enterFrame`/`leaveFrame` emitted for recursive functions that use memory, `Zig.Error.stackOverflow` (outcome `stack_overflow`), premise [STK-01](../../../docs/premises.md#stk-01) | `Stack.lean`; `architecture-audit/memory-model/check.sh` (`stack_depth.zig`: model and native both overflow `depth(10^7)` under an 8 MiB stack) |
| MM-14 race log cost | `Mem.solo`/`raceCheck`: no footprint scan while only the main thread can run (`raceCheck_eq_raceAt`) | the proof build; `depth(20000)` runs in about 1.5 s in the interpreter (was quadratic: `depth(4000)` 24 s) |

```sh
lake build ZigLean.Mem.Lemmas
for t in tests/roadmap/memory-hardening/*.lean; do lake env lean "$t"; done
```

[audit]: ../../../docs/architecture-audit/memory-model.md
