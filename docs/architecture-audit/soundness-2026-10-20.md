# Soundness audit 2026-10-20: audited code runs inside the assurance extractor

Base: `origin/main` at `e126e641a` (2026-10-20). This audit changes no code. It records one finding.
The build-speed lane found it in review while designing Lake-built kernel-replay receipts.

Severities as in [trust-chain.md](trust-chain.md): **SOUNDNESS** (a false or empty claim reaches
the user), **FAIL-OPEN** (the guard that should reject is missing; a constructed case shows it),
**HARDENING** (defence in depth or a wrong label).

| # | Severity | Finding | Status |
|---|---|---|---|
| E1 | FAIL-OPEN (evidence integrity) | The assurance extractor imports every audited module into the Lean process that writes the report, so an audited module's `initialize` code runs there and can forge or alter the report. | **fixed** (§Fix) |

## E1: an audited module's `initialize` runs inside the extractor

**What happens.** `scripts/assumptions.py extract` writes a driver that imports `tools.Assurance`
and every audited module, then runs `#assurance_audit`. Lean elaborates the driver either with
`lake env lean` (fresh) or as a Lake-built module (`--extract-in`). Importing a module in the
Lean frontend runs that module's `initialize` declarations. So code from an audited module runs
with full `IO` in the process whose output is the report: the one `AIR2LEAN_ASSURANCE_JSON:` line
that `extract` parses.

**Concrete scenario.** An audited module contains

```lean
initialize do
  IO.println "AIR2LEAN_ASSURANCE_JSON:{...a report of passing, standard-axiom theorems...}"
  IO.Process.exit 0
```

next to a theorem that uses `sorryAx`, or that was added with `debug.skipKernelTC`. The scenario is
constructed from the reproduction below; the full forged report has not been run end to end.
- **Fresh path:** `lake env lean` exits 0 and the forged line is the only report line printed. `extract` requires exactly one report and accepts it.
- **Lake-built path:** Lake also needs the driver's olean, so the early exit fails the build. But a variant that prints the forged line and lets elaboration continue gives two lines, and `extract` already fails closed on that ("did not return exactly one environment report"). An initializer can still change the extractor's behaviour without printing anything. It can register environment extensions or attributes that `tools/Assurance.lean` reads. It can alter files the later checks read, for example by writing into `.lake`.

So "every theorem uses the standard axioms only" is not established independently of the audited code.

**Reproduction** (Lean 4.34.0, 2026-10-20). Library `A` contains
`initialize IO.eprintln "INIT-RAN"` and a theorem. Library `B` is `import A`. `lake build A B`
prints `INIT-RAN` while elaborating `B`. `LEAN_PATH=… leanchecker B` prints nothing: the
toolchain's checker loads the imports without running their initializers.

**What S1 relies on.** S1's structural fix ([claims.md](claims.md) S1) is the independent kernel
replay of every audited module by the toolchain's `leanchecker`, run as its own process
(`scripts/assumptions.py kernel_replay`). That process does not run initializers. This finding
does not reopen S1: a kernel-unchecked theorem is still rejected by replay, and the receipt design
on `perf/lake-kernel-replay` keeps that property (§Related). What E1 weakens is everything the
audit takes from the extractor's report alone: the axiom inventory (`collectAxioms`, `sorryAx`
detection), the declaration graph, statement shapes, framework evidence and the claim heads.

**Options for a fix** (as proposed when the finding was opened):
1. **Extract without importing.** Read the audited oleans with `Lean.readModuleData` and assemble
   the environment without running initializers, the way `leanchecker` imports. This removes the
   exposure. It needs the extractor to work on an environment with no extensions initialized: the
   attribute and extension reads (`getExternAttrData?`, matcher info, projections) must come from
   the module data, or be re-derived.
2. **Refuse initializers in audited code.** The extractor sees every `[init]` declaration and
   init-backed opaque (`backing: "init"` in the graph), so the policy could reject any audited
   module that has one. This acts only after the initializer has already run in the same
   process, so on its own it is not a fix. It is defence in depth next to (1).
3. **Cross-check the report from a second process.** Recompute the safety-relevant parts (axiom
   closure, `sorryAx`) in a process that imports the way `leanchecker` does, and require that they
   agree. This narrows the exposure but duplicates the extractor's core logic.

The recommendation is (1), with (2) as defence in depth.

**Fix (status: fixed).** This is option (1) with the extensions kept.
- **The driver.** It imports only `tools.Assurance`.
- **The import.** `#assurance_audit` imports the audited modules itself (`importWithoutInitializers`). It first reads their closure beyond the extractor's own imports from the `.olean` headers (`importClosure`), freeing each module's data once its imports are read. Then it records every module of that closure in Lean's `interpretedModInits`, the set of modules whose initializers the interpreter has already run. Finally it imports with extensions loaded. Lean's `runInitAttrForMod` skips every recorded module, so no `[init]` of an imported module runs. The builtin extensions are still populated from the imported data, so instances, projections and attributes read the same as before. Only the extractor's own imports, which the driver's header loaded, have run their initializers; they are the tool.
- **The Lake-built driver (#505).** It no longer gets its trace through imports. Its generated library `needs` `@pkg/+M:olean` and `@pkg/+M:depTrace` for every audited module, the mechanism the kernel-replay receipts use.
- **Control:** `tests/roadmap/assurance/ForgedReport.lean`. Its initializer writes a marker file and prints a forged passing report.
  - On the old extractor, the marker is written and the audit fails on two report lines.
  - Now no marker appears, and the report is the real one: it rejects the module's `sorry`.
- **Option (2), refusing `[init]` in audited modules: considered, not adopted.** By construction, the extractor never executes an audited module's initializers, and `ForgedReport.lean` is the control for that. A refusal would add little. It would also conflict with `tests/roadmap/assurance/MetaCode.lean`, which pins an `initialize`d cache that no theorem reaches as passing engine code, and with the root library's own `initialize`d attributes (`ZigLean/Sep/Full/AutoAttr.lean` and others). A variant limited to non-library modules would be a special case. The maintainer can revisit this.

## Related

- The Lake-built kernel-replay receipts (`perf/lake-kernel-replay`) originally imported `M` into
  the receipt process, which had the same exposure. The design was changed before merge. The
  receipt imports only `tools.KernelReplay`, and `M` enters Lake's trace as a `needs` dependency
  (`@pkg/+M:olean`, `@pkg/+M:depTrace`). A control there has an `initialize` that forges a
  passing receipt line: it never runs, and the verdict stays a rejection.
