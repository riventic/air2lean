# CLAUDE.md

Standing rules for anyone (human or agent) working on air2lean. Project scope and status live in
[README.md](README.md), [ROADMAP.md](ROADMAP.md) and [remaining-acceptance.md](remaining-acceptance.md).

## Direction

- **Long-term over band-aid.** Pick the decision that serves the project long term. Do not take a
  short-term workaround that will have to be redone.
- **Full language support, not snippets.** Implement general support for a Zig feature, type, std
  module or target. Do not prove one code snippet in a way that breaks when the code changes. A
  proof should follow from general semantics and reusable rules.
- **General tactics over module-specific ones.** A proof about a module supplies its invariant and
  little else; the generated code is walked by general tactics and rules in the libraries
  (`ZigLean`). When a module-specific tactic seems necessary, generalize it into the library
  instead. Module-specific tactic glue is debt to be removed.
- **One mechanism over special cases.** When something fails, fix the underlying model, translator
  rule or proof rule. Do not add per-case exceptions, premises or allow-lists.
- **Soundness first.** A soundness finding outranks new features. Every finding needs a concrete
  counterexample or a failure scenario. Audit reports go in `docs/architecture-audit/`.
- **Fail closed.** If the translator cannot model something precisely, it rejects the input with a
  clear diagnostic. It never guesses. A conservative over-approximation is allowed when the model
  says `.illegal` where native code might not; document it.
- **No weakened statements.** Do not weaken a theorem or a spec (`AllocSpec`, `FAllocSpec`, the
  sync specs) to make a proof go through. Report the exact obstruction, with a kernel-checked
  counterexample where possible.

- **Zig 0.17 first, older versions still supported.** New features, std translations, targets and
  proofs target Zig 0.17 first. Solve gaps in older versions too. An older version may be left
  partially supported only when supporting it would weaken support for another version. Then it
  rejects the construct with a clear diagnostic and is never mis-modelled.

## One proof framework

- **There is one proof framework: the full-state separation logic with `fsym`.** Proofs are
  `FTriple` (partial), `FTotalTriple` (total) or `CTriple` (concurrent) and are walked by `fsym`
  (`docs/sep-full-state.md`, `docs/proof-automation.md`; both on `codex/alloc-arena-proof` until
  that branch lands on main).
  Termination, cost, stack room and allocation bounds are resources or pre/postconditions inside
  these judgments, not judgments of their own.
- **Extend it, never fork it.** New capability comes as library lemmas and `@[fsym]` rules.
  Do not add a new judgment (`…Triple`, `…Returns`, `…Within`, `Stops`, `Halts`, …), tactic
  (`syntax`/`macro`/`elab … : tactic`), proof template or automation, and do not add to the legacy
  layer (`ZigLean/Sep` outside `Full/`: `Triple`, `TotalTriple`, `TTriple`, templates, `vc_gen`
  targets), which is being migrated and deleted. If `fsym` cannot do something, stop and report
  the exact missing rule or engine feature instead of building around it.
- **The allow-list is the gate.** `assurance/proof-framework.json` lists every judgment and
  tactic and every file that still uses the legacy layer; `scripts/proof-framework.py` (preflight,
  so CI) fails on new entries, and the lists only shrink. Changing it needs the maintainer's
  approval ([docs/proof-framework.md](docs/proof-framework.md)).

## Coordination

- **One goal at a time.** Parallel work serves the current project goal (ROADMAP.md, "Current
  state"). A side track starts only with the maintainer's approval, and a parked track keeps a
  handoff and a pushed WIP branch.
- **Scope agents to the framework, not just to a requirement.** Every task brief names the
  framework rules above. "Make requirement X complete" never licenses new machinery.
- **Few branches, short-lived.** A branch merges or is closed; no stacked chains of PRs on unmerged
  branches. Remove a worktree when its branch is merged or parked, and delete merged branches.
- **Before merging, check the diff for new judgments, tactics or legacy-layer additions.**

## Trusted base

- **Allocators, threads and IO come from translated real Zig code.** Prove them down to the OS
  primitives: `posix.mmap`/`munmap`/`mremap`, futex, clone/pthread, and macOS malloc/free (OSM-02).
  Never hand-write a model of a std module. Legacy hand-written allocator models are to be removed,
  not extended.
- **Every assumption is an explicit premise** with an ID in `docs/premises.md` and
  `assurance/premises.json`. This includes OS behaviour, CPU count, spawn policy, allocator thread
  safety and opt-in admissions such as `--assume-no-libc`. Claims list their premises.
- **C goes through `zig translate-c`** and the existing pipeline. There are no C-specific runtime
  models.
- **Upstream Zig bugs** are drafted in `docs/upstream/` and collected on our own issue board. They
  are never filed upstream without the maintainer's decision.

## Workflow

- Run `/review` and `/simple` on every PR. Keep PRs small.
- **Merge when green locally; CI does not block** (maintainer decision 2026-10-12). Before
  merging: merge `main` into the PR, run `scripts/regen.sh --pr`, `scripts/preflight.sh` and every
  CI part the PR touches locally (including x86_64-linux under Rosetta); then merge it at once
  (`gh pr merge <N> --admin --merge`), one PR at a time. CI still runs on every PR and on `main`
  as a warning; a red result after merge is fixed forward immediately.
- **Whole-tree generated files are never committed in PRs** (`assurance/generated.json`: coverage
  inventories, premise index, provenance manifests, pins and receipts). CI produces them on the
  merged tree and publishes them on the `generated` branch (docs/ci.md#whole-tree-generated-files);
  `scripts/generated.py materialize` (or `fetch`/`regen`) puts them in a checkout.
- Run heavy builds through `scripts/build-guard.py`. Regenerate the other generated files (theorem
  inventory, goldens, `Gen.lean`) rather than hand-merging them.
- After merging `main`, run `scripts/regen.sh`: it regenerates every generated file in order
  (`--pr` skips the whole-tree files). Do not write private regeneration scripts; fix or extend
  `scripts/regen.py` instead.
- On the dev Mac, set `AIR2LEAN_CAS_DIR=$HOME/.cache/air2lean/cas`: worktrees then share patched
  compilers (`scripts/zig-air.sh <version>`), Lean build outputs and AIR exports. Unset (CI), nothing
  is cached. See [docs/build-cache.md](docs/build-cache.md).
- Start every new worktree with `scripts/worktree-init.sh [--zig <version>]`: it builds the Lean
  packages through the shared cache (only modules no worktree has built yet are compiled), the
  requested patched compilers and the generated files.
- Run `scripts/preflight.sh` before every push: it materializes the whole-tree files and checks
  every committed generated file CI checks for staleness, in minutes.
- **Local first.** Every CI part can be run on the development Mac, and a PR is pushed and merged
  only after the parts it touches are green locally. CI is never the test loop and never a
  merge gate. Do not push to find out whether something is still red.
- **x86_64-linux runs locally under Rosetta.** Native x86_64-linux runs (build modes, native
  differential, harnesses) go in a `--platform linux/amd64` Docker container, which runs under
  Rosetta at near-native speed. aarch64-linux runs go in a native `linux/arm64` container, and
  aarch64-macos runs on the host. No platform needs CI just to get a result.
- Agents keep a handoff file in `~/.cache/air2lean/handoffs/` and use private scratch directories.

## Agent working style

- **Edit code with the Edit and Write tools**, never with `python3 - <<EOF … open(p).write(…)`,
  `sed -i` or heredocs. Read files with Read and search with Grep/Glob, not `cat`/`sed -n`/`grep`
  in the shell.
- **Inner loop: build only what you changed.** While working, build the touched module
  (`scripts/build-guard.py … lake build <Module>`) or run the one check script of the fixture.
  Run `scripts/regen.sh --pr`, `scripts/preflight.sh` and the native/Docker rows once, before
  merging, not after every edit.
- **No polling.** Do not loop on CI or on other agents; CI does not gate merges. Wait for a
  background command with one `until` loop at most.
