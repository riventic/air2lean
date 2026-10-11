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

- Run `/review` and `/simple` on every PR. Integrate work in batch PRs. Merge only when CI is green
  at the verified head commit.
- **Merge through the merge queue** (docs/ci.md#coordinator-merge-flow): `gh pr merge <N> --merge
  --auto` once `all-checks` is green on the PR head. The queue runs the full CI on the merge
  result and advances `main` only when it is green; that `merge_group` run is the commit's
  evidence. PR runs reuse unchanged parts' results; the queue never does.
- Run heavy builds through `scripts/build-guard.py`. Regenerate generated files (coverage, premise
  index, theorem inventory, pins, provenance) rather than hand-merging them.
- Run `scripts/preflight.sh` before every push: it checks every generated file CI checks for staleness, in minutes.
- **Local first, CI confirms.** Every CI part can be run on the development Mac, and a PR is pushed
  only after the parts it touches are green locally. CI is the final, independent check before
  merge, never the test loop. Do not push to find out whether something is still red.
- **x86_64-linux runs locally under Rosetta.** Native x86_64-linux runs (build modes, native
  differential, harnesses) go in a `--platform linux/amd64` Docker container, which runs under
  Rosetta at near-native speed. aarch64-linux runs go in a native `linux/arm64` container, and
  aarch64-macos runs on the host. No platform needs CI just to get a result.
- Agents keep a handoff file in `~/.cache/air2lean/handoffs/` and use private scratch directories.
