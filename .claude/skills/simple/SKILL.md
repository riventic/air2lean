---
name: simple
description: Use when changed code should be cleaned up without changing what it does — the user asks to simplify, tidy, clean up, de-duplicate, or de-complicate a diff/branch/file, or a just-finished implementation reads as over-built. Fans four cleanup agents (reuse, simplification, efficiency, altitude) over the diff and applies the fixes. Quality only — it does not hunt for correctness bugs, that is /review.
disable-model-invocation: false
user-invocable: true
allowed-tools: Bash, Read, Grep, Glob, Edit, Agent
argument-hint: "[<target>]"
---

# /simple — Cleanup pass over the changed code

Port of Claude Code's bundled `simplify` skill, extracted from the CLI binary (2.1.296) and kept as a file for the same reasons `/review` is: always listed, always readable, never subject to the bundled skill's invocation limits. Named `simple` so it does not shadow the bundled `/simplify`, which stays callable and is the upstream cross-check.

**From each shape line to the end of its Phase 2, this is upstream's text character for character** — both cells, the 4-agent one and the `Agent`-unavailable fallback. Three deviations, and no others: the shape lines name `/simple`, the intros point at `/review`, and the fallback's two phase headings sit at `###` so they nest under the section that holds them. Outside the copied prompt: everything above the rule below, the "When the `Agent` tool is absent" header and the note under it, and `## Related` at the end. Nothing sits *inside* a copied phase.

**Inline the angle text into each agent prompt** — sub-agents never see this file.

**Scope: quality, not correctness.** This skill changes how the code reads, never what it does. It finds no bugs and looks for none — `/review` is the bug hunter.

## Arguments

| Argument | Meaning |
|---|---|
| `<target>` | A `<pr#>`, branch, path, or `a...b` range. Blank = the current diff. |

There is no report-only mode: Phase 2 *is* the skill. For a cleanup list you can read before anything is touched, run `/review --no-fix` — its reuse/simplification/efficiency/altitude angles are the same four, riding along behind the correctness ones.

---

`/simple → 4 cleanup agents in parallel → apply the fixes`

You are improving the quality of the changed code, not hunting for bugs. Review
it for reuse, simplification, efficiency, and altitude issues, then fix what you
find. Do not look for correctness bugs — that is what `/review` is for.

## Phase 0 — Gather the diff

Run `git diff @{upstream}...HEAD` (or `git diff main...HEAD` / `git diff HEAD~1`
if there's no upstream) to get the unified diff under review. If there are
uncommitted changes, or the range diff is empty, also run `git diff HEAD` and
include the working-tree changes in scope — the review often runs before the
commit. If a PR number, branch name, or file path was passed as an argument,
review that target instead. Treat this diff as the review scope.

## Phase 1 — Review (4 cleanup agents in parallel)

Launch **4 independent review agents** via the Agent tool, all in a
single message so they run concurrently. Pass each agent the diff and one of
the four angles below. Each returns its findings with `file`, `line`, a
one-line `summary`, and the concrete cost (what is duplicated, wasted, or
harder to maintain).

### Reuse

Flag new code that re-implements something the codebase
already has — Grep shared/utility modules and files adjacent to the change,
and name the existing helper to call instead.

### Simplification

Flag unnecessary complexity the diff adds: redundant or derivable state,
copy-paste with slight variation, deep nesting, dead code left behind. Name
the simpler form that does the same job.

### Efficiency

Flag wasted work the diff introduces: redundant computation or repeated I/O,
independent operations run sequentially, blocking work added to startup or
hot paths. Also flag long-lived objects built from closures or captured
environments — they keep the entire enclosing scope alive for the object's
lifetime (a memory leak when that scope holds large values); prefer a
class/struct that copies only the fields it needs. Name the cheaper
alternative.

### Altitude

Check that each change fixes the root cause at the right depth rather than
patching a symptom with a fragile bandaid. Special cases layered on shared
infrastructure are a sign the fix isn't deep enough — prefer the simpler, more
general change to the underlying mechanism over adding special cases, and name
that change.

## Phase 2 — Apply the fixes

Wait for all four agents to complete, dedup findings that point at the same
line or mechanism, and fix each remaining one directly. Skip any finding whose
fix would change intended behavior, require changes well outside the reviewed
diff, or that you judge to be a false positive — note the skip rather than
arguing with it. Finish with a brief summary of what was fixed and what was
skipped (or confirm the code was already clean).


---

## When the `Agent` tool is absent

Upstream ships this as a second standalone cell and the CLI picks one at call time; here both live in one file, so this section repeats only what differs. Phase 0 and the four angles are the ones above — read "below" in the quoted text as "above".

`/simple → Agent tool unavailable → single-pass inline cleanup → apply the fixes`

You are improving the quality of the changed code, not hunting for bugs. Review
it for reuse, simplification, efficiency, and altitude issues, then fix what you
find. Do not look for correctness bugs — that is what `/review` is for.

The Agent tool isn't available in this context, so the usual
4-agent fan-out can't run. Work through all four angles below yourself, in
this same context, in one pass — do not skip an angle for lack of fan-out.

### Phase 1 — Review (4 cleanup angles, single pass)

Review the diff against each angle below in turn. For each, note findings with
`file`, `line`, a one-line `summary`, and the concrete cost (what is
duplicated, wasted, or harder to maintain).

### Phase 2 — Apply the fixes

Dedup findings that point at the same line or mechanism, and fix each
remaining one directly. Skip any finding whose fix would change intended
behavior, require changes well outside the reviewed diff, or that you judge to
be a false positive — note the skip rather than arguing with it. Finish with a
brief summary of what was fixed and what was skipped (or confirm the code was
already clean). State clearly in your summary that this was a single-pass
review done without the Agent tool, not the full 4-agent
fan-out, so whoever reads it isn't misled about what actually ran.

## Related

- [/review](../review/SKILL.md) — the bug hunter. Carries these same four angles as ride-alongs behind its correctness ones, capped and outranked by real bugs. Run it for "is this right"; run `/simple` for "is this clean".
- `Skill(skill: "simplify", …)` — the bundled original, for cross-checking this port.
