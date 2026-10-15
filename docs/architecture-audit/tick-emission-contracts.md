# L8 tick emission: contract compatibility question

Status: **maintainer decision required** before the emitter changes. Checked against
`origin/main` 96dfa27e51da1167170a74c23272e03723e7b75d (2026-10-15). This records a
rollout obstruction, not a soundness defect in the current translator: it emits no ticks and
does not yet claim tick bounds for generated loops.

Task 09 requires a tick at the start of every memory or concurrent loop-body run, including
the final exit, and at every memory or concurrent recursive call-group member's entry. It
also requires that every existing proof build unchanged, with no weakened theorem
statements. Those requirements are incompatible with an existing public theorem under the
current full-state judgments.

## The concrete counterexample

`Proofs/Lists/Linked.lean` currently proves, for every assertion `R`:

```lean
theorem reverse_tstep_nil (pr : Option Ptr) (R : FAssn) :
    FTTotalTriple R (reverse.loop6.run ⟨pr, none⟩)
      (fun r => ⟪r = (.br5, ⟨pr, none⟩)⟫ ⋆ R)
```

Choose `R = emp`. The empty-list branch of `Lists.Open.reverse.loop6` currently returns
`(.br5, ⟨pr, none⟩)` without touching memory. After the required instrumentation, this
branch first executes `Zig.tick`, then returns that same value. For the start memory with no
globals (`TicksCX.m0`), this changes `m.ticks` from `0` to `1`.

The start memory holds `emp` next to the frame `Ghost.credAuth 0`
(`TicksCX.start_holds_auth`). This is a permitted frame of both the thread theorem's
sequential reading (`FTTotalTriple.toFTotalTriple`) and its partial reading. After the tick,
no resource can hold next to this same frame: `TickAuth.meter` would require
`r'.gh.ac.frag .cred + 1 ≤ 0`. Consequently **every postcondition fails**, not just the
original postcondition. The full-state judgment must reject the unchanged theorem.

The primitive version is already kernel-checked in
`tests/roadmap/sep-full/TicksCX.lean`:

```lean
theorem tick_without_credit : ¬ FTriple emp Zig.tick (fun _ => emp)
```

The same file's `meter_cx` shows that the zero-credit authority is accepted before the tick
and rejected afterwards. The final exit must tick even for an empty list, so this failure
does not depend on list length, arithmetic automation, a backend, a Zig version, an
allocator, or an unsupported loop case. A new `fsym` rule cannot prove this false contract.

## Old design approval and the requested statement change

The user-invoked design `~/.cache/air2lean/handoffs/plans/tick-cost.md` records the following
coordinator decision (2026-10-14):

> D3 APPROVED as a correction, conditional on the kernel counterexample (tick without
> credits/unmetered under a held meter) being checked first, like push_without_sp_cx.

Its D3 proposal says that every tick requires one credit or `unmetered`, and that old
credit-free statements of code that ticks are false. The old stack/tick handoff further
says: “Scope (1): plain only where forced now (stack allocs); L8b adds `plain` (same atom!)
to loop clients.” Main reflects this staging: the list theorem above has no `plain`.

Using that design would change the example's public statement as follows:

| Part | Current public statement | Proposed plain-mode statement |
| --- | --- | --- |
| Precondition | `R` | `R ⋆ plain` |
| Command | Current `reverse.loop6.run ⟨pr, none⟩` | The same definition name after adding a tick |
| Postcondition | `⟪r = (.br5, ⟨pr, none⟩)⟫ ⋆ R` | `⟪r = (.br5, ⟨pr, none⟩)⟫ ⋆ (R ⋆ plain)` |

This asks clients for another resource and excludes the counterexample frame. It therefore
does not preserve the old precondition. Task 09's explicit unchanged-proof and no-weakened-
statement requirements must be reconciled with the older correction approval by the
maintainer; this lane has not silently applied that change.

No new judgment, tactic, legacy rule, allow-list entry, extra premise, or unmetered exception
has been introduced. Omitting the final-exit tick or letting `tick` ignore a held meter would
invalidate the approved cost unit or its non-mintability argument and is not a solution.

## Certificate obligation for the eventual emitter change

`Air2Lean/Certificate.lean`'s `loopCert` currently proves equality between the AIR interpreter
and generated loop bodies, including the complete output `Zig.Mem`. Its memory-mode body
equation compares `execBody` with the generated body at the same input memory. But
`Air2Lean/Sem.lean`'s `execLoop` currently runs `execBody` without a tick. Adding a tick only to
the emitter changes the right side's output memory and makes that equation false on an
immediately exiting memory loop.

The eventual emitter PR must extend the generic AIR loop semantics and certificate proof
together, preserving the correspondence statement and the approved D5 distinction: pure
`Result`/`Zig.M` loops remain unmetered. Recursion currently lies outside the memory
certificate fragment because of `Zig.enterFrame`; concurrent functions are also explicitly
outside that fragment. The tick-placement completeness check must nevertheless cover their
generated definitions, including dispatch loops, all call-group members and every backend.

This is coordinated with Task 12's canonicalization certificate lane. No certificate
fragment was reduced and no equality was replaced with a weaker relation in this report.

## Resumption requirements

The maintainer must first resolve whether the documented D3 correction authorizes the
explicit public mode changes above despite Task 09's unchanged-proof requirement. If so,
record the affected statement changes and the existing kernel counterexample, and carry the
same `plain` atom through each affected client and adequacy theorem. Keep allocator
contracts unchanged as required by approved D4. Otherwise report the incompatible
requirements without implementing a second logic or a meter bypass.

After that decision, L8b-1 must validate handwritten tick loops and recursive functions in
sequential, thread, concurrent and WP modes. Existing engine ledger T1 (counted-credit
planning) and T4 (concurrent tick execution) remain open; their success must be established
before the one emitter regeneration. L8b-2 is a standalone PR, announced before publication,
locally gated including Rosetta, and left unmerged for the coordinator. L8c starts from main
after that emitter PR lands and retires the approved allocator-model counts (D6), preserving
the exact loop bounds and kernel negative controls.
