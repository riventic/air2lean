# Conc/Base split: legacy ownership bridge

Task 01 is blocked by a real use of the legacy ownership judgment, rather than by pure
vocabulary alone. This report records the task's required stop condition; it does not complete
the split or approve a framework change. The finding is tracked by engine ledger #conc-base-owned.

Inspected base: `origin/main` at `543faecd7a0bed75b3e841ef052182eacb699816`, fetched on
2026-10-15. The relevant declarations are unchanged in this report.

## Exact dependency

`ZigLean/Sep/Full/ThreadOwned.lean` imports `ZigLean.Conc.Csl` at line 4 and uses its legacy
`Owned` judgment in three places:

| Full-state declaration | Legacy dependency | Source lines |
| --- | --- | --- |
| `Zig.Full.FOwned.legacy` | Returns `Zig.Owned (fun u => ((own u).heap.fix m).erase) m` | 270–294 |
| `Zig.Full.FOwned.fork` | Applies `Zig.Owned.fork` to `(legacy ho).current t`, then uses the resulting `csize` and `owns` fields | 318–320, 335, 348 |
| `Zig.Full.FOwned.join` | Applies `Zig.Owned.join (legacy ho)`, then uses the resulting `csize` and `owns` fields | 375, 400, 407 |

`Zig.Owned` is defined at `ZigLean/Conc/Csl.lean:144–149`; its `fork` and `join` rules start
at lines 283 and 379. Its fields package heap inclusion, disjointness, access-clock ownership,
the empty parts of nonexistent threads, and clock/thread array size agreement. These are the
legacy judgment and rules that Task 01 explicitly says must stay outside Base.

The failure scenario is removing the `Conc.Csl` import after extracting only its pure helper
lemmas. The conclusion of `FOwned.legacy` still names `Owned`, while the proofs of `fork` and
`join` still apply its rules and consume their results. Pure heap and clock facts do not supply
those declarations. Keeping a transitive `Conc.Csl` import would retain the dependency; moving
or restating `Owned` under Base would violate the task's classification and stop condition.
This is a migration obstruction, not a counterexample to the current theorems' soundness.

## Other vocabulary observed before stopping

The remaining imports contain useful pure model vocabulary, but moving it does not remove the
ownership bridge above. This is an initial classification, not a complete elaborator dependency
inventory:

| Full-state module | Candidate vocabulary or facts | Qualification |
| --- | --- | --- |
| `ThreadTls` | TLS operational facts such as `tlsPtr_run`; `WP.liftMem_setTls` is also used | A WP rule must be classified separately from pure TLS facts; Task 02 may extract TLS facts independently |
| `ThreadFacts` | `Conc.AllLe` | A plain clock relation, currently available through the lock import |
| `LockWord` | `Conc.LPh`, `Conc.AllLe`, `Conc.joinedB`, `Conc.LocsKeep` and their model facts; weak-CAS operational facts | `LocsKeep` is already judgment-like vocabulary in the framework allow-list, so moving its entry requires coordinator approval |

No Base modules, premise mappings, statements, framework entries or legacy proofs are changed.
The existing `fowned-bridges` ledger row is different: it requests symbolic-executor support for
stepping through `WP.liftMem_fowned*` and removing `ofSeq` call sites; it does not retire the
`FOwned.legacy` use of `Owned`.

## Decision requested and deletion plan

The proposed direction is to extract reusable facts about fork/join memory and clock changes
that mention neither `Owned` nor another program judgment. The existing full-state `FOwned.fork`
and `FOwned.join` can then be proved against those facts with their current statements. The
coordinator must decide this direction before Task 01 proceeds beyond its explicit stop.

After that decision, delete `FOwned.legacy` and both applications of legacy `Owned` rules,
complete the remaining pure vocabulary split, and run all Task 01 migration gates. Any proposed
move of a judgment-like allow-list entry needs separate coordinator approval. The blocker row
closes only after the legacy dependency is gone and those gates pass.
