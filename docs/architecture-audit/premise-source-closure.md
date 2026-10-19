# Source premise estimates missed checked dependencies

The historical audit on base `543faecd7` passed kernel replay for 24,120 declarations.
Comparing its 10,865 non-runtime theorem records with the original source estimator
exposed 43 records with missing IDs. The source estimate was not always a conservative
over-approximation: 41 records omitted genuine dependencies, and two exposed a false
stack-operation attribution in the compiled comparison.

The concrete failure scenarios are:

- `Cancel.Group.cancelClient_spec` reaches full-state memory and stack rules in its
  checked term, but its source estimate omitted SEM-05 and STK-02. `arr32_pre` likewise
  omitted SEM-05, STK-01 and STK-02. A high-level runtime module's row did not include
  the premises of the lower-level modules that it imports. Source fallback must include
  those runtime import mappings transitively.
- `Sync.gR_lph` omitted PRF-02, TRU-02 and TRU-03; twelve `Threadsync` declarations
  similarly omitted PRF-01. A used section variable had a type such as `Proto Tgt γ`,
  where the concrete generated target did not occur in the local theorem text. The
  source closure must include the full declared types of used variables, recursively,
  and remove the variables at the corresponding scope's `end`.
- `Zig.Handoff.Layout.ws_box` and three related declarations omitted SEM-03. The field
  chain `Lo.WS.In` resolves through the result type of `WS` to the full-state word rule;
  following only the first field loses that dependency. Runtime import mappings also
  recover hidden lock dependencies in `Threadsync.gD_free` and `Threadsync.gD_lock`.
- `Threadsync.dinit_started` and `Threadsync.dstore` exposed a different issue: the old
  token rule treats the inert `Zig.Error.stackOverflow` constructor as a native stack
  operation. This constructor is data and does not consume stack room. These two
  historical source-index gaps must be distinguished from the 41 genuine omissions.
  Lean's generated recursors and case-analysis helpers can mention a constructor absent
  from the theorem's source. The source fallback now applies the existing closure-token
  rules to the declarations of reached runtime modules and their runtime imports, as
  well as using their premise mappings. This conservatively recovers both records.
  Correcting the inert-constructor attribution itself requires separate review of every
  resulting premise reduction; it must not become a per-theorem exception.

The source-only repairs preserve the existing premise tables and token rules. On main
`7ef586aa35afe7219e1bf16ad0ec2734cfe617c2`, before/after comparison has the same 5,302
source theorem rows in 304 files. It changes 4,013 rows by adding conservative IDs and
removes none. These additions are an over-approximation, not evidence that every added
premise is a genuine dependency of every affected theorem. In particular, `dstore` and
`dinit_started` both conservatively gain STK-01 while the constructor token rule remains
unchanged. Runtime token fallback reasons explicitly identify that source approximation.

All 43 historical gap records match current source rows. Comparing their preserved
compiled premise sets with the repaired source estimates leaves no missing ID. This is
a historical comparison, not new kernel evidence.

A fresh all-shipped audit on `7ef586aa35afe7219e1bf16ad0ec2734cfe617c2` passed kernel
replay of 351 modules, with 24,158 selected theorems and 57,027 dependency nodes. Applying
main's unchanged premise tables to that graph yields 10,920 non-runtime records, 44 with
gaps in main's source estimate.
The additional record is `Lists.Alloc.freedSeg_snoc` in `Proofs/Lists/Alloc.lean`: its
section variable `I : FAllocInv` is used through `I.freed`, whose projection belongs to
`ZigLean.Sep.Full.AllocSpec`. Main's compiled baseline attributes ORD-01, ORD-02, SEM-03
and SEM-04 through that module, while the original source estimate misses them. Including
the used variable's type conservatively recovers the owner module and all four IDs.
The semantic need for each coarse attribution remains a separate precision question.

All 43 historical names remain among the current 44, but nine missing-ID sets changed:
the four `Handoff.Layout` records also miss SEM-04 and OSM-01; the four `Threads.Disjoint`
records now miss only SEM-05; and `Threadsync.gD_free` also misses SEM-04 and OSM-01.
The repaired estimator has zero gaps against this same fresh graph. All 351 of the audit's
recorded source bindings match the repair branch byte-for-byte, the report passes the
existing freshness verifier, and actual installed Lean runtime inputs are unchanged
before and after the audit. The 10,920 compiled premise sets themselves are unchanged;
only their source coverage is repaired. This shared-graph comparison does not replace
the repair branch's own required gates.

Regressions cover a used section variable's generated type argument, its absence outside
the section, a nested field-result chain, transitive runtime imports, and result case
analysis whose generated helper can name another constructor. Controls keep unused
runtime imports and runtime-source tokens out of statement-only rules. This repair
adds no declaration-level premise refinement, client proof, proof rule, artifact cache
or scheduling change. Whole-tree generated premise files remain uncommitted.
