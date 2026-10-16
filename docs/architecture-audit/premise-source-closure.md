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
  Correcting that attribution requires separate review of every resulting premise
  reduction; it must not become a per-theorem exception.

The source-only repairs preserve the existing premise tables and token rules. On main
`7ef586aa35afe7219e1bf16ad0ec2734cfe617c2`, before/after comparison has the same 5,302
source theorem rows in 304 files. It changes 3,222 rows by adding conservative IDs and
removes none. These additions are an over-approximation, not evidence that every added
premise is a genuine dependency of every affected theorem. In particular, runtime import
fallback recovers STK-01 for `dstore`; the historical `dinit_started` false attribution
still remains after these source-only repairs.

All 43 historical gap records match current source rows. Comparing their preserved
compiled premise sets with the repaired source estimates leaves only `dinit_started`'s
STK-01 discrepancy. This is a historical comparison, not new kernel evidence. Main's
current CI audit reports 10,920 compiled records and 44 source-index gaps; its log does
not list their names and no premise-audit JSON was uploaded. The extra record and the
current strict result require actual report evidence before claiming that every gap is
resolved.

Regressions cover a used section variable's generated type argument, its absence outside
the section, a nested field-result chain, and transitive runtime imports. This repair
adds no declaration-level premise refinement, client proof, proof rule, cache mechanism
or scheduling change. Whole-tree generated premise files remain uncommitted.
