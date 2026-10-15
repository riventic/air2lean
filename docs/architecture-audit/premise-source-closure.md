# Source premise estimates missed checked dependencies

Audit base: `543faecd7`. The checked shipped audit passed kernel replay for 24,120
declarations. Comparing its 10,865 non-runtime theorem records with the original
source estimator exposed 43 records with missing IDs. This is separate from premise
precision: the original source estimate was not always an over-approximation.

Concrete failures and the generic corrections:

- `Cancel.Group.cancelClient_spec` reached full-state memory/stack rules in its checked
  term, but its source estimate omitted SEM-05 and STK-02. Similarly `arr32_pre` omitted
  SEM-05, STK-01 and STK-02. A high-level runtime module's manually maintained row did not
  include every imported lower-level rule. Source fallback now unions runtime import
  mappings. The checked index still uses the actual term rather than importing this union.
- `Sync.gR_lph` omitted PRF-02, TRU-02 and TRU-03; twelve `Threadsync` declarations had the
  analogous PRF-01 omission. Their used section variables carried types such as
  `Proto Tgt γ`, where the concrete generated target was absent from the local theorem
  text. Source fallback now includes the full type of each used section variable,
  recursively, and removes scoped variables at the corresponding `end`.
- `Zig.Handoff.Layout.ws_box` and three related declarations omitted SEM-03. The field
  chain `Lo.WS.In` resolves through the result type of `WS` to the full-state word rule;
  the source resolver followed only the first field. It now follows result types along
  the complete chain. Runtime import fallback also recovers hidden lock dependencies
  for `Threadsync.gD_free` and `Threadsync.gD_lock`.
- Two of the 43 records (`Threadsync.dinit_started`, `Threadsync.dstore`) instead exposed
  a false carrier: the old token rule treated the inert `Zig.Error.stackOverflow`
  constructor as a native stack operation. The constructor is data and does not consume
  stack room. The rule now retains STK-01 for allocation, frame entry and recursive calls,
  while the constructor alone adds none. This changes no theorem or operational model.

Thus 41 records needed genuine source-closure corrections; two needed removal of an
unsupported token attribution. Regressions cover section-type arguments, nested field
chains, imported runtime mappings, the inert error constructor and retention for actual
stack operations. The declaration-carrier tests additionally retain required premises
through runtime proof bodies, private names and equation lemmas, reject missing graph
edges, and retain every unreviewed module fallback.

Three baselines must remain distinct in reports:

1. The original source estimator, with the omissions above.
2. The repaired conservative source estimator, used for visibly labelled fallback rows
   and the generated index's per-premise drop counts.
3. The old compiled module-boundary attribution, used for the declaration-carrier subset
   check and its `module_premises`/`dropped` fields. The checked shipped comparison
   dropped OSM-01 from 525 records, SEM-04 from 389, and ORD-05 from 21, with no additions
   to that compiled baseline. The independent inert-error rule correction is not counted
   as one of those carrier reductions.

Comparing the final records with the preserved original compiled module sets gives no
additions and these complete removal counts: OSM-01 525, SEM-04 389, ORD-05 21, STK-01 13.
The STK-01 removals are the independent inert-constructor correction (including generated
helper theorems), rather than declaration-carrier refinement. The current classifier's
`drop_counts` isolates carrier refinement against the current module/token rules.

The final shipped classification preserves those counts after broadening both carrier
families to include every primitive model helper and native target fact. It passes strict
source-gap comparison with zero gaps across all 10,865 non-runtime theorem records and
no additions to the compiled module baseline. Its guarded classification used 20.758 s
of workload (554.377 s admission wait) and peaked at 1,375,232 KiB; the underlying shipped
kernel audit used 910.355 s. This historical audit predates the toolchain binding described below.

Representative drops are `Lists.Alloc.create_spec` (ORD-05: no pointer-atomic primitive
family in its checked closure), `Cancel.Group.Inv.main` (SEM-04: a resource predicate,
without a return/total carrier), and `Sync.MutexCounter.mutexCounter_safe` (OSM-01: no
mapping primitive, helper or native target fact). The last theorem still retains SEM-04:
its checked rule dependencies include `Zig.Full.FReturns`, and the unrefined legacy
`AllocSpec.Norm` module also retains that premise. Partial client statements alone do
not justify removing internal proof dependencies.

Both source estimators enumerate 5,248 rows on this base. Runtime-import fallback and the
resolver corrections add conservative IDs to 3,171 source rows; for example MTH-01 enters
3,142, SEM-05 enters 1,318 and STK-02 enters 1,333. These counts measure the deliberately
broader estimate, not genuine dependencies of all those theorems. Removing the inert
constructor token removes STK-01 from 42 source estimates. Checked rows replace that
estimate with the actual declaration closure; only unrepresented declarations keep it.

A subset check is a regression constraint, not a soundness proof. Reviewed carrier
coverage, complete kernel dependencies, actual artifact/source/toolchain freshness and
conservative fallback remain necessary; see [the derivation rules](../premises.md#how-premises-are-derived).

## Executable hashes omitted the shared kernel runtime and compiled toolchain inputs

The pinned Lean 4.34.0 macOS `lean` and `leanchecker` executables are 49,968 and 78,224
bytes. `otool -L` shows they load `libInit_shared`, `libleanshared`, `libleanshared_1`,
`libleanshared_2` and, for the checker, `libLake_shared`. A library could change while
the executable hashes stayed identical, allowing a replay cache or premise cache keyed
only by the stubs to reuse evidence from a different kernel runtime.

The shared `assumptions.toolchain_runtime_sha256` binds all toolchain executables and
bundled `.dylib`, `.so`/versioned `.so`, and `.dll` files, plus installed `.olean`,
`.olean.private` and `.olean.server` logical inputs and `.ir`/`.ir.sig` runtime inputs, by deterministic relative paths
and bytes. Standard toolchain modules are exempt from replay, making their compiled inputs
necessary even when every project artifact is unchanged. Lean's installed
`Environment.lean` (`importModulesCore`, `readIRPartsOfMod`) also loads IR/signatures for
non-module import roots and meta imports; these can affect the extractor without changing
executable or olean bytes. The pinned installation contains 2,518 IR files (375,682,224 bytes)
and 2,518 signatures. Mutable `.hash` metadata is excluded.
The helper follows directory/file symlinks, binds link identity and target content,
and rejects broken/cyclic links and loader environment overlays. Host system libraries
remain part of the existing trusted host base. The digest now binds the extractor
sidecar, replay cache, freshness validation and premise input key; before/after checks
reject a toolchain change during extraction or replay. Report batches hash the complete
toolchain before and after verification, without persistent memoization; a verifier cannot
be retained after the batch closes. The complete installed digest, including IR/signatures,
took 2.571 seconds on this Mac. Replay workers also honor the guard's assigned job budget.

The existing replay-record fields and receipt revision/dirty-tree checks remain unchanged.
New audit freshness records carry the runtime digest; premise-cache admission requires
matching extractor/replay bindings, so legacy reports are regenerated. The original
910.355-second shipped run above is historical timing evidence and is not retroactively
accepted by the new cache. Readiness requires a fresh audit with the runtime binding.

The loader boundary also includes project compiled inputs, including dependencies used
only by the extractor. `Lean.Environment.readModuleDataPartsOfMod` opportunistically
loads `.olean.server` and `.olean.private` for module-system files;
`readIRPartsOfMod` checks for `.ir.sig` and then loads `.ir` independently of module-ness.
The current project emits no such companions, so adding one must invalidate reuse even
when every executable and main `.olean` stays unchanged. The shared traversal now binds
the logical/IR files exposed by the actual ordered search roots, their paths and symlink
identities, additions/absence, and top-level directory presence (Lean's lookup selects a
library by its first matching top-level root). Hash metadata and unrelated native build
outputs are excluded. Extraction, replay and cache admission are bracketed by fresh
manifest checks; verification batches repeat their checks before accepting results.
The extractor sidecar and reusable Lake replay key use the same compiled-input binding.
Replay reuse additionally authenticates each candidate's actual imported closure from
the environment header, including resolved artifact ownership. Missing, IR-only, cyclic
or private/external closure takes ordinary fresh replay. This prevents an unchanged Lake
artifact from reusing a proof checked against an earlier private import. An explicit
private search path also must preserve the trusted project/standard library directories
and root companions; an alias to the main extractor `.olean` alone cannot authorize a
different sibling IR file or helper library.
The project scan measured 0.596 seconds on this checkout; it runs per audit/batch, never
per theorem. The commands pass no explicit module setup or plugin arguments, so arbitrary
plugins/dynlibs are outside this invocation's supported input surface. Existing loader
overlay rejection and the separately bound pinned runtime remain in force.

A Linux baseline completed the shipped audit (24,120 declarations), then failed closed
because `.lake/build/lib/lean/tests` would shadow the standalone audit's private modules.
The generic fix preserves those foreign cache artifacts: a read-only view exposes only
the configured, assurance-owned Lake library roots, and one explicit search path is
applied after Lake's environment setup to compilation, extraction, artifact lookup and
replay. A module must resolve to its fresh private output; missing output, stale companions
and a different resolved artifact are rejected. The real regression compiles an opposing
shared/private definition, checks a private client, extracts and replays it, verifies the
actual module path, preserves the shared artifact and rejects missing private output.
The cache regression changes an external definition while retaining the Lake artifact
and Lake-library key, then requires ordinary kernel replay to reject the earlier proof.
Failed stages now include a bounded child-log tail in the outer premise diagnostic.

Regressions mutate a shared library while keeping executable stubs identical, delete a
library, change a symlink target to identical bytes, follow a toolchain-local directory
alias, compare relocation-stable digests, mutate compiled logical inputs while ignoring hash
metadata, reject loader overlays, invalidate the extractor sidecar, reject legacy premise-cache
reports, and catch changes after the last report check but before batch acceptance. Receipt compatibility checks retain
their existing strict revision and artifact validation.

The first retry after introducing shared-library/olean binding failed closed after
1,740.041 seconds of workload (35.738 seconds admission wait), peaking at 5,319,808 KiB.
Extraction covered 24,120 declarations; kernel replay rejected exactly
`ZigLean.Sep.AllocSpec`. Its checker produced no output. The macOS crash report
`leanchecker-2026-10-15-204807.ips` identifies PID 94788, parent audit PID 4610,
`SIGABRT` (signal 6), and an invalid free in `lean::region_reader::~region_reader`,
called from `lean_compacted_region_read` / `readModuleDataPartsOfMod`. This is a
runtime/import failure, not a theorem counterexample or a watchdog limit. The failed
report is retained and cannot produce a precise index. Replay diagnostics now preserve
the subprocess exit code in their existing output field. The IR binding was added after
this failed attempt.

A supported diagnostic recheck copied the complete 36-module project import closure,
verified every copied olean against the failed report, and ran the same pinned checker
arguments on read-only copies under the ordinary global guard. Actual toolchain and
artifact hashes matched before and after; this recheck passed, peaking at 501,872 KiB.
The original crash is therefore not consistently reproduced by that isolated check.
This is diagnostic evidence only: it cannot replace complete in-worktree replay/freshness
or authorize a premise drop. Fresh final evidence remains required.
