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
   check and its `module_premises`/`dropped` fields. The initial checked shipped comparison
   dropped OSM-01 from 525 records, SEM-04 from 389, and ORD-05 from 21, with no additions
   to that compiled baseline. The independent inert-error rule correction is not counted
   as one of those carrier reductions.

A subset check is a regression constraint, not a soundness proof. Reviewed carrier
coverage, complete kernel dependencies, actual artifact/source/toolchain freshness and
conservative fallback remain necessary; see [the derivation rules](../premises.md#how-premises-are-derived).
