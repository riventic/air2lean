# Restricted RwLock contract client

The public `Proofs/Sync/RwLock.lean` already proves `rwLockRead_spec` (successful results
2, 12 or 22) and `rwLockRead_safe` (no scheduler error for every fuel and oracle).
These are partial correctness and strict safety statements, not fairness or termination.
The roadmap's former missing-proof assessment is stale. C14 remains partial because its
broader reusable RwLock/Condition/Event/WaitGroup contract bundle is not complete.

`RwLockContract.lean` is an unqualified source adapter to the existing shared-lock proofs.
It retains reader 0, writer 1, the fixed Zig 0.16 `std.Io` layout, count at most 2, concrete
`Sync.Tgt`, and the full semaphore/protocol premises. `ProtectedFacts` parameterizes facts
entailed by the owned counter assertion. It does not generalize the protected heap or prove
multiple readers/writers. Release aliases the original proof; no primitive proof is copied.
Generic Mutex and Semaphore contracts already have independent clients.

`rwLockSnapshotPair` is new public source preparation. It reuses the existing writer,
holds one shared acquisition across two loads, releases, joins, and returns their decimal
pair. Expected successful results are 0, 11 or 22. No generated AIR/Gen/golden fixture was
handwritten or changed. The snapshot result lemma is arithmetic. The new local snapshot fragment also has an
owned two-load WP contract, derived from the existing protected-load proof, plus a generic
local separation frame theorem. Neither is the generated-program theorem. A generated-program
WP proof and all-fuel/all-oracle result/safety theorems are still pending ROOT export and
kernel qualification. Compiler optimization may change the load shape; the proof must use
the actual export rather than assume that two source reads survive as two AIR loads.

The remaining client proof must establish the following boundaries:

- Acquisition yields the counter resource and clock transfer through the complete invariant.
  Both observations remain under the same hold; release transfers the resource back through
  the state word or semaphore. Pure snapshot facts cannot justify resource transfer.
- A disjoint caller frame/sentinel needs an explicit frame invariant and preservation proof.
  The present adapter does not establish a new sentinel heap assertion.
- Join the writer before stack reclamation; shared unlock or a successful snapshot alone is
  not a lifetime/quiescence witness. Preserve the original allocation and release-clock facts.
- Keep sole-waiter, permit/no-overflow, wake-witness and fixed-thread premises. No broadcast,
  timeout, cancellation, reuse-generation or arbitrary reader pool behavior follows.

ROOT validation and meaningful negative cases, not yet executed:

1. Export/translate the new function and compare the existing writer/primitive bodies and
   target inventory. Build the actual generated definition and original proof module.
2. Prove both new scheduler theorems for all fuel/oracles. Then check representative reader-
   first, writer-first and contended schedules with exact expected 0/11/22 results; finite
   witnesses do not replace the theorem.
3. Use a protected-frame sentinel and assert its literal value and ownership after release
   and join. Introduce a read outside the hold and require the protected-load/race boundary
   to fail, rather than accepting an unrelated parser/build failure.
4. Split the reads with an unlock/relock and exhibit a valid writer interleaving yielding
   unequal observations; this demonstrates why same-snapshot equality requires one hold.
5. Omit join before reclamation and require the lifetime/last-access obligation to fail.
   Drop acquire/release clock transfer and require the ownership protocol proof to fail.

An arbitrary protected-resource kit requires refactoring `U.parts`, `Car`, `Res`, `wp_n`
and the shared/exclusive transition lemmas, currently fixed to `NPts` at block 0 + 56.
That larger extraction and generic Event/WaitGroup contracts are separate remaining scopes.
