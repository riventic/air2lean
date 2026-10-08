# Restricted RwLock contract client and reusable sync contracts

The public `Proofs/Sync/RwLock.lean` already proves `rwLockRead_spec` (successful results
2, 12 or 22) and `rwLockRead_safe` (no scheduler error for every fuel and oracle).
These are partial correctness and strict safety statements, not fairness or termination.
The roadmap's former missing-proof assessment is stale. C14 remains partial: the reusable
Mutex/Semaphore/Condition contracts and two independent clients are below
([Reusable synchronization contracts](#reusable-synchronization-contracts)); a general
RwLock contract and Event/WaitGroup contracts are not complete.

`RwLockContract.lean` is a locally kernel-checked adapter to the existing shared-lock proofs.
It retains reader 0, writer 1, the fixed Zig 0.16 `std.Io` layout, count at most 2, concrete
`Sync.Tgt`, and the full semaphore/protocol premises. `ProtectedFacts` parameterizes facts
entailed by the owned counter assertion. It does not generalize the protected heap or prove
multiple readers/writers. Release aliases the original proof; no primitive proof is copied.
Generic Mutex and Semaphore contracts already have independent clients.

`rwLockSnapshotPair` is a restricted source client. It reuses the existing writer,
holds one shared acquisition across two loads, releases, joins, and returns their decimal
pair. Expected successful results are 0, 11 or 22. No C14 AIR/Gen/golden fixture was
handwritten. The accepted Weak CAS prefix supplies its existing generated fixtures and
primitive proofs unchanged. ROOT has now exported and translated the new source client.
The checked-in Gen candidate is an unchanged copy of that actual output, including its
profile header; all preexisting generated bodies and dispatch targets are byte-identical
to the accepted prefix. The snapshot result lemma is arithmetic. The local fragment has an
owned two-load WP contract, derived from the existing protected-load proof, plus a generic
local separation frame theorem. The joined-phase adapter derives all-child-joined from
the existing protocol shape and proves that freeing the live stack allocation preserves
that obligation. It intentionally does not retain the live-block invariant after free.
The client module's WP and all-fuel/all-oracle result/strict-safety theorems have passed
local kernel checking against the actual generated body. Their scope is the restricted
protocol above. The retained targeted Linux Zig 0.16.0 Sync pipeline passed fresh
AIR/golden and translation checks, 20 snapshot native/model matches (100 Sync matches
total), and the complete `Proofs` umbrella, with no fail matches, exclusions, caps or
mismatches. This is bounded evidence on the earlier feature prefix; the current
Outcome/public composition and final CI remain pending. Compiler optimization may
change the load shape; the proof must use
the actual export rather than assume that two source reads survive as two AIR loads.

The checked client proof retains the following boundaries; broader extensions remain partial:

- Acquisition yields the counter resource and clock transfer through the complete invariant.
  Both observations remain under the same hold; release transfers the resource back through
  the state word or semaphore. Pure snapshot facts cannot justify resource transfer.
- A disjoint caller frame/sentinel needs an explicit frame invariant and preservation proof.
  The present adapter does not establish a new sentinel heap assertion.
- Join the writer before stack reclamation; shared unlock or a successful snapshot alone is
  not a lifetime/quiescence witness. Preserve the original allocation and release-clock facts.
- Keep sole-waiter, permit/no-overflow, wake-witness and fixed-thread premises. No broadcast,
  timeout, cancellation, reuse-generation or arbitrary reader pool behavior follows.

The ordinary `Proofs.Sync.Proofs` umbrella imports the kit and client. The adapter and
client WP/result/strict-safety theorems have passed ROOT's kernel check. The direct counter
race negative also passes the kernel. The finite looped client/sentinel/missing-join
fixtures execute as ordinary runtime assertions after the existing proof build, since
`Zig.loop`'s `partial_fixpoint` is opaque to definitional kernel reduction. These runtime
assertions have passed locally: they strictly require complete success or the intended
lifetime error. Model negatives are not exported source artifacts.
The existing native/Lean differential Sync roster now includes the new client and 20
empty-argument inputs; its Linux AIR golden is ROOT's exact unmodified new function dump.

Completed local checks and remaining validation:

1. ROOT export/translation, the original proof module, the restricted adapter, new
   WP/result/safety theorems and umbrella have passed locally. All original generated
   bodies and dispatch targets remain byte-identical on that retained feature prefix.
   The targeted Linux Zig 0.16.0 Sync golden/native/model pipeline passed as recorded
   above; the current composed-source gate and final CI remain pending.
2. Both scheduler theorems cover every fuel/oracle. The finite compiled client witness
   additionally completes with an allowed 0/11/22 value, joined tasks and a freed Shared
   allocation. Additional schedule witnesses do not replace these theorems.
3. The compiled production-client caller preserves sentinel 73 and reclaims both allocations.
   This is a finite witness; a general all-oracle caller-frame invariant remains separate.
   The direct counter read without the acquire/join clock edge is kernel-rejected by the
   actual footprint checker with `.illegal`.
4. Split the reads with an unlock/relock and exhibit a valid writer interleaving yielding
   unequal observations; this demonstrates why same-snapshot equality requires one hold.
5. The modeled missing-join client, using the actual writer and lock calls, is rejected
   by the scheduler lifetime guard with `.illegal`. A successful snapshot/unlock is not
   substituted for the proof's joined-phase reclamation premise.

An arbitrary protected-resource kit requires refactoring `U.parts`, `Car`, `Res`, `wp_n`
and the shared/exclusive transition lemmas, currently fixed to `NPts` at block 0 + 56.
That larger extraction and generic Event/WaitGroup contracts are separate remaining scopes.

## Reusable synchronization contracts

`Proofs/Sync/Contracts.lean` packages each sync object as a `Prop` structure over its
*operations*, proved once against the translated Zig 0.16.0 std code:

| Contract | Proved once by | Lock invariant / ownership transfer | Scope |
|---|---|---|---|
| `MutexContract lk ul` | `Sync.Contracts.mutex` (`MutexOps.lock_specOn`, `unlock_specOn`) | `lock` moves a heap with `L.R` from the lock to the holder's `held` part; `unlock` moves it back | every protocol with the lock (`Lock.FitsOn`), any resource, any thread count |
| `SemContract S wait post` | `Sync.Contracts.semaphore` (`Sem.wait_spec`, `post_spec`) | `post` moves `h₃` from the caller's part into the free permits' `Res`; `wait` moves `T` out | every protocol with the semaphore (`Sem.Fits`); one condition waiter at a time |
| `CondContract S wait signal` | `Sync.Contracts.condition` (`Sem.condWait_spec`, `signal_spec`) | `wait` gives the mutex's resource back and returns holding a new one; the caller rechecks its predicate | the condition and mutex of an `Io.Semaphore` layout; predicate "permit count is 0"; one waiter |
| `RwContract E …` | `Sync.Contracts.rwLock` (existing `RwLockRead` specs) | shared/exclusive acquire gives `NPts`, release returns it | only the restricted protocol above (reader 0, writer 1, `NPts`) |

A client that takes a contract as a hypothesis receives the operations as abstract
functions, so its proof cannot unfold the std implementation. Two new model clients (written
in Lean, not Zig exports; they call the translated std operations) are proved this way:

- `Proofs/Sync/SnapshotCache.lean`: a writer updates `a += 1; b -= 1` twice under the
  mutex, breaking `a + b = 10` between its stores; `main` reads `a` and `b` under one hold.
  `cache_spec` (result 10) and `cache_safe` quantify over every fuel and every oracle of
  `Sched.run`. The proof uses only `MutexContract` and `Lock.FitsOn`: a thread in the middle
  of an update runs no lock code (`ok`) and holds the mutex, so the holder `main` cannot
  observe it.
- `Proofs/Sync/Mailbox.lean`: a producer owns the message cells from the spawn, writes
  `a = 3`, `b = 4` and `post`s a semaphore with no permit; `main` `wait`s (std's
  condition-variable loop with predicate recheck), reads the message while the producer may
  still run, joins and frees. `mailbox_spec` (result 34) and `mailbox_safe` quantify over
  every fuel and every oracle. The proof uses only `SemContract` and `Sem.Fits`; its
  deadlock-freedom obligation (`Fits.live`) covers the consumer asleep at the condition
  before the post.

`tests/roadmap/sync-contracts/Runtime.lean` executes both clients under five fixed oracles
as compiled finite witnesses (complete runs with 10 / 34, joined threads, freed block).

Not covered, stated: fairness, termination and starvation freedom (every contract is partial
correctness plus strict safety); a reusable RwLock contract for arbitrary readers and
resources; an `Io.Event`/`ResetEvent` kit (the translated `Io_Event_*` code is proved only
inside the fixed `handoff` protocol); WaitGroup (Zig 0.16.0's `examples/sync` has no
translated `WaitGroup`; the 0.15.2 one is a fixed two-task client); broadcast, several
condition waiters, timeouts and cancellation. The two clients are Lean model clients: no Zig
source, AIR golden or native/model differential exists for them.
