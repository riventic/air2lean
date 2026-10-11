# Tutorial: concurrent clients

Use a proof over all thread schedules: two threads increment a shared counter under an
`Io.Mutex` (translated from Zig 0.16.0's std code).

Source ([`examples/sync/sync.zig`](../../examples/sync/sync.zig)):

```zig
fn work(c: *Counter) void {
    for (0..2) |_| {
        c.m.lockUncancelable(c.io);
        defer c.m.unlock(c.io);
        c.n += 1;
    }
}

pub fn mutexCounter(io: Io) !u32 {
    var c: Counter = .{ .io = io };
    const t = try std.Thread.spawn(.{}, work, .{&c});
    work(&c);
    t.join();
    return c.n;
}
```

The translation is `Sync.mutexCounter` in [`Proofs/Sync/Gen.lean`](../../Proofs/Sync/Gen.lean),
run by the interleaving scheduler `Sched.run env dispatch fuel o`, where the oracle `o` picks the
next thread at each sync operation and `env` is the stated environment (here any `env` whose
thread assignment succeeds, `env.spawn = .available`). [`Proofs/Sync/Mutex.lean`](../../Proofs/Sync/Mutex.lean)
proves, for every oracle and fuel, `mutexCounter_spec` (a finished run returns `.ok 4`) and
`mutexCounter_safe` (no run ends in an error: no data race, no deadlock at the futex, no
panic).

## Steps

```sh
lake build Proofs.Sync.Mutex
lake env lean tutorials/concurrent-clients/Main.lean
```

[`Main.lean`](Main.lean) combines the two into `finished_run_returns_four`: every run that the
scheduler finishes succeeds and returns 4. The error case is refuted by `mutexCounter_safe`,
the value fixed by `mutexCounter_spec`.

## Exercise

Prove that no schedule loses an increment, so no finished run returns 3:

```lean
theorem never_three (env : Env) (henv : env.spawn = .available) (σ : Placement) (io : Io) (fuel : Nat)
    (o : Nat → Nat) (m : Mem) :
    (Sched.run env dispatch fuel o (mutexCounter io) (mem0 σ)).run ≠ some (.ok (.ok 3, m))
```

A solution is in [`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) keeps the proof of `finished_run_returns_four` but claims the
result is 3 (a lost update). Lean must reject it:

```sh
lake env lean tutorials/concurrent-clients/Negative.lean   # must fail
```

## Assumptions and remaining obligations

[`docs/premise-index.md`](../../docs/premise-index.md) derives these premises for `Main.lean`
(definitions in [`docs/premises.md`](../../docs/premises.md)):

- [PRF-02](../../docs/premises.md#prf-02): the recorded `abi64-le-v1` profile in the first line
  of `Proofs/Sync/Gen.lean` (x86_64-linux-musl, Zig 0.16.0, ReleaseSafe).
- [THR-01](../../docs/premises.md#thr-01): threads interleave only at sync operations, and the
  result is partial correctness: a run that runs out of `fuel` (`none`) is not covered.
- [THR-02](../../docs/premises.md#thr-02): `Thread.spawn` always succeeds in an `available`
  environment (`henv : env.spawn = .available`).
- [THR-03](../../docs/premises.md#thr-03): the theorems take the run environment `env`; they
  cover `available` environments only (a `fallible` one lets thread assignment fail).
- [ALC-10](../../docs/premises.md#alc-10): the allocator is thread-safe in concurrent code.
- [THR-05](../../docs/premises.md#thr-05): the futex under the mutex is a model.
- [IOM-01](../../docs/premises.md#iom-01): the `std.Io` parameter is the model `Io`, not
  whatever `Io` a caller passes.
- [THR-08](../../docs/premises.md#thr-08): the protocol (rely-guarantee / CSL) proof rules.
- [ORD-01](../../docs/premises.md#ord-01), [ORD-02](../../docs/premises.md#ord-02),
  [ORD-03](../../docs/premises.md#ord-03), [ORD-04](../../docs/premises.md#ord-04): the RC11
  approximation for atomics, no load buffering, `seq_cst` as `acq_rel`, weak CAS failure.
- [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02),
  [SEM-03](../../docs/premises.md#sem-03): value/safety semantics, block memory, partial
  correctness.
- [SEM-07](../../docs/premises.md#sem-07): block addresses are the environment's placement
  (`docs/address-placement.md`); the result holds for every placement.
- [TRU-01](../../docs/premises.md#tru-01), [TRU-02](../../docs/premises.md#tru-02),
  [TRU-03](../../docs/premises.md#tru-03): Lean kernel, translation and native lowering.

Remaining obligations: the result is about the initial memory `mem0 σ` of this program (for every
placement `σ` of its blocks, `docs/address-placement.md`), and it
is not a liveness or fairness guarantee (no theorem says a run finishes). Spawn failure is
excluded by THR-02; see [spawn failure](../../docs/spawn-failure.md) for the fallible policy.
