# Tutorial: cross-target verification

Check that one proof about `Thread.Mutex.lock` holds for the translation of both targets, and see
what does not transfer.

## What a proof is about

Every generated module states the target it models. A schema-12 translation starts with a
`-- air2lean-profile:` line that records the target triple, CPU and features, build mode, Zig
version, backend and error-set width of the analyzed AIR ([profiles](../../docs/profiles.md)).
For example the first line of [`Proofs/Sync/Gen.lean`](../../Proofs/Sync/Gen.lean) records
`x86_64-linux-musl`, Zig 0.16.0, ReleaseSafe. A theorem over that module carries premise
[PRF-02](../../docs/premises.md#prf-02): it is about exactly that profile. A module without the
line, such as the committed `Threadsync/Gen.lean` used below, uses the legacy reference model,
[PRF-01](../../docs/premises.md#prf-01) (64-bit, little-endian). See which premise a theorem has with
`python3 scripts/premises.py explain <theorem>`.

## The two targets

In Zig 0.15.2 `Thread.Mutex` is `FutexImpl` on Linux and `os_unfair_lock` on macOS, so the
translated `Thread_Mutex_lock` is a different function. The Linux translation is the committed
[`Proofs/Threadsync/Gen.lean`](../../Proofs/Threadsync/Gen.lean); the macOS translation is the
golden `tests/golden/0.15.2/threadsync/Gen-darwin.lean`, which CI copies over `Gen.lean` and
rebuilds natively on aarch64-macos. [`Proofs/Threadsync/Lock.lean`](../../Proofs/Threadsync/Lock.lean)
proves `lock_spec` and `unlock_spec` for whichever translation is present. Its only
target-specific input is `Threadsync.mutexC`, the contended value of the mutex word: 3 on Linux
(`FutexImpl`), 1 on macOS. A client proof that states its hypothesis as `L.c = mutexC` and
goes through `lock_spec` therefore compiles against either translation unchanged.

Other qualified evidence per target (not part of this checked proof):

- **Model ABI scopes:** `x86_64-linux-<abi>` and `aarch64-macos-<abi>`, 64-bit little-endian
  only; narrower or big-endian targets are rejected by the translator.
- **Native ABI observations:** `scripts/abi-probe.py` records bounded layout and integer
  observations for x86_64-linux-gnu and aarch64-linux-gnu on the matching CPU
  ([bounded Linux native ABI observations](../../docs/profiles.md#bounded-linux-native-abi-observations)).
  These are evidence for listed layouts, not a proof of correspondence.
- **CI:** three Zig versions on Linux and selected macOS paths
  ([support matrix](../../docs/support-matrix.md)).

## Steps

```sh
lake build Proofs.Threadsync.Lock
lake env lean tutorials/cross-target/Main.lean
```

[`Main.lean`](Main.lean) proves `lock_keeps_current`: after `Thread.Mutex.lock` by thread `t`
the running thread is still `t`. It weakens the postcondition of `lock_spec` and never names the
contended value, so the same file is the proof for both targets.

To run it against macOS, copy the golden over the generated module and rebuild, then restore
the file. The CI step "Build threadsync proofs (macOS translation)" does exactly this on the
0.15.2 job (with a trap that restores `Gen.lean` on failure) and also elaborates `Main.lean` and
`Solution.lean` against it:

```sh
cp tests/golden/0.15.2/threadsync/Gen-darwin.lean Proofs/Threadsync/Gen.lean
lake build Proofs.Threadsync.Lock
lake env lean tutorials/cross-target/Main.lean
lake env lean tutorials/cross-target/Solution.lean
lake env lean tutorials/cross-target/NegativeMacos.lean   # must fail
git checkout Proofs/Threadsync/Gen.lean
```

For a new target: export AIR with the patched Zig (`-target ...`), translate it
([getting started](../../docs/getting-started.md)), check that the profile line names the target,
re-run `scripts/check.sh` against the goldens and check that every theorem you rely on lists the
expected profile premise.

## Exercise

Prove the same for `Thread.Mutex.unlock` by the holder:

```lean
theorem unlock_keeps_current (hP : L.Fits P U) (hc : L.c = mutexC) {p : Ptr} (hp : p = L.ptr)
    (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_unlock p) (fun _ _ m' _ => m'.current = t) G m d
```

A solution is in [`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) states the hypothesis with the macOS value (`L.c = 1`) against
the committed Linux translation, whose `mutexC` is 3. Lean must reject it with an application
type mismatch: a lock proof does not move between targets by editing the constant.
[`NegativeMacos.lean`](NegativeMacos.lean) is the mirror image for the macOS translation (the
Linux constant 3 must fail there); only the CI macOS step runs it, because it elaborates on the
Linux translation.

```sh
lake env lean tutorials/cross-target/Negative.lean   # must fail
```

## Assumptions and remaining obligations

[`docs/premise-index.md`](../../docs/premise-index.md) derives these premises for `Main.lean`
(definitions in [`docs/premises.md`](../../docs/premises.md)):

- [PRF-01](../../docs/premises.md#prf-01): the committed `Threadsync/Gen.lean` has no profile
  header, so the proof is about the legacy 64-bit little-endian reference model. A schema-12
  translation of another target names its triple in the header and gives the recorded-profile
  premise instead.
- [THR-01](../../docs/premises.md#thr-01), [THR-05](../../docs/premises.md#thr-05),
  [THR-08](../../docs/premises.md#thr-08): the interleaving scheduler, the futex model and the
  protocol rules `lock_spec` is built on.
- [ORD-01](../../docs/premises.md#ord-01), [ORD-02](../../docs/premises.md#ord-02),
  [ORD-04](../../docs/premises.md#ord-04): the RC11 approximation, no load buffering and weak
  CAS failure for the atomics of the lock.
- [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02),
  [SEM-03](../../docs/premises.md#sem-03): value/safety semantics, block memory, partial
  correctness.
- [SEM-07](../../docs/premises.md#sem-07): block addresses are the environment's placement
  (`docs/address-placement.md`); the result holds for every placement.
- [TRU-01](../../docs/premises.md#tru-01), [TRU-02](../../docs/premises.md#tru-02),
  [TRU-03](../../docs/premises.md#tru-03): Lean kernel, translation and native lowering for the
  target.

Remaining obligations: the clean container runs the Linux translation only; the macOS
translation is checked by the CI golden-swap step, not in a macOS clean container. Each proof is about one recorded profile, and nothing transfers a proof between
profiles. WASM, 32-bit and big-endian targets are not modelled, and there is no cross-target
proof run in the clean container (Q05).
