# Soundness finding: invented bytes of model handles (BUG-2)

Class: SOUNDNESS. Status: fixed (branch `codex/enc-exactness-2`). Found by the encode/decode
exactness audit (`docs/architecture-audit/enc-exactness.md`).

## Finding

The model keeps three std values as handles: `std.mem.Allocator` and `std.Io` (two pointers on
the target: the implementation's state and its `vtable`) and `std.Thread` (a `pthread_t` or a
pointer). The model has none of those addresses. Their `Enc` instances still wrote bytes the
target does not have:

- `Allocator` and `Io`: 16 `Byte.int 0` (`ZigLean/Mem/Alloc.lean`, `ZigLean/Conc/Call.lean`;
  `allocatorEnc` of `ZigLean/Mem/Width.lean` for a 32-bit profile);
- `Thread` (`ThreadId`): the model's thread number as a little-endian `u64`
  (`ZigLean/Mem/Thread.lean`).

Every view of those bytes through another type then proved a value native code does not
produce: `std.mem.asBytes(&allocator)`, a `*const [2]u64` cast of `&allocator`, a cast through
`*anyopaque`, `@memcpy` into an integer. In the other direction, any 16 bytes decoded as an
`Allocator` or `Io` (its decoder ignored them), so integer bytes read through a `*Allocator` gave
a working allocator, where native code calls through whatever `vtable` those bytes hold.

## Counterexample

`examples/lists/lists.zig`:

```zig
pub fn allocatorWord(a: Allocator) u64 {
    var c = a;
    _ = &c;
    return @as(*const [2]u64, @ptrCast(&c))[1];
}
```

The translation stores `a` (`Zig.store (α := Zig.Allocator)`) and loads a `u64` at byte 8.
Before the fix the model returned `0`; native code returns the `vtable` address
(`4372500824` for the differential harness's `TestAllocator` on aarch64-macos, Zig 0.16.0).

## Fix

One byte kind for every value the model keeps as a handle: `Byte.handle (h : ModelHandle) (i : Fin 16)`
(`ZigLean/Mem/Basic.lean`), byte `i` of the handle `h` (`.allocator`, `.io`, `.thread tid`).
`handleBytes h n` encodes, `handleOfBytes n bs` decodes (`ZigLean/Mem/Enc.lean`): it accepts only
the first `n` bytes of one handle, in order, and throws `.unspecified` for anything else. The
`Enc` instances of `Allocator`, `Io`, `ThreadId` and `allocatorEnc w` use them. No other decoder
reads a handle byte (`byteBits`, `Byte.defBits` and the pointer decoders fall through to
`.unspecified`; `exposeBytes` maps only pointer bytes), so:

- an `Allocator`, `Io` or `Thread` reads back as itself (`LawfulEnc` instances in
  `ZigLean/Conc/Own.lean` and `ZigLean/Conc/Lemmas.lean`; `handleOfBytes_handleBytes`);
- its bytes read as any other type are `.unspecified`: the model never proves a value for them;
- bytes that are not one handle's own (integers, another handle, a pointer) read as a handle are
  `.unspecified`: no invented allocator, `Io` or thread.

This replaces the earlier fail-closed attempt (a translator check rejecting pointer casts of these
types), which a cast through `*anyopaque` or `@ptrFromInt` bypassed. The decoder rule covers every
path to the bytes, including those.

Proofs: a load of `io` now needs its bytes, so the concurrency proofs that read `io`
(`Proofs/Iogroup/Counter.lean`, `Proofs/Sync/{Mutex,Handoff,SemCounter,RwLock}.lean`) carry
`blk.bytes.extract 0 16 = Enc.encode (⟨⟩ : Io)` in their block invariant (`BlkOk`), kept by every
step that leaves those cells alone (`Mem.extract_of_heap_eq`). `Proofs/Threads/Counter.lean` reads
its thread handles back through `LawfulEnc ThreadId` (no `< 2^64` premise any more).

## Regression

- `tests/review/Memory.lean` (`handleTests`, `scripts/review.sh`): each handle reads back; its
  bytes read as a `u64` are `.unspecified`; zero or integer bytes read as a handle are
  `.unspecified`; an `Allocator`'s bytes read as an `Io` are `.unspecified`.
- Native differential (`scripts/diff.sh`, example `lists`): `allocatorWord` runs natively (the
  harness's allocator) and in the model; the model's `.unspecified` is pinned in
  `tests/diff/lists/unspecified.txt`, so a model that reads a value again fails the run.
