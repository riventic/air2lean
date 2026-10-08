# Pointer atomics (C09)

An atomic op whose pointee is a single or many pointer (`*T`, `[*]T`, `?*T`) is translated to a
pointer op (`ZigLean/Mem/AtomicPtr.lean`, `ZigLean/Conc/PtrAtomic.lean`):

| AIR | Lean |
|---|---|
| `atomic_load` | `Zig.atomicLoadPtrC (T) ord align p` |
| `atomic_store_*` | `Zig.atomicStorePtrC (α := T) ord align p v` |
| `atomic_rmw` `.Xchg` | `Zig.atomicXchgPtrC (α := T) ord align p v` |
| `cmpxchg_strong` / `cmpxchg_weak` | `Zig.cmpxchgPtrC` / `Zig.cmpxchgWeakPtrC (α := T) succ fail align p expected new` |

`T` is `Zig.Ptr` (`*T`, `[*]T`) or `Option (Zig.Ptr)` (`?*T`). The RC11 rules are those of the
integer ops: the same preparation, oracle options, clocks and race checks, at an 8-byte atomic
location.

**Provenance.** A message holds the pointer's own bytes (`Enc.encode`: eight `Byte.ptrFrag`
bytes, or eight zero bytes for `null`). A load decodes them, so the pointer that one thread
publishes is read back by another thread with its block and offset, and an access through it
reaches that block (or fails if the block is dead). Bytes that are not one whole pointer
(integer bytes, `undefined`) throw `.unspecified`, as for a plain pointer load.

**Compare** (`Zig.ptrValEq`). `cmpxchg` compares pointer identities, not bare integers:

| `expected` against the pointer read | result |
|---|---|
| same block and offset | equal: the CAS can succeed |
| different identity, different address | not equal: the CAS fails and returns the pointer read |
| different identity, same address (a pointer past its block that reaches another block, an address without a block, `null` against a pointer at address 0), or an address the memory cannot resolve | `.unspecified` |

The hardware compares addresses. For the last row the model claims neither the success nor the
failure, so a proof cannot rely on either; it must exclude the case (strict mode) or accept an
error result. Two pointers to different blocks therefore never compare equal (`ptrValEq_ne`,
`ptrValEq_blocks`), and a successful pointer CAS read `expected` itself
(`Conc.Proto.cmpxchgPtrAt_success`, `cmpxchgWeakPtrAt_success`). Block addresses are never
reused in the model (`Mem.nextAddr` only grows), so the case needs out-of-bounds arithmetic or
an integer-made pointer.

**Other atomic formats.** Only `.Xchg` is an RMW on a pointer (Zig's rule). A `usize` from
`@intFromPtr` stays an integer atomic: its compare is the integer compare. The checker rejects,
each with its reason: float atomics (no float atomic messages; float RMW arithmetic and the
bitwise compare of a float `cmpxchg` are not qualified), slice pointees, and C or allowzero
pointer pointees (their address-zero encoding is not qualified in memory).

## Evidence

- `Proofs/Atomics/PtrPublish.lean`: a publish/read example over all schedules. Thread A
  allocates a node, writes 42 and release-stores its pointer to an atomic `?*u32`; `main`
  acquire-loads it and reads the node through it, joins A, loads the slot again and destroys the
  node. `publishRead_spec`: every completed run returns 0 or 42 (visibility). `publishRead_safe`:
  no run gives an error — no race, no access to a dead block, no invalid or double free, no
  undecodable pointer (lifetime under join-before-free: after the join, `main` owns the node,
  and the load after the join reads A's message because the join orders it before `main`). The
  program is written in the shape of generated code with the pointer ops; it is a model-level
  example, not an exported AIR file.
- `tests/roadmap/pointer-atomics/Generate.lean`: offline AIR fixtures for load, store, `.Xchg`,
  strong and weak `cmpxchg` on `*u32` and `?*u32`, checked and emitted by the translator; the
  generated file's kernel-checked runs show that a load keeps the block, that a CAS with the same
  identity succeeds and one with another block fails, and that a pointer one past another node
  (same address) or a raw address is `.unspecified`, never a success. The same file checks the
  rejections of float, slice, C and allowzero pointees and of a non-`Xchg` pointer RMW.

Run (serialized build lane):

```sh
lake build ZigLean ZigLean.Conc.PtrAtomicLemmas air2lean
lake env lean Proofs/Atomics/PtrPublish.lean
lake env lean --run tests/roadmap/pointer-atomics/Generate.lean "$out"
lake env lean "$out/PtrAtomics.lean"
```

## Limits

No compiler export of a Zig pointer-atomic program is qualified here (no patched-compiler run);
the native behavior of the same-address case is the hardware compare, which the model leaves
`.unspecified`. Pointer atomics share every RC11 limit of ORD-01 to ORD-04 (no SC order, no
read-view transfer, weak CAS safety only).
