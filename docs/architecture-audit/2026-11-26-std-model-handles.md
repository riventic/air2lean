# Private state of the hand-written std models is readable by the program (2026-11-26)

Class: SOUNDNESS. Status: **open, a maintainer decision** (§Decision). Lane `std-handles`;
found by the probes of PR #886 (`Io.AnyFuture`), confirmed on main `c07988d74` and again on
`26e195789`. No translator or model change is made by the PR that adds this note.

## The fact

A hand-written std model (`docs/std-models.md` §Retiring the hand models) replaces std code that
writes into an object the program owns. The model does not make those writes, or makes other
ones:

- `Io.Group.async`/`concurrent`/`await`/`cancel` (STD-08; 0.16.0, 0.17.1): the model keeps the
  group's tasks in `Mem.groups`, keyed by the group's address (`Thread.groupAdd`, `groupTake`;
  `ZigLean/Conc/Call.lean`). It never writes the group. Natively `Io.Threaded` stores its record
  in `token: std.atomic.Value(?*anyopaque)` and uses `state: usize`.
- `Thread.Mutex.DarwinImpl.lock`/`unlock`/`tryLock` (STD-06; 0.14.1, 0.15.2, macOS): the model's
  lock word is 0 or 1 (`Zig.osUnfairLockC`). Natively `os_unfair_lock` keeps the owner's thread
  port in it.
- `Io.async`/`Io.Future(T).await`/`cancel` (STD-09; 0.16.0): `any_future` points to the model's
  record (`Zig.Future.slotAlloc`), natively to `Io.Threaded`'s.

The object is an ordinary struct in the translation (`Io_Group`, `Thread_Mutex_DarwinImpl`) or a
special type with ordinary pointer bytes (`Zig.Future`). So every read of it by the program is
a read of the model's bytes: a definite value in the model that is not the native one.

## Counterexamples

Each program is exported with the patched compilers for x86_64-linux (`Io.Group`,
`Io.Future`) or aarch64-macos (`Thread.Mutex`) in `ReleaseSafe` and translated alone with
`air2lean … --allocator-model {std,translated}`. Native values: stock Zig 0.16.0 and 0.17.1,
`ReleaseSafe`, aarch64-macos, `std.Io.Threaded` (`.init(page_allocator, .{})`), three runs each.

```zig
fn task(out: *u32) void { out.* = 7; }

pub fn hasToken(io: Io) bool {          // accepted, both allocator models, 0.16.0 and 0.17.1
    var out: u32 = 0;
    var g: Io.Group = .init;
    g.async(io, task, .{&out});
    const p = g.token.load(.monotonic) != null;
    g.await(io) catch {};
    return p;
}
```

Model: the store of `.init` is the only write of `g`, so the load reads `none` and the result
is `false` in every environment and schedule. Native: `true` (std's own doc of `token`: "`null`
indicates no pending tasks"; `false` only when the task ran in the caller). The same holds for
`@intFromPtr(g.token.load(.monotonic))` (model 0, native an address) and `g.state` (model 0).

```zig
pub fn peekGroup(io: Io) u64 {          // accepted under --allocator-model translated
    …
    const t = g.token.load(.monotonic);
    const w = @as(*u64, @ptrCast(@alignCast(t.?))).*;
    …
}
```

The cast is the recovery from `*anyopaque` that translated mode admits; std mode rejects it
(cast provenance). In the model the token is null, so `t.?` takes the safety-check panic
branch; natively the function reads the first word of `Io.Threaded`'s group record.

The read needs neither the field nor the type:

```zig
const W = struct { n: u64, g: Io.Group };   // exported offsets: n at 0, g at 8

pub fn sibling(io: Io) u64 {            // accepted, both allocator models, 0.16.0 and 0.17.1
    var out: u32 = 0;
    var w: W = .{ .n = 1, .g = .init };
    w.g.async(io, task, .{&out});
    const p: [*]u64 = @ptrCast(&w.n);
    const s = p[1];
    w.g.await(io) catch {};
    return s;
}

pub fn siblingInt(io: Io) u64 {         // accepted, both allocator models, 0.16.0 and 0.17.1
    …
    const s = @as(*const u64, @ptrFromInt(@intFromPtr(&w.n) + 8)).*;
    …
}
```

`sibling` is translated to `Zig.load (BitVec 64) 8 (p.elem 8 1)`: a load inside the block of
`w`, of the eight zero bytes of a null `?*anyopaque` (`Enc (Option Ptr)`), so the model returns
0. Native: nonzero. `siblingInt`: `Zig.ptrFromAddr` gives the block that covers an address,
whatever the integer came from (`ZigLean/Mem/Basic.lean`); the model has no exposure condition.

`Io.Future` after PR #886, without naming `Io.AnyFuture` (0.16.0, accepted in both models):

```zig
pub fn futRecord(io: Io, x: u32) u64 {
    var f = io.async(square, .{x});
    const a = @as(*const usize, @ptrCast(&f)).*;      // pointer bytes read as an integer (MM-11)
    const w = if (a != 0) @as(*const u64, @ptrFromInt(a + 8)).* else 0;
    _ = f.await(io);
    return w;
}
```

`a` is the address of the model's record; `a + 8` is where the model's task stores its result
(`Future.complete`), natively a field of `Io.Threaded`'s future. `a != 0` alone is the
`pending` counterexample of PR #886 again (natively null when the task ran inline).

## Audit: what the program can do, per model

A = accepted (translated without a diagnostic), R = rejected, per `--allocator-model`
`std` / `translated`. Probed versions are the ones the model's rows are qualified for.

### `Io.Group` (STD-08) — 0.17.1 and 0.16.0, identical results

| Access | Program | std / translated | Model value | Native |
|---|---|---|---|---|
| (b) null test of `token` | `g.token.load(.monotonic) != null` | A / A | `false` | `true` |
| (c) integer of `token` | `@intFromPtr(g.token.load(.monotonic))` | A / A | 0 | an address |
| (a) dereference of `token` | `@as(*u64, @ptrCast(@alignCast(t.?))).*` | R / A | the null-unwrap panic | the record's first word |
| `state: usize` | `g.state` | A / A | 0 | the implementation's word |
| field of a copy | `const g2 = g; … g2.state` | A / A | 0 | as above |
| pointer cast of the group | `@as(*const [2]usize, @ptrCast(&g))[0]` | R / A | 0 | an address |
| through `*anyopaque` | `const o: *anyopaque = &g; @as(*const usize, @ptrCast(@alignCast(o))).*` | R / A | 0 | an address |
| bytes | `std.mem.asBytes(&g)[0]` | R / A | 0 | a byte of the address |
| through the address | `@as(*const usize, @ptrFromInt(@intFromPtr(&g))).*` | A / A | 0 | an address |
| sibling field, pointer arithmetic | `sibling` above | A / A | 0 | an address |
| sibling field, address | `siblingInt` above | A / A | 0 | an address |

The std-mode rejections are the cast-provenance rule ("a pointer cast has unresolved or cyclic
symbolic storage provenance"), not a rule about the group.

### `Thread.Mutex.DarwinImpl` (STD-06) — 0.15.2 and 0.14.1, aarch64-macos, identical results

| Access | Program | std / translated | Model value | Native |
|---|---|---|---|---|
| (c) the lock word, field | `m.impl.oul._os_unfair_lock_opaque` while held | A / A | 1 | the owner's thread port (not run natively) |
| (c) the lock word, cast | `@as(*const u32, @ptrCast(&m)).*` while held | A / A | 1 | as above |
| sibling field | `struct { n: u32, m: Mutex }`, `[*]u32` from `&b.n` | A / A | 1 | as above |

The Linux `FutexImpl` of the same versions is translated std code: its word is the native one.

### `Io.Future(T)` (STD-09) — 0.16.0 (0.17.1: `Io.async` is not qualified, every use rejected)

| Access | Program | std / translated | Model value | Native |
|---|---|---|---|---|
| (a) (b) `any_future`, typed | `f.any_future.?`, `f.any_future != null` | R / R (PR #886) | | |
| (b) (c) `any_future`, bytes | `@as(*const usize, @ptrCast(&f)).*` | A / A | the address of the model's record | null if inline, else `Io.Threaded`'s record |
| (a) the record | `futRecord` above | A / A | the task's result | a field of the native record |
| sibling field | `struct { n: u64, f: Io.Future(u32) }`, `[*]u64` from `&w.n` | A / A | as the bytes row | as the bytes row |
| `result` before `await` | `f.result` | A / A | undefined bytes: the load fails | undefined |

### `mem.Allocator` (STD-01, std mode), `Io` (STD-05/08/09), `Thread` (STD-02)

These three are the handles of [model-handle-bytes.md](model-handle-bytes.md): their bytes are
`Byte.handle`, and every other view of them is `.unspecified` (never a value), by the decoder,
on every path. Probed on 0.17.1, 0.16.0, 0.15.2, 0.14.1 (`Io`: 0.16.0, 0.17.1):

| Access | Program | std / translated | Outcome |
|---|---|---|---|
| bytes | `@as(*const [2]usize, @ptrCast(&c))[1]` (`Allocator`, `Io`), `@as(*const usize, @ptrCast(&t)).*` (`Thread`) | A / A | `.unspecified` at run time: sound |
| field of `Allocator` (std mode), `Io` | `a.ptr`, `a.vtable`, `io.userdata`, `io.vtable` | A / A | the checker accepts; the emitted `(p0).1` does not compile in Lean (`Invalid projection`): fail-late, not a wrong value. In translated mode `mem.Allocator` is the ordinary struct with its native fields. |
| `Thread.getHandle()` | | R / R | no AIR and no model |

No row here is a wrong value. The fail-late row should be a checker diagnostic (§Follow-ups).

## Why a checker rule does not close it

The lane's task was one fail-closed checker rule. Three were evaluated; each has a
counterexample above that it still accepts.

| Option | Rule | Still accepted |
|---|---|---|
| A | The registry declares per model which fields are public; the checker rejects an access to any other field of a hand-modelled std type. | `sibling`, `siblingInt`, the address round trip, and in translated mode the pointer cast, `*anyopaque` and `asBytes` rows: none of them names a field. Also needs a registry schema change. |
| B | Taint: a pointer loaded from model-owned storage is model-private; its recovery, dereference and integer cast are rejected. | `hasToken` and `g.state` (no pointer is used), and every byte view (`sibling` reads the pointer's bytes as an integer; nothing is "loaded as a pointer"). |
| C | Reject every use of a field of a hand-modelled type in a translated function. A variant derives the types without a list: the receiver type of a hand-model row (`Io.Group.async` → `Io.Group`), which is also what `mem.Allocator`, `Thread`, `Io` and `Io.Future` are. | As A. Extending C to casts and `@intFromPtr` of a pointer whose pointee holds such a type closes the cast rows but not `sibling`/`siblingInt`: `&w.n` is a `*u64`. |
| D | C, and the type may only be a whole stack or global object, never a field (no sibling exists). | Rejects `struct { m: Thread.Mutex, n: u32 }` and every user struct with an `Io.Group`: committed fixtures (`threadsync` on macOS) stop translating. And `@ptrFromInt` of a computed address still reaches the block (`ptrFromAddr` needs no exposure). |

The cause is the memory model, not the checker: a pointer may move anywhere inside its block,
and an integer address reaches any block. A static rule over types cannot see which bytes a
`[*]u64` reaches. This is the conclusion [model-handle-bytes.md](model-handle-bytes.md) reached
for `Allocator`, `Io` and `Thread` ("the earlier fail-closed attempt (a translator check
rejecting pointer casts of these types), which a cast through `*anyopaque` or `@ptrFromInt`
bypassed"); PR #886's rule for std-declared opaque types has the same gap (`futRecord`).

## Decision

**Recommended: E, the existing handle mechanism for the remaining model-owned objects.** The
bytes that a hand model owns are `Byte.handle` bytes; the decoder makes every other view
`.unspecified` on every path (field, cast, `*anyopaque`, sibling arithmetic, integer round
trip, `@memcpy`), as it does today for `Allocator`, `Io` and `Thread`. Concretely:

1. `Io.Group`: a model handle type like `Io` (a `ModelHandle` constructor, a type
   specialization in `Air2Lean/Air/Json.lean` when its rows are active, `Enc` through
   `handleBytes … 16`, the constant `Io.Group.init` as its value). The group ops stay keyed by
   address. `g.token`/`g.state` then have no field to name.
2. `Io.Future(T)`: its `any_future` word as handle bytes instead of the model record's pointer
   bytes; `result` stays `T`.
3. `Thread.Mutex.DarwinImpl` (0.14.1, 0.15.2, macOS): the fail-closed rejection that is already
   the interim direction for STD-06 (`docs/std-models.md`), or the OSL-01 OS row of decision
   2026-11-24, whose lock word then needs the same treatment (it is the OS's, not the
   program's).
4. One checker diagnostic for a field projection of a model handle type, so that `a.ptr` and
   `g.token` are rejected by the translator and not by the Lean compiler.

Why this needs the maintainer: it changes the representation of a hand model (the lane's rules
forbid extending a hand model's semantics), the generated code of every `Io.Group` client
(`Io_Group` disappears from `Gen.lean`: the goldens and `Proofs/Iogroup`, `Proofs/Cancel`
change) and the block invariants of those proofs (as `BlkOk` did for `io` in BUG-2). It adds no
premise: STD-08/09 stay. It goes with the hand models (§Retiring the hand models): a translated
`Io.Group` has the native token.

Alternatives, if E is not wanted:

- **C′, the derived static rule as an interim** (receiver types of hand-model rows; no field
  projection, no cast or `@intFromPtr` of a pointer whose pointee holds one). It closes every
  typed row of the tables and leaves `sibling`/`siblingInt`. It is a transitional rule that E
  deletes, so by CLAUDE.md it needs a recorded deletion plan; it does not make a theorem about
  an `Io.Group` client sound against an adversarial program.
- **Reject the modelled API** where its object is program-visible (`Io.Group`, `Io.async`):
  sound, and deletes the `iogroup`, `cancellation` and `futures` fixtures.

## Related finding: a group re-initialized with pending tasks

Found while probing; not a read of private state, so E does not fix it.

```zig
fn slow(out: *u32) void { …busy loop…; @atomicStore(u32, out, 7, .seq_cst); }

pub fn reinit(io: Io) u32 {             // accepted, both allocator models, 0.16.0 and 0.17.1
    var out: u32 = 0;
    var g: Io.Group = .init;
    g.async(io, slow, .{&out});
    g = .init;
    g.await(io) catch {};
    return @atomicLoad(u32, &out, .seq_cst);
}
```

Model: the tasks stay under the group's address, `await` joins them, the result is 7 and no
run has an error. Native (0.16.0 and 0.17.1): `await` returns at once (the token is null), the
function returns 0, and the orphaned worker then fails std's assertion (`Io/Threaded.zig:1797`,
`:1845` in 0.17.1: `reached unreachable code`), in some runs before the result is printed. So
the model proves a result and safety that the native run does not have. The store of `.init`
is the same instruction as the initialization, so no rule over types separates them; the model
would have to treat a store over a group with pending tasks as `.illegal`. A copy
(`var g2 = g; g2.await(io)`) goes the other way: the model joins nothing and the later plain
read of `out` races (`.illegal`), where native code joins, which is conservative.

## Follow-ups (probed, not changed)

- **No unguarded `!` access on untrusted AIR in `Air2Lean/Check.lean`.** The 24 lines with
  `get!`, `[k]!` or `head!` were read: each follows a size comparison, a `some (.ptr ..)` match
  or a non-empty test on the same value (`memAccess`/`fieldPtr` after `memPtrTy`,
  `checkCallSignatureWith` and `checkCallSignatureCached` after the argument count, the offset
  scans after `offsets.size != fields.size`, `checkFallibleSpawnCall` after `names.size == 2`,
  `indexes[fileIndex]!` over the array built in the same loop order).
- **`?*T → *U` emits no alignment check** (`Air2Lean/Emit.lean`, the `srcOptPtr && dstPtr` arm:
  `Zig.optPtrUnwrap`; the `*T → *U` arm below emits `Zig.checkAlign`). Probe:
  `pub fn optBytes(o: ?*u8) *u64 { return @ptrCast(@alignCast(o)); }`, 0.17.1 and 0.16.0. In
  `ReleaseSafe` the AIR tests the address itself before the cast, so nothing is missing. In
  `ReleaseFast` (only with `--allow-unqualified-build-mode`) the translation is
  `Zig.optPtrUnwrap p0` alone: a misaligned operand is undefined natively and no error in the
  model until the pointer is used. Fix: the same `checkAlign` after the unwrap when the target
  alignment is larger; it changes no qualified output, but it is an emitter change with its own
  golden check.
- **Hand-made `[]u8 → *anyopaque` and `*anyopaque → []u8` `ptr_cast`s pass the checker** (the
  first in both allocator models, the second in translated mode) and are emitted as
  `pure (p0)`, which the Lean compiler rejects (`Application type mismatch`). Zig rejects both
  casts, so only hand-made AIR has them. They should be a checker diagnostic, with the
  field-projection diagnostic of §Decision item 4 (the same class: accepted, then a Lean error).

## Evidence

Probe sources, exports, translations and logs: `~/.cache/air2lean/scratch/std-handles/`
(`src/*.zig`, `probe.sh`, `probe-*-main.log`, `native/n.zig`). Translator: main `26e195789`.
Not run: a kernel evaluation of the model on the counterexamples (the model values above follow
from the cited definitions), and the native `os_unfair_lock` word.
