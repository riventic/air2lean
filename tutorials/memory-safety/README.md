# Proving memory safety: no use after free, no double free, no leak

This tutorial proves three memory-safety properties of translated Zig, end to end, for every
allocation-failure pattern:

1. **no use after free, no double free, no invalid free**: the run never throws `.illegal`;
2. **no leak**: after the run, the live heap is exactly the live heap before it, on success
   and on every out-of-memory path;
3. **functional result**: on success the list holds the pushed items, in order.

It also checks three wrong clients. Each one breaks one of the properties, so the properties
are not vacuous.

## Steps

```sh
lake build Proofs.Lists.Sep
lake env lean tutorials/memory-safety/Main.lean       # the client and its three properties
lake env lean tutorials/memory-safety/Controls.lean   # double free, use after free, leak refuted
lake env lean tutorials/memory-safety/Solution.lean   # the exercise, solved
lake env lean tutorials/memory-safety/Negative.lean   # must fail
```

Lean exits with no output when every proof of `Main.lean`, `Controls.lean` and `Solution.lean`
checks. No file uses `sorry` or `native_decide`. `#print axioms` on the theorems lists only
`propext`, `Classical.choice` and `Quot.sound`. `python3 scripts/tutorials.py check` runs the
`Main`, `Solution` and `Negative` checks with the other tutorials.

## Exercise

Prove that reversing a list with the generated `reverse` and then freeing it with the
generated `freeAll` leaks nothing: from a memory whose heap is the list plus a disjoint rest
`hR`, the run returns and the heap after it is `hR`.

```lean
def reverseThenFree (a : Allocator) (hd : Option Ptr) : MemM Unit :=
  reverse hd >>= fun r => freeAll a r

theorem reverseThenFree_no_leak (a : Allocator) (hd : Option Ptr) (xs : List (BitVec 32))
    (m : Mem) (hL hR : Heap) (hs : m.Seq) (hdj : Heap.Disjoint hL hR) (hm : m.heap = hL ∪ hR)
    (hl : list hd xs hL) :
    ∃ m', (reverseThenFree a hd).run m = pure ((), m') ∧ m'.heap = hR
```

Hint: compose `reverse_total` and `freeAll_total` with `TotalTriple.bind`. A solution is in
[`Solution.lean`](Solution.lean).

## Negative control

[`Negative.lean`](Negative.lean) claims that a client that pushes a node and never frees it
ends owning no bytes (`TotalTriple emp (forgetFree a v) (fun _ => emp)`). On success,
`push_total`'s post-condition owns the new node, so Lean must reject the proof with a type
mismatch (`python3 scripts/tutorials.py check` requires that error in the last theorem).

## The code

[`examples/lists/lists.zig`](../../examples/lists/lists.zig) is translated to
[`Proofs/Lists/Gen.lean`](../../Proofs/Lists/Gen.lean). The tutorial uses four of its generated
functions unchanged: `push` (`a.create(Node)`, then two stores), `reverse`, `freeAll` (a loop of
`a.destroy(n)`) and `sum`. [`Proofs/Lists/Sep.lean`](../../Proofs/Lists/Sep.lean) proves one
separation-logic spec per function: `push_total`, `reverse_total` and `freeAll_total`.

[`Main.lean`](Main.lean) composes them in a Lean client, `buildThenFree`, the Lean form of:

```zig
fn buildThenFree(a: Allocator, xs: []const u32) !void {
    var head: ?*Node = null;
    for (xs) |x| head = push(a, head, x) catch |e| { freeAll(a, head); return e; };
    head = reverse(head);
    freeAll(a, head);
}
```

## The theorems

| Theorem | Statement |
|---|---|
| `build_total` | `TotalTriple emp (build a xs) (built xs)`: `build` returns `list hd xs` (the items of `xs`, in order), or `error.OutOfMemory` and owns no bytes |
| `buildThenFree_total` | `TotalTriple emp (buildThenFree a xs) (fun r => ⌜Ended r⌝)`: returns `ok` or `error.OutOfMemory` and owns no bytes after |
| `buildThenFree_memory_safe` | `∀ m, m.Seq → ∃ r m', (buildThenFree a xs).run m = pure (r, m') ∧ Ended r ∧ m'.heap = m.heap` |
| `buildThenFree_no_illegal` | `m.Seq → (buildThenFree a xs).run m ≠ throw e`, for every `e`, including `.illegal` |
| `buildThenFree_no_leak` | `m.Seq → (buildThenFree a xs).run m = pure (r, m') → m'.heap = m.heap` |
| `buildThenFree_every_policy` | the same from `{ m with failAt := k, allocPolicy := pol }`, for every `k` and `pol` |
| `buildThenFree_address_reuse` | the same from `m.withReuse pick pm`: the allocator may give a freed node's address to a later node, for every reuse oracle `pick` and provenance mode `pm` |

[`Controls.lean`](Controls.lean) holds the refuted clients; Lean accepts it. `Room m` says that the next 16-byte
allocation succeeds under `m`'s policy. `SafeNoLeak c` is the property of
`buildThenFree_memory_safe`.

| Client (Zig form) | Theorem |
|---|---|
| `doubleFree`: `freeAll(a, n); a.destroy(n);` | `doubleFree_illegal`: `m.Seq → Room m → run m = throw .illegal`; `doubleFree_unsafe`: `¬SafeNoLeak (doubleFree a v)` |
| `useAfterFree`: `freeAll(a, n); return sum(n);` | `useAfterFree_illegal`: `m.Seq → Room m → run m = throw .illegal`; `useAfterFree_unsafe`: `¬SafeNoLeak (useAfterFree a v)` |
| the first two under address reuse | `doubleFree_reuse`, `useAfterFree_reuse`: `run (m.withReuse pick pm) = throw .illegal` for every `pick` and `pm` |
| `forgetFree`: `_ = try push(a, null, v);` | `forgetFree_leaks`: `m.Seq → Room m → ∃ m', run m = pure (.ok (), m') ∧ m'.heap ≠ m.heap`; `forgetFree_unsafe`: `¬SafeNoLeak (forgetFree a v)` |

## How each property maps to the model

**No use after free, no double free, no invalid free.** The model is described in
[docs/generated-code.md §Memory](../../docs/generated-code.md#memory) and
[docs/std-models.md §Allocator model](../../docs/std-models.md#allocator-model). Memory is a
list of blocks, and `free` marks a block dead. Every load and store goes through
`Mem.access`, which throws `.illegal` on a dead block, out of bounds or misaligned.
`destroy`/`free` (`rawFree`, `ZigLean/Mem/Alloc.lean`) also throw `.illegal` unless the
pointer is the start of a live heap block of exactly the freed length. So a second free, a
free of an inner pointer, a free with the wrong length, or a read or write after free throws
`.illegal`. `buildThenFree_memory_safe` shows that the run is `pure _`. It is therefore no
`throw`, and in particular not `.illegal`. The negative controls show the converse: the same
generated `freeAll`, then the model's `destroy` (what a translated `a.destroy(n)` calls) or the
generated `sum`, throws `.illegal`.

**No leak.** `Mem.heap` is the map of every live byte of every live block. That includes the
caller's heap blocks, globals and stack. The specs are total separation-logic triples
(`TotalTriple`, `ZigLean/Sep/Total.lean`). They start from `emp` and frame the caller's whole
heap. `buildThenFree_total` ends in `⌜Ended r⌝`, which owns no bytes. So
`m'.heap = Heap.empty ∪ m.heap = m.heap`: every block the client allocated is dead again, and
no byte of a block it did not allocate changed. On the out-of-memory path `pushAll` frees
the partial list with the generated `freeAll` before it returns the error. Without that free,
`build_total`'s post-condition for `.error` (`⌜e = "OutOfMemory"⌝`, no bytes) would not hold.
`forgetFree_leaks` shows the converse: one node left live makes `m'.heap ≠ m.heap`.

**Every allocation-failure pattern.** Allocation `k` fails if `Mem.failAt = some k`, if
`k ∈ Mem.allocPolicy.failures`, or if the request is above `Mem.allocPolicy.maxBytes`
(`rawAlloc`). The theorems hold for every `m : Mem` with `m.Seq`, so they hold for every
failure index, every finite failure trace and every cap. That covers a failure of the first
push, of the last push, of any push in between, and no failure.
`buildThenFree_every_policy` states this explicitly.

**Every address-reuse policy.** A real allocator may give a freed node's address to the next
node. The model's opt-in reuse policy (`Mem.allocPolicy.reuseAddr`,
[docs/address-reuse.md](../../docs/address-reuse.md)) does that. The checks above use the
pointer's block id, which is never reused, not its address. So the properties hold under every
reuse policy (`buildThenFree_address_reuse`), and a stale node pointer stays dead even when a
live node has its address (`doubleFree_reuse`, `useAfterFree_reuse`).

**Values.** `list hd xs` (`Proofs/Lists/Sep.lean`) owns the chain of 16-byte nodes from
`hd`, with `val` fields `xs`. `build_total` gives it for the items in order: `pushAll` gives
them reversed, and the generated `reverse` turns them around.

## Assumptions and remaining obligations

The theorems of `Main.lean` hold in the model under the premises of
[docs/premises.md](../../docs/premises.md). The per-theorem list is in
[docs/premise-index.md](../../docs/premise-index.md#tutorialsmemory-safetymainlean)
(`python3 scripts/premises.py explain buildThenFree_memory_safe`):

* [ALC-01](../../docs/premises.md#alc-01): one modelled allocator. Fresh `.heap` blocks;
  a free must name the start and the whole length of a live heap block, or it is `.illegal`.
* [ALC-02](../../docs/premises.md#alc-02): the allocation policy (`failAt`, `allocPolicy`).
  The theorems quantify over it.
* [ALC-08](../../docs/premises.md#alc-08): the opt-in address-reuse policy and provenance mode
  (`buildThenFree_address_reuse`). The theorem quantifies over both.
* [SEM-01](../../docs/premises.md#sem-01), [SEM-02](../../docs/premises.md#sem-02): safety
  checks are `Zig.Error`s, and memory is the byte-level block model. A dead access is
  `.illegal`.
* [SEM-03](../../docs/premises.md#sem-03), [SEM-04](../../docs/premises.md#sem-04): loops are
  `partial_fixpoint`s, and the specs here are total. Each run provably returns.
* [PRF-01](../../docs/premises.md#prf-01): the committed `Gen.lean` uses the legacy 64-bit
  little-endian layout (a `Node` is 16 bytes).
* [THR-01](../../docs/premises.md#thr-01), [ORD-01](../../docs/premises.md#ord-01),
  [ORD-02](../../docs/premises.md#ord-02): derived from the checked pointer formation
  `ptrProject p (·.add k)` (MM-3) in the list proofs: the source derivation resolves `·.add` by
  name and also reaches `Zig.RmwOp.add`. These proofs run on sequential memory and use no
  thread or atomic operation.
* [TRU-01](../../docs/premises.md#tru-01), [TRU-02](../../docs/premises.md#tru-02),
  [TRU-03](../../docs/premises.md#tru-03): the Lean kernel, the Zig exporter and translator, and
  the backend and native execution are trusted.

The hypothesis `m.Seq` (`ZigLean/Sep/Heap.lean`) says that one thread runs and that every live
block lies below `nextAddr`. The empty memory `{}` satisfies it (`default_seq`), and every
single-threaded memory operation the specs use preserves it.

## Limits

* **The client is Lean, not translated Zig.** `pushAll`, `build` and `buildThenFree` are
  handwritten Lean that calls generated functions. `push`, `reverse`, `freeAll` and `sum` are
  translated Zig, and so are their loops and allocator calls. `lists.zig`'s own build-then-free
  function, `listSum` (with `defer freeAll`), is not proved here. Its `sum` can overflow a `u64`
  for long inputs, so a spec for it needs a bound on the input.
* **Per function, compositional.** Each generated function has its own spec. The client is
  proved from those specs with the frame rule, not by unfolding the whole program. A property
  of a function is only as strong as its spec: `push_total`, `reverse_total` and
  `freeAll_total` are exact about ownership, so leaks show up.
* **Model, not native allocator.** "No leak" is about `Mem.heap`. It covers every model
  address-reuse policy (ALC-08), not the native allocator's actual addresses, metadata or
  fragmentation (ALC-01). The allocation policy is a
  model parameter. It is not a guarantee about the host's memory (ALC-02).
* **Single-threaded.** `m.Seq` is a hypothesis. Concurrent clients use the schedule-quantified
  proofs of [docs/proofs.md](../../docs/proofs.md#proofs-over-all-schedules).
* **Supported subset and versions.** The proofs are about the committed 0.16.0 translation in
  `Proofs/Lists/Gen.lean`. The 0.15.2 translation of these four functions is identical
  (`tests/golden/0.15.2/lists/Gen.lean`). `lists` is not built for 0.14.1. Only code in the
  [supported subset](../../README.md#scope) translates. A use after free that Zig's
  `ReleaseSafe` does not detect is still `.illegal` here. The proof shows that the run never
  reaches one.
* **Trust base.** The kernel checks the proofs about the generated Lean. The step to compiled
  Zig trusts the exporter, the translator and the `ZigLean` semantics
  ([What a proof covers](../../README.md#what-a-proof-covers)).
