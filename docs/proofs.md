# Proofs about memory

A function that uses memory (`docs/generated-code.md` §Memory) returns `Zig.MemM α`. `ZigLean/Sep/` is a separation logic for such functions. Import `ZigLean.Sep`; the generated code does not import it.

## Model

| Name | What |
|---|---|
| `Heap` | a partial map from a location (block, byte offset) to a `Cell`: the byte, and the address, size and kind of its block |
| `Mem.heap m` | the heap of all live bytes of `m` |
| `Assn` | `Heap → Prop` |
| `P ∗ Q` | the heap splits into two disjoint parts: `P` holds of one, `Q` of the other |
| `⌜φ⌝` | the fact `φ`, and no bytes |
| `emp` | no bytes |
| `bytesAt p A S K bs` | exactly the bytes `bs` at `p`, in a block with address `A`, size `S` and kind `K` (`.heap` for a block of the allocator) |
| `pts p a v` | `p` points to `v : T` (`Zig.Enc T`); an access with alignment `a` is aligned |
| `arr p vs` | `p` points to the items `vs : List T`, one after the other, the first aligned to `Enc.align T` |

`open Zig Assn` gives the notation `∗` and `⌜φ⌝`.

## Triples

`Triple P c Q`: if `P` holds of a part of the memory, `c` does not throw; if `c` returns `v`, `Q v` holds of that part after it, and the rest of the memory (the frame) is unchanged. A program that does not terminate satisfies every triple (partial correctness).

`Triple` also needs `Mem.SingleThread m` before `c` runs, and gives it back for the result memory. A program that never spawns a thread (`Proofs/Threads/` is the only one that does) gets this for free: `Triple.of_run` and every rule below thread it through, so a proof never states it. `ZigLean/Mem/Lemmas.lean` has the pieces: `singleThread_empty` (true at program start, from an empty footprint), `singleThread_write`/`singleThread_recordAt` (preserved by a write or a recorded access), `noRace_of_singleThread` (turns it into the `NoRace` a `*_run` lemma below needs).

| Rule | Statement |
|---|---|
| `Triple.frame` | `Triple P c Q → Triple (P ∗ R) c (fun v => Q v ∗ R)` |
| `Triple.conseq`, `ret`, `bind`, `ex`, `lift` | the structural rules |
| `Triple.load`, `Triple.store` | `pts p a v` before and after (`0 < Enc.size T`; `store` needs `LawfulEnc T`) |
| `Triple.alloc`, `Triple.free` | a new block with undefined bytes; `free` needs every byte of the block, from offset 0 |
| `Triple.create`, `Triple.destroy` | the allocator (`ZigLean/Sep/Alloc.lean`): `newBlock` is a new `.heap` block or `error.OutOfMemory` and no bytes; `destroy` needs the whole `.heap` block |
| `loop_sep_spec`, `loop_sep_ghost` | a `Zig.loop` with an invariant that is an assertion (below) |

A proof about generated code does not apply the rules one by one. It unfolds the code with `simp [f, zig_unfold, …]` and gives it the result of each memory operation. The `*_run` lemmas give that result, for a heap `h` that owns the bytes, in a memory whose heap is `h ∪ hF`. Unlike `Triple`, a `*_run` lemma is not wrapped: it takes `Mem.SingleThread m` as an explicit hypothesis and returns `Mem.SingleThread m'` as part of its conclusion, so a hand-written proof that calls one directly (`Proofs/Lists/Sep.lean`, `Proofs/Pointers/Proofs.lean`, `Proofs/Slices/Sep.lean`) threads it from one call to the next, starting from `singleThread_empty`.

| Lemma | Operation | After |
|---|---|---|
| `pts_load_run` | `load T a p` | the value, memory unchanged |
| `pts_store_run` | `store a p w` | `pts p a w` in a new `h'`; `hF` unchanged |
| `arr_load_run`, `arr_store_run` | item `i` of `arr p vs` | `vs[i]`; `arr p (vs.set i w)` |
| `arr_memmove_run` | `Zig.memmove` of `n` items from `s` to `d` | `arr p (copyItems vs d s n)`: all bytes read before the first write |
| `arr_memset_run` | `Zig.memset` of all items | `arr p (List.replicate n w)` |
| `alloc_run`, `free_run` | `Zig.alloc`, `Zig.free` | a new owned block; the block removed |
| `create_run`, `rawFree_run` | `Allocator.create`, `Zig.rawFree` | `newBlock`; the `.heap` block removed |

## A spec

```lean
theorem swap_sep (p q : Ptr) (x y : BitVec 32) :
    Triple (pts p 4 x ∗ pts q 4 y) (swap p q) (fun _ => pts p 4 y ∗ pts q 4 x) := by
  apply Triple.of_run
  rintro m _ hF hd hm ⟨h₁, h₂, h₁₂, rfl, hp, hq⟩
  -- `p` with the frame `h₂ ∪ hF`, `q` with the frame `h₁ ∪ hF`
  ...
  simp [swap, zig_unfold, lx, ly, s₁, s₂]
```

`Triple.of_run` turns the goal into: for a memory `m` with `m.heap = hP ∪ hF` and `P hP`, find the result, the memory after, and the new owned heap. To read `p` in `pts p 4 x ∗ pts q 4 y`, use the frame `h₂ ∪ hF` (`Heap.union_assoc`, `Heap.union_left_comm`).

Literals: after `simp`, a constant is `1#32`, not `(1 : BitVec 32)`, and `(a + b).toNat` is `(a.toNat + b.toNat) % 2 ^ w` with the power as a number. State the facts that `simp` needs in that form (`Proofs/Slices/Sep.lean`, `copyWithin_spec`).

## A loop

`loop_sep_spec body again I meas post hF` needs, for each iteration from a heap `h` with `I s h`: the run of the body, the new heap `h'` (with the same frame `hF`), and either `I s' h'` and a smaller `meas s'` (the loop repeats), or `post e s' h'` (it exits). The invariant `I` is on the locals `s` and the owned heap. Like a `*_run` lemma, `loop_sep_spec` is not wrapped by `Triple`: each iteration takes and returns `Mem.SingleThread`, so a call site threads it the same way.

`reverse` (`Proofs/Slices/Sep.lean`): the invariant `revInv` says that the items before `i` and after `j` are swapped and the others are unchanged; `revMeas s = j + 1 - i`. `reverse_step` proves one iteration; `reverse_spec` starts the loop with `i = 0`, `j = n - 1`.

A walk over a linked list ends because the rest of the list gets shorter, and the locals do not give that length. `loop_sep_ghost` takes the measure from the invariant: `I s n` has a number `n`, and each repeat gives an `n' < n`. In `Proofs/Lists/Sep.lean`, the invariant of `reverse` is: `prev` has the first items in the other order, and `cur` has the other `n` items.

## Globals

`mem0` holds one block per global. `Mem.heap_split` splits a live block off a memory as owned bytes; `counter_init` uses it to show that at program start the memory owns the counter with the value 0, and `bump_spec` is the triple of one `bump`.

## Proved examples

| File | Theorems |
|---|---|
| `Proofs/Pointers/Sep.lean` | `swap_sep`, `swap_self_sep` (`swap(p, p)` keeps the value) |
| `Proofs/Slices/Sep.lean` | `counter_init`, `bump_spec`, `copyWithin_spec` (the ranges can overlap), `fill_sep`, `reverse_spec` |
| `Proofs/Lists/Sep.lean` | `push_spec` (a new node, or `error.OutOfMemory` and no bytes), `reverse_spec` (the list in the other order), `freeAll_spec` (after it, no bytes are owned: every node is freed) |

`append` of `ArrayListUnmanaged` has no proof. Its `@memcpy` alias check compares the addresses of the old and the new block. A proof of that check needs a fact that no assertion can state: every block ends below `Mem.nextAddr`.
