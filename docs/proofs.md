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

`Triple` also needs `Mem.SingleThread m` before `c` runs, and gives it back for the result memory. A program that never spawns a thread (`Proofs/Threads/`, `Proofs/Atomics/` and `Proofs/Sync/` do; §Proofs over all schedules) gets this for free: `Triple.of_run` and every rule below thread it through, so a proof never states it. `ZigLean/Mem/Lemmas.lean` has the pieces: `singleThread_empty` (true at program start, from an empty footprint), `singleThread_write`/`singleThread_recordAt` (preserved by a write or a recorded access), `noRace_of_singleThread` (turns it into the `NoRace` a `*_run` lemma below needs).

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

## Proofs over all schedules

`ZigLean/Conc/Logic.lean` is a program logic for concurrent functions (`Zig.ConcM`, [docs/std-models.md](std-models.md) §Thread model). `Conc.Proto.run_sound`: every result of `Sched.run dispatch fuel o main m0`, for every oracle `o` and every `fuel`, satisfies `main`'s post (partial correctness: an error or no result satisfies every spec). In strict mode (`Proto.strict := true`) also no run gives an error: `Conc.Proto.run_safe` (no data race, no deadlock, no overflow, no other illegal behaviour; no result, out of fuel, is still allowed). One proof gives both (`run_spec`).

| Part | What |
|---|---|
| Protocol (`Conc.Proto`) | A ghost value per thread (only the proof sees it); an invariant `inv G m` on the ghost values of all threads and the memory; the ghost value `init tgt` of a new thread; `fin g` of a thread that ended. |
| One thread (`Proto.Safe`) | Rely–guarantee: at each stop the thread picks its new ghost value and shows `inv`; when it goes on, it knows only `inv` and its own ghost value. A run between two stops keeps the number of threads. A `join` of thread `u` gives `fin (G u)`. |
| Rules (`Proto.WP`) | `pure'`, `bind`, `liftMem`, `sync`, `loop`; for generated code (`ZigLean/Conc/Lemmas.lean`) `liftM`, `callMC`, `callRC`, `pickC`, `spawnC`, `joinC`, `map`. The post gets the depth that is left: each loop repeat passes a sync op (the depth gets smaller) or makes a measure smaller, so a spin-wait needs no measure. |
| Strict mode | No error leaf; a `MemM` step needs a proof that it does not throw (`liftM`/`callMC`/`callRC` take it); a `join` must be of a later thread that exists and was not joined, so a thread that waits waits for a later one, and the thread ids go up: no deadlock (`ready_ne`); a `pick` knows its choice is in range; no futex wait. A spawned thread and `main` must end with every thread they spawned joined (`joinedAll`). |
| No error, from its cause | `MemM.bind_err`, `lift_err` and the others go from an error back to the step that threw it; `noRace_of` (every overlapping access happened before, or does not race by its kind), `join_run`, `locIdx_noErr`, `loadPrep_noErr`, `atomicRmwAt_noErr`, `atomicLoadAt_noErr`, `optCount_le_one`. |
| A step from its result | In partial correctness a step can fail (a race is `.illegal`), so the lemmas go from a result back to the memory: `load_ok`, `store_ok`, `storeUndef_ok`, `alloc_ok`, `free_ok`, `locIdx_found`/`locIdx_new`, `atomicRmwAt_ok`, `atomicLoadAt_ok`. |
| RC11 at an RMW chain (`ALoc.Chain`) | An RMW reads only the newest message (`readOpts_chain`). A read whose clock is `≥` the newest message's clock reads only it (`readOpts_floor`, `le_floorPos`). |

`Proofs/Threads/Counter.lean` proves `parallelCounter n = 4 * n` under every schedule. The invariant: the counter's messages are an RMW chain, and their number minus 1 is the sum of the threads' increments (their ghost values); each message's clock is `≤` the clock of some thread, and a thread that `main` joined has a clock `≤` `main`'s; each context holds the counter's address and `n`. After the 4 joins `main`'s clock is `≥` every message's clock, so its load reads the newest message.

`parallelCounter_safe` proves in strict mode that no run of `parallelCounter` gives an error. The protocol adds `Ex`: the three stack blocks are live with their sizes and aligned addresses; each footprint entry is a read of a context, an atomic access to the counter, a plain write that happened before every thread (the spawn copies `main`'s clock), or `main`'s access to the handles; every thread was spawned by `main`; the handle slots hold the thread ids. So no access races (`noRace_b0`, `noRace_b1`, `noRace_b2`), and every join is of thread `k + 1`, spawned and not yet joined.

Not yet (`PLAN.md` §Next): deadlock freedom with futex waits (the mutex counter); assertions on what a thread has seen, for release/acquire (message passing) and relaxed atomics.

## Proved examples

| File | Theorems |
|---|---|
| `Proofs/Pointers/Sep.lean` | `swap_sep`, `swap_self_sep` (`swap(p, p)` keeps the value) |
| `Proofs/Slices/Sep.lean` | `counter_init`, `bump_spec`, `copyWithin_spec` (the ranges can overlap), `fill_sep`, `reverse_spec` |
| `Proofs/Threads/Counter.lean` | `parallelCounter_spec` (`4 * n` under every schedule), `parallelCounter_safe` (no run gives an error) |
| `Proofs/Lists/Sep.lean` | `push_spec` (a new node, or `error.OutOfMemory` and no bytes), `reverse_spec` (the list in the other order), `freeAll_spec` (after it, no bytes are owned: every node is freed) |

`append` of `ArrayListUnmanaged` has no proof. Its `@memcpy` alias check compares the addresses of the old and the new block. A proof of that check needs a fact that no assertion can state: every block ends below `Mem.nextAddr`.
