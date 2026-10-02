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

`Triple` also needs `Mem.Seq m` before `c` runs, and gives it back for the result memory. `Mem.Seq` is `Mem.SingleThread` (one thread) and `Mem.AddrBelow` (every live byte is in a block that ends below `Mem.nextAddr`, so a new block lies above every live block: `alloc_run`'s last fact). A program that never spawns a thread (`Proofs/Threads/`, `Proofs/Atomics/` and `Proofs/Sync/` do; §Proofs over all schedules) gets this for free: `Triple.of_run` and every rule below thread it through, so a proof never states it. `ZigLean/Mem/Lemmas.lean` has the pieces: `singleThread_empty` (true at program start, from an empty footprint), `singleThread_write`/`singleThread_recordAt` (preserved by a write or a recorded access), `noRace_of_singleThread` (turns it into the `NoRace` a `*_run` lemma below needs).

| Rule | Statement |
|---|---|
| `Triple.frame` | `Triple P c Q → Triple (P ∗ R) c (fun v => Q v ∗ R)` |
| `Triple.conseq`, `ret`, `bind`, `ex`, `lift` | the structural rules |
| `Triple.load`, `Triple.store` | `pts p a v` before and after (`0 < Enc.size T`; `store` needs `LawfulEnc T`) |
| `Triple.alloc`, `Triple.free` | a new block with undefined bytes; `free` needs every byte of the block, from offset 0 |
| `Triple.create`, `Triple.destroy` | the allocator (`ZigLean/Sep/Alloc.lean`): `newBlock` is a new `.heap` block or `error.OutOfMemory` and no bytes; `destroy` needs the whole `.heap` block |
| `loop_sep_spec`, `loop_sep_ghost` | a `Zig.loop` with an invariant that is an assertion (below) |

A proof about generated code does not apply the rules one by one. It unfolds the code with `simp [f, zig_unfold, …]` and gives it the result of each memory operation. The `*_run` lemmas give that result, for a heap `h` that owns the bytes, in a memory whose heap is `h ∪ hF`. Unlike `Triple`, a `*_run` lemma is not wrapped: it takes `Mem.Seq m` as an explicit hypothesis and returns `Mem.Seq m'` as part of its conclusion, so a hand-written proof that calls one directly (`Proofs/Lists/Sep.lean`, `Proofs/Pointers/Proofs.lean`, `Proofs/Slices/Sep.lean`) threads it from one call to the next, starting from `singleThread_empty`.

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

`loop_sep_spec body again I meas post hF` needs, for each iteration from a heap `h` with `I s h`: the run of the body, the new heap `h'` (with the same frame `hF`), and either `I s' h'` and a smaller `meas s'` (the loop repeats), or `post e s' h'` (it exits). The invariant `I` is on the locals `s` and the owned heap. Like a `*_run` lemma, `loop_sep_spec` is not wrapped by `Triple`: each iteration takes and returns `Mem.Seq`, so a call site threads it the same way.

`reverse` (`Proofs/Slices/Sep.lean`): the invariant `revInv` says that the items before `i` and after `j` are swapped and the others are unchanged; `revMeas s = j + 1 - i`. `reverse_step` proves one iteration; `reverse_spec` starts the loop with `i = 0`, `j = n - 1`.

A walk over a linked list ends because the rest of the list gets shorter, and the locals do not give that length. `loop_sep_ghost` takes the measure from the invariant: `I s n` has a number `n`, and each repeat gives an `n' < n`. In `Proofs/Lists/Sep.lean`, the invariant of `reverse` is: `prev` has the first items in the other order, and `cur` has the other `n` items.

## Globals

`mem0` holds one block per global. `Mem.heap_split` splits a live block off a memory as owned bytes; `counter_init` uses it to show that at program start the memory owns the counter with the value 0, and `bump_spec` is the triple of one `bump`.

## Proofs over all schedules

`ZigLean/Conc/Logic.lean` is a program logic for concurrent functions (`Zig.ConcM`, [docs/std-models.md](std-models.md) §Thread model). `Conc.Proto.run_sound`: every result of `Sched.run dispatch fuel o main m0`, for every oracle `o` and every `fuel`, satisfies `main`'s post (partial correctness: an error or no result satisfies every spec). In strict mode (`Proto.strict := true`) also no run gives an error: `Conc.Proto.run_safe` (no data race, no deadlock, no overflow, no other illegal behaviour; no result, out of fuel, is still allowed). One proof gives both (`run_spec`).

| Part | What |
|---|---|
| Protocol (`Conc.Proto`) | A ghost value per thread (only the proof sees it); an invariant `inv G m` on the ghost values of all threads and the memory; the ghost values `init tgt g` that a new thread can start with (the spawner picks one, so it can give the thread a part of what it owns); `fin g` of a thread that ended. |
| One thread (`Proto.Safe`) | Rely–guarantee: at each stop the thread picks its new ghost value and shows `inv`; when it goes on, it knows only `inv` and its own ghost value. A run between two stops keeps the number of threads. A `join` of thread `u` gives `fin (G u)`. |
| Rules (`Proto.WP`) | `pure'`, `bind`, `liftMem`, `sync`, `loop`; for generated code (`ZigLean/Conc/Lemmas.lean`) `liftM`, `callMC`, `callRC`, `callRC_ok`, `callC`, `pickC`, `spawnC`, `joinC`, `futexWaitC`, `futexWakeC`, `map`. The post gets the depth that is left: each loop repeat passes a sync op (the depth gets smaller) or makes a measure smaller, so a spin-wait needs no measure. |
| Strict mode | No error leaf; a `MemM` step needs a proof that it does not throw (`liftM`/`callMC`/`callRC` take it); a `join` must be of a later thread that exists and was not joined, and `Proto.joins` holds of the joining thread's ghost value; a `pick` knows its choice is in range. A spawned thread and `main` must end with every thread they spawned joined (`joinedAll`). |
| Futex | The futex queue is in the memory (`Mem.waiters`, `Mem.woken`), so `inv` can name it. A wait begins with the thread not in the queue; a wait that sleeps keeps `inv` with the thread's ghost value. In strict mode each wait keeps `Live`: if the thread sleeps, not every thread has ended (`fin`), sleeps, or waits at a join (`joins`). |
| No deadlock (`ready_ne`) | A thread that cannot go on waits at a join of a later thread that has not ended, or sleeps at a futex. The chain of joins goes up the thread ids, so it ends at a sleeping thread, and its `Live` excludes that every thread waits. |
| No error, from its cause | `MemM.bind_err`, `lift_err` and the others go from an error back to the step that threw it; `noRace_of` (every overlapping access happened before, or does not race by its kind), `join_run`, `locIdx_noErr`, `loadPrep_noErr`, `storePrep_noErr`, `casPrep_noErr`, `atomicRmwAt_noErr`, `atomicLoadAt_noErr`, `atomicStoreAt_noErr`, `cmpxchgAt_noErr`, `atomicRmwAs_noErr`, `cmpxchgAs_noErr`, `alloc_noErr`, `free_noErr`, `optCount_le_one`, `optCount_eq`; `futexWait_run_woken`/`futexWait_run_go` (a futex wait's run). |
| A step from its result | In partial correctness a step can fail (a race is `.illegal`), so the lemmas go from a result back to the memory: `load_ok`, `store_ok`, `storeUndef_ok`, `alloc_ok`, `free_ok`, `locIdx_found`/`locIdx_new`/`locIdx_single` (one atomic location), `atomicRmwAt_ok`, `atomicLoadAt_ok`, `atomicStoreAt_ok`, `cmpxchgAt_ok`, `atomicRmwAs_ok`, `cmpxchgAs_ok`, `fork_run`, `join_eq`, `futexWait_ok`. |
| RC11 at an RMW chain (`ALoc.Chain`) | An RMW reads only the newest message (`readOpts_chain`, `rmw_chain_pos`). A `cmpxchg` that reads the expected value reads the newest message (`cas_chain_pos`); it can always read it (`casOpts_ne`). A read whose clock is `≥` the newest message's clock reads only it (`readOpts_floor`, `le_floorPos`). A new RMW of the newest message keeps the chain (`ALoc.Chain.push`). A read and a store always have an option (`readOpts_ne`, `writeSlots_ne`; `writeSlots_bounds`). |
| Views | After an acquire read, the thread's clock is above the message's release clock (`loadM_acq_le`). An entry that overlaps an access, races with it by its kind, and whose clock is concurrent with the thread's bumped clock makes the access race (`race_of`; `VClock.le_eq_false`). |
| Frames and the start | `Grows` (clocks not smaller, the rest the same), `Before` (a clock below every thread), `BlkAt`; `Solo` and `solo_store` for `main`'s stores before its first spawn. |

`Proofs/Threads/Counter.lean` proves `parallelCounter n = 4 * n` under every schedule. The invariant: the counter's messages are an RMW chain, and their number minus 1 is the sum of the threads' increments (their ghost values); each message's clock is `≤` the clock of some thread, and a thread that `main` joined has a clock `≤` `main`'s; each context holds the counter's address and `n`. After the 4 joins `main`'s clock is `≥` every message's clock, so its load reads the newest message.

`parallelCounter_safe` proves in strict mode that no run of `parallelCounter` gives an error. The protocol adds `Ex`: the three stack blocks are live with their sizes and aligned addresses; each footprint entry is a read of a context, an atomic access to the counter, a plain write that happened before every thread (the spawn copies `main`'s clock), or `main`'s access to the handles; every thread was spawned by `main`; the handle slots hold the thread ids. So no access races (`noRace_b0`, `noRace_b1`, `noRace_b2`), and every join is of thread `k + 1`, spawned and not yet joined.

`Proofs/Sync/Mutex.lean` proves that `mutexCounter` (two threads, each adds 1 two times under the translated std `Io.Mutex` of Zig 0.16.0) gives 4 under every schedule (`mutexCounter_spec`), and that no run gives an error (`mutexCounter_safe`). `Proofs/Iogroup/Counter.lean` proves the same for `groupCounter` (three `Io.Group` tasks, each adds 1 under an `Io.Mutex`; 3 after `Group.await`). Both proofs use the lock rules (§A lock that owns a resource).

**What a thread has seen** (`Proofs/Atomics/`). The invariant states it on the messages of an atomic location, with the clocks:

- `MessagePassing.lean`: `mpRelAcq` gives 0 or 42 and never errs. A flag message that holds 1 has every write to `data` below its release clock (`FlagLoc`); the acquire load joins that clock into `main`'s, so the read of `data` does not race and sees 42.
- `Relaxed.lean`: every result of `mpRelaxed` (relaxed flag) is 0 (partial correctness). Until the join, `main`'s clock has 0 at the writer's component, and the writer's clock at `main`'s component is not above `main`'s own (`view`). So after a read of 1, the writer's write of `data` is concurrent with `main`'s read: a race (`read_race`).
- `Stack.lean`: `stackPush` (two pushers with a `cmpxchgWeak` loop) gives 120 or 210 and never errs. The head's messages are an RMW chain whose values are one of 5 lists (`Chains`); a pusher is `done` exactly when its node is in the list, `next[v]` holds the value under `v`, and each message is below its pusher's clock. A pusher's ghost value `cas h` says that it wrote `next[u] := h`. After both joins `main`'s clock is above both pushers' clocks (`JoinLe`), so the acquire load reads the newest message and the reads of `next` do not race. Zig 0.15.2 reads `next[k]` by a load of the whole `Stack` (the head too); the proof has a branch for each translation (`first`), as `Proofs/Layout/Mem.lean` has for 0.14.1.

## Concurrent separation logic

A thread owns a part of the heap, and the parts move between the threads at the sync ops (`ZigLean/Conc/Own.lean`, `ZigLean/Conc/Csl.lean`). So a thread's code is proved with triples, as sequential code, and the invariant only says who owns which part.

| Part | What |
|---|---|
| Ownership (`Mem.OwnsC`, `Mem.Owns`) | The clock `c` owns the heap `h` if every recorded access to a byte of `h` (and to a block that does not exist yet) happened before `c`; thread `t` owns `h` if its clock does. Then a plain access by `t` to `h` does not race (`Mem.Owns.noRace`). A later clock owns what an earlier one owns (`Mem.OwnsC.mono`). |
| A step of the owner (`StepIn hF`) | A step of the current thread that changes only its part: the rest `hF` and the other threads' clocks are the same, and each new footprint entry touches no byte of `hF`. So every part of `hF` keeps its owner (`Mem.OwnsC.frame`, `Mem.Owns.frame`). |
| Thread triples (`TTriple`) | `Triple` with ownership in place of `Seq`. Rules: `conseq`, `frame`, `frameL`, `ret`, `bind`, `bind_eq`, `ex`, `lift`, `load`, `store`, `loadAt`/`storeAt` (at a byte offset of `bytesAt`; `storeAt'` needs only the size of the value's encoding), `alloc`, `alloc_next`, `free`. `bytesAt_split` splits owned bytes at an offset; `bytesAt_blk` reads the block of owned bytes. |
| The parts (`Owned own m`) | `own u` is thread `u`'s part: in `m.heap` with the same cells, two parts are disjoint, each thread owns its part, a thread that does not exist has none. A proof puts a thread's part in its ghost value: after a stop the thread knows only `inv` and its ghost value, and `Owned` tells it that its part is unchanged. |
| Transfers | A step with a thread triple (`Owned.step`; `WP.liftMem_owned`, `WP.liftM_owned`, and `WP.liftMem_upd`, `WP.liftM_upd` for the parts `upd own t h`); spawn (`Owned.fork`: the parent gives a part to the new thread, whose clock is the parent's); join (`Owned.join`: the parent takes the joined thread's part, whose clock the join merges); a step that changes no part (`Owned.keep`: an atomic op on a location that no thread owns, a futex op); the start (`Owned.start`), a smaller part (`Owned.shrink`), a part that gets a heap the thread owns (`Owned.add`). |

`Proofs/Threads/Disjoint.lean` proves that `disjoint a b` (two threads each write their own flag, as in `race` but on two flags) gives `a + b` under every schedule and never errs (`disjoint_spec`, `disjoint_safe`). `writeFlag` is a thread triple over the two blocks that the thread owns (`writeFlag_spec`, from the rules above). `main` owns its four blocks, gives `{c1, x}` and `{c2, y}` at the spawns, and takes them back at the joins, with the flag written. The invariant has no footprint and no clock facts: `Owned` has them.

### A lock that owns a resource

The translated `Io.Mutex` (0.16.0) and `Thread.Mutex` (0.15.2, `FutexImpl`) own a part of the heap (the resource) while they are free; `lock` gives it to the thread that takes the lock, and `unlock` gives it back (`ZigLean/Conc/Lock.lean`, `ZigLean/Conc/LockRules.lean`). The rules are proved once, for every protocol that has the lock (`Lock.Fits`: its invariant is `Lock.Inv` and a rest `U` that a step of the lock's code keeps).

| Part | What |
|---|---|
| The lock (`Lock`) | The word (4 bytes at offset `o` of block `b`), its contended value `c` (`2` for `Io.Mutex`, `3` for `Thread.Mutex`) and the resource `R`, an assertion that can read the ghost values of all threads (for example: the counter holds the sum of their increments). The ghost value of a thread tells its place in the lock's code (`LPh`: `gone`, `out`, `spin`, `wait`, `holds`, `wake`, and `away` at the futex wait of another sync object), its part of the heap, and the resource while it holds the lock. `Lock.prod` is a lock whose ghost value is `LG × X`. |
| The invariant (`Lock.Inv`) | The threads' parts (`Owned`). The word is `0` iff no thread holds the lock; at most one thread holds it. The word's location is an RMW chain of `0`, `1` and `c`. The free lock owns a heap with `R` (`Lock.Owns`: each access to it happened before every thread that is not `gone`, or before the release clock of the newest message); the holder's resource has `R` (`res`). A thread in the futex queue waits at the word (at `wait`) or at another futex (`away`, `Lock.Queue`); if a thread waits at the word, a thread that is not asleep is in the lock's code, and holds the lock only with the word `2` (`wit`). So a futex wait at the word keeps `Live` (`Fits.live`), and no thread waits at the word when all are asleep or ended (`Fits.noWaits`). |
| The lock's code | `wp_cas`, `wp_xchgLock`, `wp_wait`, `wp_xchgUnlock`, `wp_wake`: the ops of `lock` and `unlock` in generated code (`States` gives the generated values: the enum of `Io.Mutex`, the `u32` of `Thread.Mutex`). `Thread.Mutex` also has `wp_orLock` (`tryLock`'s `or(1)`), `wp_loadLock` (a relaxed load) and `Fits.toWait` (`spin` to `wait` before its futex wait). The acquire RMW that takes the lock adopts the release clock of the newest message, so the thread owns the resource; the release RMW of `unlock` puts the holder's clock in the new message, so the lock owns the resource again. In strict mode no op throws (`Inv.cas_noErr`, `Inv.xchg_noErr`, `Inv.wait_ok`). A step of the lock's code keeps the threads at other futexes, the atomic locations at other addresses (`LocsKeep`) and each clock that happened before the newest message (`Lock.Before`); a release step tells the rest of the invariant that the holder's clock happened before the lock (`Fits.stable`). |
| Other steps | A step of a thread on its own part (`Inv.stepIn`), a plain read of bytes that no thread owns (`Inv.read`), a plain read of the word and the resource by the only thread that is not `gone` (`Inv.readAll`), a change of a ghost value outside the lock's code (`Inv.ghost`), a spawn (`Inv.fork`), a join (`Inv.join`), the start of the lock (`Inv.make`) and its end, when one thread is above all the others (`Inv.take`), a futex wait or wake at another word (`Inv.waitOff`, `Inv.wakeOff`), an op at a shared atomic word (`Inv.wordOp`), other ghost values with the same lock places (`Inv.congr`). |

`Proofs/Sync/Lock.lean` has `lock` and `unlock` of the translated `Io.Mutex` for every protocol with the lock (`MutexOps.lock_spec`, `MutexOps.unlock_spec`); `Mutex.lean` and `Handoff.lean` use them. `Proofs/Threadsync/Lock.lean` has the same for `Thread.Mutex` (`ThreadMutexOps`), for both translations: Linux `FutexImpl` (contended value `3`, the committed `Gen.lean`) and macOS `DarwinImpl` (`os_unfair_lock`, a model built from the model's ops, `docs/std-models.md`; contended value `1`, `tests/golden/0.15.2/threadsync/Gen-darwin.lean`). `if_decl` compiles the proofs of the translation that exists; `mutexC` and `mutexOf` give the OS-specific values, so `Mutex.lean`, `WaitGroup.lean` and `Handoff.lean` compile with either `Gen.lean`. CI builds them against `Gen-darwin.lean` in the 0.15.2 job.

`Proofs/Sync/Semaphore.lean` has `wait` and `post` of the translated `Io.Semaphore` for every protocol with the semaphore (`Sem.Fits`): `Sem.wait_spec` (the thread takes a permit and the resource `T` that the protocol gives with it) and `Sem.post_spec` (it gives them back). The semaphore's mutex is a lock that owns the permit count and the resource of the free permits (`Sem.R`); the condition's state and epoch are shared words with the invariant `Sem.Inv`: at most one thread waits at the condition (the protocol shows it, `hone`), and a thread waits there only with a ghost value that the protocol allows (`Sem.wx`). A waiter's place records the epoch value it read (`SPh.reg`), so it sleeps at the epoch's futex only while no signal came. No deadlock: a waiter sleeps only while the permit count is 0 (then the protocol shows that a thread goes on, `Fits.live`) or a thread holds the mutex in `signal`. `Proofs/Sync/SemCounter.lean` uses the specs.

A proof file over all schedules can set `attribute [local irreducible] Proto.WP`: the rules need `WP` only as a name, and when a type check unfolds `WP`, it runs the program (`Proofs/Threadsync/Mutex.lean`).

### A shared atomic word

A word of a sync object that no thread owns: the state and the epoch of an `Io.Condition` or a `Thread.Condition`, the state of an `Io.Event` or a `Thread.ResetEvent`, the `u64` state of a `Thread.WaitGroup` (`ZigLean/Conc/Word.lean`; `Word n nb`: `n` bits in `nb` bytes, 32 or 64). Each access to it is atomic (`Word.Ok`), so its ops do not race, and an RMW reads the newest message. A proof keeps facts on the word's writes (`Word.hist`: bytes, clock, release clock of each message, oldest first) in its invariant.

| Part | What |
|---|---|
| Ops | `Ok.load` (reads write `j`, at least each write that happened before the thread: `Word.Floor`; an acquire adopts its release clock), `Ok.rmw` (reads the newest write and adds one: `rmwEnt`), `Ok.cas` (an RMW of the newest write, or a read of write `j` with another value). In strict mode no op throws (`Ok.load_noErr`, `Ok.rmw_noErr`, `Ok.cas_noErr`). |
| Other steps | A step that keeps the word (`Word.Keep`, same writes: `hist_keep`): a step of the lock's code (`keep_lockStep`), a step of a thread on its own part (`keep_stepIn`), a spawn, a join, a plain read, an op at another word (`keep_op`). An op at a word keeps the lock's invariant (`Lock.Inv.wordOp`). |

## Proved examples

| File | Theorems |
|---|---|
| `Proofs/Pointers/Sep.lean` | `swap_sep`, `swap_self_sep` (`swap(p, p)` keeps the value) |
| `Proofs/Slices/Sep.lean` | `counter_init`, `bump_spec`, `copyWithin_spec` (the ranges can overlap), `fill_sep`, `reverse_spec` |
| `Proofs/Threads/Counter.lean` | `parallelCounter_spec` (`4 * n` under every schedule), `parallelCounter_safe` (no run gives an error) |
| `Proofs/Threads/Disjoint.lean` | `disjoint_spec` (`a + b` under every schedule), `disjoint_safe` (no data race: the threads own disjoint blocks), in concurrent separation logic |
| `Proofs/Sync/Mutex.lean` | `mutexCounter_spec` (4 under every schedule, with the std `Io.Mutex`), `mutexCounter_safe` (no data race, no deadlock at the futex, no other error) |
| `Proofs/Iogroup/Counter.lean` | `groupCounter_spec` (3 under every schedule, with `Io.Group` and the std `Io.Mutex`), `groupCounter_safe` (no data race, no deadlock, no other error) |
| `Proofs/Threadsync/Mutex.lean` | `mutexCounter_spec` (4 under every schedule, with the std `Thread.Mutex` of 0.15.2), `mutexCounter_safe` (no data race, no deadlock at the futex, no other error) |
| `Proofs/Threadsync/WaitGroup.lean` | `waitGroup_spec` (2 under every schedule, with the std `Thread.WaitGroup`, `Thread.ResetEvent` and `Thread.Mutex` of 0.15.2), `waitGroup_safe` (no data race, the plain read of the whole `Tally` included; no deadlock at a futex, no other error) |
| `Proofs/Threadsync/Handoff.lean` | `handoff_spec` (7 under every schedule, with the std `Thread.Mutex`, `Thread.Condition` and `Thread.ResetEvent` of 0.15.2), `handoff_safe` (no data race, no deadlock at a futex, no `unreachable`) |
| `Proofs/Sync/Handoff.lean` | `handoff_spec` (7 under every schedule, with the std `Io.Mutex`, `Io.Condition` and `Io.Event`), `handoff_safe` (no data race, no deadlock at a futex, no `unreachable`) |
| `Proofs/Sync/SemCounter.lean` | `semaphoreCounter_spec` (4 under every schedule, with the std `Io.Semaphore`, `Io.Mutex` and `Io.Condition`), `semaphoreCounter_safe` (no data race, no deadlock at a futex, no other error) |
| `Proofs/Atomics/MessagePassing.lean` | `mpRelAcq_spec` (0 or 42 under every schedule), `mpRelAcq_safe` (release/acquire: no data race) |
| `Proofs/Atomics/Relaxed.lean` | `mpRelaxed_spec` (every result is 0: a read of 1 races) |
| `Proofs/Atomics/Stack.lean` | `stackPush_spec` (120 or 210 under every schedule), `stackPush_safe` (no data race, no index out of bounds, no other error) |
| `Proofs/Lists/Sep.lean` | `push_spec` (a new node, or `error.OutOfMemory` and no bytes), `reverse_spec` (the list in the other order), `freeAll_spec` (after it, no bytes are owned: every node is freed) |
| `Proofs/Lists/Append.lean` | `append_run` (`ArrayListUnmanaged(u32).append`: `xs ++ [v]`, or `error.OutOfMemory` and the same list; a new buffer when the old one is full) |

`Proofs/Lists/Append.lean` proves `append` of `ArrayListUnmanaged(u32)` as a `*_run` lemma (`append_run`): the list `xs ++ [v]`, or `error.OutOfMemory` and the same list. When the buffer is full, `ensureTotalCapacityPrecise` allocates a new block, checks that the old and the new items do not overlap (`@memcpy`), copies them and frees the old block. The check holds because the new block lies above every live block (`alloc_run`'s last fact, from `Mem.AddrBelow`). The list's items pointer with capacity 0 points into a block of 0 bytes, which no assertion can state; `append_run` takes it as a fact about the memory (`ptrOk`) and gives it back. The proof holds for the 0.15.2 and the 0.16.0 translations: a `first` with a guard (a definition only the 0.15.2 translation has) picks the loads of each.
