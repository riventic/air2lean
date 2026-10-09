import ZigLean.Conc.Csl
import ZigLean.Conc.Tls

/-!
# Thread-local storage: identity, initialization, lifetime

Lemmas about `ZigLean/Mem/Tls.lean` and the rules a proof over all schedules uses for a
spawned thread with thread-local storage (`ConcM.tlsThread`). A proof-only module: it imports
`ZigLean.Mem.Lemmas`, so it stays out of the `ZigLean` umbrella.

- **No aliasing** (`TlsWF`, `TlsWF.no_alias`): every registered instance is a block of the
  memory, and no block is the instance of two threads. So the same key (the same `threadlocal`
  name) in two different threads gives two different blocks. `TlsWF` holds at program start
  (`TlsWF.mainTls`) and every memory step keeps it: a step that keeps the thread records and
  does not remove blocks (`TlsWF.of_threads`: every load, store, allocation, free and atomic
  op), a spawn (`TlsWF.fork`), a join (`TlsWF.join`) and a thread start (`TlsWF.tlsEnter`).
- **Initialization** (`tlsEnter_init`): after a thread start, each instance of the thread is a
  new, live block holding exactly the initial bytes of its global, whatever the other threads
  did to their instances.
- **Lifetime** (`tlsExit_dead`): after a thread end, every instance of the thread is dead, so
  any later access through a pointer to it throws `.illegal` (`load_dead`).
- **Rules for proofs** (`TTripleIn`): a thread triple that may also read the thread records
  (which every thread triple keeps): `tlsPtr` is a step that reads only them (`TTripleIn.tlsPtr`).
  `WP.liftMem_ownedIn` uses such a triple in a thread, `WP.liftM_tlsPtr` is the step in a
  concurrent body, and `Owned.setTls` and `liftMem_bind`
  handle the registration of a thread start.
-/

namespace Zig

open Assn Conc Conc.Proto

/-! ## The thread records -/

@[simp] theorem Mem.setTls_blocks (m : Mem) (t : ThreadId) (ids : Array (BlockId × BlockId)) :
    (m.setTls t ids).blocks = m.blocks := rfl

@[simp] theorem Mem.setTls_current (m : Mem) (t : ThreadId) (ids : Array (BlockId × BlockId)) :
    (m.setTls t ids).current = m.current := rfl

@[simp] theorem Mem.setTls_clocks (m : Mem) (t : ThreadId) (ids : Array (BlockId × BlockId)) :
    (m.setTls t ids).clocks = m.clocks := rfl

@[simp] theorem Mem.setTls_footprint (m : Mem) (t : ThreadId) (ids : Array (BlockId × BlockId)) :
    (m.setTls t ids).footprint = m.footprint := rfl

@[simp] theorem Mem.heap_setTls (m : Mem) (t : ThreadId) (ids : Array (BlockId × BlockId)) :
    (m.setTls t ids).heap = m.heap := rfl

@[simp] theorem Mem.setTls_threads_size (m : Mem) (t : ThreadId)
    (ids : Array (BlockId × BlockId)) : (m.setTls t ids).threads.size = m.threads.size := by
  simp [Mem.setTls]

theorem Mem.tlsOf_setTls (m : Mem) (t u : ThreadId) (ids : Array (BlockId × BlockId))
    (ht : t < m.threads.size) :
    (m.setTls t ids).tlsOf u = if u = t then ids else m.tlsOf u := by
  unfold Mem.tlsOf Mem.setTls
  simp only [Array.getElem?_modify]
  by_cases hu : u = t
  · subst hu; simp [Array.getElem?_eq_getElem ht]
  · simp [Ne.symm hu, hu]

theorem Mem.tlsOf_of_threads {m m' : Mem} (h : m'.threads = m.threads) (t : ThreadId) :
    m'.tlsOf t = m.tlsOf t := by
  unfold Mem.tlsOf; rw [h]

theorem Mem.tlsInstance_of_threads {m m' : Mem} (h : m'.threads = m.threads) (t : ThreadId)
    (key : BlockId) : m'.tlsInstance t key = m.tlsInstance t key := by
  unfold Mem.tlsInstance; rw [Mem.tlsOf_of_threads h]

/-- An instance found by its key is registered. -/
theorem Mem.tlsInstance_mem {m : Mem} {t : ThreadId} {key b : BlockId}
    (h : m.tlsInstance t key = some b) : (key, b) ∈ m.tlsOf t := by
  unfold Mem.tlsInstance at h
  cases hf : (m.tlsOf t).find? (·.1 == key) with
  | none => rw [hf] at h; cases h
  | some x =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hx := Array.mem_of_find?_eq_some hf
    have hk := Array.find?_some hf
    simp only [beq_iff_eq] at hk
    obtain ⟨k, b'⟩ := x
    simp only at hk h
    subst hk h
    exact hx

/-- The first instance of a thread is found by its key. -/
theorem Mem.tlsInstance_head {m : Mem} {t : ThreadId} {key b : BlockId}
    (h : (m.tlsOf t)[0]? = some (key, b)) : m.tlsInstance t key = some b := by
  unfold Mem.tlsInstance
  rcases hx : m.tlsOf t with ⟨l⟩
  rw [hx] at h
  cases l with
  | nil => simp at h
  | cons x xs =>
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [List.find?_cons]

/-! ## `tlsPtr` -/

theorem tlsPtr_run {m : Mem} {key b : BlockId} (h : m.tlsInstance m.current key = some b) :
    (tlsPtr key).run m = pure (⟨some b, 0⟩, m) := by
  unfold tlsPtr
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  simp only [h]
  rfl

theorem tlsPtr_ok {m m' : Mem} {key : BlockId} {p : Ptr}
    (h : ((tlsPtr key).run m).run = some (.ok (p, m'))) :
    ∃ b, m.tlsInstance m.current key = some b ∧ p = ⟨some b, 0⟩ ∧ m' = m := by
  unfold tlsPtr at h
  obtain ⟨a, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  split at h₁
  · rename_i b hb
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₁
    exact ⟨b, hb, rfl, rfl⟩
  · exact (MemM.throw_ok h₁).elim

/-! ## No aliasing -/

/-- Every registered instance is a block, and no block is the instance of two threads. -/
structure TlsWF (m : Mem) : Prop where
  below : ∀ t x, x ∈ m.tlsOf t → x.2 < m.blocks.size
  disj : ∀ t u, t ≠ u → ∀ x ∈ m.tlsOf t, ∀ y ∈ m.tlsOf u, x.2 ≠ y.2

/-- **The same `threadlocal` name in two threads is two blocks.** -/
theorem TlsWF.no_alias {m : Mem} (hw : TlsWF m) {t u : ThreadId} (htu : t ≠ u) {key b c : BlockId}
    (hb : m.tlsInstance t key = some b) (hc : m.tlsInstance u key = some c) : b ≠ c :=
  hw.disj t u htu _ (Mem.tlsInstance_mem hb) _ (Mem.tlsInstance_mem hc)

/-- So two pointers that `tlsPtr` gives to two threads for the same key differ. -/
theorem TlsWF.tlsPtr_ne {m m₁ m₂ : Mem} (hw : TlsWF m) {t u : ThreadId} (htu : t ≠ u)
    {key : BlockId} {p q : Ptr} {m₁' m₂' : Mem}
    (h₁ : m₁ = { m with current := t }) (h₂ : m₂ = { m with current := u })
    (hp : ((tlsPtr key).run m₁).run = some (.ok (p, m₁')))
    (hq : ((tlsPtr key).run m₂).run = some (.ok (q, m₂'))) : p ≠ q := by
  obtain ⟨b, hb, rfl, -⟩ := tlsPtr_ok hp
  obtain ⟨c, hc, rfl, -⟩ := tlsPtr_ok hq
  subst h₁ h₂
  have := hw.no_alias htu (key := key) hb hc
  intro he; cases he; exact this rfl

/-- A step that keeps the thread records and removes no block keeps `TlsWF`: every load,
store, allocation, free and atomic op. -/
theorem TlsWF.of_threads {m m' : Mem} (hw : TlsWF m) (ht : m'.threads = m.threads)
    (hb : m.blocks.size ≤ m'.blocks.size) : TlsWF m' where
  below t x hx := Nat.lt_of_lt_of_le (hw.below t x (Mem.tlsOf_of_threads ht t ▸ hx)) hb
  disj t u htu x hx y hy :=
    hw.disj t u htu x (Mem.tlsOf_of_threads ht t ▸ hx) y (Mem.tlsOf_of_threads ht u ▸ hy)

/-- Program start: the main thread's instances are the key blocks. -/
theorem TlsWF.mainTls {m : Mem} {keys : Array BlockId} (hk : ∀ k ∈ keys, k < m.blocks.size)
    (h0 : 0 < m.threads.size) (hn : ∀ u, m.tlsOf u = #[]) : TlsWF (m.mainTls keys) where
  below t x hx := by
    unfold Mem.mainTls at hx
    rw [Mem.tlsOf_setTls _ _ _ _ h0] at hx
    split at hx
    · obtain ⟨k, hk', rfl⟩ := Array.mem_map.mp hx; exact hk k hk'
    · rw [hn] at hx; simp at hx
  disj t u htu x hx y hy := by
    unfold Mem.mainTls at hx hy
    rw [Mem.tlsOf_setTls _ _ _ _ h0] at hx hy
    by_cases ht : t = 0
    · have hu : ¬ u = 0 := fun h => htu (ht.trans h.symm)
      rw [if_neg hu, hn] at hy; simp at hy
    · rw [if_neg ht, hn] at hx; simp at hx

/-- A spawn adds a thread with no instance yet. -/
theorem TlsWF.fork {m m' : Mem} {c : ThreadId} (hw : TlsWF m)
    (hf : (Thread.fork.run m).run = some (.ok (c, m'))) : TlsWF m' := by
  rw [Proto.fork_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨-, rfl⟩ := hf
  have e : ∀ t, ({ m with
      clocks := (m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current)).push
        (VClock.bump (m.clocks[m.current]!) m.current),
      threads := m.threads.push { spawner := m.current, joined := false } } : Mem).tlsOf t =
      m.tlsOf t := by
    intro t
    unfold Mem.tlsOf
    simp only [Array.getElem?_push]
    split
    · rename_i h; subst h; simp [Array.getElem?_eq_none]
    · rfl
  exact ⟨fun t x hx => hw.below t x (e t ▸ hx),
    fun t u htu x hx y hy => hw.disj t u htu x (e t ▸ hx) y (e u ▸ hy)⟩

/-- A join keeps every thread's instances. -/
theorem TlsWF.join {m m' : Mem} {tid : ThreadId} (hw : TlsWF m)
    (hj : ((Thread.join tid).run m).run = some (.ok ((), m'))) : TlsWF m' := by
  obtain ⟨rec, hr, -, rfl⟩ := Proto.join_eq hj
  have e : ∀ t, ({ m with
      clocks := m.clocks.set! m.current
        (VClock.merge (VClock.bump (m.clocks[m.current]!) m.current) (m.clocks[tid]!)),
      threads := m.threads.set! tid { rec with joined := true } } : Mem).tlsOf t =
      m.tlsOf t := by
    intro t
    unfold Mem.tlsOf
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    split
    · rename_i h; subst h
      obtain ⟨hl, hget⟩ := Array.getElem?_eq_some_iff.mp hr
      simp [hl, hget]
    · rfl
  exact ⟨fun t x hx => hw.below t x (e t ▸ hx),
    fun t u htu x hx y hy => hw.disj t u htu x (e t ▸ hx) y (e u ▸ hy)⟩

/-! ## Thread start -/

theorem tlsAlloc_ok {m m' : Mem} {bs : Array Byte} {a : Nat} {p : Ptr}
    (h : ((tlsAlloc bs a).run m).run = some (.ok (p, m'))) :
    p = ⟨some m.blocks.size, 0⟩ ∧ m'.threads = m.threads ∧ m'.current = m.current ∧
      m'.blocks.size = m.blocks.size + 1 ∧
      (∀ b, b < m.blocks.size → m'.blocks[b]? = m.blocks[b]?) ∧
      ∃ blk, m'.blocks[m.blocks.size]? = some blk ∧ blk.live = true ∧ blk.bytes = bs ∧
        blk.kind = .global := by
  unfold tlsAlloc at h
  obtain ⟨q, m₁, ha, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Proto.alloc_ok ha
  obtain ⟨_, m₂, hs, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
  obtain ⟨b, blk, o, hacc, -, -, rfl⟩ := Proto.storeBytes_ok hs
  obtain ⟨hpb, hblk, -, -, hfit, -, ho⟩ := access_eq hacc
  simp only [Option.some.injEq] at hpb
  subst hpb
  simp only [Mem.afterAlloc, Array.getElem?_push_size, Option.some.injEq] at hblk
  subst hblk
  simp only [Int.toNat_zero] at ho
  subst ho
  refine ⟨rfl, rfl, rfl, ?_, fun b hb => ?_, ?_⟩
  · simp [Mem.write, Mem.recordAt, Mem.afterAlloc]
  · simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, Mem.afterAlloc, Array.getElem?_push]
    simp [Nat.ne_of_gt hb, Nat.ne_of_lt hb]
  · refine ⟨Block.mk (writeBytes (Array.replicate bs.size .undef) 0 bs) a .global true
      (m.newAddr bs.size a), ?_, rfl, writeBytes_all (by simp), rfl⟩
    simp [Mem.write, Mem.recordAt, Mem.afterAlloc, Array.set!_eq_setIfInBounds]

theorem tlsAllocs_ok : ∀ {inits : List (BlockId × Array Byte × Nat)} {m m' : Mem}
    {ids : Array (BlockId × BlockId)},
    ((tlsAllocs inits).run m).run = some (.ok (ids, m')) →
    m'.threads = m.threads ∧ m'.current = m.current ∧
      m'.blocks.size = m.blocks.size + inits.length ∧
      (∀ b, b < m.blocks.size → m'.blocks[b]? = m.blocks[b]?) ∧ ids.size = inits.length ∧
      ∀ i (hi : i < inits.length), ids[i]? = some (inits[i].1, m.blocks.size + i) ∧
        ∃ blk, m'.blocks[m.blocks.size + i]? = some blk ∧ blk.live = true ∧
          blk.bytes = inits[i].2.1 ∧ blk.kind = .global
  | [], m, m', ids, h => by
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h
    simp
  | (key, bs, a) :: rest, m, m', ids, h => by
    unfold tlsAllocs at h
    obtain ⟨p, m₁, h1, h₁⟩ := MemM.bind_ok h
    obtain ⟨rfl, ht1, hc1, hs1, hold1, blk, hb1, hl1, hbs1, hk1⟩ := tlsAlloc_ok h1
    obtain ⟨ids', m₂, h2, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨ht2, hc2, hs2, hold2, hsz2, hi2⟩ := tlsAllocs_ok h2
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₂
    refine ⟨ht2.trans ht1, hc2.trans hc1, ?_, fun b hb => ?_, ?_, fun i hi => ?_⟩
    · rw [hs2, hs1]; simp only [List.length_cons]; omega
    · rw [hold2 b (by omega), hold1 b hb]
    · rw [Array.size_append, hsz2]; simp only [List.length_cons]; simp; omega
    · cases i with
      | zero =>
        refine ⟨by simp [Array.getElem?_append_left], blk, ?_, hl1, hbs1, hk1⟩
        rw [Nat.add_zero, hold2 _ (by omega), hb1]
      | succ j =>
        obtain ⟨hid, blk', hb', hl', hbs', hk'⟩ :=
          hi2 j (by simp only [List.length_cons] at hi; omega)
        refine ⟨?_, blk', ?_, hl', by simpa using hbs', hk'⟩
        · rw [Array.getElem?_append_right (by simp)]
          simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
            Nat.add_sub_cancel, hid, List.getElem_cons_succ, hs1]
          congr 2; omega
        · rw [hs1] at hb'; rw [← hb']; congr 1; omega

/-- **Initialization per thread.** After a thread start, the thread's `i`-th instance is the
key of `inits[i]` registered to a new block, which is live, writable and holds exactly the
initial bytes of `inits[i]`; the other threads' instances and all older blocks are unchanged. -/
theorem tlsEnter_init {inits : List (BlockId × Array Byte × Nat)} {m m' : Mem} {x : Unit}
    (ht : m.current < m.threads.size)
    (h : ((tlsEnter inits).run m).run = some (.ok (x, m'))) :
    m'.current = m.current ∧ m'.threads.size = m.threads.size ∧
      (∀ u, u ≠ m.current → m'.tlsOf u = m.tlsOf u) ∧
      m'.blocks.size = m.blocks.size + inits.length ∧
      (∀ b, b < m.blocks.size → m'.blocks[b]? = m.blocks[b]?) ∧
      (m'.tlsOf m.current).size = inits.length ∧
      ∀ i (hi : i < inits.length),
        (m'.tlsOf m.current)[i]? = some (inits[i].1, m.blocks.size + i) ∧
        ∃ blk, m'.blocks[m.blocks.size + i]? = some blk ∧ blk.live = true ∧
          blk.bytes = inits[i].2.1 ∧ blk.kind = .global := by
  unfold tlsEnter at h
  obtain ⟨ids, m₁, h1, h₁⟩ := MemM.bind_ok h
  obtain ⟨ht1, hc1, hs1, hold1, hsz1, hi1⟩ := tlsAllocs_ok h1
  have e := Proto.modify_ok h₁
  subst e
  have ht' : m₁.current < m₁.threads.size := by rw [ht1, hc1]; exact ht
  refine ⟨hc1, by simp [ht1], fun u hu => ?_, hs1, hold1, ?_, fun i hi => ?_⟩
  · rw [Mem.tlsOf_setTls _ _ _ _ ht', if_neg (by rw [hc1]; exact hu), Mem.tlsOf_of_threads ht1]
  · rw [← hc1, Mem.tlsOf_setTls _ _ _ _ ht', if_pos rfl, hsz1]
  · rw [← hc1, Mem.tlsOf_setTls _ _ _ _ ht', if_pos rfl]
    exact hi1 i hi

/-- A thread start keeps `TlsWF`: its new instances are new blocks. -/
theorem TlsWF.tlsEnter {inits : List (BlockId × Array Byte × Nat)} {m m' : Mem} {x : Unit}
    (hw : TlsWF m) (ht : m.current < m.threads.size)
    (h : ((tlsEnter inits).run m).run = some (.ok (x, m'))) : TlsWF m' := by
  obtain ⟨-, -, hother, hs, -, hsz, hi⟩ := tlsEnter_init ht h
  -- An instance of the current thread is a new block.
  have hnew : ∀ y ∈ m'.tlsOf m.current, m.blocks.size ≤ y.2 ∧ y.2 < m'.blocks.size := by
    intro y hy
    obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hy
    have hl : i < inits.length := hsz ▸ hi'
    have := (hi i hl).1
    rw [Array.getElem?_eq_getElem hi', Option.some.injEq] at this
    rw [this, hs]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hl _⟩
  refine ⟨fun t y hy => ?_, fun t u htu y hy z hz => ?_⟩
  · by_cases htc : t = m.current
    · subst htc; exact (hnew y hy).2
    · rw [hother t htc] at hy
      exact Nat.lt_of_lt_of_le (hw.below t y hy) (by rw [hs]; exact Nat.le_add_right _ _)
  · by_cases htc : t = m.current
    · subst htc
      rw [hother u (Ne.symm htu)] at hz
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (hw.below u z hz) (hnew y hy).1)
    · rw [hother t htc] at hy
      by_cases huc : u = m.current
      · subst huc; exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hw.below t y hy) (hnew z hz).1)
      · rw [hother u huc] at hz; exact hw.disj t u htu y hy z hz

/-! ## Thread end -/

/-- Block `b` exists and is dead. -/
def Mem.Dead (m : Mem) (b : BlockId) : Prop := ∃ blk, m.blocks[b]? = some blk ∧ blk.live = false

/-- The bytes of block `b`, dead or live. -/
def Mem.bytesOf (m : Mem) (b : BlockId) : Option (Array Byte) := (m.blocks[b]?).map (·.bytes)

theorem freeBlocks_ok : ∀ {bs : List BlockId} {m m' : Mem} {x : Unit},
    ((freeBlocks bs).run m).run = some (.ok (x, m')) →
    m'.threads = m.threads ∧ m'.current = m.current ∧ m'.blocks.size = m.blocks.size ∧
      (∀ b, m'.bytesOf b = m.bytesOf b) ∧ ∀ b, b ∈ bs ∨ m.Dead b → m'.Dead b
  | [], m, m', x, h => by
    obtain ⟨-, rfl⟩ := MemM.pure_ok h
    exact ⟨rfl, rfl, rfl, fun _ => rfl, fun b hb => hb.resolve_left (by simp)⟩
  | c :: cs, m, m', x, h => by
    unfold freeBlocks at h
    obtain ⟨_, m₁, h1, h₁⟩ := MemM.bind_ok h
    obtain ⟨c', blk, hc, hblk, rfl⟩ := Proto.free_ok h1
    simp only [Option.some.injEq] at hc
    subst hc
    obtain ⟨ht, hcur, hs, hby, hd⟩ := freeBlocks_ok h₁
    have hcl : c < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
    refine ⟨ht, hcur, by rw [hs]; simp, fun b => ?_, fun b hb => hd b ?_⟩
    · rw [hby b]
      unfold Mem.bytesOf
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases h : c = b
      · subst h; rw [if_pos rfl, if_pos hcl, hblk]; rfl
      · rw [if_neg h]
    by_cases hbc : b = c
    · subst hbc
      right
      exact ⟨{ blk with live := false }, by simp [Array.set!_eq_setIfInBounds, hcl], rfl⟩
    · rcases hb with hb | ⟨blk', hb', hl'⟩
      · left; simp only [List.mem_cons] at hb; exact hb.resolve_left hbc
      · right
        refine ⟨blk', ?_, hl'⟩
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        rw [if_neg (Ne.symm hbc)]; exact hb'

/-- **Lifetime.** After a thread end, every instance of the thread is dead. -/
theorem tlsExit_dead {m m' : Mem} {x : Unit} (h : (tlsExit.run m).run = some (.ok (x, m'))) :
    m'.threads = m.threads ∧ m'.current = m.current ∧ m'.blocks.size = m.blocks.size ∧
      (∀ b, m'.bytesOf b = m.bytesOf b) ∧ (∀ b, m.Dead b → m'.Dead b) ∧
      ∀ y ∈ m.tlsOf m.current, m'.Dead y.2 := by
  unfold tlsExit at h
  obtain ⟨_, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨ht, hc, hs, hby, hd⟩ := freeBlocks_ok h₁
  exact ⟨ht, hc, hs, hby, fun b hb => hd b (.inr hb), fun y hy => hd y.2 (.inl (by
    simp only [List.mem_map, Array.mem_toList_iff]; exact ⟨y, hy, rfl⟩))⟩

/-- An access through a pointer into a dead block throws `.illegal`. -/
theorem access_dead {m : Mem} {p : Ptr} {b : BlockId} {n a : Nat} (hd : m.Dead b)
    (hp : p.block = some b) : m.access p n a = throw .illegal := by
  obtain ⟨blk, hb, hl⟩ := hd
  simp [Mem.access, hp, hb, hl]

/-- A load through a pointer into a dead block never succeeds: it throws `.illegal`
(`access_dead`), a use after free. -/
theorem load_dead {T : Type} [Enc T] {m m' : Mem} {p : Ptr} {b : BlockId} {a : Nat} {v : T}
    (hd : m.Dead b) (hp : p.block = some b) : ((load T a p).run m).run ≠ some (.ok (v, m')) :=
  fun h => by
    obtain ⟨b', blk, o, hacc, -, -, -⟩ := Proto.load_ok h
    obtain ⟨hpb, hblk, hl, -⟩ := access_eq hacc
    obtain ⟨blk', hb', hl'⟩ := hd
    rw [hp, Option.some.injEq] at hpb
    subst hpb
    rw [hb', Option.some.injEq] at hblk
    subst hblk
    rw [hl'] at hl
    cases hl

/-! ## Rules for proofs -/

/-- Thread `t`'s instance of `key` in the thread records `R` (`Mem.tlsInstance` reads only
them). -/
def recInstance (R : Array ThreadRec) (t : ThreadId) (key : BlockId) : Option BlockId :=
  (((((R[t]?).map (·.tls)).getD #[]).find? (·.1 == key))).map (·.2)

theorem Mem.tlsInstance_eq (m : Mem) (t : ThreadId) (key : BlockId) :
    m.tlsInstance t key = recInstance m.threads t key := rfl

/-- A lifted pure step with a known result. -/
theorem TTriple.liftR_ok {α : Type} {r : Result α} {x : α} {P : Assn} (hr : r.run = some (.ok x)) :
    TTriple P (StateT.lift r : MemM α) (fun y => ⌜y = x⌝ ∗ P) :=
  TTriple.of_run fun m hP hF hd hm hp _ ho => by
    refine ⟨x, m, hP, ?_, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, ho, StepIn.refl m _⟩
    rw [show r = pure x from hr]; rfl

/-- `TTriple` for a step that may read the thread records: run by thread `t` with the records
`R`. Every thread triple keeps both (`StepIn.current`, `StepIn.threads`), so a sequence of
them, with `tlsPtr` among them, has one `t` and one `R`. -/
def TTripleIn {α : Type} (t : ThreadId) (R : Array ThreadRec) (P : Assn) (c : MemM α)
    (Q : α → Assn) : Prop :=
  ∀ m hP hF, m.current = t → m.threads = R → Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP →
    m.current < m.clocks.size → m.Owns m.current hP →
    match (c.run m).run with
    | none => True
    | some (.error _) => False
    | some (.ok (v, m')) =>
      ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Owns m'.current hQ ∧
        StepIn hF m m'

namespace TTripleIn

variable {α β : Type} {t : ThreadId} {R : Array ThreadRec} {P P' : Assn} {Q Q' : α → Assn}
  {c : MemM α}

theorem of (h : TTriple P c Q) : TTripleIn t R P c Q :=
  fun m hP hF _ _ hd hm hp hc ho => h m hP hF hd hm hp hc ho

theorem conseq (ht : TTripleIn t R P c Q) (hp : ∀ h, P' h → P h) (hq : ∀ v h, Q v h → Q' v h) :
    TTripleIn t R P' c Q' := by
  intro m hP hF hct hR hd hm hp' hc ho
  have := ht m hP hF hct hR hd hm (hp _ hp') hc ho
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, a, b, c, d, e⟩ := this; exact ⟨hQ, a, b, hq _ _ c, d, e⟩

theorem bind {S : β → Assn} {f : α → MemM β} (hc : TTripleIn t R P c Q)
    (hf : ∀ v, TTripleIn t R (Q v) (f v) S) : TTripleIn t R P (c >>= f) S := by
  intro m hP hF hct hR hd hm hp hcl ho
  have h1 := hc m hP hF hct hR hd hm hp hcl ho
  simp only [StateT.run_bind, ExceptT.run_bind]
  revert h1
  cases (c.run m).run with
  | none => intro; trivial
  | some r =>
    cases r with
    | error e => intro h1; exact h1.elim
    | ok r =>
      obtain ⟨v, m'⟩ := r
      rintro ⟨hQ, hd', hm', hq, ho', hs⟩
      have hcl' : m'.current < m'.clocks.size := by rw [hs.current, hs.size]; exact hcl
      have h2 := hf v m' hQ hF (hs.current.trans hct) (hs.threads.trans hR) hd' hm' hq hcl' ho'
      dsimp only [Bind.bind, Option.bind]
      split at h2
      · trivial
      · exact h2
      · obtain ⟨hS, a, b, c, d, hs'⟩ := h2
        exact ⟨hS, a, b, c, d, hs.trans hs'⟩

theorem lift {φ : Prop} (h : φ → TTripleIn t R P c Q) : TTripleIn t R (⌜φ⌝ ∗ P) c Q := by
  intro m hP hF hct hR hd hm hp hc ho
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m hP hF hct hR hd hm hp hc ho

/-- A step whose post names its result `v`, then the rest. -/
theorem bind_eq {v : α} {P' : Assn} {f : α → MemM β} {S : β → Assn}
    (hc : TTripleIn t R P c (fun r => ⌜r = v⌝ ∗ P')) (hf : TTripleIn t R P' (f v) S) :
    TTripleIn t R P (c >>= f) S :=
  hc.bind fun _ => TTripleIn.lift fun hr => hr ▸ hf

theorem ret (v : α) : TTripleIn t R (Q v) (pure v : MemM α) Q := of (TTriple.ret v)

/-- `tlsPtr` reads only the thread records: the thread's own instance. -/
theorem tlsPtr {key b : BlockId} (hk : recInstance R t key = some b) :
    TTripleIn t R P (Zig.tlsPtr key) (fun r => ⌜r = ⟨some b, 0⟩⌝ ∗ P) := by
  intro m hP hF hct hR hd hm hp _ ho
  have hi : m.tlsInstance m.current key = some b := by
    rw [Mem.tlsInstance_eq, hR, hct]; exact hk
  rw [tlsPtr_run hi]
  exact ⟨hP, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, ho, StepIn.refl m _⟩

end TTripleIn

/-- One new instance: the thread owns a new writable block with the initial bytes. -/
theorem TTriple.tlsAlloc {bs : Array Byte} {a : Nat} (ha : 0 < a) (hn : 0 < bs.size) :
    TTriple emp (tlsAlloc bs a) (fun p => Assn.ex fun A =>
      ⌜p.off = 0 ∧ A % a = 0⌝ ∗ bytesAt p A bs.size .global bs) := by
  unfold Zig.tlsAlloc
  refine (TTriple.alloc .global bs.size a ha).bind fun p =>
    TTriple.ex fun A => TTriple.lift fun ⟨h0, hA⟩ => ?_
  refine (TTriple.storeBytesAt (k := 0) (a := a) bs (by simp [Ptr.add]) hn (by simp)
    (by simp [h0, hA]) (by decide)).bind fun _ => ?_
  rw [writeBytes_all (by simp)]
  exact (TTriple.ret p).conseq (fun h hb => ⟨A, sep_lift.mpr ⟨⟨h0, hA⟩, hb⟩⟩) (fun _ _ h => h)

/-- The instances of a program with one `threadlocal` global. -/
theorem TTriple.tlsAllocs_one {key : BlockId} {bs : Array Byte} {a : Nat} (ha : 0 < a)
    (hn : 0 < bs.size) :
    TTriple emp (tlsAllocs [(key, bs, a)]) (fun ids => Assn.ex fun b => Assn.ex fun A =>
      ⌜ids = #[(key, b)] ∧ A % a = 0⌝ ∗ bytesAt ⟨some b, 0⟩ A bs.size .global bs) := by
  unfold tlsAllocs
  refine (TTriple.tlsAlloc ha hn).bind fun p => TTriple.ex fun A => TTriple.lift fun ⟨h0, hA⟩ => ?_
  simp only [tlsAllocs, pure_bind]
  refine (TTriple.ret _).conseq (fun h hb => ?_) (fun _ _ h => h)
  obtain ⟨b, hpb, -, -⟩ := id hb
  have hp : p = ⟨some b, 0⟩ := by cases p; simp_all
  subst hp
  exact ⟨b, A, sep_lift.mpr ⟨by simp [hA], hb⟩⟩

theorem tlsExit_run_one {m : Mem} {key b : BlockId} (h : m.tlsOf m.current = #[(key, b)]) :
    tlsExit.run m = (free ⟨some b, 0⟩ >>= fun _ => (pure () : MemM Unit)).run m := by
  simp [tlsExit, h, freeBlocks, StateT.run_bind, StateT.run_get]

/-- Thread end with one instance: the thread gives up its block. -/
theorem TTripleIn.tlsExit_one {t : ThreadId} {R : Array ThreadRec} {key b : BlockId} {A S : Nat}
    {K : BlockKind} {bs : Array Byte} {Q : Assn}
    (hR : ((R[t]?).map (·.tls)).getD #[] = #[(key, b)]) (hS : bs.size = S) (hpos : 0 < S) :
    TTripleIn t R (bytesAt ⟨some b, 0⟩ A S K bs ∗ Q) tlsExit (fun _ => Q) := by
  intro m hP hF hct hR' hd hm hp hc ho
  have hreg : m.tlsOf m.current = #[(key, b)] := by
    unfold Mem.tlsOf; rw [hR', hct]; exact hR
  rw [tlsExit_run_one hreg]
  have ht : TTriple (bytesAt ⟨some b, 0⟩ A S K bs ∗ Q)
      (free ⟨some b, 0⟩ >>= fun _ => (pure () : MemM Unit)) (fun _ => Q) :=
    ((TTriple.free hS rfl hpos).frame.conseq (fun _ h => h)
      fun _ _ h => sep_emp.mp (sep_comm h)).bind fun _ => TTriple.ret (Q := fun _ => Q) ()
  exact ht m hP hF hd hm hp hc ho

namespace Conc.Proto

variable {Tgt γ σ α : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}
  {n : Nat} {own : ThreadId → Heap}

/-- `WP.liftMem_owned` for a `TTripleIn`: a step of thread `t` with the thread records `R`. -/
theorem WP.liftMem_ownedIn {x : MemM α} {R : Array ThreadRec} {Pa : Assn} {Qa : α → Assn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : TTripleIn t R Pa x Qa) (ho : Owned own m)
    (hc : m.current = t) (hR : m.threads = R) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' hQ, (x.run m).run = some (.ok (a, m')) → Owned (upd own t hQ) m' → Qa a hQ →
      StepIn (m.heap.diff (own t)) m m' → Q a G m' n) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  obtain ⟨hm, hd⟩ := Heap.diff_split (ho.sub t)
  have hcs : m.current < m.clocks.size := by rw [hc, ho.csize]; exact htl
  have hx := ht m (own t) _ hc hR hd hm hp hcs (hc ▸ ho.owns t htl)
  refine WP.liftMem (fun e he => ?_) fun a m' hr => ?_
  · rw [he] at hx; exact hx.elim
  · rw [hr] at hx
    obtain ⟨hQ, hd', hm', hq, ho', hs⟩ := hx
    have ho'' : m'.Owns t hQ := by rw [hs.current, hc] at ho'; exact ho'
    exact ⟨by rw [hs.threads], h a m' hQ hr (ho.step hc htl hs hm' hd' ho'') hq hs⟩

/-- `tlsPtr` in a concurrent body: the thread's own instance, no memory change. -/
theorem WP.liftM_tlsPtr {key b : BlockId} {s : σ} {Q : Ptr × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (hk : m.tlsInstance m.current key = some b) (h : Q (⟨some b, 0⟩, s) G m n) :
    P.WP t ((_root_.liftM (tlsPtr key) : CM Tgt σ Ptr).run s) Q G m n :=
  WP.liftM (fun e he => by rw [tlsPtr_run hk] at he; cases he) fun a m' hr => by
    rw [tlsPtr_run hk] at hr
    simp only [pure, StateT.pure, ExceptT.run, ExceptT.pure, ExceptT.mk, Option.some.injEq,
      Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, h⟩

/-- The registration of a thread start keeps the threads' parts. -/
theorem _root_.Zig.Owned.setTls {u : ThreadId} {ids : Array (BlockId × BlockId)} (ho : Owned own m) :
    Owned own (m.setTls u ids) :=
  ⟨ho.sub, ho.disj, fun v hv => ho.owns v (by simpa using hv), fun v hv => ho.outside v
    (by simpa using hv), by simpa using ho.csize⟩

theorem _root_.Zig.Conc.joinedB_setTls (m : Mem) (u : ThreadId) (ids : Array (BlockId × BlockId)) :
    joinedB (m.setTls u ids) = joinedB m := by
  funext v
  unfold joinedB Mem.setTls
  simp only [Array.getElem?_modify]
  split
  · rename_i h; subst h; cases m.threads[u]? <;> rfl
  · rfl

/-- The registration of a thread start: only the thread's record changes. -/
theorem WP.liftMem_setTls {ids : Array (BlockId × BlockId)}
    {Q : PUnit → (ThreadId → γ) → Mem → Nat → Prop} (h : Q () G (m.setTls m.current ids) n) :
    P.WP t (ConcM.liftMem (modify fun m : Mem => m.setTls m.current ids) : ConcM Tgt PUnit) Q G m n := by
  refine WP.liftMem (fun e he => ?_) fun a m' hr => ?_
  · have : ((modify fun m : Mem => m.setTls m.current ids : MemM PUnit).run m).run =
        some (.ok ((), m.setTls m.current ids)) := rfl
    rw [this] at he; cases he
  · have e := modify_ok hr
    subst e
    exact ⟨by simp, h⟩

/-- A `MemM` run split at a `bind`. -/
theorem liftMem_bind {β : Type} (x : MemM α) (f : α → MemM β) :
    (ConcM.liftMem (x >>= f) : ConcM Tgt β) = ConcM.liftMem x >>= fun a => ConcM.liftMem (f a) := by
  funext k m₀
  show CoN.leaf ((x >>= f).run m₀) = (CoN.leaf (x.run m₀)).bind _
  rw [StateT.run_bind]
  match hx : (x.run m₀).run with
  | none => rw [show x.run m₀ = ExceptT.mk none from hx]; rfl
  | some (.error e) => rw [show x.run m₀ = ExceptT.mk (some (.error e)) from hx]; rfl
  | some (.ok (a, m₁)) => rw [show x.run m₀ = ExceptT.mk (some (.ok (a, m₁))) from hx]; rfl

end Conc.Proto

end Zig
