import ZigLean.Conc.Lemmas
import ZigLean.Conc.Tls
import ZigLean.Sep.Base.Pts

/-!
# Operational facts about thread-local storage

Identity, initialization and lifetime facts of `ZigLean/Mem/Tls.lean`, independent of heap-only
thread judgments. These facts describe every successful run, including runs whose later access
fails: an instance belongs to its thread and is dead after `tlsExit`.

The full-state thread rules and all-schedules protocols use the same operational facts.
-/

namespace Zig

open Conc Conc.Proto

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

end Zig
