import ZigLean.Conc.Lock

/-!
# The rules of a lock's code

The steps of `Io.Mutex`'s code (`lock`, `unlock`; translated from Zig 0.16.0's std code) and of
`Thread.Mutex`'s code (0.15.2, `FutexImpl`) on the word of a lock `L` (`ZigLean/Conc/Lock.lean`),
proved once for every protocol that has the lock (`Lock.Fits`). `c` is the lock's contended value
(`2` or `3`; `States` gives the values of the generated code):

| Rule | Op | Place before | Place after |
|---|---|---|---|
| `wp_cas` | `cmpxchg(0 → 1)`, acquire | `out` | `holds` (with the resource), or `spin` (read `1`), or `wait` (read `c`) |
| `wp_orLock` | `or(1)`, acquire (`c = 3`) | `out` | `holds` (read `0`, with the resource), or `spin` (read `1` or `3`) |
| `wp_loadLock` | load, relaxed | any but `gone` | the same |
| `Fits.toWait` | (no op) | `spin` | `wait` |
| `wp_xchgLock` | `xchg(c)`, acquire | `spin` | `holds` (read `0`, with the resource), or `wait` |
| `wp_wait` | futex wait for `c` | `wait` | `spin` (it sleeps while the word is `c`) |
| `wp_xchgUnlock` | `xchg(0)`, release | `holds` | `out` (read `1`), or `wake` (read `c`); the lock gets the resource |
| `wp_wake` | futex wake of 1 | `wake` | `out` |

`Thread.Futex.wait`/`wake` and the ops on bits (`atomicRmwC`) are the same ops
(`threadFutexWaitC_eq`, `threadFutexWakeC_eq`, `atomicRmwC_eq`).
Each rule is a stop (the pick of the op, or the futex op) and then the op. It gives the
protocol's invariant with the thread's new place; the rest of the invariant (`U`) stays, by
`Lock.Fits.stable`. In strict mode no op throws, and a futex wait keeps `Live` (`Fits.live`).
The `Lock.Inv` form of each step is `Inv.cas`, `Inv.orLock`, `Inv.load`, `Inv.xchgLock`,
`Inv.wait`, `Inv.xchgUnlock` and `Inv.wake`; the RMW cases under them are `Inv.acquire`,
`Inv.contend`, `Inv.rmwKeep` (the same value again) and `Inv.release`.

The acquire RMW that takes the lock adopts the release clock of the newest message, so the
thread owns the resource (`Lock.Owns`); the release RMW of `unlock` puts the thread's clock in the
new message, so the lock owns it again.
-/

namespace Zig
namespace Conc

open Assn Proto

namespace Lock

variable {γ : Type} {L : Lock γ}

/-! ## The word: access and race check -/

theorem Inv.access {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m) :
    ∃ blk, m.blocks[L.b]? = some blk ∧ blk.live = true ∧ L.o + 4 ≤ blk.bytes.size ∧
      m.access L.ptr 4 4 = pure (L.b, blk, L.o) ∧ m.accessW L.ptr 4 4 = pure (L.b, blk, L.o) := by
  obtain ⟨blk, hb, hl, hs, ha, hk⟩ := hi.blk
  have hacc : m.access L.ptr 4 4 = pure (L.b, blk, L.o) := by
    have := access_of (p := L.ptr) (n := 4) (a := 4) (m := m) rfl hb hl (by simp [Lock.ptr])
      (by simp only [Lock.ptr]; omega) (by simpa [Lock.ptr] using ha)
    simpa [Lock.ptr] using this
  refine ⟨blk, hb, hl, hs, hacc, ?_⟩
  unfold Mem.accessW; rw [hacc]
  simp [hk, pure, bind, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.bindCont]

/-- An atomic access to the word does not race. -/
theorem Inv.noRace {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m) {k : AccessKind}
    (hk : k.isAtomic = true) (ht : m.current < m.threads.size)
    (hg : L.ph (G m.current) ≠ .gone) : NoRace m L.b L.o 4 k := by
  refine noRace_of fun e he hb h1 h2 => ?_
  rcases hi.wfp e he (hits_of hb h1 h2) with ⟨ha, -⟩ | h
  · refine .inr ?_; unfold racePair; simp [ha, hk]
  · exact .inl (h _ ht hg)

/-- The word as the block's bytes. -/
theorem u32_bytes {m : Mem} {blk : Block} {v : BitVec 32} (hb : m.blocks[L.b]? = some blk) :
    L.U32 m v ↔ (intOfBytes 32 (blk.bytes.extract L.o (L.o + 4))).run = some (.ok v) := by
  unfold Lock.U32 curBytes; rw [hb]; rfl

theorem u32_eq {m : Mem} {a b : BitVec 32} (ha : L.U32 m a) (hb : L.U32 m b) : a = b := by
  unfold Lock.U32 at ha hb; rw [ha] at hb; cases hb; rfl

theorem ofNat_inj {a b : Nat} (ha : a < 4) (hb : b < 4)
    (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- The word is `w` (`< 3`): a thread holds the lock iff `w ≠ 0`. -/
theorem Inv.free_iff {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m) {w : Nat} (hw : L.Val w)
    (hu : L.U32 m (BitVec.ofNat 32 w)) : w = 0 ↔ L.Free G := by
  obtain ⟨w₀, hw₀, hu₀, hz⟩ := hi.word
  have e := ofNat_inj hw₀.lt hw.lt (u32_eq hu₀ hu)
  subst e; exact hz

/-! ## A step in the lock's code -/

/-- A clock below one that happened before the newest message of the word. -/
theorem before_le {m : Mem} {c c' : VClock} (h : L.Before m c') (hle : VClock.le c c' = true) :
    L.Before m c := by
  obtain ⟨i, l, hl, h'⟩ := h; exact ⟨i, l, hl, VClock.le_trans hle h'⟩

theorem Step.clocks {t : ThreadId} {m m' : Mem} (hs : L.Step t m m') (u : Nat) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  by_cases hu : u = t
  · subst hu; exact hs.mine
  · rw [hs.others u hu]; exact VClock.le_refl _

theorem Step.allLe {t : ThreadId} {m m' : Mem} {c : VClock} (hs : L.Step t m m')
    (h : AllLe m c) : AllLe m' c :=
  allLe_mono hs.threads (fun u _ => hs.clocks u) h

theorem Step.liveLe {G G' : ThreadId → γ} {t : ThreadId} {m m' : Mem} {c : VClock}
    (hs : L.Step t m m') (hg : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone)
    (h : L.LiveLe G m c) : L.LiveLe G' m' c :=
  (LiveLe.mono hs.threads (fun u _ => hs.clocks u) h).weaken hg

theorem Step.someLe {t : ThreadId} {m m' : Mem} {c : VClock} (hs : L.Step t m m')
    (h : SomeLe m c) : SomeLe m' c :=
  someLe_mono hs.threads (fun u _ => hs.clocks u) h

theorem Step.trans {t : ThreadId} {m₁ m₂ m₃ : Mem} (h₁ : L.Step t m₁ m₂) (h₂ : L.Step t m₂ m₃)
    (hb : m₂.blocks = m₁.blocks ∨ m₃.blocks = m₂.blocks) : L.Step t m₁ m₃ := by
  refine ⟨h₂.threads.trans h₁.threads, fun e he => ?_, h₂.groups.trans h₁.groups,
    h₂.csize.trans h₁.csize,
    fun u hu => (h₂.others u hu).trans (h₁.others u hu), VClock.le_trans h₁.mine h₂.mine,
    h₂.bsize.trans h₁.bsize, ?_, fun w hw => (h₂.waiters w hw).trans (h₁.waiters w hw),
    fun c h => h₂.before c (h₁.before c h), h₁.locs.trans h₂.locs, fun e he => ?_⟩
  rotate_right
  · rcases h₂.fpt e he with h | h
    · rcases h₁.fpt e h with h' | ⟨ht, hle⟩
      · exact .inl h'
      · exact .inr ⟨ht, VClock.le_trans hle h₂.mine⟩
    · exact .inr h
  · rcases h₂.fp e he with h | h
    · rcases h₁.fp e h with h' | ⟨a, b, c, d, f⟩
      · exact .inl h'
      · exact .inr ⟨a, b, c, d, h₂.someLe f⟩
    · exact .inr h
  rcases hb with hb | hb
  · rcases h₂.blocks with e | ⟨blk, bs, h1, h2, h3, h4, h5⟩
    · exact .inl (e.trans hb)
    · refine .inr ⟨blk, bs, by rw [← hb]; exact h1, h2, h3, h4, ?_⟩
      rw [h5]; simp only [Mem.write, hb]
  · rcases h₁.blocks with e | ⟨blk, bs, h1, h2, h3, h4, h5⟩
    · exact .inl (hb.trans e)
    · exact .inr ⟨blk, bs, h1, h2, h3, h4, hb.trans h5⟩

/-- The heap after a step in the lock's code: the same, but at the word. -/
theorem Step.heap {t : ThreadId} {m m' : Mem} (hs : L.Step t m m') {l : Zig.Loc}
    (hl : ¬ (l.1 = L.b ∧ L.o ≤ l.2 ∧ l.2 < L.o + 4)) : m'.heap l = m.heap l := by
  rcases hs.blocks with e | ⟨blk, bs, h1, h2, h3, h4, h5⟩
  · obtain ⟨b, x⟩ := l; simp only [Mem.heap, e]
  · have : m'.heap l = (m.write L.b blk L.o bs).heap l := by
      obtain ⟨b, x⟩ := l; simp only [Mem.heap, h5]
    rw [this, Mem.heap_write h1 h2 (by omega)]
    rw [h3]; simp only [hl, ↓reduceIte]

/-- A step in the lock's code keeps the threads' parts, which have no byte of the word, if each
new access is atomic, at the word. -/
theorem Step.owned {t : ThreadId} {m m' : Mem} {own : ThreadId → Heap} (hs : L.Step t m m')
    (ho : Owned own m) (hoff : ∀ u, L.Off (own u)) (hbl : L.b < m.blocks.size)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.block = L.b ∧ e.off = L.o ∧ e.len = 4)) :
    Owned own m' := by
  refine ho.keep (by rw [hs.threads]) hs.csize
    (fun u l c hc => ?_) (Nat.le_of_eq hs.bsize.symm) (fun u _ => hs.clocks u) (fun e he => ?_)
  · have hw : ¬ (l.1 = L.b ∧ L.o ≤ l.2 ∧ l.2 < L.o + 4) := by
      rintro ⟨h1, h2, h3⟩
      obtain ⟨b, x⟩ := l; simp only at h1 h2 h3; subst h1
      rw [hoff u x h2 h3] at hc; cases hc
    rw [hs.heap hw]; exact ho.sub u l c hc
  · rcases hfp e he with h | ⟨hb, ho', hl⟩
    · exact .inl h
    · refine .inr ⟨by rw [hb, hs.bsize]; exact hbl, fun u ⟨x, h1, h2, h3⟩ => ?_⟩
      rw [hb] at h3; rw [ho'] at h1 h2; rw [hl] at h2
      exact h3 (hoff u x h1 (by omega))

/-! ## Changes that keep the blocks and the locations -/

/-- A new access that touches no part; it touches no resource and, if it hits the word, is
atomic, or it happened before each thread that has not ended. -/
def NewOk (G : ThreadId → γ) (m m' : Mem) (e : FootprintEntry) : Prop :=
  e.block < m.blocks.size ∧ (∀ u, ¬ e.Touches (L.own G m u)) ∧
    ((∀ hL, L.R G hL → L.Off hL → ¬ e.Touches hL) ∨ L.LiveLe G m' e.clock) ∧
    (L.Hits e → (e.kind.isAtomic = true ∧ SomeLe m' e.clock) ∨ L.LiveLe G m' e.clock)

/-- A memory with the same blocks, threads, atomic locations and futex queue, clocks that are not
smaller, and new accesses that keep `NewOk`. -/
theorem Inv.mono {G : ThreadId → γ} {m m' : Mem} (hi : L.Inv G m) (ht : m'.threads = m.threads)
    (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics) (hw : m'.waiters = m.waiters)
    (hcs : m'.clocks.size = m.clocks.size)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ L.NewOk G m m' e) : L.Inv G m' := by
  have hjb : joinedB m' = joinedB m := joinedB_congr ht
  have hown : L.own G m' = L.own G m := by funext u; unfold Lock.own; rw [hjb]
  have hheap : m'.heap = m.heap := by funext l; obtain ⟨b, x⟩ := l; simp only [Mem.heap, hb]
  have hcur : curBytes m' L.b L.o 4 = curBytes m L.b L.o 4 := curBytes_congr hb _ _ _
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold Lock.U32; rw [hcur]
  have hloc : ∀ i l, L.Loc m' i l ↔ L.Loc m i l := fun i l => by unfold Lock.Loc; rw [ha]
  have hall : ∀ {c}, L.LiveLe G m c → L.LiveLe G m' c := fun h => LiveLe.mono ht (fun u _ => hcl u) h
  have hsome : ∀ {c}, SomeLe m c → SomeLe m' c := fun h => someLe_mono ht (fun u _ => hcl u) h
  refine ⟨?_, hi.pdisj, hi.idle, fun u hu => ?_, by rw [hb]; exact hi.blk, ?_, hi.one,
    ⟨fun l hl => hi.loc.only l (ha ▸ hl), fun i l hl => ?_⟩, fun u => hown ▸ hi.off u,
    fun e he hh => ?_, fun i l hl => ?_, fun hF => ?_, hi.res, by rw [hw]; exact hi.fq,
    fun hp => ?_⟩
  · rw [hown]
    refine hi.own.keep (by rw [ht]) hcs (fun u => hheap ▸ hi.own.sub u)
      (Nat.le_of_eq (by rw [hb])) (fun u _ => hcl u) (fun e he => ?_)
    rcases hfp e he with h' | ⟨hbl, hno, -⟩
    · exact .inl h'
    · exact .inr ⟨by rw [hb]; exact hbl, hno⟩
  · rw [ht, hjb]; exact hi.live u hu
  · obtain ⟨w, hw', hu, hz⟩ := hi.word; exact ⟨w, hw', (hU32 _).mpr hu, hz⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hi.loc.ok i l ((hloc i l).mp hl)
    exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
  · rcases hfp e he with h' | ⟨-, -, -, hat⟩
    · rcases hi.wfp e h' hh with ⟨hat', hle'⟩ | hle'
      · exact .inl ⟨hat', hsome hle'⟩
      · exact .inr (hall hle')
    · exact hat hh
  · obtain ⟨h1, h2⟩ := hi.rel i l ((hloc i l).mp hl)
    exact ⟨hsome h1, fun u hu => VClock.le_trans (h2 u hu) (hcl u)⟩
  · obtain ⟨hL, hR, hsub, hdj, hoff, how⟩ := hi.free hF
    refine ⟨hL, hR, hheap ▸ hsub, fun u => hown ▸ hdj u, hoff, fun e he htc => ?_⟩
    rcases hfp e he with h' | ⟨hbl, -, hnR, -⟩
    · rcases how e h' (by rw [← hb]; exact htc) with h | ⟨i, l, hl, hle⟩
      · exact .inl (hall h)
      · exact .inr ⟨i, l, (hloc i l).mpr hl, hle⟩
    · rcases hnR with hnR | hle
      · rcases htc with htc | hb'
        · exact absurd htc (hnR hL hR hoff)
        · rw [hb] at hb'; exact absurd hbl (Nat.not_lt.mpr hb')
      · exact .inl hle
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (hw ▸ hp)
    exact ⟨v, ht ▸ hv, hw ▸ hq, h1, fun hh => (hU32 _).mpr (h2 hh)⟩

theorem recordAt_le (m : Mem) (b o n : Nat) (k : AccessKind) (u : Nat) :
    VClock.le (m.clocks[u]!) ((m.recordAt b o n k).clocks[u]!) = true := by
  simp only [Mem.recordAt]; rw [getElem!_set!_ite]
  split
  · rename_i h; rw [h.1]; exact VClock.le_bump _ _
  · exact VClock.le_refl _

/-- The record of an atomic access to the word by the current thread. -/
theorem Inv.record {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m) {k : AccessKind}
    (hk : k.isAtomic = true) (ht : m.current < m.threads.size) :
    L.Inv G (m.recordAt L.b L.o 4 k) := by
  have hcs : m.current < m.clocks.size := by rw [hi.own.csize]; exact ht
  obtain ⟨blk, hblk, -⟩ := hi.blk
  refine hi.mono rfl rfl rfl rfl (by simp [Mem.recordAt]) (recordAt_le m _ _ _ _) fun e he => ?_
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · refine .inr ⟨(Array.getElem?_eq_some_iff.mp hblk).1, fun u ⟨x, h1, h2, h3⟩ => ?_,
      .inl fun hL _ hoff ⟨x, h1, h2, h3⟩ => ?_, fun _ => .inl ⟨hk, m.current, ht, ?_⟩⟩
    · dsimp only at h1 h2 h3; exact h3 (hi.off u x h1 (by omega))
    · dsimp only at h1 h2 h3; exact h3 (hoff x h1 (by omega))
    · simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]

/-- Recording an atomic access to the word is a lock step, without changing its messages. -/
theorem Inv.recordStep {G : ThreadId → γ} {m : Mem} {t : ThreadId} {k : AccessKind}
    (hi : L.Inv G m) (hc : m.current = t) (ht : t < m.threads.size)
    (hk : k.isAtomic = true) : L.Step t m (m.recordAt L.b L.o 4 k) := by
  have hcs : t < m.clocks.size := by rw [hi.own.csize]; exact ht
  refine ⟨rfl, fun e he => ?_, rfl, by simp [Mem.recordAt], ?_, ?_, rfl, .inl rfl,
    fun _ _ => Iff.rfl, fun _ h => h, .of_eq rfl, fun e he => ?_⟩
  · simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨rfl, rfl, rfl, hk, t, ht, ?_⟩
      simp only [Mem.recordAt, hc]
      rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]
  · intro u hu
    simp only [Mem.recordAt, hc]
    rw [getElem!_set!_ite, if_neg (fun h => hu h.1)]
  · simp only [Mem.recordAt, hc]
    rw [getElem!_set!_ite]; simp [hcs, VClock.le_bump]
  · simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨hc, ?_⟩
      simp only [Mem.recordAt, hc]
      rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]

/-- A plain read by the current thread of `n` bytes at `o` of block `b` that no part, no resource
and not the word has. -/
theorem Inv.read {G : ThreadId → γ} {m : Mem} {b o n : Nat} (hi : L.Inv G m)
    (hb : b < m.blocks.size) (hn : 0 < n)
    (hno : ∀ u x, o ≤ x → x < o + n → L.own G m u (b, x) = none)
    (hnR : ∀ hL, L.R G hL → ∀ x, o ≤ x → x < o + n → hL (b, x) = none)
    (hnw : b ≠ L.b ∨ o + n ≤ L.o ∨ L.o + 4 ≤ o) :
    L.Inv G (m.recordAt b o n .read) := by
  refine hi.mono rfl rfl rfl rfl (by simp [Mem.recordAt]) (recordAt_le m _ _ _ _) fun e he => ?_
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · refine .inr ⟨hb, fun u ⟨x, h1, h2, h3⟩ => ?_, .inl fun hL hR _ ⟨x, h1, h2, h3⟩ => ?_,
      fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_⟩
    · dsimp only at h1 h2 h3; exact h3 (hno u x h1 (by omega))
    · dsimp only at h1 h2 h3; exact h3 (hnR hL hR x h1 (by omega))
    · exfalso
      dsimp only at hb' h1 h2
      rcases hnw with h | h | h
      · exact h hb'
      · rcases h2 with h2 | h2 <;> omega
      · rcases h2 with h2 | h2 <;> omega

/-- A plain read by the current thread, the only thread that has not ended, of `n` bytes at
`o` of block `b` that no part has: it can read the word and the resource. The caller shows that
the read does not race. -/
theorem Inv.readAll {G : ThreadId → γ} {m : Mem} {b o n : Nat} (hi : L.Inv G m)
    (hb : b < m.blocks.size) (hn : 0 < n) (ht : m.current < m.threads.size)
    (hsole : ∀ u < m.threads.size, u ≠ m.current → L.ph (G u) = .gone)
    (hno : ∀ u x, o ≤ x → x < o + n → L.own G m u (b, x) = none) :
    L.Inv G (m.recordAt b o n .read) := by
  have hcs : m.current < m.clocks.size := by rw [hi.own.csize]; exact ht
  have hle : L.LiveLe G (m.recordAt b o n .read) (VClock.bump (m.clocks[m.current]!) m.current) := by
    intro u hu hg
    simp only [Mem.recordAt] at hu ⊢
    by_cases hu' : u = m.current
    · subst hu'; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]
    · exact absurd (hsole u hu hu') hg
  refine hi.mono rfl rfl rfl rfl (by simp [Mem.recordAt]) (recordAt_le m _ _ _ _) fun e he => ?_
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · refine .inr ⟨hb, fun u ⟨x, h1, h2, h3⟩ => ?_, .inr hle, fun _ => .inr hle⟩
    dsimp only at h1 h2 h3; exact h3 (hno u x h1 (by rcases h2 with h2 | h2 <;> omega))

/-! ## The word's atomic location -/

theorem loc_get {m : Mem} {i : Nat} {l : ALoc} (hl : L.Loc m i l) :
    ∃ h : i < m.atomics.size, m.atomics[i] = l ∧ m.atomics[i]! = l := by
  obtain ⟨h, e⟩ := Array.getElem?_eq_some_iff.mp hl.2
  exact ⟨h, e, by rw [getElem!_pos m.atomics i h, e]⟩

theorem loc_unique {m : Mem} {i j : Nat} {l l' : ALoc} (hl : L.Loc m i l) (hl' : L.Loc m j l') :
    i = j ∧ l = l' := by
  have e : i = j := by have := hl.1; rw [hl'.1] at this; cases this; rfl
  subst e
  have := hl.2; rw [hl'.2] at this; cases this; exact ⟨rfl, rfl⟩

theorem loc_at {m : Mem} {i : Nat} {l : ALoc} (hl : L.Loc m i l) : l.block = L.b ∧ l.off = L.o := by
  obtain ⟨hi', hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hl.1
  obtain ⟨h, e, -⟩ := loc_get hl
  rw [e] at hp
  simpa using hp

/-- The location after a change of location `i` that keeps its block and offset. -/
theorem loc_set {m m' : Mem} {i : Nat} {l l' : ALoc} (hl : L.Loc m i l)
    (ha : m'.atomics = m.atomics.set! i l') (hb : l'.block = l.block) (ho : l'.off = l.off) :
    L.Loc m' i l' := by
  obtain ⟨hi', hp, hj⟩ := Array.findIdx?_eq_some_iff_getElem.mp hl.1
  obtain ⟨hlb, hlo⟩ := loc_at hl
  have hs : (m.atomics.set! i l').size = m.atomics.size := by simp
  refine ⟨Array.findIdx?_eq_some_iff_getElem.mpr ⟨by rw [ha, hs]; exact hi', ?_, fun j hji => ?_⟩, ?_⟩
  · simp only [ha, Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds, ↓reduceIte]
    simp [hb, ho, hlb, hlo]
  · simp only [ha, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by omega), if_neg (Nat.ne_of_gt hji)]
    exact hj j hji
  · rw [ha, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [hi']

/-- The word's location after `locIdx`: the memory is the same, or it has a new location (the
first atomic op at the word). -/
theorem Inv.locIdx {G : ThreadId → γ} {m m₁ : Mem} {li : Nat} (hi : L.Inv G m)
    (ht : m.current < m.threads.size)
    (h : ((locIdx L.b L.o 4).run m).run = some (.ok (li, m₁))) :
    ∃ l, L.Loc m₁ li l ∧ L.Inv G m₁ ∧ m₁.blocks = m.blocks ∧ m₁.clocks = m.clocks ∧
      m₁.threads = m.threads ∧ m₁.footprint = m.footprint ∧ m₁.waiters = m.waiters ∧
      m₁.current = m.current ∧ m₁.groups = m.groups ∧ (∀ i l, L.Loc m i l → L.Loc m₁ i l) ∧
      LocsKeep L.b L.o 4 m m₁ := by
  cases hf : m.atomics.findIdx? (fun l => l.block == L.b && l.off == L.o) with
  | some i =>
    obtain ⟨hi', -, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    have hl : L.Loc m i m.atomics[i] := ⟨hf, Array.getElem?_eq_getElem hi'⟩
    obtain ⟨hlen, -, -, -, hlast⟩ := hi.loc.ok i _ hl
    have hg : m.atomics[i]! = m.atomics[i] := getElem!_pos m.atomics i hi'
    obtain ⟨rfl, rfl⟩ := locIdx_found hf (by rw [hg]; exact hlen) (by rw [hg]; exact hlast) h
    exact ⟨_, hl, hi, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h, .of_eq rfl⟩
  | none =>
    obtain ⟨rfl, rfl⟩ := locIdx_new hf h
    have hno : ∀ i l, ¬ L.Loc m i l := fun i l hl => by rw [hl.1] at hf; cases hf
    let nl : ALoc := firstLoc m L.b L.o 4
    have hnl : L.Loc { m with atomics := m.atomics.push nl, nextMsg := m.nextMsg + 1 }
        m.atomics.size nl := by
      refine ⟨?_, by simp⟩
      show (m.atomics.push nl).findIdx? _ = _
      rw [Array.findIdx?_push, hf]; simp [nl, firstLoc]
    have honly : ∀ i l, L.Loc { m with atomics := m.atomics.push nl, nextMsg := m.nextMsg + 1 }
        i l → i = m.atomics.size ∧ l = nl := fun i l hl => loc_unique hl hnl
    refine ⟨nl, hnl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun i l h => absurd h (hno i l),
      .push rfl rfl rfl rfl⟩
    obtain ⟨w, hw, hu, -⟩ := hi.word
    exact ⟨⟨hi.own.sub, hi.own.disj, hi.own.owns, hi.own.outside, hi.own.csize⟩, hi.pdisj,
      hi.idle, hi.live, hi.blk, hi.word, hi.one,
      ⟨fun l hl hb h1 h2 => by
        rcases Array.mem_push.mp hl with hl | rfl
        · exact hi.loc.only l hl hb h1 h2
        · rfl,
       fun i l hl => by
        obtain ⟨rfl, rfl⟩ := honly i l hl
        refine ⟨rfl, by simp [nl, firstLoc], fun j hj => by simp [nl, firstLoc] at hj,
          fun j hj => ?_, ?_⟩
        · simp only [nl, firstLoc, List.size_toArray, List.length_cons, List.length_nil] at hj
          obtain rfl : j = 0 := by omega
          exact ⟨w, hw, hu⟩
        · simp [ALoc.lastBytes, nl, firstLoc, firstMsg, curBytes]⟩,
      hi.off, hi.wfp,
      fun i l hl => by
        obtain ⟨rfl, rfl⟩ := honly i l hl
        exact ⟨⟨m.current, ht, VClock.le_default _⟩, fun u _ => VClock.le_default _⟩,
      fun hF => by
        obtain ⟨hL, hR, hsub, hdj, hoff, how⟩ := hi.free hF
        refine ⟨hL, hR, hsub, hdj, hoff, fun e he htc => ?_⟩
        rcases how e he htc with h' | ⟨i, l, hl, -⟩
        · exact .inl h'
        · exact absurd hl (hno i l),
      hi.res, hi.fq, hi.wit⟩

/-! ## The memory after an RMW at the word -/

/-- An RMW at the word that read its newest message `rd` and wrote `new`. -/
theorem rmw_eff {m₁ m₂ M : Mem} {li : Nat} {l : ALoc} {ord : AtomicOrder} {rd : Msg}
    {new : BitVec 32} {blk : Block} (hl : L.Loc m₁ li l) (h0 : 0 < l.msgs.size)
    (hb : m₁.blocks[L.b]? = some blk) (hm₂ : m₂ = if ord.isAcq then acqM m₁ rd.relClock else m₁)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) ord rd new) :
    M.threads = m₁.threads ∧ M.footprint = m₁.footprint ∧ M.waiters = m₁.waiters ∧
      M.groups = m₁.groups ∧ M.current = m₁.current ∧ M.clocks = m₂.clocks ∧
      M.blocks = (m₁.write L.b blk L.o (padTo (intSize 32) (intBytes new))).blocks ∧
      M.atomics = m₁.atomics.set! li { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) } := by
  obtain ⟨h, -, hl0⟩ := loc_get hl
  obtain ⟨hlb, hlo⟩ := loc_at hl
  have h2 : m₂.atomics = m₁.atomics ∧ m₂.blocks = m₁.blocks ∧ m₂.threads = m₁.threads ∧
      m₂.footprint = m₁.footprint ∧ m₂.waiters = m₁.waiters ∧ m₂.current = m₁.current ∧
      m₂.groups = m₁.groups := by
    subst hm₂; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨ha₂, hb₂, ht₂, hf₂, hw₂, hc₂, hg₂⟩ := h2
  have hl₂ : m₂.atomics[li]! = l := by rw [ha₂]; exact hl0
  have hblk₂ : m₂.blocks[(m₂.atomics[li]!).block]? = some blk := by rw [hl₂, hlb, hb₂]; exact hb
  have hins := insertM_last (msg := rmwMsg m₂ ord rd new) hblk₂
  rw [hl₂] at hins
  have hp : l.msgs.size - 1 + 1 = l.msgs.size := by omega
  subst hM
  unfold rmwM
  rw [← hm₂, hp]
  dsimp only
  rw [hins]
  refine ⟨ht₂, hf₂, hw₂, hg₂, hc₂, rfl, ?_, ?_⟩
  · simp only [observeM, Mem.write, hlb, hlo, hb₂]; rfl
  · simp only [observeM, ha₂]

/-! ## The invariant after an RMW at the word -/

theorem merge_le {a b c : VClock} (ha : VClock.le a c = true) (hb : VClock.le b c = true) :
    VClock.le (VClock.merge a b) c = true :=
  VClock.le_iff.mpr fun i => by
    rw [VClock.get_merge]
    have h1 := VClock.le_iff.mp ha i
    have h2 := VClock.le_iff.mp hb i
    simp only [Nat.max_def]; split <;> omega

theorem bs4 (v : BitVec 32) : (padTo (intSize 32) (intBytes v)).size = 4 :=
  LawfulEnc.size_encode (α := BitVec 32) v

theorem back_push (xs : Array Msg) (x : Msg) : (xs.push x).back! = x := by
  rw [Array.back!, getElem!_pos _ _ (by simp)]
  simp

/-- The memory `M` after an RMW at the word by thread `t` that read the newest message of `l`
and wrote the message `msg` with the value `w'`: the invariant with the ghost values `G'`, from
the facts that depend on them. -/
theorem Inv.rmw {G G' : ThreadId → γ} {m₁ M : Mem} {t : ThreadId} {li : Nat} {l : ALoc}
    {msg : Msg} {blk : Block} {w' : Nat} (hi : L.Inv G m₁) (hl : L.Loc m₁ li l)
    (hb : m₁.blocks[L.b]? = some blk) (hst : L.Step t m₁ M)
    (hblocks : M.blocks = (m₁.write L.b blk L.o msg.bytes).blocks)
    (hat : M.atomics = m₁.atomics.set! li { l with msgs := l.msgs.push msg })
    (hwq : M.waiters = m₁.waiters)
    (hmr : msg.rmwOf = some (l.msgs[l.msgs.size - 1]!).id) (hms : msg.bytes.size = 4)
    (hw' : L.Val w') (hmv : (intOfBytes 32 msg.bytes).run = some (.ok (BitVec.ofNat 32 w')))
    (hown : Owned (L.own G' M) M)
    (hpdisj : ∀ u, Heap.Disjoint (L.part (G' u)) (L.held (G' u)))
    (hidle : ∀ u, L.ph (G' u) ≠ .holds → L.held (G' u) = Heap.empty)
    (hlive : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone)
    (hz : w' = 0 ↔ L.Free G') (hone : ∀ u v, L.ph (G' u) = .holds → L.ph (G' v) = .holds → u = v)
    (hoff : ∀ u, L.Off (L.own G' M u))
    (hrel : SomeLe M msg.relClock ∧
      ∀ u, L.ph (G' u) = .holds → VClock.le msg.relClock (M.clocks[u]!) = true)
    (hfree : L.Free G' → ∃ hL, L.R G' hL ∧ hL.Sub M.heap ∧
      (∀ u, Heap.Disjoint hL (L.own G' M u)) ∧ L.Off hL ∧ L.Owns G' M hL)
    (hres : ∀ u, L.ph (G' u) = .holds → L.R G' (L.held (G' u)))
    (hfq : L.Queue G' M.waiters)
    (hwit : L.U32 M (BitVec.ofNat 32 w') → L.Waits M.waiters → ∃ v, v < M.threads.size ∧
      M.waiters.any (·.1 == v) = false ∧ (L.ph (G' v)).busy = true ∧
      (L.ph (G' v) = .holds → L.U32 M (BitVec.ofNat 32 L.c))) :
    L.Inv G' M := by
  obtain ⟨blk₀, hb₀, hlv, hsz, ha4, hk⟩ := hi.blk
  rw [hb] at hb₀; cases hb₀
  obtain ⟨hlen, h0, hch, hval, -⟩ := hi.loc.ok li l hl
  obtain ⟨hlb, hlo⟩ := loc_at hl
  have hli : li < m₁.atomics.size := (loc_get hl).1
  let l' : ALoc := { l with msgs := l.msgs.push msg }
  have hl' : L.Loc M li l' := loc_set hl hat rfl rfl
  have hMb : M.blocks[L.b]? = some { blk with bytes := writeBytes blk.bytes L.o msg.bytes } := by
    rw [hblocks]; simp only [Mem.write]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
      (Array.getElem?_eq_some_iff.mp hb).1]
  have hcur : curBytes M L.b L.o 4 = msg.bytes := by
    unfold curBytes; rw [hMb]
    simp only [Option.map_some, Option.getD_some]
    have := extract_writeBytes blk.bytes L.o msg.bytes (by omega)
    rwa [hms] at this
  have hU : L.U32 M (BitVec.ofNat 32 w') := by unfold Lock.U32; rw [hcur]; exact hmv
  have hjb : joinedB M = joinedB m₁ := joinedB_congr hst.threads
  have honly : ∀ i l₀, L.Loc M i l₀ → i = li ∧ l₀ = l' := fun i l₀ h => loc_unique h hl'
  refine ⟨hown, hpdisj, hidle, fun u hu => ?_, ?_, ⟨w', hw', hU, hz⟩, hone, ⟨fun l₀ hl₀ hb' h1 h2 => ?_,
    fun i l₀ hl₀ => ?_⟩, hoff, fun e he hh => ?_, fun i l₀ hl₀ => ?_, hfree, hres, hfq, hwit hU⟩
  · rw [hst.threads, hjb]; exact hi.live u (hlive u hu)
  · refine ⟨_, hMb, hlv, ?_, ha4, hk⟩
    show L.o + 4 ≤ (writeBytes blk.bytes L.o msg.bytes).size
    rw [writeBytes_size _ _ _ (by omega)]; exact hsz
  · rw [hat, Array.set!_eq_setIfInBounds] at hl₀
    rcases Array.mem_or_eq_of_mem_set (w := hli) (by simpa [Array.setIfInBounds, hli] using hl₀)
      with h | rfl
    · exact hi.loc.only l₀ h hb' h1 h2
    · exact hlo
  · obtain ⟨rfl, rfl⟩ := honly i l₀ hl₀
    refine ⟨hlen, by simp [l'], hch.push h0 hmr, fun j hj => ?_, ?_⟩
    · simp only [l', Array.size_push] at hj
      simp only [l', Array.getElem_push]
      split
      · exact hval j (by assumption)
      · exact ⟨w', hw', hmv⟩
    · unfold ALoc.lastBytes; simp [l', hcur]
  · rcases hst.fp e he with h | ⟨-, -, -, hat', hle⟩
    · rcases hi.wfp e h hh with ⟨ha', hle⟩ | hle
      · exact .inl ⟨ha', hst.someLe hle⟩
      · exact .inr (hst.liveLe hlive hle)
    · exact .inl ⟨hat', hle⟩
  · obtain ⟨rfl, rfl⟩ := honly i l₀ hl₀
    simp only [l', back_push]
    exact hrel

/-- The facts of an RMW at the word by thread `t` that read the newest message `rd`. -/
theorem Inv.rmwStep {G : ThreadId → γ} {m₁ M : Mem} {t li : Nat} {l : ALoc} {ord : AtomicOrder}
    {new : BitVec 32} (hi : L.Inv G m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t)
    (ht : t < m₁.threads.size)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) ord (l.msgs[l.msgs.size - 1]!) new) :
    ∃ blk m₂, m₁.blocks[L.b]? = some blk ∧
      m₂ = (if ord.isAcq then acqM m₁ (l.msgs[l.msgs.size - 1]!).relClock else m₁) ∧
      L.Step t m₁ M ∧ M.current = t ∧ M.waiters = m₁.waiters ∧ M.clocks = m₂.clocks ∧
      M.blocks = (m₁.write L.b blk L.o (rmwMsg m₂ ord (l.msgs[l.msgs.size - 1]!) new).bytes).blocks ∧
      M.atomics = m₁.atomics.set! li
        { l with msgs := l.msgs.push (rmwMsg m₂ ord (l.msgs[l.msgs.size - 1]!) new) } := by
  obtain ⟨blk, hb, hlv, hsz, -, -⟩ := hi.blk
  obtain ⟨-, h0, -⟩ := hi.loc.ok li l hl
  obtain ⟨hth, hfp, hwq, hg, hcur, hcl, hbl, hat⟩ := rmw_eff (new := new) hl h0 hb rfl hM
  have hcs : m₁.current < m₁.clocks.size := by rw [hi.own.csize, hc]; exact ht
  have hm₂ : ∀ m₂ : Mem, m₂ = (if ord.isAcq then acqM m₁ (l.msgs[l.msgs.size - 1]!).relClock
      else m₁) → m₂.clocks.size = m₁.clocks.size ∧ (∀ u, u ≠ t → m₂.clocks[u]! = m₁.clocks[u]!) ∧
      VClock.le (m₁.clocks[t]!) (m₂.clocks[t]!) = true := by
    intro m₂ e; subst e
    split
    · refine ⟨by simp [acqM], fun u hu => ?_, ?_⟩
      · simp only [acqM]; rw [getElem!_set!_ite, if_neg (fun h => hu (h.1.trans hc))]
      · rw [← hc, acqM_clock _ _ hcs]; exact VClock.le_merge_left _ _
    · exact ⟨rfl, fun _ _ => rfl, VClock.le_refl _⟩
  obtain ⟨hs1, hs2, hs3⟩ := hm₂ _ rfl
  refine ⟨blk, _, hb, rfl, ⟨hth, fun e he => .inl (hfp ▸ he), hg, by rw [hcl, hs1],
    fun u hu => by rw [hcl, hs2 u hu], by rw [hcl]; exact hs3, by rw [hbl]; simp [Mem.write],
    .inr ⟨blk, _, hb, hlv, bs4 new, hsz, hbl⟩, fun _ _ => by rw [hwq],
    fun c ⟨i, l₀, hl₀, hle⟩ => ?_, LocsKeep.set hl.2 (loc_at hl).1 (loc_at hl).2
      (by exact (loc_at hl).1) (by exact (loc_at hl).2) (by exact (hi.loc.ok li l hl).1) hat,
    fun e he => .inl (hfp ▸ he)⟩, hcur.trans hc, hwq, hcl, hbl, hat⟩
  obtain ⟨rfl, rfl⟩ := loc_unique hl hl₀
  refine ⟨_, _, loc_set hl hat rfl rfl, ?_⟩
  have hbk : l.msgs.back! = l.msgs[l.msgs.size - 1]! := rfl
  simp only [back_push, rmwMsg]
  rw [hbk] at hle
  split
  · exact VClock.le_trans hle (VClock.le_merge_left _ _)
  · exact hle

/-- The heap of the word stays outside the word after a lock step. -/
theorem Step.sub {t : ThreadId} {m m' : Mem} {h : Heap} (hs : L.Step t m m') (hoff : L.Off h)
    (hsub : h.Sub m.heap) : h.Sub m'.heap := fun l c hc => by
  have hw : ¬ (l.1 = L.b ∧ L.o ≤ l.2 ∧ l.2 < L.o + 4) := by
    rintro ⟨h1, h2, h3⟩
    obtain ⟨b, x⟩ := l; simp only at h1 h2 h3; subst h1
    rw [hoff x h2 h3] at hc; cases hc
  rw [hs.heap hw]; exact hsub l c hc

/-- A new access of a lock step touches no heap without the word's bytes. -/
theorem Step.fpOff {t : ThreadId} {m m' : Mem} {h : Heap} (hs : L.Step t m m') (hoff : L.Off h)
    {e : FootprintEntry} (he : e ∈ m'.footprint) (hn : e ∉ m.footprint) : ¬ e.Touches h := by
  rintro ⟨x, h1, h2, h3⟩
  rcases hs.fp e he with h' | ⟨hb, ho, hl, -⟩
  · exact hn h'
  · rw [hb] at h3; rw [ho] at h1 h2; rw [hl] at h2
    exact h3 (hoff x h1 (by omega))

theorem not_free_iff {G : ThreadId → γ} : ¬ L.Free G ↔ ∃ u, L.ph (G u) = .holds := by
  unfold Lock.Free
  constructor
  · intro h; exact Classical.byContradiction fun hn => h fun u hu => hn ⟨u, hu⟩
  · rintro ⟨u, hu⟩ h; exact h u hu

theorem ph_set_upd {G : ThreadId → γ} {t u : ThreadId} {p : LPh} {h : Heap} :
    L.ph (upd G t (L.set (G t) p h) u) = if u = t then p else L.ph (G u) := by
  unfold upd; split
  · rename_i hu; subst hu; exact L.ph_set _ _ _
  · rfl

/-- `t` is not in the futex queue if its place is not `wait` or `away`. -/
theorem Inv.notQ {G : ThreadId → γ} {m : Mem} {t : ThreadId} (hi : L.Inv G m)
    (hw : L.ph (G t) ≠ .wait) (ha : L.ph (G t) ≠ .away) : m.waiters.any (·.1 == t) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp h
  have ht : (m.waiters[i]).1 = t := by simpa using he
  rcases hi.fq _ (Array.getElem_mem hi') with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [ht] at h2
  · exact hw h2
  · exact ha h2

/-- The futex queue without `t`, which is not at a futex wait: the waiters stay. -/
theorem fq_keep {G : ThreadId → γ} {m : Mem} {t : ThreadId} {p : LPh} {h : Heap} (hi : L.Inv G m)
    (hw : L.ph (G t) ≠ .wait) (ha : L.ph (G t) ≠ .away) :
    L.Queue (upd G t (L.set (G t) p h)) m.waiters :=
  hi.fq.mono (fun w hw => hw) fun w hwm => by
    have hwt : w.1 ≠ t := fun e => by
      rcases hi.fq w hwm with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [e] at h2
      · exact hw h2
      · exact ha h2
    rw [ph_set_upd, if_neg hwt]

/-- Thread `t` takes the free lock with an acquire RMW that writes `w'` (`1` from `out`, `2` from
`spin`): it holds the lock, with a resource `hL` of `R`. -/
theorem Inv.acquire {G : ThreadId → γ} {m₁ M : Mem} {t li : Nat} {l : ALoc} {w' : Nat}
    (hi : L.Inv G m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t)
    (hph : (L.ph (G t) = .out ∧ w' = 1) ∨ (L.ph (G t) = .spin ∧ w' = L.c)) (hF : L.Free G)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) .acquire (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 w')) :
    L.Step t m₁ M ∧ M.current = t ∧ ∃ hL, L.R G hL ∧ L.Inv (upd G t (L.set (G t) .holds hL)) M := by
  have hpt : L.ph (G t) ≠ .gone := by rcases hph with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hnh : L.ph (G t) ≠ .holds := by rcases hph with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hnw : L.ph (G t) ≠ .wait := by rcases hph with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hna : L.ph (G t) ≠ .away := by rcases hph with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hw3 : L.Val w' := by rcases hph with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> first | exact L.val1 | exact L.valC
  have hw0 : w' ≠ 0 := by rcases hph with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> first | decide | exact L.c_ne0
  obtain ⟨ht, hjt⟩ := hi.live t hpt
  have hheld : L.held (G t) = Heap.empty := hi.idle t hnh
  have hownt : L.own G m₁ t = L.part (G t) := by simp [Lock.own, hjt, hheld]
  obtain ⟨hL, hR, hsub, hdj, hoff, how⟩ := hi.free hF
  obtain ⟨blk, m₂, hb, hm₂, hst, hcM, hwM, hclM, hbM, haM⟩ := hi.rmwStep hl hc ht hM
  have hacq : AtomicOrder.acquire.isAcq = true := rfl
  rw [hacq, if_pos rfl] at hm₂
  subst hm₂
  have hcs : m₁.current < m₁.clocks.size := by rw [hi.own.csize, hc]; exact ht
  have hct : M.clocks[t]! = VClock.merge (m₁.clocks[t]!) (l.msgs[l.msgs.size - 1]!).relClock := by
    rw [hclM, ← hc, acqM_clock _ _ hcs]
  have hbl : L.b < m₁.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hjb : joinedB M = joinedB m₁ := joinedB_congr hst.threads
  have hown : L.own (upd G t (L.set (G t) .holds hL)) M = upd (L.own G m₁) t (L.own G m₁ t ∪ hL) := by
    rw [own_upd hjb hjt, L.part_set, L.held_set, hownt]
  have hphu := fun u => ph_set_upd (L := L) (G := G) (t := t) (p := .holds) (h := hL) (u := u)
  have ho1 : Owned (L.own G m₁) M := hst.owned hi.own hi.off hbl fun e he => by
    rcases hst.fp e he with h | ⟨a, b, c, -⟩
    · exact .inl h
    · exact .inr ⟨a, b, c⟩
  have howns : M.OwnsC (M.clocks[t]!) hL := by
    intro e he htc
    by_cases hm : e ∈ m₁.footprint
    · rcases how e hm (htc.imp id fun h => by rw [← hst.bsize]; exact h) with h | ⟨i, l₀, hl₀, hle⟩
      · exact VClock.le_trans (h t ht hpt) (hst.clocks t)
      · obtain ⟨rfl, rfl⟩ := loc_unique hl₀ hl
        rw [hct]
        exact VClock.le_trans hle (VClock.le_merge_right _ _)
    · rcases htc with htc | hbe
      · exact absurd htc (hst.fpOff hoff he hm)
      · rcases hst.fp e he with h | ⟨heb, -⟩
        · exact absurd h hm
        · rw [heb, hst.bsize] at hbe; exact absurd hbl (Nat.not_lt.mpr hbe)
  have ho : Owned (L.own (upd G t (L.set (G t) .holds hL)) M) M := by
    rw [hown]; exact ho1.add (by rw [hst.threads]; exact ht) (hst.sub hoff hsub) hdj howns
  refine ⟨hst, hcM, hL, hR, hi.rmw hl hb hst hbM haM hwM rfl (bs4 _) hw3 (intOfBytes_rmw _) ho
    (fun u => ?_) (fun u hu => ?_) (fun u hu => ?_) ?_ (fun u v hu hv => ?_) (fun u => ?_) ?_
    (fun hF' => ?_) (fun u hu => ?_) (by rw [hwM]; exact fq_keep hi hnw hna) (fun hU hp => ?_)⟩
  · unfold upd; split
    · rename_i hu; subst hu; rw [L.part_set, L.held_set]
      have := hdj u; rw [hownt] at this; exact this.symm
    · exact hi.pdisj u
  · rw [hphu] at hu; unfold upd; split
    · rename_i h; simp [h] at hu
    · rename_i h; simp only [h, ↓reduceIte] at hu; exact hi.idle u hu
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; exact hpt
    · exact hu
  · refine ⟨fun h => absurd h hw0, fun h => absurd (by rw [hphu]; simp) (h t)⟩
  · rw [hphu] at hu hv
    split at hu
    · split at hv
      · rename_i h1 h2; rw [h1, h2]
      · exact absurd hv (hF v)
    · exact absurd hu (hF u)
  · rw [hown]; unfold upd; split
    · rename_i hu; subst hu; exact off_union (hi.off u) hoff
    · exact hi.off u
  · have hrel : (rmwMsg (acqM m₁ (l.msgs[l.msgs.size - 1]!).relClock) .acquire
        (l.msgs[l.msgs.size - 1]!) (BitVec.ofNat 32 w')).relClock =
        (l.msgs[l.msgs.size - 1]!).relClock := rfl
    rw [hrel]
    refine ⟨hst.someLe (hi.rel li l hl).1, fun u hu => ?_⟩
    rw [hphu] at hu
    split at hu
    · rename_i h; subst h; rw [hct]; exact VClock.le_merge_right _ _
    · exact absurd hu (hF u)
  · exact absurd hF' fun h => by have := h t; rw [hphu] at this; simp at this
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h
      rw [show upd G u (L.set (G u) .holds hL) u = L.set (G u) .holds hL from upd_self _ _ _,
        L.held_set, L.R_set]
      exact hR
    · exact absurd hu (hF u)
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (hwM ▸ hp)
    refine ⟨v, by rw [hst.threads]; exact hv, hwM ▸ hq, ?_, fun hh => ?_⟩
    · rw [hphu]; split
      · rfl
      · exact h1
    · rw [hphu] at hh
      split at hh
      · rename_i h; subst h
        rcases hph with ⟨h, -⟩ | ⟨-, rfl⟩
        · rw [h] at h1; cases h1
        · exact hU
      · exact absurd hh (hF v)

/-- Thread `t` in `lock`'s loop writes `2` to the held lock (an acquire RMW): the holder stays, and
`t` goes to the futex wait. -/
theorem Inv.contend {G : ThreadId → γ} {m₁ M : Mem} {t li : Nat} {l : ALoc}
    (hi : L.Inv G m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t) (hph : L.ph (G t) = .spin)
    (hnF : ¬ L.Free G)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) .acquire (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 L.c)) :
    L.Step t m₁ M ∧ M.current = t ∧ L.Inv (upd G t (L.set (G t) .wait Heap.empty)) M := by
  obtain ⟨ht, hjt⟩ := hi.live t (by rw [hph]; decide)
  have hheld : L.held (G t) = Heap.empty := hi.idle t (by rw [hph]; decide)
  obtain ⟨u0, hu0⟩ := not_free_iff.mp hnF
  have hu0t : u0 ≠ t := fun e => by rw [e, hph] at hu0; cases hu0
  obtain ⟨blk, m₂, hb, hm₂, hst, hcM, hwM, hclM, hbM, haM⟩ := hi.rmwStep hl hc ht hM
  have hacq : AtomicOrder.acquire.isAcq = true := rfl
  rw [hacq, if_pos rfl] at hm₂
  subst hm₂
  have hbl : L.b < m₁.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hjb : joinedB M = joinedB m₁ := joinedB_congr hst.threads
  have hown : L.own (upd G t (L.set (G t) .wait Heap.empty)) M = L.own G m₁ := by
    rw [own_upd hjb hjt, L.part_set, L.held_set]
    funext u; unfold upd; split
    · rename_i h; subst h; simp [Lock.own, hjt, hheld]
    · rfl
  have hphu := fun u => ph_set_upd (L := L) (G := G) (t := t) (p := .wait) (h := Heap.empty) (u := u)
  have hholds : ∀ u, L.ph (upd G t (L.set (G t) .wait Heap.empty) u) = .holds ↔
      L.ph (G u) = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; rw [hph]; decide
    · exact Iff.rfl
  have hGu : ∀ u, u ≠ t → upd G t (L.set (G t) .wait Heap.empty) u = G u := fun u h => upd_ne _ _ h
  have ho : Owned (L.own (upd G t (L.set (G t) .wait Heap.empty)) M) M := by
    rw [hown]
    exact hst.owned hi.own hi.off hbl fun e he => by
      rcases hst.fp e he with h | ⟨a, b, c, -⟩
      · exact .inl h
      · exact .inr ⟨a, b, c⟩
  refine ⟨hst, hcM, hi.rmw hl hb hst hbM haM hwM rfl (bs4 _) L.valC (intOfBytes_rmw _) ho
    (fun u => ?_) (fun u hu => ?_) (fun u hu => ?_) ?_ (fun u v hu hv => ?_) (fun u => ?_) ?_
    (fun hF' => ?_) (fun u hu => ?_)
    (by rw [hwM]; exact fq_keep hi (by rw [hph]; decide) (by rw [hph]; decide)) (fun hU _ => ?_)⟩
  · unfold upd; split
    · rw [L.held_set]; exact Heap.disjoint_empty _
    · exact hi.pdisj u
  · rw [hphu] at hu
    unfold upd; split
    · exact L.held_set _ _ _
    · rename_i h; rw [if_neg h] at hu; exact hi.idle u hu
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; rw [hph]; decide
    · exact hu
  · refine ⟨fun h => absurd h L.c_ne0, fun h => absurd ((hholds u0).mpr hu0) (h u0)⟩
  · exact hi.one u v ((hholds u).mp hu) ((hholds v).mp hv)
  · rw [hown]; exact hi.off u
  · refine ⟨hst.someLe (hi.rel li l hl).1, fun u hu => ?_⟩
    exact VClock.le_trans ((hi.rel li l hl).2 u ((hholds u).mp hu)) (hst.clocks u)
  · exact absurd ((hholds u0).mpr hu0) (hF' u0)
  · have hut : u ≠ t := fun e => by
      have := (hholds u).mp hu; rw [e, hph] at this; cases this
    rw [hGu u hut, L.R_set]; exact hi.res u ((hholds u).mp hu)
  · obtain ⟨hu0s, -⟩ := hi.live u0 (by rw [hu0]; decide)
    refine ⟨u0, by rw [hst.threads]; exact hu0s, ?_, by rw [hGu u0 hu0t, hu0]; rfl,
      fun _ => hU⟩
    rw [hwM]; exact hi.notQ (by rw [hu0]; decide) (by rw [hu0]; decide)

/-- Thread `t` (at `out` or `spin`) writes again the value `w ≠ 0` of the held lock (an acquire
RMW, as `Thread.Mutex`'s `or 1` on a held lock): the holder stays, and `t` goes to `spin` or to the
futex wait. -/
theorem Inv.rmwKeep {G : ThreadId → γ} {m₁ M : Mem} {t li : Nat} {l : ALoc} {w : Nat} {p : LPh}
    (hi : L.Inv G m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t)
    (hph : L.ph (G t) = .out ∨ L.ph (G t) = .spin) (hp : p = .spin ∨ p = .wait)
    (hw : L.Val w) (hU0 : L.U32 m₁ (BitVec.ofNat 32 w)) (hw0 : w ≠ 0)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) .acquire (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 w)) :
    L.Step t m₁ M ∧ M.current = t ∧ L.Inv (upd G t (L.set (G t) p Heap.empty)) M := by
  have hng : L.ph (G t) ≠ .gone := by rcases hph with h | h <;> rw [h] <;> decide
  have hnh : L.ph (G t) ≠ .holds := by rcases hph with h | h <;> rw [h] <;> decide
  have hnw : L.ph (G t) ≠ .wait := by rcases hph with h | h <;> rw [h] <;> decide
  have hna : L.ph (G t) ≠ .away := by rcases hph with h | h <;> rw [h] <;> decide
  have hph' : p ≠ .holds := by rcases hp with rfl | rfl <;> decide
  have hpb : p.busy = true := by rcases hp with rfl | rfl <;> rfl
  have hnF : ¬ L.Free G := fun hF => hw0 ((hi.free_iff hw hU0).mpr hF)
  obtain ⟨ht, hjt⟩ := hi.live t hng
  have hheld : L.held (G t) = Heap.empty := hi.idle t hnh
  obtain ⟨u0, hu0⟩ := not_free_iff.mp hnF
  have hu0t : u0 ≠ t := fun e => by rw [e] at hu0; exact hnh hu0
  obtain ⟨blk, m₂, hb, hm₂, hst, hcM, hwM, hclM, hbM, haM⟩ := hi.rmwStep hl hc ht hM
  have hacq : AtomicOrder.acquire.isAcq = true := rfl
  rw [hacq, if_pos rfl] at hm₂
  subst hm₂
  have hbl : L.b < m₁.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hjb : joinedB M = joinedB m₁ := joinedB_congr hst.threads
  have hown : L.own (upd G t (L.set (G t) p Heap.empty)) M = L.own G m₁ := by
    rw [own_upd hjb hjt, L.part_set, L.held_set]
    funext u; unfold upd; split
    · rename_i h; subst h; simp [Lock.own, hjt, hheld]
    · rfl
  have hphu := fun u => ph_set_upd (L := L) (G := G) (t := t) (p := p) (h := Heap.empty) (u := u)
  have hholds : ∀ u, L.ph (upd G t (L.set (G t) p Heap.empty) u) = .holds ↔
      L.ph (G u) = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; exact ⟨fun h => absurd h hph', fun h => absurd h hnh⟩
    · exact Iff.rfl
  have hGu : ∀ u, u ≠ t → upd G t (L.set (G t) p Heap.empty) u = G u := fun u h => upd_ne _ _ h
  have ho : Owned (L.own (upd G t (L.set (G t) p Heap.empty)) M) M := by
    rw [hown]
    exact hst.owned hi.own hi.off hbl fun e he => by
      rcases hst.fp e he with h | ⟨a, b, c, -⟩
      · exact .inl h
      · exact .inr ⟨a, b, c⟩
  refine ⟨hst, hcM, hi.rmw hl hb hst hbM haM hwM rfl (bs4 _) hw (intOfBytes_rmw _) ho
    (fun u => ?_) (fun u hu => ?_) (fun u hu => ?_) ?_ (fun u v hu hv => ?_) (fun u => ?_) ?_
    (fun hF' => ?_) (fun u hu => ?_)
    (by rw [hwM]; exact fq_keep hi hnw hna) (fun hU hq => ?_)⟩
  · unfold upd; split
    · rw [L.held_set]; exact Heap.disjoint_empty _
    · exact hi.pdisj u
  · rw [hphu] at hu
    unfold upd; split
    · exact L.held_set _ _ _
    · rename_i h; rw [if_neg h] at hu; exact hi.idle u hu
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; exact hng
    · exact hu
  · refine ⟨fun h => absurd h hw0, fun h => absurd ((hholds u0).mpr hu0) (h u0)⟩
  · exact hi.one u v ((hholds u).mp hu) ((hholds v).mp hv)
  · rw [hown]; exact hi.off u
  · refine ⟨hst.someLe (hi.rel li l hl).1, fun u hu => ?_⟩
    exact VClock.le_trans ((hi.rel li l hl).2 u ((hholds u).mp hu)) (hst.clocks u)
  · exact absurd ((hholds u0).mpr hu0) (hF' u0)
  · have hut : u ≠ t := fun e => by
      have := (hholds u).mp hu; rw [e] at this; exact hnh this
    rw [hGu u hut, L.R_set]; exact hi.res u ((hholds u).mp hu)
  · obtain ⟨v, hv, hvq, h1, h2⟩ := hi.wit (hwM ▸ hq)
    refine ⟨v, by rw [hst.threads]; exact hv, hwM ▸ hvq, ?_, fun hh => ?_⟩
    · rw [hphu]; split
      · exact hpb
      · exact h1
    · have hvh := (hholds v).mp hh
      have e := ofNat_inj hw.lt L.c_lt (u32_eq hU0 (h2 hvh))
      rw [← e]; exact hU

/-- The holder `t` writes `0` (`unlock`, a release RMW) where the word was `w`: no thread holds the
lock, and the lock owns the resource again. `t` goes to `out` (`w = 1`) or to the futex wake
(`w = 2`). `w = 1` with `p = .out` needs `L.c ≠ 1`. -/
theorem Inv.release {G : ThreadId → γ} {m₁ M : Mem} {t li : Nat} {l : ALoc} {w : Nat}
    {p : LPh} (hi : L.Inv G m₁) (hl : L.Loc m₁ li l) (hc : m₁.current = t)
    (hph : L.ph (G t) = .holds) (hw : L.U32 m₁ (BitVec.ofNat 32 w))
    (hp : (w = 1 ∧ p = .out ∧ L.c ≠ 1) ∨ (w = L.c ∧ p = .wake))
    (hM : M = rmwM m₁ li (l.msgs.size - 1) .release (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 0)) :
    L.Step t m₁ M ∧ M.current = t ∧ L.Before M (m₁.clocks[t]!) ∧
      L.Inv (upd G t (L.set (G t) p Heap.empty)) M := by
  obtain ⟨ht, hjt⟩ := hi.live t (by rw [hph]; decide)
  have hpg : p ≠ .gone := by rcases hp with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> decide
  have hph' : p ≠ .holds := by rcases hp with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> decide
  have honly : ∀ u, L.ph (G u) = .holds → u = t := fun u hu => hi.one u t hu hph
  obtain ⟨blk, m₂, hb, hm₂, hst, hcM, hwM, hclM, hbM, haM⟩ := hi.rmwStep hl hc ht hM
  have hacq : AtomicOrder.release.isAcq = false := rfl
  rw [hacq] at hm₂
  simp only [Bool.false_eq_true, ↓reduceIte] at hm₂
  subst m₂
  have hbl : L.b < m₁.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hjb : joinedB M = joinedB m₁ := joinedB_congr hst.threads
  have hownt : L.own G m₁ t = L.part (G t) ∪ L.held (G t) := by simp [Lock.own, hjt]
  have hown : L.own (upd G t (L.set (G t) p Heap.empty)) M = upd (L.own G m₁) t (L.part (G t)) := by
    rw [own_upd hjb hjt, L.part_set, L.held_set, Heap.union_empty]
  have hphu := fun u => ph_set_upd (L := L) (G := G) (t := t) (p := p) (h := Heap.empty) (u := u)
  have hnh : ∀ u, L.ph (upd G t (L.set (G t) p Heap.empty) u) ≠ .holds := by
    intro u hu; rw [hphu] at hu
    split at hu
    · exact hph' hu
    · rename_i h; exact h (honly u hu)
  have hGu : ∀ u, u ≠ t → upd G t (L.set (G t) p Heap.empty) u = G u := fun u h => upd_ne _ _ h
  have hsP : (L.part (G t)).Sub (L.own G m₁ t) := by rw [hownt]; exact Heap.sub_union_left
  have hsH : (L.held (G t)).Sub (L.own G m₁ t) := by
    rw [hownt]; exact Heap.sub_union_right (hi.pdisj t)
  have ho1 : Owned (L.own G m₁) M := hst.owned hi.own hi.off hbl fun e he => by
    rcases hst.fp e he with h | ⟨a, b, c, -⟩
    · exact .inl h
    · exact .inr ⟨a, b, c⟩
  have ho : Owned (L.own (upd G t (L.set (G t) p Heap.empty)) M) M := by
    rw [hown]; exact ho1.shrink hsP
  have hcl : M.clocks = m₁.clocks := hclM
  have hrelM : (rmwMsg m₁ .release (l.msgs[l.msgs.size - 1]!) (BitVec.ofNat 32 0)).relClock =
      VClock.merge (l.msgs[l.msgs.size - 1]!).relClock (m₁.clocks[t]!) := by
    simp [rmwMsg, AtomicOrder.isRel, hc]
  have hrt : VClock.le (l.msgs[l.msgs.size - 1]!).relClock (m₁.clocks[t]!) = true :=
    (hi.rel li l hl).2 t hph
  have hoffH : L.Off (L.held (G t)) := off_sub (hi.off t) fun l h => hsH.ne h
  refine ⟨hst, hcM, ⟨li, _, loc_set hl haM rfl rfl, by
      rw [back_push, hrelM]; exact VClock.le_merge_right _ _⟩,
    hi.rmw hl hb hst hbM haM hwM rfl (bs4 _) L.val0 (intOfBytes_rmw _) ho
    (fun u => ?_) (fun u hu => ?_) (fun u hu => ?_) ?_ (fun u v hu _ => absurd hu (hnh u))
    (fun u => ?_) ?_ (fun _ => ?_) (fun u hu => absurd hu (hnh u))
    (by rw [hwM]; exact fq_keep hi (by rw [hph]; decide) (by rw [hph]; decide))
    (fun hU hp' => ?_)⟩
  · unfold upd; split
    · rw [L.held_set]; exact Heap.disjoint_empty _
    · exact hi.pdisj u
  · unfold upd; split
    · exact L.held_set _ _ _
    · rename_i h; exact hi.idle u (fun e => h (honly u e))
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; rw [hph]; decide
    · exact hu
  · exact ⟨fun _ => hnh, fun _ => rfl⟩
  · rw [hown]; unfold upd; split
    · rename_i h; subst h; exact off_sub (hi.off u) fun l h => hsP.ne h
    · exact hi.off u
  · rw [hrelM]
    refine ⟨⟨t, by rw [hst.threads]; exact ht, ?_⟩, fun u hu => absurd hu (hnh u)⟩
    rw [hcl]; exact merge_le hrt (VClock.le_refl _)
  · -- the lock owns the resource again
    have hl' := loc_set hl haM rfl rfl
    refine ⟨L.held (G t), by rw [L.R_set]; exact hi.res t hph, hst.sub hoffH (hsH.trans
      (hi.own.sub t)), fun u => ?_, hoffH, fun e he htc => ?_⟩
    · rw [hown]; unfold upd; split
      · rename_i h; subst h; exact (hi.pdisj u).symm
      · rename_i h; exact Heap.disjoint_sub (hi.own.disj u t h) hsH |>.symm
    · by_cases hm : e ∈ m₁.footprint
      · refine .inr ⟨li, _, hl', ?_⟩
        rw [back_push, hrelM]
        have := hi.own.owns t ht e hm (htc.imp (fun ⟨x, h1, h2, h3⟩ => ⟨x, h1, h2, hsH.ne h3⟩)
          fun h => by rw [← hst.bsize]; exact h)
        exact VClock.le_trans this (VClock.le_merge_right _ _)
      · rcases htc with htc | hbe
        · exact absurd htc (hst.fpOff hoffH he hm)
        · rcases hst.fp e he with h | ⟨heb, -⟩
          · exact absurd h hm
          · rw [heb, hst.bsize] at hbe; exact absurd hbl (Nat.not_lt.mpr hbe)
  · rcases hp with ⟨rfl, rfl, hc1⟩ | ⟨rfl, rfl⟩
    · -- `w = 1`: the old witness is not `t`
      obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (hwM ▸ hp')
      have hvt : v ≠ t := fun e => by
        subst e
        have := ofNat_inj (by decide) L.c_lt (u32_eq hw (h2 hph))
        exact hc1 this.symm
      refine ⟨v, by rw [hst.threads]; exact hv, hwM ▸ hq, by rw [hGu v hvt]; exact h1,
        fun hh => absurd hh (hnh v)⟩
    · -- `w = 2`: `t` is at the wake
      refine ⟨t, by rw [hst.threads]; exact ht, ?_, by rw [hphu]; simp; rfl,
        fun hh => absurd hh (hnh t)⟩
      rw [hwM]; exact hi.notQ (by rw [hph]; decide) (by rw [hph]; decide)

/-! ## The futex queue -/

/-- A thread that is not in the futex queue is not the thread of a waiter. -/
theorem ne_of_notQ {ws : Array (ThreadId × Ptr)} {t : ThreadId} (hq : ws.any (·.1 == t) = false)
    {w : ThreadId × Ptr} (hw : w ∈ ws) : w.1 ≠ t := fun e => by
  have : ws.any (·.1 == t) = true := Array.any_eq_true.mpr (by
    obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hw
    exact ⟨i, hi', by simp [e]⟩)
  rw [hq] at this; cases this

/-- A change of the futex queue and of the place of thread `t` (`t` does not hold the lock and
goes to `p`, not `holds`): the memory is the same but `current`, `waiters` and `woken`. -/
theorem Inv.queue {G : ThreadId → γ} {m : Mem} {t c : ThreadId} {p : LPh}
    {ws : Array (ThreadId × Ptr)} {wk : Array ThreadId} (hi : L.Inv G m)
    (hnh : L.ph (G t) ≠ .holds) (hng : L.ph (G t) ≠ .gone) (hp : p ≠ .holds) (hpg : p ≠ .gone)
    (hfq : L.Queue (upd G t (L.set (G t) p Heap.empty)) ws)
    (hwit : L.Waits ws → ∃ v, v < m.threads.size ∧ ws.any (·.1 == v) = false ∧
      (L.ph (upd G t (L.set (G t) p Heap.empty) v)).busy = true ∧
      (L.ph (upd G t (L.set (G t) p Heap.empty) v) = .holds → L.U32 m (BitVec.ofNat 32 L.c))) :
    L.Inv (upd G t (L.set (G t) p Heap.empty))
      { m with current := c, waiters := ws, woken := wk } := by
  obtain ⟨ht, hjt⟩ := hi.live t hng
  have hheld : L.held (G t) = Heap.empty := hi.idle t hnh
  have hown : L.own (upd G t (L.set (G t) p Heap.empty))
      { m with current := c, waiters := ws, woken := wk } = L.own G m := by
    rw [own_upd (m' := { m with current := c, waiters := ws, woken := wk }) (m := m) rfl hjt,
      L.part_set, L.held_set]
    funext u; unfold upd; split
    · rename_i h; subst h; simp [Lock.own, hjt, hheld]
    · rfl
  have hphu := fun u => ph_set_upd (L := L) (G := G) (t := t) (p := p) (h := Heap.empty) (u := u)
  have hholds : ∀ u, L.ph (upd G t (L.set (G t) p Heap.empty) u) = .holds ↔
      L.ph (G u) = .holds := by
    intro u; rw [hphu]; split
    · rename_i h; subst h; exact ⟨fun h => absurd h hp, fun h => absurd h hnh⟩
    · exact Iff.rfl
  have hfree : L.Free (upd G t (L.set (G t) p Heap.empty)) ↔ L.Free G := by
    unfold Lock.Free; exact forall_congr' fun u => not_congr (hholds u)
  have hgw : ∀ u, L.ph (upd G t (L.set (G t) p Heap.empty) u) ≠ .gone → L.ph (G u) ≠ .gone :=
    fun u h => by
      rw [hphu] at h; split at h
      · rename_i e; subst e; exact hng
      · exact h
  refine ⟨by rw [hown]; exact ⟨hi.own.sub, hi.own.disj, hi.own.owns, hi.own.outside, hi.own.csize⟩,
    fun u => ?_, fun u hu => ?_, fun u hu => ?_, hi.blk, ?_, fun u v hu hv => ?_,
    ⟨hi.loc.only, hi.loc.ok⟩, fun u => by rw [hown]; exact hi.off u, hi.wfpW hgw,
    fun i l hl => ?_, fun hF => ?_, fun u hu => ?_, hfq, hwit⟩
  · unfold upd; split
    · rw [L.held_set, L.part_set]; exact Heap.disjoint_empty _
    · exact hi.pdisj u
  · unfold upd; split
    · exact L.held_set _ _ _
    · rename_i h; rw [hphu, if_neg h] at hu; exact hi.idle u hu
  · rw [hphu] at hu
    split at hu
    · rename_i h; subst h; exact hi.live _ hng
    · exact hi.live u hu
  · obtain ⟨w, hw, hu, hz⟩ := hi.word; exact ⟨w, hw, hu, hz.trans hfree.symm⟩
  · exact hi.one u v ((hholds u).mp hu) ((hholds v).mp hv)
  · obtain ⟨h1, h2⟩ := hi.rel i l hl
    exact ⟨h1, fun u hu => h2 u ((hholds u).mp hu)⟩
  · obtain ⟨hL, hR, hsub, hdj, hoff, how⟩ := hi.free (hfree.mp hF)
    exact ⟨hL, by rw [L.R_set]; exact hR, hsub, fun u => by rw [hown]; exact hdj u, hoff,
      how.weaken hgw⟩
  · have hut : u ≠ t := fun e => by
      have := (hholds u).mp hu; rw [e] at this; exact hnh this
    rw [upd_ne _ _ hut, L.R_set]; exact hi.res u ((hholds u).mp hu)

/-- The old witness of the queue, if `t` keeps a busy place or was not busy. -/
theorem wit_keep {G : ThreadId → γ} {m : Mem} {t : ThreadId} {p : LPh} (hi : L.Inv G m)
    (hnh : L.ph (G t) ≠ .holds) (hp : p ≠ .holds) (hb : (L.ph (G t)).busy = true → p.busy = true) :
    L.Waits m.waiters → ∃ v, v < m.threads.size ∧ m.waiters.any (·.1 == v) = false ∧
      (L.ph (upd G t (L.set (G t) p Heap.empty) v)).busy = true ∧
      (L.ph (upd G t (L.set (G t) p Heap.empty) v) = .holds → L.U32 m (BitVec.ofNat 32 L.c)) := by
  intro hpos
  obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hpos
  refine ⟨v, hv, hq, ?_, fun hh => ?_⟩
  · rw [ph_set_upd]; split
    · rename_i h; subst h; exact hb h1
    · exact h1
  · rw [ph_set_upd] at hh
    split at hh
    · exact absurd hh hp
    · exact h2 hh

/-- `lock`'s futex wait for `2` by thread `t` (at `wait`, not in the queue). If it sleeps, the
invariant holds with `t` in the queue: the word is `2`, so a thread holds the lock. Else `t` goes to
`spin`. -/
theorem Inv.wait {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {b : Bool} (hi : L.Inv G m)
    (hph : L.ph (G t) = .wait) (hq : m.waiters.any (·.1 == t) = false)
    (h : ((Thread.futexWait L.ptr (BitVec.ofNat 32 L.c)).run { m with current := t }).run =
      some (.ok (b, m'))) :
    L.Step t m m' ∧ if b then L.Inv G m' else
      (m'.current = t ∧ L.Inv (upd G t (L.set (G t) .spin Heap.empty)) m') := by
  have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
  have hng : L.ph (G t) ≠ .gone := by rw [hph]; decide
  have hspin : ∀ wk : Array ThreadId,
      L.Inv (upd G t (L.set (G t) .spin Heap.empty))
        { m with current := t, waiters := m.waiters, woken := wk } := fun wk =>
    hi.queue hnh hng (by decide) (by decide)
      (hi.fq.mono (fun w hw => hw) fun w hw => by rw [ph_set_upd, if_neg (ne_of_notQ hq hw)])
      (wit_keep hi hnh (by decide) fun _ => rfl)
  rcases futexWait_ok h with ⟨-, rfl, rfl⟩ | ⟨-, bid, blk, o, v, ha, hv, ⟨rfl, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
  · exact ⟨Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl), rfl, hspin _⟩
  · -- it sleeps: the word is `2`
    refine ⟨Step.same rfl rfl rfl rfl rfl rfl fun w hw => ?_, ?_⟩
    · simp only [Array.mem_push]
      exact ⟨fun h => h.resolve_right fun e => hw (by rw [e]), .inl⟩
    simp only [↓reduceIte]
    obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hi.access
    have : ({ m with current := t } : Mem).access L.ptr 4 4 = m.access L.ptr 4 4 := rfl
    rw [this, ha₀] at ha
    cases ha
    have h2 : L.U32 m (BitVec.ofNat 32 L.c) := (u32_bytes hb₀).mpr hv
    obtain ⟨u0, hu0⟩ := not_free_iff.mp fun hF =>
      absurd ((hi.free_iff L.valC h2).mpr hF) L.c_ne0
    have hu0t : u0 ≠ t := fun e => by rw [e, hph] at hu0; cases hu0
    have hG : upd G t (L.set (G t) .wait Heap.empty) = G := by
      rw [← hph, ← hi.idle t hnh]; exact upd_set_self G t
    have := hi.queue (c := t) (ws := m.waiters.push (t, L.ptr)) (wk := m.woken) (p := .wait) hnh hng
      (by decide) (by decide) (fun w hw => ?_) (fun _ => ?_)
    · rw [hG] at this; exact this
    · rw [hG]
      rcases Array.mem_push.mp hw with hw | rfl
      · exact hi.fq w hw
      · exact .inl ⟨rfl, hph⟩
    · rw [hG]
      obtain ⟨hu0s, -⟩ := hi.live u0 (by rw [hu0]; decide)
      refine ⟨u0, hu0s, ?_, by rw [hu0]; rfl, fun _ => h2⟩
      rw [Array.any_push, hi.notQ (by rw [hu0]; decide) (by rw [hu0]; decide)]
      simp [Ne.symm hu0t]
  · exact ⟨Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl), rfl, hspin _⟩

/-- A spurious return of `lock`'s futex wait for `2` by thread `t` (at `wait`, not in the
queue): `t` goes to `spin` with the memory before the wait. -/
theorem Inv.spurious {G : ThreadId → γ} {m : Mem} {t : ThreadId} (hi : L.Inv G m)
    (hph : L.ph (G t) = .wait) (hq : m.waiters.any (·.1 == t) = false) :
    L.Step t m { m with current := t } ∧ { m with current := t }.current = t ∧
      L.Inv (upd G t (L.set (G t) .spin Heap.empty)) { m with current := t } := by
  have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
  have hng : L.ph (G t) ≠ .gone := by rw [hph]; decide
  exact ⟨Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl), rfl,
    hi.queue (wk := m.woken) hnh hng (by decide) (by decide)
      (hi.fq.mono (fun w hw => hw) fun w hw => by rw [ph_set_upd, if_neg (ne_of_notQ hq hw)])
      (wit_keep hi hnh (by decide) fun _ => rfl)⟩

/-- `unlock`'s futex wake of `n ≥ 1` waiters by thread `t` (at `wake`): `t` goes to `out`; a woken
thread is the new witness of the queue. -/
theorem Inv.wake {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {n : Nat} (hi : L.Inv G m)
    (hph : L.ph (G t) = .wake) (hn : 1 ≤ n)
    (h : ((Thread.futexWake L.ptr n).run { m with current := t }).run = some (.ok ((), m'))) :
    L.Step t m m' ∧ m'.current = t ∧ L.Inv (upd G t (L.set (G t) .out Heap.empty)) m' := by
  have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
  have hng : L.ph (G t) ≠ .gone := by rw [hph]; decide
  have hm' := Proto.modify_ok h
  generalize hwk : ((m.waiters.filter (·.2 == L.ptr)).extract 0 n).map (·.1) = woke at hm'
  -- a woken thread waited at the word, so it is not at another futex
  have hwoke : ∀ u ∈ woke, L.ph (G u) = .wait := by
    intro u hu
    rw [← hwk] at hu
    obtain ⟨w, hw, rfl⟩ := Array.mem_map.mp hu
    have hw' : w ∈ m.waiters.filter (·.2 == L.ptr) := by
      obtain ⟨k, -, rfl⟩ := Array.mem_extract_iff_getElem.mp hw; exact Array.getElem_mem _
    replace hw' := Array.mem_filter.mp hw'
    rcases hi.fq w hw'.1 with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exact absurd (by simpa using hw'.2) h1
  subst hm'
  refine ⟨Step.same rfl rfl rfl rfl rfl rfl fun w hw => ?_, rfl,
    hi.queue hnh hng (by decide) (by decide)
    ((fq_keep hi (by rw [hph]; decide) (by rw [hph]; decide)).mono
      (fun w hw => (Array.mem_filter.mp hw).1) fun _ _ => rfl) (fun hpos => ?_)⟩
  · simp only [Array.mem_filter, Bool.not_eq_true', and_iff_left_iff_imp]
    intro hwm
    apply Bool.eq_false_iff.mpr
    intro hc
    rcases hi.fq w hwm with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hw h1
    · rw [hwoke w.1 (Array.contains_iff_mem.mp hc)] at h2; cases h2
  -- the first waiter at the word was woken
  have h0 : 0 < (m.waiters.filter (·.2 == L.ptr)).size := by
    obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hpos
    have hm := Array.mem_filter.mp (Array.getElem_mem hi')
    exact Array.size_pos_of_mem (Array.mem_filter.mpr ⟨hm.1, he⟩)
  let w0 := (m.waiters.filter (·.2 == L.ptr))[0]
  have hw0 : w0.1 ∈ woke := by
    rw [← hwk]
    exact Array.mem_map.mpr ⟨w0, Array.mem_extract_iff_getElem.mpr ⟨0, by simp; omega, rfl⟩, rfl⟩
  have hw0p : L.ph (G w0.1) = .wait := hwoke _ hw0
  have hw0t : w0.1 ≠ t := fun e => by rw [e, hph] at hw0p; cases hw0p
  obtain ⟨hw0s, -⟩ := hi.live w0.1 (by rw [hw0p]; decide)
  refine ⟨w0.1, hw0s, ?_, by rw [ph_set_upd, if_neg hw0t, hw0p]; rfl, fun hh => ?_⟩
  · apply Array.any_eq_false.mpr
    intro i hi' he
    have hm := Array.getElem_mem hi'
    rw [Array.mem_filter] at hm
    have : woke.contains (m.waiters.filter fun w => !woke.contains w.1)[i].1 = false := by
      simpa using hm.2
    simp only [beq_iff_eq] at he
    rw [he, Array.contains_iff_mem.mpr hw0] at this
    cases this
  · rw [ph_set_upd, if_neg hw0t, hw0p] at hh; cases hh

/-! ## Another futex -/

/-- A change of the futex queue and the woken threads, with the same ghost values. -/
theorem Inv.requeue {G : ThreadId → γ} {m : Mem} {c : ThreadId} {ws : Array (ThreadId × Ptr)}
    {wk : Array ThreadId} (hi : L.Inv G m) (hfq : L.Queue G ws)
    (hwit : L.Waits ws → ∃ v, v < m.threads.size ∧ ws.any (·.1 == v) = false ∧
      (L.ph (G v)).busy = true ∧ (L.ph (G v) = .holds → L.U32 m (BitVec.ofNat 32 L.c))) :
    L.Inv G { m with current := c, waiters := ws, woken := wk } :=
  ⟨⟨hi.own.sub, hi.own.disj, hi.own.owns, hi.own.outside, hi.own.csize⟩, hi.pdisj, hi.idle,
    hi.live, hi.blk, hi.word, hi.one, ⟨hi.loc.only, hi.loc.ok⟩, hi.off, hi.wfp, hi.rel, hi.free,
    hi.res, hfq, hwit⟩

/-- A futex wait of thread `t` (`away`, not in the queue) at another futex `p`. If it sleeps, the
invariant holds with `t` in the queue; else `t` goes to `out`. -/
theorem Inv.waitOff {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {p : Ptr} {e : BitVec 32}
    {b : Bool} (hi : L.Inv G m) (hph : L.ph (G t) = .away) (hp : p ≠ L.ptr)
    (hq : m.waiters.any (·.1 == t) = false)
    (h : ((Thread.futexWait p e).run { m with current := t }).run = some (.ok (b, m'))) :
    if b then L.Inv G m' else
      (m'.current = t ∧ L.Inv (upd G t (L.set (G t) .out Heap.empty)) m') := by
  have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
  have hng : L.ph (G t) ≠ .gone := by rw [hph]; decide
  have hout : ∀ wk : Array ThreadId,
      L.Inv (upd G t (L.set (G t) .out Heap.empty))
        { m with current := t, waiters := m.waiters, woken := wk } := fun wk =>
    hi.queue hnh hng (by decide) (by decide)
      (hi.fq.mono (fun w hw => hw) fun w hw => by rw [ph_set_upd, if_neg (ne_of_notQ hq hw)])
      (wit_keep hi hnh (by decide) fun h => by rw [hph] at h; cases h)
  rcases futexWait_ok h with ⟨-, rfl, rfl⟩ | ⟨-, -, -, -, -, -, -, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
  · exact ⟨rfl, hout _⟩
  · -- it sleeps at `p`
    refine hi.requeue (fun w hw => ?_) fun hw => ?_
    · rcases Array.mem_push.mp hw with hw | rfl
      · exact hi.fq w hw
      · exact .inr ⟨hp, hph⟩
    · have hw' : L.Waits m.waiters := by
        unfold Lock.Waits at hw ⊢
        rw [Array.any_push] at hw
        simpa [hp] using hw
      obtain ⟨v, hv, hvq, h1, h2⟩ := hi.wit hw'
      have hvt : v ≠ t := fun e => by rw [e, hph] at h1; cases h1
      refine ⟨v, hv, ?_, h1, h2⟩
      rw [Array.any_push, hvq]; simp [Ne.symm hvt]
  · exact ⟨rfl, hout _⟩

/-- A spurious return of a futex wait of thread `t` (`away`, not in the queue) at another
futex: `t` goes to `out` with the memory before the wait. -/
theorem Inv.spuriousOff {G : ThreadId → γ} {m : Mem} {t : ThreadId} (hi : L.Inv G m)
    (hph : L.ph (G t) = .away) (hq : m.waiters.any (·.1 == t) = false) :
    ({ m with current := t } : Mem).current = t ∧
      L.Inv (upd G t (L.set (G t) .out Heap.empty)) { m with current := t } := by
  have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
  have hng : L.ph (G t) ≠ .gone := by rw [hph]; decide
  exact ⟨rfl, hi.queue (wk := m.woken) hnh hng (by decide) (by decide)
    (hi.fq.mono (fun w hw => hw) fun w hw => by rw [ph_set_upd, if_neg (ne_of_notQ hq hw)])
    (wit_keep hi hnh (by decide) fun h => by rw [hph] at h; cases h)⟩

/-- A futex wake by thread `t` at another futex `p`: the threads at the word stay. -/
theorem Inv.wakeOff {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {p : Ptr} {n : Nat}
    (hi : L.Inv G m) (hp : p ≠ L.ptr)
    (h : ((Thread.futexWake p n).run { m with current := t }).run = some (.ok ((), m'))) :
    L.Inv G m' := by
  have hm' := Proto.modify_ok h
  generalize hwk : ((m.waiters.filter (·.2 == p)).extract 0 n).map (·.1) = woke at hm'
  -- a woken thread waited at `p`, so it is `away`
  have hwoke : ∀ u ∈ woke, L.ph (G u) = .away := by
    intro u hu
    rw [← hwk] at hu
    obtain ⟨w, hw, rfl⟩ := Array.mem_map.mp hu
    have hw' : w ∈ m.waiters.filter (·.2 == p) := by
      obtain ⟨k, -, rfl⟩ := Array.mem_extract_iff_getElem.mp hw; exact Array.getElem_mem _
    replace hw' := Array.mem_filter.mp hw'
    rcases hi.fq w hw'.1 with ⟨h1, -⟩ | ⟨-, h⟩
    · exact absurd (by simpa [h1] using hw'.2) (Ne.symm hp)
    · exact h
  subst hm'
  have hsub : ∀ w ∈ m.waiters.filter (fun w => !woke.contains w.1), w ∈ m.waiters :=
    fun w hw => (Array.mem_filter.mp hw).1
  refine hi.requeue (hi.fq.mono hsub fun _ _ => rfl) fun hw => ?_
  have hw' : L.Waits m.waiters := by
    obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hw
    exact Array.any_eq_true.mpr (by
      obtain ⟨j, hj, hje⟩ := Array.mem_iff_getElem.mp (hsub _ (Array.getElem_mem hi'))
      exact ⟨j, hj, by rw [hje]; exact he⟩)
  obtain ⟨v, hv, hvq, h1, h2⟩ := hi.wit hw'
  refine ⟨v, hv, Bool.eq_false_iff.mpr fun hc => ?_, h1, h2⟩
  obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hc
  have := ne_of_notQ hvq (hsub _ (Array.getElem_mem hi'))
  exact this (by simpa using he)

/-! ## The ops of `Io.Mutex` -/

/-- The states of `Io.Mutex` in the generated code: an enum with the bits `0`, `1`, `2`. -/
structure States (α : Type) [Packed α 32] where
  unl : α
  one : α
  two : α
  /-- The bits of `two`: `2` (`Io.Mutex`) or `3` (`Thread.Mutex`). -/
  c : Nat
  bits0 : Packed.toBits unl = 0
  bits1 : Packed.toBits one = 1
  bits2 : Packed.toBits two = BitVec.ofNat 32 c
  dec0 : (Packed.ofBits? (α := α) (BitVec.ofNat 32 0)).run = some (.ok unl)
  dec1 : (Packed.ofBits? (α := α) (BitVec.ofNat 32 1)).run = some (.ok one)
  dec2 : (Packed.ofBits? (α := α) (BitVec.ofNat 32 c)).run = some (.ok two)
  ne01 : unl ≠ one
  ne02 : unl ≠ two
  ne12 : one ≠ two

theorem intSize32 : intSize 32 = 4 := rfl

/-- The preparation of an atomic write op at the word by thread `t`: the access, the record and
the location. -/
theorem Inv.prep {G : ThreadId → γ} {m m₁ : Mem} {t li b o : Nat} {blk : Block}
    (hi : L.Inv G m) (hc : m.current = t) (ht : t < m.threads.size)
    (hacc : m.accessW L.ptr (intSize 32) 4 = pure (b, blk, o))
    (hl : ((Zig.locIdx b o (intSize 32)).run (m.recordAt b o (intSize 32) .atomicWrite)).run =
      some (.ok (li, m₁))) :
    b = L.b ∧ o = L.o ∧ ∃ l, L.Loc m₁ li l ∧ L.Inv G m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.waiters = m.waiters ∧ m₁.blocks = m.blocks ∧ m₁.atomics[li]! = l := by
  obtain ⟨blk₀, -, -, -, -, ha₀⟩ := hi.access
  rw [intSize32] at hacc hl
  rw [ha₀] at hacc
  cases hacc
  have hcs : m.current < m.clocks.size := by rw [hi.own.csize, hc]; exact ht
  have hir := hi.record (k := .atomicWrite) rfl (hc ▸ ht)
  obtain ⟨l, hl', hi₁, hb₁, hc₁, ht₁, hf₁, hw₁, hcu₁, hg₁, hlk, hks⟩ := hir.locIdx (hc ▸ ht) hl
  refine ⟨rfl, rfl, l, hl', hi₁, ⟨by rw [ht₁]; rfl, fun e he => ?_, by rw [hg₁]; rfl,
    by rw [hc₁]; simp [Mem.recordAt], fun u hu => ?_, ?_, by rw [hb₁]; rfl, .inl (by rw [hb₁]; rfl),
    fun _ _ => by rw [hw₁]; rfl, fun _ ⟨i, l₀, h₀, hle⟩ => ⟨i, l₀, hlk i l₀ h₀, hle⟩,
    (LocsKeep.of_eq (m := m) (m' := m.recordAt L.b L.o 4 .atomicWrite) rfl).trans hks, fun e he => ?_⟩,
    by rw [hcu₁, ← hc]; rfl, by rw [hw₁]; rfl, by rw [hb₁]; rfl, (loc_get hl').2.2⟩
  · rw [hf₁] at he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨rfl, rfl, rfl, rfl, m.current, by rw [ht₁]; exact hc ▸ ht, ?_⟩
      rw [hc₁]; simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]
  · rw [hc₁]; simp only [Mem.recordAt]; rw [getElem!_set!_ite, if_neg (fun h => hu (h.1.trans hc))]
  · rw [hc₁, ← hc]; simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_bump]
  · rw [hf₁] at he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨hc, ?_⟩
      rw [hc₁, ← hc]; simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]

/-- The preparation of an atomic read at the word by thread `t`: the access, the record and
the location. -/
theorem Inv.prepR {G : ThreadId → γ} {m m₁ : Mem} {t li b o : Nat} {blk : Block}
    (hi : L.Inv G m) (hc : m.current = t) (ht : t < m.threads.size)
    (hacc : m.access L.ptr (intSize 32) 4 = pure (b, blk, o))
    (hl : ((Zig.locIdx b o (intSize 32)).run (m.recordAt b o (intSize 32) .atomicRead)).run =
      some (.ok (li, m₁))) :
    b = L.b ∧ o = L.o ∧ ∃ l, L.Loc m₁ li l ∧ L.Inv G m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.waiters = m.waiters ∧ m₁.blocks = m.blocks ∧ m₁.atomics[li]! = l := by
  obtain ⟨blk₀, -, -, -, ha₀, -⟩ := hi.access
  rw [intSize32] at hacc hl
  rw [ha₀] at hacc
  cases hacc
  have hcs : m.current < m.clocks.size := by rw [hi.own.csize, hc]; exact ht
  have hir := hi.record (k := .atomicRead) rfl (hc ▸ ht)
  obtain ⟨l, hl', hi₁, hb₁, hc₁, ht₁, hf₁, hw₁, hcu₁, hg₁, hlk, hks⟩ := hir.locIdx (hc ▸ ht) hl
  refine ⟨rfl, rfl, l, hl', hi₁, ⟨by rw [ht₁]; rfl, fun e he => ?_, by rw [hg₁]; rfl,
    by rw [hc₁]; simp [Mem.recordAt], fun u hu => ?_, ?_, by rw [hb₁]; rfl, .inl (by rw [hb₁]; rfl),
    fun _ _ => by rw [hw₁]; rfl, fun _ ⟨i, l₀, h₀, hle⟩ => ⟨i, l₀, hlk i l₀ h₀, hle⟩,
    (LocsKeep.of_eq (m := m) (m' := m.recordAt L.b L.o 4 .atomicRead) rfl).trans hks, fun e he => ?_⟩,
    by rw [hcu₁, ← hc]; rfl, by rw [hw₁]; rfl, by rw [hb₁]; rfl, (loc_get hl').2.2⟩
  · rw [hf₁] at he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨rfl, rfl, rfl, rfl, m.current, by rw [ht₁]; exact hc ▸ ht, ?_⟩
      rw [hc₁]; simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]
  · rw [hc₁]; simp only [Mem.recordAt]; rw [getElem!_set!_ite, if_neg (fun h => hu (h.1.trans hc))]
  · rw [hc₁, ← hc]; simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_bump]
  · rw [hf₁] at he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · refine .inr ⟨hc, ?_⟩
      rw [hc₁, ← hc]; simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs, VClock.le_refl]

/-- CAS preparation checks a writable pointer but initially records a read. -/
theorem Inv.prepC {G : ThreadId → γ} {m m₁ : Mem} {t li b o : Nat} {blk : Block}
    (hi : L.Inv G m) (hc : m.current = t) (ht : t < m.threads.size)
    (hacc : m.accessW L.ptr (intSize 32) 4 = pure (b, blk, o))
    (hl : ((Zig.locIdx b o (intSize 32)).run (m.recordAt b o (intSize 32) .atomicRead)).run =
      some (.ok (li, m₁))) :
    b = L.b ∧ o = L.o ∧ ∃ l, L.Loc m₁ li l ∧ L.Inv G m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.waiters = m.waiters ∧ m₁.blocks = m.blocks ∧ m₁.atomics[li]! = l := by
  have ha := (accessW_pure (by rw [hacc]; rfl)).1
  exact hi.prepR hc ht ha hl

/-- Each message of the word holds `0`, `1` or `2`; the newest one holds the word. -/
theorem Inv.msgVal {G : ThreadId → γ} {m : Mem} {li j : Nat} {l : ALoc} {v : BitVec 32}
    (hi : L.Inv G m) (hl : L.Loc m li l) (hj : j < l.msgs.size)
    (h : (intOfBytes 32 (l.msgs[j]!).bytes).run = some (.ok v)) :
    ∃ w, L.Val w ∧ v = BitVec.ofNat 32 w ∧ (j = l.msgs.size - 1 → L.U32 m v) := by
  obtain ⟨-, -, -, hval, hlast⟩ := hi.loc.ok li l hl
  obtain ⟨w, hw, hv⟩ := hval j hj
  rw [getElem!_pos l.msgs _ hj, hv] at h
  cases h
  refine ⟨w, hw, rfl, fun e => ?_⟩
  subst e
  unfold Lock.U32; rw [← hlast]
  unfold ALoc.lastBytes
  rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem hj]
  simpa using hv

theorem States.dec {α : Type} [Packed α 32] (S : States α) (hS : S.c = L.c) {w : Nat}
    (hw : L.Val w) :
    ∃ v, (Packed.ofBits? (α := α) (BitVec.ofNat 32 w)).run = some (.ok v) ∧
      ((w = 0 ∧ v = S.unl) ∨ (w = 1 ∧ v = S.one) ∨ (w = L.c ∧ v = S.two)) := by
  rcases hw with rfl | rfl | rfl
  · exact ⟨_, S.dec0, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, S.dec1, .inr (.inl ⟨rfl, rfl⟩)⟩
  · rw [← hS]; exact ⟨_, S.dec2, .inr (.inr ⟨rfl, rfl⟩)⟩

theorem decode_eq {α : Type} [Packed α 32] {b : BitVec 32} {v v' : α}
    (h : (Packed.ofBits? (α := α) b).run = some (.ok v))
    (h' : (Packed.ofBits? (α := α) b).run = some (.ok v')) : v = v' := by
  rw [h] at h'; cases h'; rfl

/-- `lock`'s first try, `cmpxchg(unlocked → locked_once)` with an acquire, by thread `t` at `out`:
on success `t` holds the lock (the word was `0`); else it read `1` (`spin`) or `2` (`wait`). -/
theorem Inv.cas {G : ThreadId → γ} {m m' : Mem} {t c : Nat} {α : Type} [Packed α 32]
    (S : States α) (hS : S.c = L.c) {r : Option α} (hi : L.Inv G m) (hph : L.ph (G t) = .out) (hc : m.current = t)
    (h : ((cmpxchgAs c .acquire .relaxed 4 L.ptr S.unl S.one).run m).run = some (.ok (r, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((r = none ∧ ∃ hL, L.R G hL ∧ L.Inv (upd G t (L.set (G t) .holds hL)) m') ∨
       (r = some S.one ∧ L.Inv (upd G t (L.set (G t) .spin Heap.empty)) m') ∨
       (r = some S.two ∧ L.Inv (upd G t (L.set (G t) .wait Heap.empty)) m')) := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  have core : ∀ o, ((cmpxchgAt c .acquire .relaxed 4 L.ptr (Packed.toBits S.unl)
      (Packed.toBits S.one)).run m).run = some (.ok (o, m')) →
      L.Step t m m' ∧ m'.current = t ∧
      ((o = none ∧ ∃ hL, L.R G hL ∧ L.Inv (upd G t (L.set (G t) .holds hL)) m') ∨
       ∃ w, L.Val w ∧ w ≠ 0 ∧ o = some (BitVec.ofNat 32 w) ∧ L.Inv G m') := by
    intro o ho
    obtain ⟨b, blk, off, li, m₁, pos, old, hacc, -, hl, hpos, hold, hcase⟩ := cmpxchgAt_ok ho
    obtain ⟨rfl, rfl, l, hl', hi₁, hst₁, hcu₁, -, hb₁, hl0⟩ := hi.prepC hc ht hacc hl
    obtain ⟨-, h0, hch, -, -⟩ := hi₁.loc.ok li l hl'
    rw [hl0] at hold
    rcases hcase with ⟨rfl, rfl, -, hm'⟩ | ⟨hne, rfl, hm'⟩
    · -- success: the newest message holds `0`
      have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hpos
        (by rw [hl0]; exact hold)
      rw [hl0] at hpl hm'
      rw [hpl] at hold hm'
      obtain ⟨w, -, -, hU⟩ := hi₁.msgVal hl' (by omega) hold
      have hU0 : L.U32 m₁ (BitVec.ofNat 32 0) := by
        have := hU rfl; rw [S.bits0] at this; exact this
      have hF : L.Free G := (hi₁.free_iff L.val0 hU0).mp rfl
      rw [S.bits1] at hm'
      have ht₁ : t < m₁.threads.size := by rw [hst₁.threads]; exact ht
      have hi₂ := hi₁.record (k := .atomicWrite) rfl (hcu₁ ▸ ht₁)
      have hstR := hi₁.recordStep hcu₁ ht₁ (k := .atomicWrite) rfl
      obtain ⟨hst₂, hcM, hL, hR, hi'⟩ := hi₂.acquire (w' := 1) hl' hcu₁
        (.inl ⟨hph, rfl⟩) hF hm'
      exact ⟨hst₁.trans (hstR.trans hst₂ (.inl rfl)) (.inl hb₁), hcM,
        .inl ⟨rfl, hL, hR, hi'⟩⟩
    · -- failure: a relaxed read
      obtain ⟨hlt, -⟩ := casOpts_pos hpos
      rw [hl0] at hlt
      obtain ⟨w, hw, rfl, -⟩ := hi₁.msgVal hl' hlt hold
      have hw0 : w ≠ 0 := fun e => hne (by rw [e, S.bits0]; rfl)
      have hmM : m' = observeM m₁ li ((m₁.atomics[li]!).msgs[pos]!).id := by
        rw [hm']; unfold loadM; rfl
      refine ⟨hst₁.trans (by rw [hmM]; exact Step.same rfl rfl rfl rfl rfl rfl fun _ _ => Iff.rfl)
        (.inl hb₁),
        by rw [hmM, ← hcu₁]; rfl, .inr ⟨w, hw, hw0, rfl, ?_⟩⟩
      rw [hmM]
      exact hi₁.mono rfl rfl rfl rfl rfl (fun _ => VClock.le_refl _) fun e he => .inl he
  rcases cmpxchgAs_ok h with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hst, hcu, h1 | ⟨w, -, -, he, -⟩⟩ := core none ho
    · exact ⟨hst, hcu, .inl ⟨rfl, h1.2⟩⟩
    · cases he
  · obtain ⟨hst, hcu, ⟨he, -⟩ | ⟨w, hw, hw0, he, hi'⟩⟩ := core (some b) ho
    · cases he
    · cases he
      have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
      have hng : L.ph (G t) ≠ .gone := by rw [hph]; decide
      have hnw : L.ph (G t) ≠ .wait := by rw [hph]; decide
      have hret : ∀ p : LPh, p ≠ .holds → p ≠ .gone →
          L.Inv (upd G t (L.set (G t) p Heap.empty)) m' := fun p hp hpg => by
        have := hi'.queue (c := m'.current) (ws := m'.waiters) (wk := m'.woken) hnh hng hp hpg
          (fq_keep hi' hnw (by rw [hph]; decide))
          (wit_keep hi' hnh hp fun h => by rw [hph] at h; cases h)
        cases m'; exact this
      obtain ⟨v', hv', hcase⟩ := S.dec hS hw
      have := decode_eq hd hv'
      subst this
      refine ⟨hst, hcu, .inr ?_⟩
      rcases hcase with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hw0
      · exact .inl ⟨rfl, hret _ (by decide) (by decide)⟩
      · exact .inr ⟨rfl, hret _ (by decide) (by decide)⟩

/-- An RMW `op` at the word by thread `t`: it reads the newest message (a chain), whose value `w`
is the word, and writes `op.apply w v`. -/
theorem Inv.rmwAt {G : ThreadId → γ} {m m' : Mem} {t c : Nat} {op : RmwOp} {ord : AtomicOrder}
    {v b : BitVec 32} (hi : L.Inv G m) (hc : m.current = t) (ht : t < m.threads.size)
    (h : ((atomicRmwAt c op false ord 4 L.ptr v).run m).run = some (.ok (b, m'))) :
    ∃ m₁ li l w, L.Loc m₁ li l ∧ L.Inv G m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.blocks = m.blocks ∧ L.Val w ∧ b = BitVec.ofNat 32 w ∧ L.U32 m₁ (BitVec.ofNat 32 w) ∧
      m' = rmwM m₁ li (l.msgs.size - 1) ord (l.msgs[l.msgs.size - 1]!) (op.apply false b v) := by
  obtain ⟨b0, blk, off, li, m₁, pos, hacc, -, hl, hpos, hold, hm'⟩ := atomicRmwAt_ok h
  obtain ⟨rfl, rfl, l, hl', hi₁, hst₁, hcu₁, -, hb₁, hl0⟩ := hi.prep hc ht hacc hl
  obtain ⟨-, h0, hch, -, -⟩ := hi₁.loc.ok li l hl'
  have hpl := rmw_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact h0) (by rw [hl0]; exact hch) hpos
  rw [hl0] at hpl hold hm'
  rw [hpl] at hold hm'
  obtain ⟨w, hw, rfl, hU⟩ := hi₁.msgVal hl' (by omega) hold
  exact ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU rfl, hm'⟩

/-- An `xchg` at the word by thread `t`: it reads the newest message (a chain), whose value `w` is
the word, and writes `v`. -/
theorem Inv.xchgAt {G : ThreadId → γ} {m m' : Mem} {t c : Nat} {ord : AtomicOrder} {v b : BitVec 32}
    (hi : L.Inv G m) (hc : m.current = t) (ht : t < m.threads.size)
    (h : ((atomicRmwAt c .xchg false ord 4 L.ptr v).run m).run = some (.ok (b, m'))) :
    ∃ m₁ li l w, L.Loc m₁ li l ∧ L.Inv G m₁ ∧ L.Step t m m₁ ∧ m₁.current = t ∧
      m₁.blocks = m.blocks ∧ L.Val w ∧ b = BitVec.ofNat 32 w ∧ L.U32 m₁ (BitVec.ofNat 32 w) ∧
      m' = rmwM m₁ li (l.msgs.size - 1) ord (l.msgs[l.msgs.size - 1]!) v := by
  obtain ⟨m₁, li, l, w, h1, h2, h3, h4, h5, h6, h7, h8, hm'⟩ := hi.rmwAt hc ht h
  exact ⟨m₁, li, l, w, h1, h2, h3, h4, h5, h6, h7, h8, by simpa only [RmwOp.apply] using hm'⟩

/-- `lock`'s loop, `xchg(contended)` with an acquire, by thread `t` at `spin`: if the word was `0`,
`t` holds the lock; else it goes to the futex wait. -/
theorem Inv.xchgLock {G : ThreadId → γ} {m m' : Mem} {t c : Nat} {α : Type} [Packed α 32]
    (S : States α) (hS : S.c = L.c) {r : α} (hi : L.Inv G m) (hph : L.ph (G t) = .spin) (hc : m.current = t)
    (h : ((atomicRmwAs c .xchg .acquire 4 L.ptr S.two).run m).run = some (.ok (r, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((r = S.unl ∧ ∃ hL, L.R G hL ∧ L.Inv (upd G t (L.set (G t) .holds hL)) m') ∨
       (r ≠ S.unl ∧ L.Inv (upd G t (L.set (G t) .wait Heap.empty)) m')) := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  obtain ⟨b, hb, hd⟩ := atomicRmwAs_ok h
  obtain ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU, hm'⟩ := hi.xchgAt hc ht hb
  rw [S.bits2, hS] at hm'
  obtain ⟨v', hv', hcase⟩ := S.dec hS hw
  have := decode_eq hd hv'
  subst this
  by_cases hw0 : w = 0
  · subst hw0
    have hF : L.Free G := (hi₁.free_iff L.val0 hU).mp rfl
    obtain ⟨hst₂, hcM, hL, hR, hi'⟩ := hi₁.acquire (w' := L.c) hl' hcu₁ (.inr ⟨hph, rfl⟩) hF hm'
    rcases hcase with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inl ⟨rfl, hL, hR, hi'⟩⟩
    · cases h
    · exact absurd h.symm L.c_ne0
  · have hnF : ¬ L.Free G := fun hF => hw0 ((hi₁.free_iff hw hU).mpr hF)
    obtain ⟨hst₂, hcM, hi'⟩ := hi₁.contend hl' hcu₁ hph hnF hm'
    refine ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inr ⟨?_, hi'⟩⟩
    rcases hcase with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact absurd h hw0
    · exact S.ne01.symm
    · exact S.ne02.symm

/-- `unlock`'s `xchg(unlocked)` with a release, by the holder `t`: the word was `1` (`t` goes to
`out`) or `2` (`t` goes to the futex wake). -/
theorem Inv.xchgUnlock {G : ThreadId → γ} {m m' : Mem} {t c : Nat} {α : Type} [Packed α 32]
    (S : States α) (hS : S.c = L.c) {r : α} (hi : L.Inv G m) (hph : L.ph (G t) = .holds) (hc : m.current = t)
    (h : ((atomicRmwAs c .xchg .release 4 L.ptr S.unl).run m).run = some (.ok (r, m'))) :
    L.Step t m m' ∧ m'.current = t ∧ L.Before m' (m.clocks[t]!) ∧
      ((r = S.one ∧ L.Inv (upd G t (L.set (G t) .out Heap.empty)) m') ∨
       (r = S.two ∧ L.Inv (upd G t (L.set (G t) .wake Heap.empty)) m')) := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  obtain ⟨b, hb, hd⟩ := atomicRmwAs_ok h
  obtain ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU, hm'⟩ := hi.xchgAt hc ht hb
  rw [S.bits0] at hm'
  have hw0 : w ≠ 0 := fun e => (hi₁.free_iff hw hU).mp e t hph
  obtain ⟨v', hv', hcase⟩ := S.dec hS hw
  have := decode_eq hd hv'
  subst this
  have hc1 : L.c ≠ 1 := fun h =>
    S.ne12 (decode_eq S.dec1 (by have := S.dec2; rwa [hS, h] at this))
  rcases hcase with ⟨h, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd h hw0
  · obtain ⟨hst₂, hcM, hbf, hi'⟩ := hi₁.release (p := .out) hl' hcu₁ hph hU (.inl ⟨rfl, rfl, hc1⟩) hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, before_le hbf (hst₁.clocks t), .inl ⟨rfl, hi'⟩⟩
  · obtain ⟨hst₂, hcM, hbf, hi'⟩ := hi₁.release (p := .wake) hl' hcu₁ hph hU (.inr ⟨rfl, rfl⟩) hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, before_le hbf (hst₁.clocks t), .inr ⟨rfl, hi'⟩⟩

/-- `Thread.Mutex`'s `tryLock`, `or(1)` with an acquire, by thread `t` at `out` (the word's values
are `0`, `1`, `3`): if the word was `0`, `t` holds the lock; else it read `1` or `3`, the word does
not change, and `t` goes to `spin`. -/
theorem Inv.orLock {G : ThreadId → γ} {m m' : Mem} {t c : Nat} {b : BitVec 32} (hc3 : L.c = 3)
    (hi : L.Inv G m) (hph : L.ph (G t) = .out) (hc : m.current = t)
    (h : ((atomicRmwAt c .or false .acquire 4 L.ptr (1 : BitVec 32)).run m).run =
      some (.ok (b, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((b = 0 ∧ ∃ hL, L.R G hL ∧ L.Inv (upd G t (L.set (G t) .holds hL)) m') ∨
       ((b = 1 ∨ b = 3) ∧ L.Inv (upd G t (L.set (G t) .spin Heap.empty)) m')) := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  obtain ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU, hm'⟩ := hi.rmwAt hc ht h
  rcases hw with rfl | rfl | hwc
  · have hF : L.Free G := (hi₁.free_iff L.val0 hU).mp rfl
    have he : RmwOp.or.apply false (BitVec.ofNat 32 0) (1 : BitVec 32) = BitVec.ofNat 32 1 := by
      decide
    rw [he] at hm'
    obtain ⟨hst₂, hcM, hL, hR, hi'⟩ := hi₁.acquire (w' := 1) hl' hcu₁ (.inl ⟨hph, rfl⟩) hF hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inl ⟨rfl, hL, hR, hi'⟩⟩
  · have he : RmwOp.or.apply false (BitVec.ofNat 32 1) (1 : BitVec 32) = BitVec.ofNat 32 1 := by
      decide
    rw [he] at hm'
    obtain ⟨hst₂, hcM, hi'⟩ := hi₁.rmwKeep hl' hcu₁ (.inl hph) (.inl rfl) L.val1 hU (by decide) hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inr ⟨.inl rfl, hi'⟩⟩
  · subst hwc
    have he : RmwOp.or.apply false (BitVec.ofNat 32 L.c) (1 : BitVec 32) = BitVec.ofNat 32 L.c := by
      rw [hc3]; decide
    rw [he] at hm'
    obtain ⟨hst₂, hcM, hi'⟩ := hi₁.rmwKeep hl' hcu₁ (.inl hph) (.inl rfl) L.valC hU L.c_ne0 hm'
    exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, .inr ⟨.inr (by rw [hc3]; rfl), hi'⟩⟩

/-- An atomic read of the word that is not an acquire, by thread `t`: no place changes. -/
theorem Inv.load {G : ThreadId → γ} {m m' : Mem} {t c : Nat} {ord : AtomicOrder} {v : BitVec 32}
    (hi : L.Inv G m) (hc : m.current = t) (ht : t < m.threads.size) (hord : ord.isAcq = false)
    (h : ((atomicLoadAt (n := 32) c ord 4 L.ptr).run m).run = some (.ok (v, m'))) :
    L.Step t m m' ∧ m'.current = t ∧ L.Inv G m' := by
  obtain ⟨b, blk, off, li, m₁, pos, hacc, -, hl, -, -, hm'⟩ := atomicLoadAt_ok h
  obtain ⟨rfl, rfl, l, hl', hi₁, hst₁, hcu₁, -, hb₁, -⟩ := hi.prepR hc ht hacc hl
  have hmM : m' = observeM m₁ li ((m₁.atomics[li]!).msgs[pos]!).id := by
    rw [hm']; unfold loadM; rw [hord]; rfl
  refine ⟨hst₁.trans (by rw [hmM]; exact Step.same rfl rfl rfl rfl rfl rfl fun _ _ => Iff.rfl)
    (.inl hb₁), by rw [hmM, ← hcu₁]; rfl, ?_⟩
  rw [hmM]
  exact hi₁.mono rfl rfl rfl rfl rfl (fun _ => VClock.le_refl _) fun e he => .inl he

/-! ## No error at the word -/

/-- The access to the word, its race check and its location do not fail. -/
theorem Inv.prep_ok {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m)
    (ht : m.current < m.threads.size) (hg : L.ph (G m.current) ≠ .gone) :
    ∃ blk, m.accessW L.ptr (intSize 32) 4 = pure (L.b, blk, L.o) ∧
      NoRace m L.b L.o (intSize 32) .atomicWrite ∧
      ∀ e, ((Zig.locIdx L.b L.o (intSize 32)).run
        (m.recordAt L.b L.o (intSize 32) .atomicWrite)).run ≠ some (.error e) := by
  obtain ⟨blk, -, -, -, -, ha⟩ := hi.access
  have hir := hi.record (k := .atomicWrite) rfl ht
  refine ⟨blk, ha, hi.noRace rfl ht hg, fun e => locIdx_noErr_of (fun i hf => ?_) (fun hn l hl hb h1 h2 => ?_) e⟩
  · obtain ⟨hi', -, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    rw [getElem!_pos _ i hi', intSize32]
    exact (hir.loc.ok i _ ⟨hf, Array.getElem?_eq_getElem hi'⟩).1
  · have ho := hir.loc.only l hl hb (by rw [intSize32] at h2; exact h2) h1
    have := Array.findIdx?_eq_none_iff.mp hn l hl
    simp [hb, ho] at this

/-- The access of an atomic read of the word, its race check and its location do not fail. -/
theorem Inv.prepR_ok {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m)
    (ht : m.current < m.threads.size) (hg : L.ph (G m.current) ≠ .gone) :
    ∃ blk, m.access L.ptr (intSize 32) 4 = pure (L.b, blk, L.o) ∧
      NoRace m L.b L.o (intSize 32) .atomicRead ∧
      ∀ e, ((Zig.locIdx L.b L.o (intSize 32)).run
        (m.recordAt L.b L.o (intSize 32) .atomicRead)).run ≠ some (.error e) := by
  obtain ⟨blk, -, -, -, ha, -⟩ := hi.access
  have hir := hi.record (k := .atomicRead) rfl ht
  refine ⟨blk, ha, hi.noRace rfl ht hg, fun e => locIdx_noErr_of (fun i hf => ?_) (fun hn l hl hb h1 h2 => ?_) e⟩
  · obtain ⟨hi', -, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    rw [getElem!_pos _ i hi', intSize32]
    exact (hir.loc.ok i _ ⟨hf, Array.getElem?_eq_getElem hi'⟩).1
  · have ho := hir.loc.only l hl hb (by rw [intSize32] at h2; exact h2) h1
    have := Array.findIdx?_eq_none_iff.mp hn l hl
    simp [hb, ho] at this

/-- CAS's initial read record and writable pointer check do not fail. -/
theorem Inv.prepC_ok {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m)
    (ht : m.current < m.threads.size) (hg : L.ph (G m.current) ≠ .gone) :
    ∃ blk, m.accessW L.ptr (intSize 32) 4 = pure (L.b, blk, L.o) ∧
      NoRace m L.b L.o (intSize 32) .atomicRead ∧
      ∀ e, ((Zig.locIdx L.b L.o (intSize 32)).run
        (m.recordAt L.b L.o (intSize 32) .atomicRead)).run ≠ some (.error e) := by
  obtain ⟨blk, -, -, -, -, ha⟩ := hi.access
  obtain ⟨_, -, hnr, hloc⟩ := hi.prepR_ok ht hg
  exact ⟨blk, ha, hnr, hloc⟩

/-- A successful CAS may add its write access after preparing the read. -/
theorem Inv.casWrite_noErr {G : ThreadId → γ} {m m₁ : Mem} {li : Nat} {opts : Array Nat}
    {expected : BitVec 32} (hi : L.Inv G m) (ht : m.current < m.threads.size)
    (hg : L.ph (G m.current) ≠ .gone)
    (hp : ((casPrep 32 4 L.ptr expected).run m).run = some (.ok ((li, opts), m₁))) (e : Error) :
    ((casMarkWrite 32 4 L.ptr).run m₁).run ≠ some (.error e) := by
  obtain ⟨b, blk, o, ha, -, hl, -⟩ := casPrep_ok hp
  obtain ⟨rfl, rfl, _, _, hi₁, hs, hc, -⟩ := hi.prepC rfl ht ha hl
  obtain ⟨blk₁, ha₁, hnr, -⟩ := hi₁.prep_ok
    (by rw [hc, hs.threads]; exact ht) (by rw [hc]; exact hg)
  rw [casMarkWrite_run ha₁ hnr]
  simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

/-- An atomic read of the word that is not an acquire (`Thread.Mutex`'s relaxed load) does not
throw: each option is a message, which holds a value. -/
theorem Inv.load_noErr {G : ThreadId → γ} {m : Mem} {c : Nat} {ord : AtomicOrder} (hi : L.Inv G m)
    (ht : m.current < m.threads.size)
    (hg : L.ph (G m.current) ≠ .gone)
    (hcr : c < loadCount 32 ord 4 L.ptr m ∨ loadCount 32 ord 4 L.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicLoadAt (n := 32) c ord 4 L.ptr).run m).run ≠ some (.error e) := by
  obtain ⟨blk, hacc, hnr, hloc⟩ := hi.prepR_ok ht hg
  refine atomicLoadAt_noErr (loadPrep_noErr (by simpa using hacc) (by simpa using hnr)
    (by simpa using hloc)) (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at ha hl
  obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0⟩ := hi.prepR rfl ht ha hl
  obtain ⟨-, h0, -, hval, -⟩ := hi₁.loc.ok li l hl'
  have hne := readOpts_ne (m := m₁) (li := li) (by rw [hl0]; exact h0)
  have hcnt : loadCount 32 ord 4 L.ptr m = (readOpts m₁ li false).size := by
    unfold loadCount; rw [optCount_eq hp]
  have hc : c < (readOpts m₁ li false).size := by rw [hcnt] at hcr; omega
  have hlt := readOpts_lt (Array.getElem?_eq_getElem hc)
  rw [hl0] at hlt ⊢
  obtain ⟨w, -, hw⟩ := hval _ hlt
  exact ⟨_, Array.getElem?_eq_getElem hc, _, by rw [getElem!_pos l.msgs _ hlt]; exact hw⟩

/-- `lock`'s `cmpxchg` does not throw: each option is a message, which holds a state. -/
theorem Inv.cas_noErr {G : ThreadId → γ} {m : Mem} {c : Nat} {α : Type} [Packed α 32]
    (S : States α) (hS : S.c = L.c) (hi : L.Inv G m) (ht : m.current < m.threads.size)
    (hg : L.ph (G m.current) ≠ .gone)
    (hcr : c < casCount 32 .acquire 4 L.ptr (Packed.toBits S.unl) m ∨
      casCount 32 .acquire 4 L.ptr (Packed.toBits S.unl) m = 0 ∧ c = 0) (e : Error) :
    ((cmpxchgAs c .acquire .relaxed 4 L.ptr S.unl S.one).run m).run ≠ some (.error e) := by
  obtain ⟨blk, hacc, hnr, hloc⟩ := hi.prepC_ok ht hg
  have hprep : ∀ e, ((casPrep 32 4 L.ptr (Packed.toBits S.unl)).run m).run ≠ some (.error e) :=
    casPrep_noErr hacc hnr hloc
  refine cmpxchgAs_noErr (cmpxchgAt_noErr hprep ?_
    (fun _ _ _ hp => hi.casWrite_noErr ht hg hp)) ?_ e
  · intro li opts m₁ hp
    obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := casPrep_ok hp
    obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0⟩ := hi.prepC rfl ht ha hl
    obtain ⟨-, hsz, -, hval, -⟩ := hi₁.loc.ok li l hl'
    have hne := casOpts_ne (e := Packed.toBits S.unl) (m := m₁) (li := li) (by rw [hl0]; exact hsz)
    have hcnt : casCount 32 .acquire 4 L.ptr (Packed.toBits S.unl) m =
        (casOpts m₁ li (Packed.toBits S.unl)).size := by
      unfold casCount; rw [optCount_eq hp]
    have hc : c < (casOpts m₁ li (Packed.toBits S.unl)).size := by rw [hcnt] at hcr; omega
    refine ⟨_, Array.getElem?_eq_getElem hc, ?_⟩
    have hpl := (casOpts_pos (Array.getElem?_eq_getElem hc)).1
    rw [hl0] at hpl
    obtain ⟨w, -, hw⟩ := hval _ hpl
    exact ⟨_, by rw [hl0, getElem!_pos l.msgs _ hpl]; exact hw⟩
  · intro b m' hb
    obtain ⟨b0, blk', o, li, m₁, pos, old, hacc', -, hl, hpos, hold, hcase⟩ := cmpxchgAt_ok hb
    obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0⟩ := hi.prepC rfl ht hacc' hl
    rcases hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · cases h
    · cases h
      rw [hl0] at hold
      have hpl := (casOpts_pos hpos).1
      rw [hl0] at hpl
      obtain ⟨w, hw, rfl, -⟩ := hi₁.msgVal hl' hpl hold
      obtain ⟨v, hv, -⟩ := S.dec hS hw
      exact ⟨v, hv⟩

/-- An RMW on bits at the word does not throw: it reads the newest message, which holds a value. -/
theorem Inv.rmw_noErr {G : ThreadId → γ} {m : Mem} {c : Nat} {op : RmwOp} {ord : AtomicOrder}
    {v : BitVec 32} (hi : L.Inv G m) (ht : m.current < m.threads.size)
    (hg : L.ph (G m.current) ≠ .gone)
    (hcr : c < rmwCount 32 ord 4 L.ptr m ∨ rmwCount 32 ord 4 L.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicRmwAt c op false ord 4 L.ptr v).run m).run ≠ some (.error e) := by
  obtain ⟨blk, hacc, hnr, hloc⟩ := hi.prep_ok ht hg
  have hprep : ∀ e, ((loadPrep 32 ord 4 L.ptr true).run m).run ≠ some (.error e) :=
    loadPrep_noErr (by simpa using hacc) (by simpa using hnr) (by simpa using hloc)
  refine atomicRmwAt_noErr hprep (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := loadPrep_ok hp
  simp only [↓reduceIte] at ha hl
  obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0⟩ := hi.prep rfl ht ha hl
  obtain ⟨-, hsz, hch, hval, -⟩ := hi₁.loc.ok li l hl'
  have hro : readOpts m₁ li true = #[l.msgs.size - 1] := by
    rw [readOpts_chain (by rw [hl0]; exact hsz) (by rw [hl0]; exact hch), hl0]
  have hcnt : rmwCount 32 ord 4 L.ptr m = 1 := by
    unfold rmwCount; rw [optCount_eq hp, hro]; rfl
  have hc0 : c = 0 := by rw [hcnt] at hcr; omega
  subst hc0
  refine ⟨l.msgs.size - 1, by rw [hro]; rfl, ?_⟩
  obtain ⟨w, -, hw⟩ := hval (l.msgs.size - 1) (by omega)
  exact ⟨_, by rw [hl0, getElem!_pos l.msgs _ (by omega)]; exact hw⟩

/-- An `xchg` at the word does not throw: it reads the newest message, which holds a state. -/
theorem Inv.xchg_noErr {G : ThreadId → γ} {m : Mem} {c : Nat} {ord : AtomicOrder} {α : Type}
    [Packed α 32] (S : States α) (hS : S.c = L.c) {v : α} (hi : L.Inv G m) (ht : m.current < m.threads.size)
    (hg : L.ph (G m.current) ≠ .gone)
    (hcr : c < rmwCount 32 ord 4 L.ptr m ∨ rmwCount 32 ord 4 L.ptr m = 0 ∧ c = 0) (e : Error) :
    ((atomicRmwAs c .xchg ord 4 L.ptr v).run m).run ≠ some (.error e) := by
  obtain ⟨blk, hacc, hnr, hloc⟩ := hi.prep_ok ht hg
  have hprep : ∀ e, ((loadPrep 32 ord 4 L.ptr true).run m).run ≠ some (.error e) :=
    loadPrep_noErr (by simpa using hacc) (by simpa using hnr) (by simpa using hloc)
  refine atomicRmwAs_noErr (atomicRmwAt_noErr hprep ?_) ?_ e
  · intro li opts m₁ hp
    obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := loadPrep_ok hp
    simp only [↓reduceIte] at ha hl
    obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0⟩ := hi.prep rfl ht ha hl
    obtain ⟨-, hsz, hch, hval, -⟩ := hi₁.loc.ok li l hl'
    have hro : readOpts m₁ li true = #[l.msgs.size - 1] := by
      rw [readOpts_chain (by rw [hl0]; exact hsz) (by rw [hl0]; exact hch), hl0]
    have hcnt : rmwCount 32 ord 4 L.ptr m = 1 := by
      unfold rmwCount; rw [optCount_eq hp, hro]; rfl
    have hc0 : c = 0 := by rw [hcnt] at hcr; omega
    subst hc0
    refine ⟨l.msgs.size - 1, by rw [hro]; rfl, ?_⟩
    obtain ⟨w, -, hw⟩ := hval (l.msgs.size - 1) (by omega)
    exact ⟨_, by rw [hl0, getElem!_pos l.msgs _ (by omega)]; exact hw⟩
  · intro b m' hb
    obtain ⟨m₁, li, l, w, -, -, -, -, -, hw, rfl, -, -⟩ := hi.xchgAt rfl ht hb
    obtain ⟨v, hv, -⟩ := S.dec hS hw
    exact ⟨v, hv⟩

/-- The futex wait at the word does not throw. -/
theorem Inv.wait_ok {G : ThreadId → γ} {m : Mem} {t : ThreadId} {e : BitVec 32}
    (hi : L.Inv G m) :
    ∃ b m', ((Thread.futexWait L.ptr e).run { m with current := t }).run = some (.ok (b, m')) := by
  by_cases hw : ({ m with current := t } : Mem).woken.contains ({ m with current := t } : Mem).current = true
  · exact ⟨_, _, futexWait_run_woken hw⟩
  · obtain ⟨blk, hb, -, -, ha, -⟩ := hi.access
    obtain ⟨w, -, hu, -⟩ := hi.word
    rw [u32_bytes hb] at hu
    exact ⟨_, _, futexWait_run_go (by simpa using hw) ha hu⟩

/-! ### `Thread.Mutex` (0.15.2, macOS): `os_unfair_lock`, with the word `0` or `1` (`L.c = 1`)

The model (`Zig.osUnfairLockC`, `Zig.osUnfairUnlockC`, `ZigLean/Conc/Call.lean`): the lock is a loop
of an acquire `cmpxchg` `0 → 1` that, on a failure, waits at the futex while the word is `1`; the
unlock is a release `xchg` of `0` and a wake. The contended value is `1`: a thread that finds the
word `1` goes to `wait`, and the holder goes to `wake` at its unlock. -/

/-- `os_unfair_lock_lock`'s `cmpxchg` `0 → 1` with an acquire, by thread `t` at `out` (the first
try) or `spin` (after a futex wait): on success `t` holds the lock; else it read `1` and goes to
`wait`. -/
theorem Inv.casD {G : ThreadId → γ} {m m' : Mem} {t c : Nat} {r : Option (BitVec 32)}
    (hc1 : L.c = 1) (hi : L.Inv G m) (hph : L.ph (G t) = .out ∨ L.ph (G t) = .spin)
    (hc : m.current = t)
    (h : ((cmpxchgAt c .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1).run m).run =
      some (.ok (r, m'))) :
    L.Step t m m' ∧ m'.current = t ∧
      ((r = none ∧ ∃ hL, L.R G hL ∧ L.Inv (upd G t (L.set (G t) .holds hL)) m') ∨
       (r = some (BitVec.ofNat 32 L.c) ∧
        L.Inv (upd G t (L.set (G t) .wait Heap.empty)) m')) := by
  have hng : L.ph (G t) ≠ .gone := by rcases hph with h | h <;> rw [h] <;> decide
  have hnh : L.ph (G t) ≠ .holds := by rcases hph with h | h <;> rw [h] <;> decide
  have hnw : L.ph (G t) ≠ .wait := by rcases hph with h | h <;> rw [h] <;> decide
  have hna : L.ph (G t) ≠ .away := by rcases hph with h | h <;> rw [h] <;> decide
  obtain ⟨ht, -⟩ := hi.live t hng
  obtain ⟨b, blk, off, li, m₁, pos, old, hacc, -, hl, hpos, hold, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨rfl, rfl, l, hl', hi₁, hst₁, hcu₁, -, hb₁, hl0⟩ := hi.prepC hc ht hacc hl
  obtain ⟨-, h0, hch, -, -⟩ := hi₁.loc.ok li l hl'
  rw [hl0] at hold
  rcases hcase with ⟨rfl, rfl, -, hm'⟩ | ⟨hne, rfl, hm'⟩
  · -- success: the newest message holds `0`
    have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hpos
      (by rw [hl0]; exact hold)
    rw [hl0] at hpl hm'
    rw [hpl] at hold hm'
    obtain ⟨w, -, -, hU⟩ := hi₁.msgVal hl' (by omega) hold
    have hU0 : L.U32 m₁ (BitVec.ofNat 32 0) := hU rfl
    have hF : L.Free G := (hi₁.free_iff L.val0 hU0).mp rfl
    have ht₁ : t < m₁.threads.size := by rw [hst₁.threads]; exact ht
    have hi₂ := hi₁.record (k := .atomicWrite) rfl (hcu₁ ▸ ht₁)
    have hstR := hi₁.recordStep hcu₁ ht₁ (k := .atomicWrite) rfl
    obtain ⟨hst₂, hcM, hL, hR, hi'⟩ := hi₂.acquire (w' := 1) hl' hcu₁
      (hph.elim (fun h => .inl ⟨h, rfl⟩) fun h => .inr ⟨h, hc1.symm⟩) hF hm'
    exact ⟨hst₁.trans (hstR.trans hst₂ (.inl rfl)) (.inl hb₁), hcM,
      .inl ⟨rfl, hL, hR, hi'⟩⟩
  · -- failure: a relaxed read of `1`
    obtain ⟨hlt, -⟩ := casOpts_pos hpos
    rw [hl0] at hlt
    obtain ⟨w, hw, rfl, -⟩ := hi₁.msgVal hl' hlt hold
    have hw0 : w ≠ 0 := fun e => hne (by rw [e]; rfl)
    have hwc : w = L.c := by rcases hw with h | h | h <;> omega
    have hmM : m' = observeM m₁ li ((m₁.atomics[li]!).msgs[pos]!).id := by
      rw [hm']; unfold loadM; rfl
    have hi' : L.Inv G m' := by
      rw [hmM]
      exact hi₁.mono rfl rfl rfl rfl rfl (fun _ => VClock.le_refl _) fun e he => .inl he
    have hq := hi'.queue (c := m'.current) (ws := m'.waiters) (wk := m'.woken) (p := .wait) hnh hng
      (by decide) (by decide) (fq_keep hi' hnw hna) (wit_keep hi' hnh (by decide) fun _ => rfl)
    cases m'
    exact ⟨hst₁.trans (by rw [hmM]; exact Step.same rfl rfl rfl rfl rfl rfl fun _ _ => Iff.rfl)
      (.inl hb₁), by rw [hmM, ← hcu₁]; rfl, .inr ⟨by rw [hwc], hq⟩⟩

/-- `os_unfair_lock_lock`'s `cmpxchg` does not throw. -/
theorem Inv.casD_noErr {G : ThreadId → γ} {m : Mem} {c : Nat} (hi : L.Inv G m)
    (ht : m.current < m.threads.size) (hg : L.ph (G m.current) ≠ .gone)
    (hcr : c < casCount 32 .acquire 4 L.ptr (0 : BitVec 32) m ∨
      casCount 32 .acquire 4 L.ptr (0 : BitVec 32) m = 0 ∧ c = 0) (e : Error) :
    ((cmpxchgAt c .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1).run m).run ≠
      some (.error e) := by
  obtain ⟨blk, hacc, hnr, hloc⟩ := hi.prepC_ok ht hg
  have hprep : ∀ e, ((casPrep 32 4 L.ptr (0 : BitVec 32)).run m).run ≠ some (.error e) :=
    casPrep_noErr hacc hnr hloc
  refine cmpxchgAt_noErr hprep ?_ (fun _ _ _ hp => hi.casWrite_noErr ht hg hp) e
  intro li opts m₁ hp
  obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := casPrep_ok hp
  obtain ⟨rfl, rfl, l, hl', hi₁, -, -, -, -, hl0⟩ := hi.prepC rfl ht ha hl
  obtain ⟨-, hsz, -, hval, -⟩ := hi₁.loc.ok li l hl'
  have hne := casOpts_ne (e := (0 : BitVec 32)) (m := m₁) (li := li) (by rw [hl0]; exact hsz)
  have hcnt : casCount 32 .acquire 4 L.ptr (0 : BitVec 32) m =
      (casOpts m₁ li (0 : BitVec 32)).size := by
    unfold casCount; rw [optCount_eq hp]
  have hc : c < (casOpts m₁ li (0 : BitVec 32)).size := by rw [hcnt] at hcr; omega
  refine ⟨_, Array.getElem?_eq_getElem hc, ?_⟩
  have hpl := (casOpts_pos (Array.getElem?_eq_getElem hc)).1
  rw [hl0] at hpl
  obtain ⟨w, -, hw⟩ := hval _ hpl
  exact ⟨_, by rw [hl0, getElem!_pos l.msgs _ hpl]; exact hw⟩

/-- `os_unfair_lock_unlock`'s `xchg` of `0` with a release, by the holder `t`: `t` goes to the
futex wake. -/
theorem Inv.xchgRel {G : ThreadId → γ} {m m' : Mem} {t c : Nat} {b : BitVec 32}
    (hc1 : L.c = 1) (hi : L.Inv G m) (hph : L.ph (G t) = .holds) (hc : m.current = t)
    (h : ((atomicRmwAt c .xchg false .release 4 L.ptr (0 : BitVec 32)).run m).run =
      some (.ok (b, m'))) :
    L.Step t m m' ∧ m'.current = t ∧ L.Before m' (m.clocks[t]!) ∧
      L.Inv (upd G t (L.set (G t) .wake Heap.empty)) m' := by
  obtain ⟨ht, -⟩ := hi.live t (by rw [hph]; decide)
  obtain ⟨m₁, li, l, w, hl', hi₁, hst₁, hcu₁, hb₁, hw, rfl, hU, hm'⟩ := hi.xchgAt hc ht h
  have hw0 : w ≠ 0 := fun e => (hi₁.free_iff hw hU).mp e t hph
  have hwc : w = L.c := by rcases hw with h | h | h <;> omega
  obtain ⟨hst₂, hcM, hbf, hi'⟩ := hi₁.release (p := .wake) hl' hcu₁ hph hU (.inr ⟨hwc, rfl⟩) hm'
  exact ⟨hst₁.trans hst₂ (.inl hb₁), hcM, before_le hbf (hst₁.clocks t), hi'⟩

/-! ## A protocol with the lock -/

variable {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Mem → Prop} {ok : γ → Prop}

/-- If every thread has ended, sleeps at a futex or waits at a join, no thread waits at the
word: the queue's witness would go on. -/
theorem FitsOn.noWaits (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m)
    (hall : ∀ u < m.threads.size, P.fin (G u) ∨ m.waiters.any (·.1 == u) = true ∨ P.joins (G u)) :
    ¬ L.Waits m.waiters := fun hp => by
  obtain ⟨v, hv, hq, hb, -⟩ := hi.wit hp
  rcases hall v hv with h | h | h
  · rw [hP.fin _ h] at hb; cases hb
  · rw [hq] at h; cases h
  · rw [hP.joins _ h] at hb; cases hb

/-- A thread at `lock`'s futex wait is not the last one (`FitsOn.noWaits`). -/
theorem FitsOn.live (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m)
    {t : ThreadId} (ht : L.ph (G t) = .wait) : P.Live t G m := by
  intro hw hall
  apply hP.noWaits hi hall
  obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hw
  have he : (m.waiters[i]).1 = t := by simpa using he
  rcases hi.fq _ (Array.getElem_mem hi') with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact Array.any_eq_true.mpr ⟨i, hi', by simp [h1]⟩
  · rw [he, ht] at h2; cases h2

theorem FitsOn.lock (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m : Mem} (hi : P.inv G m) : L.Inv G m :=
  ((hP.inv G m).mp hi).1

/-- A lock step with `t`'s new place and resource keeps the protocol's invariant. -/
theorem FitsOn.step (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {p : LPh}
    {h : Heap} (hi : P.inv G m) (hok : ok (G t)) (hph : L.ph (G t) ≠ .gone) (hs : L.Step t m m')
    (hrel : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!))
    (hl : L.Inv (upd G t (L.set (G t) p h)) m') : P.inv (upd G t (L.set (G t) p h)) m' :=
  (hP.inv _ _).mpr ⟨hl, hP.stable G m m' t p h hok hph ((hP.inv G m).mp hi).2 hs hrel⟩

/-- A lock step with the same ghost values keeps the protocol's invariant. -/
theorem FitsOn.stay (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m m' : Mem} {t : ThreadId}
    (hi : P.inv G m) (hok : ok (G t)) (hph : L.ph (G t) ≠ .gone) (hs : L.Step t m m')
    (hl : L.Inv G m') :
    P.inv G m' := by
  have := hP.step (p := L.ph (G t)) (h := L.held (G t)) hi hok hph hs (fun h1 h2 => absurd h1 h2)
    (by rw [upd_set_self]; exact hl)
  rwa [upd_set_self] at this

/-! ## The ops in generated code (`WP`) -/

variable {σ α : Type} [Packed α 32]

/-- The protocol's invariant at a stop of `t`: the same, with `current := t`. -/
theorem FitsOn.cur (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m : Mem} (t : ThreadId)
    (hi : P.inv G m) (hok : ok (G t)) (hph : L.ph (G t) ≠ .gone) :
    P.inv G { m with current := t } :=
  hP.stay (t := t) hi hok hph (Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl))
    ((hP.lock hi).current t)

theorem FitsOn.alive (hP : L.FitsOn P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ}
    (hi : P.inv G m) (hg : G t = g) (hph : L.ph g ≠ .gone) : t < m.threads.size :=
  ((hP.lock hi).live t (by rw [hg]; exact hph)).1

/-- `lock`'s first try, `cmpxchg(unlocked → locked_once)`, by thread `t` at `out` (`g`). -/
theorem wp_casOn (hP : L.FitsOn P U ok) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ hL, P.inv (upd G₁ t (L.set g .holds hL)) m') ∨
       (r = some S.one ∧ P.inv (upd G₁ t (L.set g .spin Heap.empty)) m') ∨
       (r = some S.two ∧ P.inv (upd G₁ t (L.set g .wait Heap.empty)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((cmpxchgAsC .acquire .relaxed 4 L.ptr S.unl S.one : CM Tgt σ (Option α)).run s)
      Q G m n := by
  unfold cmpxchgAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hgone : L.ph (G₁ t) ≠ .gone := by rw [hg₁, hg]; decide
  have hok₁ : ok (G₁ t) := by rw [hg₁]; exact hok
  have hiP := hP.cur t hi₁ hok₁ hgone
  have hiL := hP.lock hiP
  have ht := hP.alive hiP hg₁ (by rw [hg]; decide)
  refine WP.callMC (fun e he => (hiL.cas_noErr S hS ht hgone hcr e he).elim) fun r m' hr => ?_
  obtain ⟨hst, hcu, hcase⟩ := hiL.cas S hS (by rw [hg₁]; exact hg) rfl hr
  refine ⟨by rw [hst.threads], h k hk G₁ m' r hcu ?_⟩
  rw [hg₁] at hcase
  rcases hcase with ⟨rfl, hL, -, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩
  · refine .inl ⟨rfl, hL, ?_⟩
    have := hP.step (p := .holds) (h := hL) hiP hok₁ hgone hst
      (fun h => absurd h (by rw [hg₁, hg]; decide)) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this
  · refine .inr (.inl ⟨rfl, ?_⟩)
    have := hP.step (p := .spin) (h := Heap.empty) hiP hok₁ hgone hst
      (fun h => absurd h (by rw [hg₁, hg]; decide)) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this
  · refine .inr (.inr ⟨rfl, ?_⟩)
    have := hP.step (p := .wait) (h := Heap.empty) hiP hok₁ hgone hst
      (fun h => absurd h (by rw [hg₁, hg]; decide)) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this

/-- `lock`'s loop, `xchg(contended)`, by thread `t` at `spin` (`g`). -/
theorem wp_xchgLockOn (hP : L.FitsOn P U ok) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .spin) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.unl ∧ ∃ hL, P.inv (upd G₁ t (L.set g .holds hL)) m') ∨
       (r ≠ S.unl ∧ P.inv (upd G₁ t (L.set g .wait Heap.empty)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC .xchg .acquire 4 L.ptr S.two : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hgone : L.ph (G₁ t) ≠ .gone := by rw [hg₁, hg]; decide
  have hok₁ : ok (G₁ t) := by rw [hg₁]; exact hok
  have hiP := hP.cur t hi₁ hok₁ hgone
  have hiL := hP.lock hiP
  have ht := hP.alive hiP hg₁ (by rw [hg]; decide)
  refine WP.callMC (fun e he => (hiL.xchg_noErr S hS ht hgone hcr e he).elim) fun r m' hr => ?_
  obtain ⟨hst, hcu, hcase⟩ := hiL.xchgLock S hS (by rw [hg₁]; exact hg) rfl hr
  refine ⟨by rw [hst.threads], h k hk G₁ m' r hcu ?_⟩
  rw [hg₁] at hcase
  rcases hcase with ⟨hr', hL, -, hl⟩ | ⟨hr', hl⟩
  · refine .inl ⟨hr', hL, ?_⟩
    have := hP.step (p := .holds) (h := hL) hiP hok₁ hgone hst
      (fun h => absurd h (by rw [hg₁, hg]; decide)) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this
  · refine .inr ⟨hr', ?_⟩
    have := hP.step (p := .wait) (h := Heap.empty) hiP hok₁ hgone hst
      (fun h => absurd h (by rw [hg₁, hg]; decide)) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this

/-- `unlock`'s `xchg(unlocked)`, by the holder `t` (`g`). -/
theorem wp_xchgUnlockOn (hP : L.FitsOn P U ok) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .holds) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.one ∧ P.inv (upd G₁ t (L.set g .out Heap.empty)) m') ∨
       (r = S.two ∧ P.inv (upd G₁ t (L.set g .wake Heap.empty)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC .xchg .release 4 L.ptr S.unl : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hgone : L.ph (G₁ t) ≠ .gone := by rw [hg₁, hg]; decide
  have hok₁ : ok (G₁ t) := by rw [hg₁]; exact hok
  have hiP := hP.cur t hi₁ hok₁ hgone
  have hiL := hP.lock hiP
  have ht := hP.alive hiP hg₁ (by rw [hg]; decide)
  refine WP.callMC (fun e he => (hiL.xchg_noErr S hS ht hgone hcr e he).elim) fun r m' hr => ?_
  obtain ⟨hst, hcu, hbf, hcase⟩ := hiL.xchgUnlock S hS (by rw [hg₁]; exact hg) rfl hr
  refine ⟨by rw [hst.threads], h k hk G₁ m' r hcu ?_⟩
  rw [hg₁] at hcase
  rcases hcase with ⟨hr', hl⟩ | ⟨hr', hl⟩
  · refine .inl ⟨hr', ?_⟩
    have := hP.step (p := .out) (h := Heap.empty) hiP hok₁ hgone hst
      (fun _ _ => hbf) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this
  · refine .inr ⟨hr', ?_⟩
    have := hP.step (p := .wake) (h := Heap.empty) hiP hok₁ hgone hst
      (fun _ _ => hbf) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this

/-- `lock`'s futex wait for `contended`, by thread `t` at `wait` (`g`): it goes on at `spin`. -/
theorem wp_waitOn (hP : L.FitsOn P U ok) (S : States α) (hS : S.c = L.c) {io : Io} {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait) (hok : ok g)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin Heap.empty)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWaitC io L.ptr S.two : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWaitC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  have he : (Packed.toBits S.two).setWidth 32 = BitVec.ofNat 32 L.c := by rw [S.bits2, hS]; rfl
  simp only [he]
  have hiL := hP.lock hi₁
  refine ⟨fun _ => hP.live hiL (by rw [hg₁]; exact hg), fun hq => ⟨fun _ => hiL.wait_ok, fun b m' hw => ?_⟩⟩
  have hgo : ∀ m', L.Step t m₁ m' → m'.current = t →
      L.Inv (upd G₁ t (L.set (G₁ t) .spin Heap.empty)) m' → Q ((), s) G₁ m' k := by
    intro m' hst hcu hl
    refine h k hk G₁ m' hcu ?_
    have := hP.step (p := .spin) (h := Heap.empty) hi₁ (by rw [hg₁]; exact hok)
      (by rw [hg₁, hg]; decide) hst
      (fun h => absurd h (by rw [hg₁, hg]; decide)) hl
    rwa [hg₁] at this
  obtain ⟨hst, hb⟩ := hiL.wait (by rw [hg₁]; exact hg) hq hw
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
    exact hgo m' hst hb.1 hb.2
  · simp only [↓reduceIte] at hb ⊢
    obtain ⟨hst', hcu', hl'⟩ := hiL.spurious (by rw [hg₁]; exact hg) hq
    exact ⟨hP.stay hi₁ (by rw [hg₁]; exact hok) (by rw [hg₁, hg]; decide) hst hb,
      hgo _ hst' hcu' hl'⟩

/-- `unlock`'s futex wake of one waiter, by thread `t` at `wake` (`g`): it goes on at `out`. -/
theorem wp_wakeOn (hP : L.FitsOn P U ok) {io : Io} {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wake) (hok : ok g) (hi : P.inv (upd G t g) m)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .out Heap.empty)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWakeC io L.ptr (1 : BitVec 32) : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWakeC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ m' hw => ?_⟩
  obtain ⟨hst, hcu, hl⟩ := (hP.lock hi₁).wake (by rw [hg₁]; exact hg) (by decide) hw
  refine h k hk G₁ m' hcu ?_
  have := hP.step (p := .out) (h := Heap.empty) hi₁ (by rw [hg₁]; exact hok)
    (by rw [hg₁, hg]; decide) hst
    (fun h => absurd h (by rw [hg₁, hg]; decide)) hl
  rwa [hg₁] at this

/-! ### `Fits`: every thread runs the lock's code -/

theorem Fits.noWaits (hP : L.Fits P U) {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m)
    (hall : ∀ u < m.threads.size, P.fin (G u) ∨ m.waiters.any (·.1 == u) = true ∨ P.joins (G u)) :
    ¬ L.Waits m.waiters := hP.on.noWaits hi hall

theorem Fits.live (hP : L.Fits P U) {G : ThreadId → γ} {m : Mem} (hi : L.Inv G m)
    {t : ThreadId} (ht : L.ph (G t) = .wait) : P.Live t G m := hP.on.live hi ht

theorem Fits.lock (hP : L.Fits P U) {G : ThreadId → γ} {m : Mem} (hi : P.inv G m) : L.Inv G m :=
  hP.on.lock hi

theorem Fits.step (hP : L.Fits P U) {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {p : LPh}
    {h : Heap} (hi : P.inv G m) (hph : L.ph (G t) ≠ .gone) (hs : L.Step t m m')
    (hrel : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!))
    (hl : L.Inv (upd G t (L.set (G t) p h)) m') : P.inv (upd G t (L.set (G t) p h)) m' :=
  hP.on.step hi trivial hph hs hrel hl

theorem Fits.stay (hP : L.Fits P U) {G : ThreadId → γ} {m m' : Mem} {t : ThreadId}
    (hi : P.inv G m) (hph : L.ph (G t) ≠ .gone) (hs : L.Step t m m') (hl : L.Inv G m') :
    P.inv G m' := hP.on.stay hi trivial hph hs hl

theorem Fits.cur (hP : L.Fits P U) {G : ThreadId → γ} {m : Mem} (t : ThreadId)
    (hi : P.inv G m) (hph : L.ph (G t) ≠ .gone) : P.inv G { m with current := t } :=
  hP.on.cur t hi trivial hph

theorem Fits.alive (hP : L.Fits P U) {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ}
    (hi : P.inv G m) (hg : G t = g) (hph : L.ph g ≠ .gone) : t < m.threads.size :=
  hP.on.alive hi hg hph

theorem wp_cas (hP : L.Fits P U) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ hL, P.inv (upd G₁ t (L.set g .holds hL)) m') ∨
       (r = some S.one ∧ P.inv (upd G₁ t (L.set g .spin Heap.empty)) m') ∨
       (r = some S.two ∧ P.inv (upd G₁ t (L.set g .wait Heap.empty)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((cmpxchgAsC .acquire .relaxed 4 L.ptr S.unl S.one : CM Tgt σ (Option α)).run s)
      Q G m n := wp_casOn hP.on S hS hg trivial hi h

theorem wp_xchgLock (hP : L.Fits P U) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .spin) (hi : P.inv (upd G t g) m)
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.unl ∧ ∃ hL, P.inv (upd G₁ t (L.set g .holds hL)) m') ∨
       (r ≠ S.unl ∧ P.inv (upd G₁ t (L.set g .wait Heap.empty)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC .xchg .acquire 4 L.ptr S.two : CM Tgt σ α).run s) Q G m n :=
  wp_xchgLockOn hP.on S hS hg trivial hi h

theorem wp_xchgUnlock (hP : L.Fits P U) (S : States α) (hS : S.c = L.c) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .holds)
    (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = S.one ∧ P.inv (upd G₁ t (L.set g .out Heap.empty)) m') ∨
       (r = S.two ∧ P.inv (upd G₁ t (L.set g .wake Heap.empty)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC .xchg .release 4 L.ptr S.unl : CM Tgt σ α).run s) Q G m n :=
  wp_xchgUnlockOn hP.on S hS hg trivial hi h

theorem wp_wait (hP : L.Fits P U) (S : States α) (hS : S.c = L.c) {io : Io} {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin Heap.empty)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWaitC io L.ptr S.two : CM Tgt σ Unit).run s) Q G m n :=
  wp_waitOn hP.on S hS hg trivial hi h

theorem wp_wake (hP : L.Fits P U) {io : Io} {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wake) (hi : P.inv (upd G t g) m)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .out Heap.empty)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((futexWakeC io L.ptr (1 : BitVec 32) : CM Tgt σ Unit).run s) Q G m n :=
  wp_wakeOn hP.on hg trivial hi h

/-! ### `Thread.Mutex` (0.15.2): the ops on bits, with the contended value `3` -/

/-- A thread at `spin` (`g`) goes to the futex wait: no memory step (`Thread.Mutex` reads the
word before its futex wait). -/
theorem Fits.toWait (hP : L.Fits P U) {t : ThreadId} {G : ThreadId → γ} {m : Mem} {g : γ}
    (hg : L.ph g = .spin) (hi : P.inv (upd G t g) m) :
    P.inv (upd G t (L.set g .wait Heap.empty)) m := by
  have hiL := hP.lock hi
  have hph : L.ph (upd G t g t) = .spin := by rw [upd_self]; exact hg
  have hnh : L.ph (upd G t g t) ≠ .holds := by rw [hph]; decide
  have hng : L.ph (upd G t g t) ≠ .gone := by rw [hph]; decide
  have hl := hiL.queue (c := m.current) (ws := m.waiters) (wk := m.woken) (p := .wait) hnh hng
    (by decide) (by decide) (fq_keep hiL (by rw [hph]; decide) (by rw [hph]; decide))
    (wit_keep hiL hnh (by decide) fun _ => rfl)
  have hm : ({ m with current := m.current, waiters := m.waiters, woken := m.woken } : Mem) = m := by
    cases m; rfl
  rw [hm] at hl
  have := hP.step (p := .wait) (h := Heap.empty) hi hng
    (Step.same rfl rfl rfl rfl rfl rfl fun _ _ => Iff.rfl) (fun h => absurd h hnh) hl
  rwa [upd_self, upd_upd] at this

/-- `tryLock`, `or(1)` with an acquire, by thread `t` at `out` (`g`). -/
theorem wp_orLock (hP : L.Fits P U) (hc3 : L.c = 3) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = 0 ∧ ∃ hL, P.inv (upd G₁ t (L.set g .holds hL)) m') ∨
       ((r = 1 ∨ r = 3) ∧ P.inv (upd G₁ t (L.set g .spin Heap.empty)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwC .or false .acquire 4 L.ptr (1 : BitVec 32) : CM Tgt σ (BitVec 32)).run s)
      Q G m n := by
  unfold atomicRmwC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hgone : L.ph (G₁ t) ≠ .gone := by rw [hg₁, hg]; decide
  have hiP := hP.cur t hi₁ hgone
  have hiL := hP.lock hiP
  have ht := hP.alive hiP hg₁ (by rw [hg]; decide)
  refine WP.callMC (fun e he => (hiL.rmw_noErr ht hgone hcr e he).elim) fun r m' hr => ?_
  obtain ⟨hst, hcu, hcase⟩ := hiL.orLock hc3 (by rw [hg₁]; exact hg) rfl hr
  refine ⟨by rw [hst.threads], h k hk G₁ m' r hcu ?_⟩
  rw [hg₁] at hcase
  rcases hcase with ⟨hr', hL, -, hl⟩ | ⟨hr', hl⟩
  · refine .inl ⟨hr', hL, ?_⟩
    have := hP.step (p := .holds) (h := hL) hiP hgone hst
      (fun h => absurd h (by rw [hg₁, hg]; decide)) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this
  · refine .inr ⟨hr', ?_⟩
    have := hP.step (p := .spin) (h := Heap.empty) hiP hgone hst
      (fun h => absurd h (by rw [hg₁, hg]; decide)) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this

/-- A relaxed load of the word by thread `t` (`g`, not `gone`): no place changes. -/
theorem wp_loadLock (hP : L.Fits P U) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t → P.inv (upd G₁ t g) m' → Q (r, s) G₁ m' k) :
    P.WP t ((atomicLoadC (n := 32) .relaxed 4 L.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicLoadC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hgone : L.ph (G₁ t) ≠ .gone := by rw [hg₁]; exact hg
  have hiP := hP.cur t hi₁ hgone
  have hiL := hP.lock hiP
  have ht := hP.alive hiP hg₁ hg
  refine WP.callMC (fun e he => (hiL.load_noErr ht hgone hcr e he).elim) fun r m' hr => ?_
  obtain ⟨hst, hcu, hl⟩ := hiL.load rfl ht rfl hr
  refine ⟨by rw [hst.threads], h k hk G₁ m' r hcu ?_⟩
  rw [← hg₁, upd_same]
  exact hP.stay hiP hgone hst hl

/-- `os_unfair_lock_lock`'s `cmpxchg` `0 → 1`, by thread `t` at `out` or `spin` (`g`). -/
theorem wp_casD (hP : L.Fits P U) (hc1 : L.c = 1) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .out ∨ L.ph g = .spin)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      ((r = none ∧ ∃ hL, P.inv (upd G₁ t (L.set g .holds hL)) m') ∨
       (r = some (BitVec.ofNat 32 L.c) ∧ P.inv (upd G₁ t (L.set g .wait Heap.empty)) m')) →
      Q (r, s) G₁ m' k) :
    P.WP t ((cmpxchgC (n := 32) .acquire .relaxed 4 L.ptr (0 : BitVec 32) 1 : CM Tgt σ _).run s)
      Q G m n := by
  have hnh : L.ph g ≠ .holds := by rcases hg with h | h <;> rw [h] <;> decide
  unfold cmpxchgC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hgone : L.ph (G₁ t) ≠ .gone := by rw [hg₁]; rcases hg with h | h <;> rw [h] <;> decide
  have hiP := hP.cur t hi₁ hgone
  have hiL := hP.lock hiP
  have ht := hP.alive hiP hg₁ (by rcases hg with h | h <;> rw [h] <;> decide)
  refine WP.callMC (fun e he => (hiL.casD_noErr ht hgone hcr e he).elim) fun r m' hr => ?_
  obtain ⟨hst, hcu, hcase⟩ := hiL.casD hc1 (by rw [hg₁]; exact hg) rfl hr
  refine ⟨by rw [hst.threads], h k hk G₁ m' r hcu ?_⟩
  rw [hg₁] at hcase
  rcases hcase with ⟨rfl, hL, -, hl⟩ | ⟨rfl, hl⟩
  · refine .inl ⟨rfl, hL, ?_⟩
    have := hP.step (p := .holds) (h := hL) hiP hgone hst
      (fun h => absurd h (by rw [hg₁]; exact hnh)) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this
  · refine .inr ⟨rfl, ?_⟩
    have := hP.step (p := .wait) (h := Heap.empty) hiP hgone hst
      (fun h => absurd h (by rw [hg₁]; exact hnh)) (by rw [hg₁]; exact hl)
    rwa [hg₁] at this

/-- `os_unfair_lock_lock`'s futex wait for `1`, by thread `t` at `wait` (`g`): it goes on at
`spin`. -/
theorem wp_waitD (hP : L.Fits P U) {s : σ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .wait)
    (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      P.inv (upd G₁ t (L.set g .spin Heap.empty)) m' → Q ((), s) G₁ m' k) :
    P.WP t ((threadFutexWaitC L.ptr (BitVec.ofNat 32 L.c) : CM Tgt σ Unit).run s) Q G m n := by
  rw [threadFutexWaitC_eq]
  refine WP.futexWaitC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  have he : (Packed.toBits (BitVec.ofNat 32 L.c)).setWidth 32 = BitVec.ofNat 32 L.c :=
    BitVec.setWidth_eq _
  simp only [he]
  have hiL := hP.lock hi₁
  refine ⟨fun _ => hP.live hiL (by rw [hg₁]; exact hg), fun hq => ⟨fun _ => hiL.wait_ok, fun b m' hw => ?_⟩⟩
  have hgo : ∀ m', L.Step t m₁ m' → m'.current = t →
      L.Inv (upd G₁ t (L.set (G₁ t) .spin Heap.empty)) m' → Q ((), s) G₁ m' k := by
    intro m' hst hcu hl
    refine h k hk G₁ m' hcu ?_
    have := hP.step (p := .spin) (h := Heap.empty) hi₁ (by rw [hg₁, hg]; decide) hst
      (fun h => absurd h (by rw [hg₁, hg]; decide)) hl
    rwa [hg₁] at this
  obtain ⟨hst, hb⟩ := hiL.wait (by rw [hg₁]; exact hg) hq hw
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
    exact hgo m' hst hb.1 hb.2
  · simp only [↓reduceIte] at hb ⊢
    obtain ⟨hst', hcu', hl'⟩ := hiL.spurious (by rw [hg₁]; exact hg) hq
    exact ⟨hP.stay hi₁ (by rw [hg₁, hg]; decide) hst hb, hgo _ hst' hcu' hl'⟩

/-- `os_unfair_lock_unlock`'s `xchg` of `0` with a release, by the holder `t` (`g`). -/
theorem wp_xchgRel (hP : L.Fits P U) (hc1 : L.c = 1) {s : σ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {g : γ} (hg : L.ph g = .holds) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' r, m'.current = t →
      P.inv (upd G₁ t (L.set g .wake Heap.empty)) m' → Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwC .xchg false .release 4 L.ptr (0 : BitVec 32) : CM Tgt σ (BitVec 32)).run s)
      Q G m n := by
  unfold atomicRmwC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hgone : L.ph (G₁ t) ≠ .gone := by rw [hg₁, hg]; decide
  have hiP := hP.cur t hi₁ hgone
  have hiL := hP.lock hiP
  have ht := hP.alive hiP hg₁ (by rw [hg]; decide)
  refine WP.callMC (fun e he => (hiL.rmw_noErr ht hgone hcr e he).elim) fun r m' hr => ?_
  obtain ⟨hst, hcu, hbf, hl⟩ := hiL.xchgRel hc1 (by rw [hg₁]; exact hg) rfl hr
  refine ⟨by rw [hst.threads], h k hk G₁ m' r hcu ?_⟩
  rw [hg₁] at hl
  have := hP.step (p := .wake) (h := Heap.empty) hiP hgone hst (fun _ _ => hbf)
    (by rw [hg₁]; exact hl)
  rwa [hg₁] at this

end Lock

end Conc
end Zig
