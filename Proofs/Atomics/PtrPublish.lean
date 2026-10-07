import ZigLean.Conc.PtrAtomic
import ZigLean.Conc.PtrAtomicLemmas
import ZigLean.Mem.Alloc

/-!
# Pointer publication over all schedules (C09)

Thread A (`producer`, thread 1) allocates a node (`Allocator.create(u32)`), writes 42 to it,
and stores its pointer to an atomic `?*u32` slot with `.release`. Thread B (`main`, thread 0)
loads the slot with `.acquire`; if it reads a pointer, it reads the node through it. Then `main`
joins A, loads the slot again (`.monotonic`) and, if it holds the node, destroys it
(join-before-free: after the join `main` owns the node). The Zig form:

```zig
fn producer(slot: *std.atomic.Value(?*u32)) void {
    const n = allocator.create(u32) catch return;
    n.* = 42;
    slot.store(n, .release);
}
pub fn publishRead() u32 {
    var slot = std.atomic.Value(?*u32).init(null);
    const h = Thread.spawn(.{}, producer, .{&slot}) catch unreachable;
    const r = if (slot.load(.acquire)) |p| p.* else 0;
    h.join();
    if (slot.load(.monotonic)) |p| allocator.destroy(p);
    return r;
}
```

`publishRead` below is written in the shape of generated code with the pointer ops of
`ZigLean/Conc/PtrAtomic.lean`; it is a model-level example, not an exported AIR file.

- **Provenance.** The slot's messages hold pointer bytes (`Byte.ptrFrag`), so the pointer that B
  reads is A's node with its block (block 1), not an integer.
- **Visibility** (`publishRead_spec`): the result is 0 (B read `null`) or 42 under every
  schedule: an acquire read of A's release message joins A's clock, so A's write of 42 happened
  before B's read of the node.
- **Lifetime** (`publishRead_safe`): no schedule gives an error. B reads the node only while it
  is live; the node is freed once, after the join, by `main`; the read after the join sees the
  newest message (the join puts A's store before it), so `main` frees the node that A published,
  and never a dead or foreign block. A failed allocation publishes nothing.

**Protocol.** Ghost values (`Gh`): `main` is `pre`, `run` (at the acquire load), `joins`, `post`
(at the load after the join); A is `start`, `wrote` (node allocated and 42 written, at its
store), `fin`. The invariant (`Inv`) keeps the slot's location (`SlotLoc`): one message `null`,
or `null` then A's message `some node`, and then A has ended, the node is live and holds 42, and
every write to the node happened before the message's release clock.
-/

open Zig Zig.Conc Zig.Conc.Proto

namespace Atomics.PtrPublish

/-! ## The program -/

/-- The spawn targets. -/
inductive Tgt where
  | producer (slot : Zig.Ptr)

/-- Thread A. -/
def producer (slot : Zig.Ptr) : Zig.ConcM Tgt Unit :=
  ((do
    match ← Zig.callMC (Zig.Allocator.create ⟨⟩ 4 4) with
    | .error _ => pure ()
    | .ok n =>
      Zig.store (α := BitVec 32) 4 n (42 : BitVec 32)
      Zig.atomicStorePtrC (α := Option Zig.Ptr) .release 8 slot (some n)) :
    Zig.CM Tgt Unit Unit).run' ()

def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .producer s => producer s

/-- Thread B (`main`). -/
def publishRead : Zig.ConcM Tgt (BitVec 32) := do
  let slot ← Zig.allocStack 8 8
  let r ← ((do
    Zig.store (α := Option Zig.Ptr) 8 slot none
    match ← Zig.spawnC (Tgt.producer slot) with
    | .error _ => pure (0 : BitVec 32)
    | .ok h =>
      let r ← match ← Zig.atomicLoadPtrC (Option Zig.Ptr) .acquire 8 slot with
        | some p => Zig.load (BitVec 32) 4 p
        | none => pure 0
      Zig.joinC h
      match ← Zig.atomicLoadPtrC (Option Zig.Ptr) .relaxed 8 slot with
      | some p => Zig.callMC (Zig.Allocator.destroy ⟨⟩ 4 p)
      | none => pure ()
      pure r) : Zig.CM Tgt Unit (BitVec 32)).run' ()
  Zig.free slot
  pure r

/-- The memory at program start. -/
def mem0 : Zig.Mem := {}

/-! ## The protocol -/

/-- A thread's ghost value. -/
inductive Gh where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- `main` at its acquire load. -/
  | run
  /-- `main` at its join. -/
  | joins
  /-- `main` at its load after the join. -/
  | post
  /-- A before its allocation. -/
  | start
  /-- A after its allocation and its write of 42, at its store. -/
  | wrote
  /-- A has ended. -/
  | fin
  deriving DecidableEq

/-- The slot (block 0). -/
def sPtr : Ptr := ⟨some 0, 0⟩
/-- The node (block 1). -/
def nPtr : Ptr := ⟨some 1, 0⟩

/-- The bytes `0..4` of block `b` hold the `u32` `v`. -/
def U32At (m : Mem) (b : Nat) (v : BitVec 32) : Prop :=
  (intOfBytes 32 (curBytes m b 0 4)).run = some (.ok v)

/-- The node is a live heap block of 4 bytes at an address that is a multiple of 4. -/
def NodeAt (m : Mem) : Prop :=
  ∃ blk, m.blocks[1]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 4 ∧ blk.kind = .heap ∧
    blk.addr % 4 = 0

/-- Every write to the node happened before `c`. -/
def NodeLe (m : Mem) (c : VClock) : Prop :=
  ∀ e ∈ m.footprint, e.block = 1 → e.kind = .write → VClock.le e.clock c = true

/-- The bytes of `null` and of the node's pointer. -/
def noneBytes : Array Byte := Enc.encode (none : Option Ptr)
def someBytes : Array Byte := Enc.encode (some nPtr : Option Ptr)

/-- The slot's atomic location: `null`, or `null` then A's message (module doc). -/
def SlotLoc (G : ThreadId → Gh) (m : Mem) (l : ALoc) : Prop :=
  l.block = 0 ∧ l.off = 0 ∧ l.len = 8 ∧ ALoc.lastBytes l = curBytes m 0 0 8 ∧
  ((∃ m0, l.msgs = #[m0] ∧ m0.bytes = noneBytes) ∨
   (∃ m0 m1, l.msgs = #[m0, m1] ∧ m0.bytes = noneBytes ∧ m1.bytes = someBytes ∧ G 1 = .fin ∧
     NodeAt m ∧ U32At m 1 42 ∧ NodeLe m m1.relClock ∧ VClock.le m1.clock (m.clocks[1]!) = true ∧
     (G 0 = .post → VClock.le m1.clock (m.clocks[0]!) = true)))

/-- No atomic location yet (the slot holds `null`), or the slot's. -/
def SlotOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  (m.atomics = #[] ∧ curBytes m 0 0 8 = noneBytes) ∨ ∃ l, m.atomics = #[l] ∧ SlotLoc G m l

/-- A footprint entry: a write before every thread; A's write to the node; a read of the node
after A ended; an atomic access to the slot. -/
def FpOk (G : ThreadId → Gh) (m : Mem) (e : FootprintEntry) : Prop :=
  (e.kind = .write ∧ Before m e.clock) ∨
  (e.block = 1 ∧ e.kind = .write ∧ e.tid = 1) ∨
  (e.block = 1 ∧ e.kind = .read ∧ G 1 = .fin) ∨
  (e.block = 0 ∧ e.kind.isAtomic = true)

/-- The threads: `main` alone before its spawn; then `main` and A, joined exactly when `main`
is at `post`. -/
def ThrOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧ m.clocks.size = m.threads.size ∧
  ((m.threads.size = 1 ∧ G 0 = .pre ∧ ∀ u, 1 ≤ u → G u = .none) ∨
   (m.threads.size = 2 ∧
    (∃ r, m.threads[1]? = some r ∧ r.spawner = 0 ∧ r.joined = decide (G 0 = .post)) ∧
    (G 0 = .run ∨ G 0 = .joins ∨ G 0 = .post) ∧ (G 1 = .start ∨ G 1 = .wrote ∨ G 1 = .fin) ∧
    (G 0 = .post → G 1 = .fin) ∧ ∀ u, 2 ≤ u → G u = .none))

/-- The invariant (see the module doc). -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  thr : ThrOk G m
  b0 : BlkAt m 0 8 8
  start : G 1 = .start → m.blocks.size = 1
  wrote : G 1 = .wrote → NodeAt m ∧ U32At m 1 42
  slot : SlotOk G m
  fp : ∀ e ∈ m.footprint, FpOk G m e
  own : ∀ e ∈ m.footprint, e.tid < m.threads.size ∧ VClock.le e.clock (m.clocks[e.tid]!) = true

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := (match tgt with
      | .producer p => if p = sPtr then some .start else none) = some g
  fin g := g = .fin
  strict := true
  joins g := g = .joins

/-- `main`'s post: the result, and every thread joined. -/
def QM : BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => (v = 0 ∨ v = 42) ∧ joinedAll 0 m

/-! ## Frame -/

theorem NodeAt.congr {m m' : Mem} (h : m'.blocks = m.blocks) (hn : NodeAt m) : NodeAt m' := by
  unfold NodeAt; rw [h]; exact hn

theorem Inv.grow {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (hg : Grows m m') : Inv G m' where
  thr := by unfold ThrOk; rw [hg.threads, hg.csize]; exact hi.thr
  b0 := hi.b0.congr hg.blocks
  start := by rw [hg.blocks]; exact hi.start
  wrote := fun h => ⟨(hi.wrote h).1.congr hg.blocks,
    by unfold U32At; rw [curBytes_congr hg.blocks]; exact (hi.wrote h).2⟩
  slot := by
    rcases hi.slot with ⟨ha, hb⟩ | ⟨l, ha, hlb, hlo, hll, hlast, h1 |
        ⟨m0, m1, hms, h0, h1, hfin, hn, h42, hle, hc1, hc0⟩⟩
    · exact .inl ⟨by rw [hg.atomics]; exact ha, by rw [curBytes_congr hg.blocks]; exact hb⟩
    · exact .inr ⟨l, by rw [hg.atomics]; exact ha, hlb, hlo, hll,
        by rw [curBytes_congr hg.blocks]; exact hlast, .inl h1⟩
    · refine .inr ⟨l, by rw [hg.atomics]; exact ha, hlb, hlo, hll,
        by rw [curBytes_congr hg.blocks]; exact hlast,
        .inr ⟨m0, m1, hms, h0, h1, hfin, hn.congr hg.blocks,
          by unfold U32At; rw [curBytes_congr hg.blocks]; exact h42,
          by unfold NodeLe; rw [hg.footprint]; exact hle,
          VClock.le_trans hc1 (hg.cle 1), fun h => VClock.le_trans (hc0 h) (hg.cle 0)⟩⟩
  fp := by
    intro e he
    rw [hg.footprint] at he
    rcases hi.fp e he with ⟨hk, hb⟩ | h | h | h
    · exact .inl ⟨hk, before_grow hg hb⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  own := by
    intro e he
    rw [hg.footprint] at he
    obtain ⟨h1, h2⟩ := hi.own e he
    exact ⟨hg.threads ▸ h1, VClock.le_trans h2 (hg.cle _)⟩

/-- The invariant depends only on the threads, the clocks, the blocks, the atomic locations and
the footprint. -/
theorem Inv.congr {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (ht : m'.threads = m.threads)
    (hc : m'.clocks = m.clocks) (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hf : m'.footprint = m.footprint) (hw : m'.waiters = m.waiters) : Inv G m' :=
  hi.grow ⟨ht, hb, ha, hf, hw, by rw [hc], fun u => by rw [hc]; exact VClock.le_refl _⟩

/-- A race-free access by the current thread: its clock is bumped and the entry recorded. The
invariant holds if the entry is one of `FpOk`, and it is not a write to the node after A ended. -/
theorem Inv.record {G : ThreadId → Gh} {m : Mem} {b o len : Nat} {k : AccessKind} (hi : Inv G m)
    (ht : m.current < m.threads.size) (hnd : b = 1 → k = .write → G 1 ≠ .fin)
    (hf : FpOk G (m.recordAt b o len k)
      { tid := m.current, clock := VClock.bump (m.clocks[m.current]!) m.current, block := b,
        off := o, len := len, kind := k }) :
    Inv G (m.recordAt b o len k) := by
  have hcs : m.current < m.clocks.size := by rw [hi.thr.2.1]; exact ht
  let m₁ : Mem := { m with clocks := m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current) }
  have hg : Grows m m₁ := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [m₁], fun u => ?_⟩
    simp only [m₁]
    rw [getElem!_set!_ite]
    split
    · rename_i h; rw [h.1]; exact VClock.le_bump _ _
    · exact VClock.le_refl _
  have hi₁ := hi.grow hg
  have hcur : (m.recordAt b o len k).clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current := by
    simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs]
  exact {
    thr := hi₁.thr, b0 := hi₁.b0, start := hi₁.start, wrote := hi₁.wrote
    slot := by
      rcases hi₁.slot with h | ⟨l, ha, hlb, hlo, hll, hlast, h1 |
          ⟨m0, m1, hms, h0, h1, hfin, hn, h42, hle, hc1, hc0⟩⟩
      · exact .inl h
      · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, .inl h1⟩
      · refine .inr ⟨l, ha, hlb, hlo, hll, hlast, .inr ⟨m0, m1, hms, h0, h1, hfin, hn, h42,
          fun e he hb1 hkw => ?_, hc1, hc0⟩⟩
        simp only [Mem.recordAt, Array.mem_push] at he
        rcases he with he | rfl
        · exact hle e he hb1 hkw
        · exact absurd hfin (hnd hb1 hkw)
    fp := by
      intro e he
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact hi₁.fp e he
      · exact hf
    own := by
      intro e he
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact hi₁.own e he
      · exact ⟨ht, by rw [hcur]; exact VClock.le_refl _⟩ }

/-- The race check of an access by the current thread to block `b`. -/
theorem noRace_inv {G : ThreadId → Gh} {m : Mem} {b o len : Nat} {k : AccessKind} (hi : Inv G m)
    (ht : m.current < m.threads.size)
    (h : ∀ e ∈ m.footprint, e.block = b → FpOk G m e →
      (e.kind = .write ∧ Before m e.clock) ∨ VClock.le e.clock (m.clocks[m.current]!) = true ∨
        racePair e.kind k = none) :
    NoRace m b o len k :=
  noRace_of fun e he hb _ _ => by
    rcases h e he hb (hi.fp e he) with ⟨-, hle⟩ | h | h
    · exact .inl (hle _ ht)
    · exact .inl h
    · exact .inr h

/-- `u`'s ghost value is `main`'s or A's: there are two threads and `u < 2`. -/
theorem thr_of {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (h : ThrOk G m)
    (hg : G u = .run ∨ G u = .joins ∨ G u = .post ∨ G u = .start ∨ G u = .wrote ∨ G u = .fin) :
    m.threads.size = 2 ∧ u < 2 := by
  obtain ⟨-, -, ⟨-, h0, hn⟩ | ⟨hs, -, -, -, -, hn⟩⟩ := h
  · by_cases hu : u = 0
    · subst hu; rw [h0] at hg; simp at hg
    · rw [hn u (by unfold ThreadId at *; omega)] at hg; simp at hg
  · refine ⟨hs, ?_⟩
    by_cases hu : 2 ≤ u
    · rw [hn u hu] at hg; simp at hg
    · unfold ThreadId at *; omega

/-- A change of A's ghost value from `start` or `wrote` keeps `ThrOk`. -/
theorem thr_upd1 {G : ThreadId → Gh} {m m' : Mem} {g : Gh} (h : ThrOk G m)
    (ht : m'.threads = m.threads) (hc : m'.clocks.size = m.clocks.size)
    (hg1 : G 1 = .start ∨ G 1 = .wrote) (hg : g = .start ∨ g = .wrote ∨ g = .fin) :
    ThrOk (upd G 1 g) m' := by
  obtain ⟨h0, hcs, ⟨-, -, hn⟩ | ⟨hs2, ⟨r, hr, hsp, hj⟩, g0, -, gp, g2⟩⟩ := h
  · rw [hn 1 (by decide)] at hg1; simp at hg1
  have e0 : upd G 1 g 0 = G 0 := upd_ne _ _ (by decide)
  refine ⟨ht ▸ h0, by rw [hc, ht]; exact hcs, .inr ⟨ht ▸ hs2, ⟨r, ht ▸ hr, hsp, by rw [e0]; exact hj⟩,
    by rw [e0]; exact g0, by rw [upd_self]; exact hg, fun hp => ?_, fun v hv => ?_⟩⟩
  · rw [e0] at hp
    have := gp hp
    rcases hg1 with h | h <;> rw [h] at this <;> cases this
  · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact g2 v hv

/-! ## The slot's atomic location -/

theorem intSize64 : intSize 64 = 8 := rfl

/-- The slot's location at an atomic op (`locIdx 0 0 8`): location 0, with the slot's messages.
The op changes only `atomics` and `nextMsg`. -/
theorem loc_slot {G : ThreadId → Gh} {m m₁ : Mem} {li : Nat} (hf : SlotOk G m)
    (h : ((locIdx 0 0 8).run m).run = some (.ok (li, m₁))) :
    li = 0 ∧ ∃ l k, SlotLoc G m l ∧ m₁ = { m with atomics := #[l], nextMsg := k } := by
  have h0 : m.atomics = #[] ∨ ∃ l, m.atomics = #[l] ∧ l.block = 0 ∧ l.off = 0 ∧ l.len = 8 ∧
      ALoc.lastBytes l = curBytes m 0 0 8 := by
    rcases hf with ⟨ha, -⟩ | ⟨l, ha, hlb, hlo, hll, hlast, -⟩
    · exact .inl ha
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast⟩
  obtain ⟨rfl, l, k, rfl, ⟨ha, rfl⟩ | ha⟩ := locIdx_single h0 h
  · rcases hf with ⟨-, hu⟩ | ⟨l, ha', -⟩
    · exact ⟨rfl, firstLoc m 0 0 8, k, ⟨rfl, rfl, rfl, rfl, .inl ⟨firstMsg m 0 0 8, rfl, hu⟩⟩, rfl⟩
    · rw [ha] at ha'; simp at ha'
  · rcases hf with ⟨ha', -⟩ | ⟨l', ha', hfl⟩
    · rw [ha] at ha'; simp at ha'
    · rw [ha] at ha'
      have : l = l' := by simpa using ha'
      subst this
      exact ⟨rfl, l, k, hfl, rfl⟩

theorem slot_locIdx_noErr {G : ThreadId → Gh} {m : Mem} (hf : SlotOk G m) (e : Error) :
    ((locIdx 0 0 8).run m).run ≠ some (.error e) := by
  refine locIdx_noErr (fun i hi => ?_) (fun hn l hl => ?_) e
  · rcases hf with ⟨ha, -⟩ | ⟨l, ha, -, -, hll, -⟩
    · rw [ha] at hi; simp at hi
    · have := (Array.findIdx?_eq_some_iff_getElem.mp hi).1
      rw [ha] at this hi ⊢
      have : i = 0 := by simp at this; omega
      subst this; exact hll
  · rcases hf with ⟨ha, -⟩ | ⟨l', ha, hlb, hlo, -, -⟩
    · rw [ha] at hl; simp at hl
    · rw [ha] at hn; simp [hlb, hlo] at hn

/-- A new slot location for the invariant. -/
theorem Inv.setLoc {G : ThreadId → Gh} {m : Mem} {l : ALoc} (hi : Inv G m) (hl : SlotLoc G m l)
    (k : Nat) : Inv G { m with atomics := #[l], nextMsg := k } :=
  { hi with slot := .inr ⟨l, rfl, hl⟩ }

/-- The slot's location has at least one message. -/
theorem SlotLoc.pos {G : ThreadId → Gh} {m : Mem} {l : ALoc} (h : SlotLoc G m l) :
    0 < l.msgs.size := by
  obtain ⟨-, -, -, -, ⟨m0, hms, -⟩ | ⟨m0, m1, hms, -⟩⟩ := h <;> rw [hms] <;> simp

/-- An atomic access to the slot: block 0, offset 0. -/
theorem acc_slot {m : Mem} {b : BlockId} {blk : Block} {o : Nat} (hb0 : BlkAt m 0 8 8)
    (h : m.access sPtr (intSize 64) 8 = pure (b, blk, o)) :
    b = 0 ∧ o = 0 ∧ m.blocks[0]? = some blk := by
  obtain ⟨blk₀, hb₀, -, -, he⟩ := access_blk (p := sPtr) (a := 8) (len := intSize 64) (o := 0) hb0
    (by decide) (fun A hA => by omega) rfl
  rw [he] at h
  cases h
  exact ⟨rfl, rfl, hb₀⟩

theorem accW_slot {m : Mem} {b : BlockId} {blk : Block} {o : Nat} (hb0 : BlkAt m 0 8 8)
    (h : m.accessW sPtr (intSize 64) 8 = pure (b, blk, o)) :
    b = 0 ∧ o = 0 ∧ m.blocks[0]? = some blk :=
  acc_slot hb0 (accessW_pure h).1

/-- An atomic access to the slot does not race. -/
theorem noRace_slot {G : ThreadId → Gh} {m : Mem} {k : AccessKind} (hk : k.isAtomic = true)
    (hi : Inv G m) (ht : m.current < m.threads.size) : NoRace m 0 0 (intSize 64) k :=
  noRace_inv hi ht fun e _ hb hf => by
    rcases hf with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ha⟩
    · exact .inl h
    · exact (blk_ne h hb (by decide)).elim
    · exact (blk_ne h hb (by decide)).elim
    · exact .inr (.inr (racePair_atomic ha hk))


/-! ## A: the allocation and the write of 42 -/

theorem recordAt_le' (m : Mem) (b o n : Nat) (k : AccessKind) (u : Nat) :
    VClock.le (m.clocks[u]!) ((m.recordAt b o n k).clocks[u]!) = true := by
  simp only [Mem.recordAt]; rw [getElem!_set!_ite]
  split
  · rename_i h; rw [h.1]; exact VClock.le_bump _ _
  · exact VClock.le_refl _

/-- The node block that A's allocation makes. -/
def nodeBlk (m : Mem) : Block :=
  { bytes := Array.replicate 4 .undef, align := 4, kind := .heap, live := true,
    addr := alignUp m.nextAddr 4 }

/-- The memory after A's allocation succeeded. -/
def allocM (m : Mem) : Mem :=
  { m with allocs := m.allocs + 1, blocks := m.blocks.push (nodeBlk m),
           nextAddr := alignUp m.nextAddr 4 + 4 + 1 }

/-- `create(u32)`: `OutOfMemory`, or a new heap block. -/
theorem create_ok {m m' : Mem} {r : Except ErrName Ptr}
    (h : ((Allocator.create ⟨⟩ 4 4).run m).run = some (.ok (r, m'))) :
    (∃ e, r = .error e ∧ m' = { m with allocs := m.allocs + 1 }) ∨
    (r = .ok ⟨some m.blocks.size, 0⟩ ∧ m' = allocM m) := by
  simp only [Allocator.create, allocBytes, show ((4 : Nat) = 0) = False from by decide,
    if_false] at h
  obtain ⟨o, m₁, hr, h₁⟩ := MemM.bind_ok h
  unfold rawAlloc at hr
  obtain ⟨a, m₂, hg, h₂⟩ := MemM.bind_ok hr
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨_, m₃, hs, h₃⟩ := MemM.bind_ok h₂
  have := MemM.set_ok hs
  subst this
  split at h₃
  · obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₃
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₁
    exact .inl ⟨_, rfl, rfl⟩
  · obtain ⟨q, ha, rfl⟩ := MemM.map_ok h₃
    obtain ⟨rfl, rfl⟩ := alloc_ok ha
    obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₁
    exact .inr ⟨rfl, rfl⟩

theorem create_noErr (m : Mem) (e : Error) :
    ((Allocator.create ⟨⟩ 4 4).run m).run ≠ some (.error e) := by
  intro h
  simp only [Allocator.create, allocBytes, show ((4 : Nat) = 0) = False from by decide,
    if_false] at h
  rcases MemM.bind_err h with h | ⟨o, m₁, -, h₁⟩
  · unfold rawAlloc at h
    rcases MemM.bind_err h with h | ⟨a, m₂, hg, h₂⟩
    · exact MemM.get_err h
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    rcases MemM.bind_err h₂ with h | ⟨_, m₃, hs, h₃⟩
    · exact MemM.set_err h
    split at h₃
    · exact MemM.pure_err h₃
    · rw [map_eq_pure_bind] at h₃
      rcases MemM.bind_err h₃ with h | ⟨_, _, -, h⟩
      · exact alloc_noErr e h
      · exact MemM.pure_err h
  · split at h₁ <;> exact MemM.pure_err h₁

/-- The node after the allocation (block 1, when the memory had one block). -/
theorem allocM_node {m : Mem} (hs : m.blocks.size = 1) : (allocM m).blocks[1]? = some (nodeBlk m) := by
  simp only [allocM]
  rw [← hs]
  exact Array.getElem?_push_size

theorem allocM_lt {m : Mem} {b : Nat} (hb : b < m.blocks.size) :
    (allocM m).blocks[b]? = m.blocks[b]? := by
  simp only [allocM, Array.getElem?_push]
  rw [if_neg (by omega)]

theorem curBytes_allocM {m : Mem} {b o len : Nat} (hb : b < m.blocks.size) :
    curBytes (allocM m) b o len = curBytes m b o len := by
  unfold curBytes; rw [allocM_lt hb]

/-- A's write of 42 to the new node does not race and gives no error. -/
theorem node_noErr {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hg : G 1 = .start)
    (hc : m.current = 1) (e : Error) :
    ((store (α := BitVec 32) 4 nPtr (42 : BitVec 32)).run (allocM m)).run ≠ some (.error e) := by
  have hs1 := hi.start hg
  have hacc : (allocM m).access nPtr (Enc.size (BitVec 32)) 4 = pure (1, nodeBlk m, 0) :=
    access_of rfl (allocM_node hs1) rfl (by simp [nPtr])
      (by simp [nPtr, nodeBlk, show Enc.size (BitVec 32) = 4 from rfl])
      (by simpa [nodeBlk, nPtr] using alignUp_mod m.nextAddr 4 (by decide))
  have ht : (allocM m).current < (allocM m).threads.size := by
    show m.current < m.threads.size; rw [hc, (thr_of hi.thr (.inr (.inr (.inr (.inl hg))))).1]; decide
  have hnr : NoRace (allocM m) 1 0 (Enc.size (BitVec 32)) .write := noRace_of fun e he hb _ _ => by
    rcases hi.fp e he with ⟨-, hle⟩ | ⟨-, -, htid⟩ | ⟨-, -, hfin⟩ | ⟨h, -⟩
    · exact .inl (hle _ ht)
    · refine .inl ?_
      have := (hi.own e he).2
      rw [htid] at this
      show VClock.le e.clock (m.clocks[m.current]!) = true
      rw [hc]; exact this
    · rw [hg] at hfin; cases hfin
    · exact (blk_ne h hb (by decide)).elim
  exact MemM.noErr_of_run (store_run (42 : BitVec 32) hacc (by simp [nodeBlk]) hnr) e

/-- A's allocation and write of 42: A goes from `start` to `wrote`. -/
theorem step_node {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (hg : G 1 = .start)
    (hc : m.current = 1)
    (h : ((store (α := BitVec 32) 4 nPtr (42 : BitVec 32)).run (allocM m)).run = some (.ok ((), m'))) :
    m'.current = 1 ∧ m'.threads = m.threads ∧ Inv (upd G 1 .wrote) m' := by
  have hs1 := hi.start hg
  obtain ⟨b, blk, o, hacc, -, rfl⟩ := store_ok h
  have hacc' : (allocM m).access nPtr (Enc.encode (42 : BitVec 32)).size 4 = pure (1, nodeBlk m, 0) :=
    access_of rfl (allocM_node hs1) rfl (by simp [nPtr]) (by rw [size_encode_u32]; simp [nPtr, nodeBlk])
      (by simpa [nodeBlk, nPtr] using alignUp_mod m.nextAddr 4 (by decide))
  rw [hacc'] at hacc
  cases hacc
  have ht : m.current < m.threads.size := by
    rw [hc, (thr_of hi.thr (.inr (.inr (.inr (.inl hg))))).1]; decide
  have hcs : m.current < m.clocks.size := by rw [hi.thr.2.1]; exact ht
  have hfit : 0 + (Enc.encode (42 : BitVec 32)).size ≤ (nodeBlk m).bytes.size := by
    rw [size_encode_u32]; simp [nodeBlk]
  generalize hM : (allocM m).recordAt 1 0 (Enc.encode (42 : BitVec 32)).size .write = M
  have hMb : M.blocks = (allocM m).blocks := by rw [← hM]; rfl
  have hb1 : M.blocks[1]? = some (nodeBlk m) := by rw [hMb]; exact allocM_node hs1
  have hcl : ∀ u, VClock.le (m.clocks[u]!) (M.clocks[u]!) = true := fun u => by
    rw [← hM]; exact recordAt_le' (allocM m) 1 0 _ .write u
  have hMc : M.clocks[1]! = VClock.bump (m.clocks[1]!) 1 := by
    rw [← hM, ← hc]
    simp only [Mem.recordAt]; rw [getElem!_set!_ite]
    simp [allocM, hcs]
  have hMfp : ∀ e ∈ M.footprint, e ∈ m.footprint ∨
      (e.tid = 1 ∧ e.clock = VClock.bump (m.clocks[1]!) 1 ∧ e.block = 1 ∧ e.kind = .write) := by
    intro e he
    rw [← hM] at he
    simp only [Mem.recordAt, allocM, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · exact .inr ⟨hc, by rw [hc], rfl, rfl⟩
  have hMt : M.threads = m.threads := by rw [← hM]; rfl
  have hMcs : M.clocks.size = m.clocks.size := by rw [← hM]; simp [Mem.recordAt, allocM]
  have hcb : ∀ o len, curBytes (M.write 1 (nodeBlk m) 0 (Enc.encode (42 : BitVec 32))) 0 o len =
      curBytes m 0 o len := fun o len => by
    rw [curBytes_write_other hb1 hfit (.inl (by decide))]
    unfold curBytes; rw [hMb, allocM_lt (by rw [hs1]; decide)]
  have hnode : NodeAt (M.write 1 (nodeBlk m) 0 (Enc.encode (42 : BitVec 32))) := by
    refine ⟨{ nodeBlk m with bytes := writeBytes (nodeBlk m).bytes 0 (Enc.encode (42 : BitVec 32)) },
      ?_, rfl, by show (writeBytes _ _ _).size = 4; rw [writeBytes_size _ _ _ hfit]; simp [nodeBlk], rfl,
      by simpa [nodeBlk] using alignUp_mod m.nextAddr 4 (by decide)⟩
    simp only [Mem.write, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hb1).1
  have hg1 : upd G 1 Gh.wrote 1 = .wrote := upd_self _ _ _
  have hg0 : upd G 1 Gh.wrote 0 = G 0 := upd_ne _ _ (by decide)
  refine ⟨by rw [← hM]; exact hc, hMt, {
    thr := thr_upd1 hi.thr hMt hMcs (.inl hg) (.inr (.inl rfl))
    b0 := BlkAt.write hb1 hfit (by
      obtain ⟨blk₀, hb₀, h1, h2, h3, h4⟩ := hi.b0
      exact ⟨blk₀, by rw [hMb, allocM_lt (by rw [hs1]; decide)]; exact hb₀, h1, h2, h3, h4⟩)
    start := fun h => by rw [hg1] at h; cases h
    wrote := fun _ => ⟨hnode, by
      unfold U32At
      have := curBytes_write_same hb1 hfit
      rw [size_encode_u32] at this
      rw [this]
      exact intOfBytes_rmw 42⟩
    slot := by
      rcases hi.slot with ⟨ha, hb⟩ | ⟨l, ha, hlb, hlo, hll, hlast, h1 | ⟨-, -, -, -, -, hfin, -⟩⟩
      · exact .inl ⟨by rw [← hM]; exact ha, by rw [hcb]; exact hb⟩
      · exact .inr ⟨l, by rw [← hM]; exact ha, hlb, hlo, hll, by rw [hcb]; exact hlast, .inl h1⟩
      · rw [hg] at hfin; cases hfin
    fp := by
      intro e he
      rcases hMfp e he with he | ⟨ht1, -, hb, hk⟩
      · rcases hi.fp e he with ⟨hk, hb⟩ | h | ⟨-, -, hfin⟩ | h
        · refine .inl ⟨hk, fun u hu => VClock.le_trans (hb u ?_) (hcl u)⟩
          rw [show (M.write 1 (nodeBlk m) 0 (Enc.encode (42 : BitVec 32))).threads = m.threads
            from hMt] at hu; exact hu
        · exact .inr (.inl h)
        · rw [hg] at hfin; cases hfin
        · exact .inr (.inr (.inr h))
      · exact .inr (.inl ⟨hb, hk, ht1⟩)
    own := by
      intro e he
      rw [show (M.write 1 (nodeBlk m) 0 (Enc.encode (42 : BitVec 32))).threads = m.threads from hMt]
      rcases hMfp e he with he | ⟨ht1, hcl1, -, -⟩
      · obtain ⟨h1, h2⟩ := hi.own e he
        exact ⟨h1, VClock.le_trans h2 (hcl _)⟩
      · refine ⟨by rw [ht1, (thr_of hi.thr (.inr (.inr (.inr (.inl hg))))).1]; decide, ?_⟩
        rw [ht1, hcl1]
        show VClock.le _ (M.clocks[1]!) = true
        rw [hMc]; exact VClock.le_refl _ }⟩

/-- A's failed allocation: A ends with nothing published. -/
theorem inv_oom {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hg : G 1 = .start) :
    Inv (upd G 1 .fin) { m with allocs := m.allocs + 1 } where
  thr := thr_upd1 hi.thr rfl rfl (.inl hg) (.inr (.inr rfl))
  b0 := hi.b0
  start := fun h => by rw [upd_self] at h; cases h
  wrote := fun h => by rw [upd_self] at h; cases h
  slot := by
    rcases hi.slot with h | ⟨l, ha, hlb, hlo, hll, hlast, h1 | ⟨-, -, -, -, -, hfin, -⟩⟩
    · exact .inl h
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, .inl h1⟩
    · rw [hg] at hfin; cases hfin
  fp := by
    intro e he
    rcases hi.fp e he with h | h | ⟨-, -, hfin⟩ | h
    · exact .inl h
    · exact .inr (.inl h)
    · rw [hg] at hfin; cases hfin
    · exact .inr (.inr (.inr h))
  own := hi.own

/-! ## A: the release store of the node's pointer -/

/-- A write to the slot's block keeps the node. -/
theorem NodeAt.write0 {m : Mem} {blk : Block} {bs : Array Byte} (hn : NodeAt m) :
    NodeAt (m.write 0 blk 0 bs) := by
  obtain ⟨b, hb, h1, h2, h3, h4⟩ := hn
  exact ⟨b, by simp only [Mem.write, Array.set!_eq_setIfInBounds]; rw [Array.getElem?_setIfInBounds_ne (by decide)]; exact hb,
    h1, h2, h3, h4⟩

/-- A's message at the slot (`some node`, after the first message): A ends. -/
theorem Inv.pushSlot {G : ThreadId → Gh} {M : Mem} {l : ALoc} {m0 msg : Msg} {blk : Block}
    (hi : Inv G M) (hg : G 1 = .wrote) (ha : M.atomics = #[l]) (hms : l.msgs = #[m0])
    (hb : M.blocks[0]? = some blk) (hbs : msg.bytes = someBytes)
    (hrel : NodeLe M msg.relClock) (hcl : VClock.le msg.clock (M.clocks[1]!) = true) :
    Inv (upd G 1 .fin) { M.write 0 blk 0 msg.bytes with atomics := #[{ l with msgs := #[m0, msg] }] } := by
  obtain ⟨l', ha', hlb, hlo, hll, -, h1⟩ : ∃ l', M.atomics = #[l'] ∧ SlotLoc G M l' := by
    rcases hi.slot with ⟨ha', -⟩ | h
    · rw [ha] at ha'; simp at ha'
    · exact h
  rw [ha] at ha'
  have hl : l = l' := by simpa using ha'
  subst hl
  have h0 : m0.bytes = noneBytes := by
    rcases h1 with ⟨m0', hm, hv0⟩ | ⟨-, -, -, -, -, hfin, -⟩
    · rw [hms] at hm
      have : m0 = m0' := by simpa using hm
      subst this; exact hv0
    · rw [hg] at hfin; cases hfin
  have hbs8 : msg.bytes.size = 8 := by rw [hbs]; exact LawfulEnc.size_encode (α := Option Ptr) _
  have hfit : 0 + msg.bytes.size ≤ blk.bytes.size := by
    obtain ⟨blk', hb', -, hs, -⟩ := hi.b0
    rw [hb] at hb'; cases hb'; omega
  have hcN : ∀ b o len, curBytes { M.write 0 blk 0 msg.bytes with
      atomics := #[{ l with msgs := #[m0, msg] }] } b o len = curBytes (M.write 0 blk 0 msg.bytes) b o len :=
    fun _ _ _ => rfl
  have hlast : ALoc.lastBytes { l with msgs := #[m0, msg] } = curBytes (M.write 0 blk 0 msg.bytes) 0 0 8 := by
    have := curBytes_write_same hb hfit
    rw [hbs8] at this
    rw [this]; rfl
  obtain ⟨hn, h42⟩ := hi.wrote hg
  have g0 : upd G 1 Gh.fin 0 = G 0 := upd_ne _ _ (by decide)
  exact {
    thr := thr_upd1 hi.thr rfl rfl (.inr hg) (.inr (.inr rfl))
    b0 := BlkAt.write hb hfit hi.b0
    start := fun h => by rw [upd_self] at h; cases h
    wrote := fun h => by rw [upd_self] at h; cases h
    slot := .inr ⟨_, rfl, hlb, hlo, hll, by rw [hcN]; exact hlast,
      .inr ⟨m0, msg, rfl, h0, hbs, upd_self _ _ _, hn.write0,
        by unfold U32At; rw [hcN, curBytes_write_other hb hfit (.inl (by decide))]; exact h42,
        hrel, hcl, fun hp => by
          rw [g0] at hp
          obtain ⟨-, -, ⟨-, hp', -⟩ | ⟨-, -, -, -, gp, -⟩⟩ := hi.thr
          · rw [hp'] at hp; cases hp
          · have := gp hp; rw [hg] at this; cases this⟩⟩
    fp := by
      intro e he
      rcases hi.fp e he with h | h | ⟨h1, h2, -⟩ | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl ⟨h1, h2, upd_self _ _ _⟩))
      · exact .inr (.inr (.inr h))
    own := hi.own }

/-- A's release store of the node's pointer: A ends. -/
theorem step_store {G : ThreadId → Gh} {m m' : Mem} {c : Nat} (hi : Inv G m) (hg : G 1 = .wrote)
    (hc : m.current = 1)
    (h : ((atomicStorePtrAt c .release 8 sPtr (some nPtr : Option Ptr)).run m).run =
      some (.ok ((), m'))) :
    m'.threads = m.threads ∧ Inv (upd G 1 .fin) m' := by
  obtain ⟨b, blk, o, li, m₁, slot, hacc, -, hl, hs, rfl⟩ := atomicStorePtrAt_ok h
  obtain ⟨rfl, rfl, hb₀⟩ := accW_slot hi.b0 hacc
  have hsz := (thr_of hi.thr (.inr (.inr (.inr (.inr (.inl hg)))))).1
  have ht : m.current < m.threads.size := by rw [hc, hsz]; decide
  have hir := hi.record (b := 0) (o := 0) (len := intSize 64) (k := .atomicWrite) ht
    (fun h => by cases h) (.inr (.inr (.inr ⟨rfl, rfl⟩)))
  have hcur : (m.recordAt 0 0 (intSize 64) .atomicWrite).current = 1 := hc
  have hszr : (m.recordAt 0 0 (intSize 64) .atomicWrite).threads.size = 2 := hsz
  have hbr : (m.recordAt 0 0 (intSize 64) .atomicWrite).blocks[0]? = some blk := hb₀
  have hthr : (m.recordAt 0 0 (intSize 64) .atomicWrite).threads = m.threads := rfl
  generalize m.recordAt 0 0 (intSize 64) .atomicWrite = mr at hir hl hcur hszr hbr hthr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_slot hir.slot hl
  obtain ⟨hlb, hlo, hll, hlast, ⟨m0, hms, h0⟩ | ⟨-, -, -, -, -, hfin, -⟩⟩ := hfl
  · have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
    obtain ⟨hf1, hs1⟩ := writeSlots_bounds hs
    rw [hl0, hms] at hs1
    have hslot : slot = (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs.size := by
      rw [hl0, hms]; simp at hs1 ⊢; omega
    have hbM : ({ mr with atomics := #[l], nextMsg := k } : Mem).blocks[
        (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).block]? = some blk := by
      rw [hl0, hlb]; exact hbr
    have hiM := hir.setLoc ⟨hlb, hlo, hll, hlast, .inl ⟨m0, hms, h0⟩⟩ k
    have hrel : NodeLe { mr with atomics := #[l], nextMsg := k }
        (storePtrMsg { mr with atomics := #[l], nextMsg := k } .release (some nPtr : Option Ptr)).relClock := by
      intro e he hb1 hkw
      show VClock.le e.clock (mr.clocks[mr.current]!) = true
      rw [hcur]
      rcases hir.fp e he with ⟨-, hbf⟩ | ⟨-, -, htid⟩ | ⟨-, hk, -⟩ | ⟨h, -⟩
      · exact hbf 1 (by rw [hszr]; decide)
      · have := (hir.own e he).2; rw [htid] at this; exact this
      · rw [hkw] at hk; cases hk
      · exact (blk_ne h hb1 (by decide)).elim
    have hiN := hiM.pushSlot hg rfl hms hbr
      (msg := storePtrMsg { mr with atomics := #[l], nextMsg := k } .release (some nPtr : Option Ptr))
      rfl hrel (by show VClock.le (mr.clocks[mr.current]!) _ = true; rw [hcur]; exact VClock.le_refl _)
    unfold storePtrM
    rw [hslot, insertM_last hbM]
    refine ⟨hthr, hiN.congr rfl rfl ?_ ?_ rfl rfl⟩
    · show mr.blocks.set! _ _ = mr.blocks.set! _ _
      rw [hl0, hlb, hlo]
    · show (#[l] : Array ALoc).set! 0 _ = _
      rw [hl0, hms]; rfl
  · rw [hg] at hfin; cases hfin

theorem store_noErr {G : ThreadId → Gh} {m : Mem} {c : Nat} (hi : Inv G m)
    (ht : m.current < m.threads.size)
    (hcr : c < storeCount 64 .release 8 sPtr m ∨ storeCount 64 .release 8 sPtr m = 0 ∧ c = 0)
    (e : Error) :
    ((atomicStorePtrAt c .release 8 sPtr (some nPtr : Option Ptr)).run m).run ≠ some (.error e) := by
  obtain ⟨blk₀, hb₀, hk₀, -, hacc₀⟩ := access_blk (p := sPtr) (a := 8) (len := intSize 64) (o := 0)
    hi.b0 (by decide) (fun A hA => by omega) rfl
  have hacc : m.accessW sPtr (intSize 64) 8 = pure (0, blk₀, 0) := by simp [Mem.accessW, hacc₀, hk₀]
  have hir := hi.record (b := 0) (o := 0) (len := intSize 64) (k := .atomicWrite) ht
    (fun h => by cases h) (.inr (.inr (.inr ⟨rfl, rfl⟩)))
  refine atomicStorePtrAt_noErr (storePrep_noErr hacc (noRace_slot rfl hi ht)
    (slot_locIdx_noErr hir.slot)) (fun li slots m₁ hp => ?_) e
  obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := storePrep_ok hp
  obtain ⟨rfl, rfl, -⟩ := accW_slot hi.b0 hacc'
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_slot hir.slot hl
  have hne := writeSlots_ne (m := { m.recordAt 0 0 (intSize 64) .atomicWrite with atomics := #[l], nextMsg := k })
    (li := 0) (by show 0 < l.msgs.size; exact hfl.pos)
  have hcount : storeCount 64 .release 8 sPtr m = (writeSlots { m.recordAt 0 0 (intSize 64) .atomicWrite with
      atomics := #[l], nextMsg := k } 0).size := optCount_eq hp
  rw [hcount] at hcr
  rcases hcr with h | ⟨h0, -⟩
  · exact h
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp hne)

end Atomics.PtrPublish
