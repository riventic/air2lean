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
      let r ← ((match ← Zig.atomicLoadPtrC (Option Zig.Ptr) .acquire 8 slot with
        | some p => Zig.load (BitVec 32) 4 p
        | none => pure 0) : Zig.CM Tgt Unit (BitVec 32))
      Zig.joinC h
      ((match ← Zig.atomicLoadPtrC (Option Zig.Ptr) .relaxed 8 slot with
        | some p => Zig.callMC (Zig.Allocator.destroy ⟨⟩ 4 p)
        | none => pure ()) : Zig.CM Tgt Unit Unit)
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
  ((m.threads.size = 1 ∧ G 0 = .pre ∧ m.blocks.size = 1 ∧ ∀ u, 1 ≤ u → G u = .none) ∨
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
  thr := by unfold ThrOk; rw [hg.threads, hg.csize, hg.blocks]; exact hi.thr
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
  obtain ⟨-, -, ⟨-, h0, -, hn⟩ | ⟨hs, -, -, -, -, hn⟩⟩ := h
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
  obtain ⟨h0, hcs, ⟨-, -, -, hn⟩ | ⟨hs2, ⟨r, hr, hsp, hj⟩, g0, -, gp, g2⟩⟩ := h
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

/-- Every thread was spawned by `main`: A joined its own threads (none). -/
theorem joinedAll_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hi : Inv G m) (hu : 0 < u) :
    joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, -, h⟩ := hi.thr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have h0' : ∀ h : 0 < m.threads.size, (m.threads[0]'h).spawner = 0 := by
    intro h
    rw [Array.getElem?_eq_getElem h] at h0
    rw [Option.some.inj h0]
  rcases h with ⟨h1, -, -⟩ | ⟨h2, ⟨r₁, hr₁, hsp, -⟩, -⟩
  · have : i = 0 := by omega
    subst this
    rw [h0' hi'] at hs; exact absurd hs (Nat.ne_of_lt hu)
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [h0' hi'] at hs; exact absurd hs (Nat.ne_of_lt hu)
    · rw [Array.getElem?_eq_getElem hi'] at hr₁
      rw [Option.some.inj hr₁, hsp] at hs; exact absurd hs (Nat.ne_of_lt hu)

/-- A (thread 1): the allocation, the write of 42 and the release store (a stop), or the end
after a failed allocation. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | producer p =>
    simp only [proto] at hg
    split at hg
    · rename_i hp
      subst hp
      cases hg
      have hi₀ : Inv G { m with current := u } := (hi : Inv G m).grow (grows_current m u)
      obtain ⟨hs2, hu2⟩ := thr_of hi₀.thr (.inr (.inr (.inr (.inl hgu))))
      have hu1 : u = 1 := by unfold ThreadId at *; omega
      subst hu1
      have hs1 : ({ m with current := 1 } : Mem).blocks.size = 1 := hi₀.start hgu
      show proto.WP 1 (producer sPtr) _ G _ d
      unfold producer
      rw [StateT.run'_eq]
      refine WP.map ?_
      simp only [StateT.run_bind]
      -- the allocation
      refine WP.bind (WP.callMC (fun e he => (create_noErr _ e he).elim) fun r m₁ hr => ?_)
      rcases create_ok hr with ⟨err, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- out of memory: A ends
        refine ⟨rfl, ?_⟩
        simp only [StateT.run_pure]
        exact WP.pure' ⟨.fin, inv_oom hi₀ hgu, rfl, fun _ => joinedAll_kid (inv_oom hi₀ hgu) (by decide)⟩
      · refine ⟨by simp [allocM], ?_⟩
        rw [show (⟨some ({ m with current := 1 } : Mem).blocks.size, 0⟩ : Ptr) = nPtr by rw [hs1]; rfl]
        simp only [StateT.run_bind, bind_assoc, atomicStorePtrC]
        -- the write of 42
        refine WP.bind (WP.liftM (fun e he => (node_noErr hi₀ hgu rfl e he).elim) fun _ m₂ hs => ?_)
        obtain ⟨hc₂, hth₂, hi₂⟩ := step_node hi₀ hgu rfl hs
        refine ⟨by rw [hth₂]; rfl, ?_⟩
        -- the release store of the node's pointer
        refine WP.bind (WP.pickC fun k₁ hk₁ => ⟨.wrote, hi₂,
          fun G₁ m₃ hg₁ hi₃ c hcr => ?_⟩)
        have hi₃' : Inv G₁ { m₃ with current := 1 } := (hi₃ : Inv G₁ m₃).grow (grows_current _ _)
        have ht₃ : ({ m₃ with current := 1 } : Mem).current < ({ m₃ with current := 1 } : Mem).threads.size := by
          show 1 < _; rw [(thr_of hi₃'.thr (.inr (.inr (.inr (.inr (.inl hg₁)))))).1]; decide
        refine WP.callMC (fun e he => (store_noErr hi₃' ht₃ hcr e he).elim) fun _ m₄ hs₄ => ?_
        obtain ⟨hth₄, hi₄⟩ := step_store hi₃' hg₁ rfl hs₄
        exact ⟨by rw [hth₄], .fin, hi₄, rfl, fun _ => joinedAll_kid hi₄ (by decide)⟩
    · cases hg

/-! ## `main` before its spawn -/

/-- `main` before its spawn: `Solo`, with the slot's block only. -/
structure Pre (m : Mem) : Prop extends Solo m where
  b0 : BlkAt m 0 8 8
  one : m.blocks.size = 1

theorem size_noneBytes : noneBytes.size = 8 := LawfulEnc.size_encode (α := Option Ptr) _

/-- `main`'s store of `null` to the slot. -/
theorem pre_store {m m' : Mem} (h : Pre m)
    (hs : ((store (α := Option Ptr) 8 sPtr none).run m).run = some (.ok ((), m'))) :
    Pre m' ∧ curBytes m' 0 0 8 = noneBytes := by
  obtain ⟨hs', hk, -, h1, -⟩ := solo_store (b := 0) (sz := 8) (al := 8) (o := 0) h.toSolo h.b0
    (by rw [size_noneBytes.symm.trans rfl] at *; exact (by
      show 0 + (Enc.encode (none : Option Ptr)).size ≤ 8
      rw [LawfulEnc.size_encode]; decide))
    (fun A hA => by omega) hs
  have hsz : m'.blocks.size = m.blocks.size := by
    obtain ⟨b, blk, o, -, -, rfl⟩ := store_ok hs
    simp [Mem.write, Mem.recordAt]
  refine ⟨{ toSolo := hs', b0 := hk _ _ _ h.b0, one := hsz ▸ h.one }, ?_⟩
  have e : (Enc.encode (none : Option Ptr)).size = 8 := LawfulEnc.size_encode _
  rw [e] at h1
  exact h1

theorem pre_store_noErr {m : Mem} (h : Pre m) (e : Error) :
    ((store (α := Option Ptr) 8 sPtr none).run m).run ≠ some (.error e) :=
  solo_store_noErr (b := 0) (sz := 8) (al := 8) (o := 0) h.toSolo h.b0
    (by show 0 + (Enc.encode (none : Option Ptr)).size ≤ 8; rw [LawfulEnc.size_encode]; decide)
    (fun A hA => by omega) e

/-- The start: before its spawn, `main` holds the invariant with the ghost value `pre`. -/
def G0 : ThreadId → Gh := fun u => if u = 0 then .pre else .none

theorem pre_inv {m : Mem} (h : Pre m) (hb : curBytes m 0 0 8 = noneBytes) : Inv G0 m where
  thr := by
    refine ⟨by rw [h.thr]; rfl, by rw [h.clk, h.thr]; rfl, .inl ⟨by rw [h.thr]; rfl, rfl, h.one,
      fun u hu => ?_⟩⟩
    unfold G0; split
    · rename_i h; unfold ThreadId at *; omega
    · rfl
  b0 := h.b0
  start := fun hg => by simp [G0] at hg
  wrote := fun hg => by simp [G0] at hg
  slot := .inl ⟨h.at0, hb⟩
  fp := fun e he => .inl ⟨(h.fp e he).1, fun u hu => by
    have : u = 0 := by rw [h.thr] at hu; simp at hu; omega
    rw [this]; exact (h.fp e he).2.2⟩
  own := fun e he => by
    obtain ⟨-, h2, h3⟩ := h.fp e he
    rw [h2]; exact ⟨by rw [h.thr]; decide, h3⟩

/-- `main`'s spawn, for the threads: A is thread 1; `main` goes to `run`, A starts. -/
theorem thr_fork {G : ThreadId → Gh} {m : Mem} (h : ThrOk G m) (hg : G 0 = .pre)
    (hc : m.current = 0) :
    m.threads.size = 1 ∧ m.blocks.size = 1 ∧ (∀ u, 1 ≤ u → G u = .none) ∧ m.clocks.size = 1 ∧
    ThrOk (upd (upd G 1 .start) 0 .run) { m with
      clocks := (m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current)).push
        (VClock.bump (m.clocks[m.current]!) m.current),
      threads := m.threads.push { spawner := m.current, joined := false } } := by
  obtain ⟨h0, hcs, hthr⟩ := h
  obtain ⟨hs1, -, hb1, hnone⟩ : m.threads.size = 1 ∧ G 0 = .pre ∧ m.blocks.size = 1 ∧
      ∀ u, 1 ≤ u → G u = .none := by
    rcases hthr with h | ⟨-, -, g0, -⟩
    · exact h
    · rcases g0 with g0 | g0 | g0 <;> rw [hg] at g0 <;> cases g0
  have hG1 : (upd (upd G 1 .start) 0 .run) 1 = .start := by rw [upd_ne _ _ (by decide), upd_self]
  have hG0 : (upd (upd G 1 .start) 0 .run) 0 = .run := upd_self _ _ _
  refine ⟨hs1, hb1, hnone, by rw [hcs, hs1], ⟨by
      rw [Array.getElem?_push_lt (by omega), ← Array.getElem?_eq_getElem (by omega)]; exact h0,
    by simp [hcs], .inr ⟨by simp [hs1], ⟨{ spawner := m.current, joined := false },
      by simp [Array.getElem_push, hs1], hc, by rw [hG0]; rfl⟩, .inl hG0, .inl hG1,
      fun hp => absurd (hG0.symm.trans hp) (by decide), fun u hu => ?_⟩⟩⟩
  rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
  exact hnone u (by unfold ThreadId at *; omega)

/-- `main`'s spawn: A is thread 1. -/
theorem inv_fork {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} (hi : Inv G m) (hg : G 0 = .pre)
    (hc : m.current = 0) (h : (Thread.fork.run m).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ Inv (upd (upd G 1 .start) 0 .run) m' := by
  rw [fork_run] at h
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hs1, hb1, hnone, hcs, hthr⟩ := thr_fork hi.thr hg hc
  refine ⟨hs1, hc, ?_⟩
  have hG1 : (upd (upd G 1 .start) 0 .run) 1 = .start := by rw [upd_ne _ _ (by decide), upd_self]
  have hcl : ∀ u < 2, VClock.le (m.clocks[0]!) (((m.clocks.set! m.current
      (VClock.bump (m.clocks[m.current]!) m.current)).push
      (VClock.bump (m.clocks[m.current]!) m.current))[u]!) = true := by
    intro u hu
    rw [hc, fork_clocks_one hcs u hu]
    exact VClock.le_bump _ _
  refine {
    thr := hthr
    b0 := hi.b0
    start := fun _ => hb1
    wrote := fun h => by rw [hG1] at h; cases h
    slot := ?_
    fp := ?_
    own := ?_ }
  · rcases hi.slot with h | ⟨l, ha, hlb, hlo, hll, hlast, h1 | ⟨-, -, -, -, -, hfin, -⟩⟩
    · exact .inl h
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, .inl h1⟩
    · rw [hnone 1 (by decide)] at hfin; cases hfin
  · intro e he
    rcases hi.fp e he with ⟨hk, hb⟩ | h | ⟨-, -, hfin⟩ | h
    · refine .inl ⟨hk, fun u hu => VClock.le_trans (hb 0 (by rw [hs1]; decide)) (hcl u ?_)⟩
      simpa [hs1] using hu
    · exact .inr (.inl h)
    · rw [hnone 1 (by decide)] at hfin; cases hfin
    · exact .inr (.inr (.inr h))
  · intro e he
    obtain ⟨h1, h2⟩ := hi.own e he
    have ht0 : e.tid = 0 := by unfold ThreadId at *; omega
    refine ⟨by rw [ht0, Array.size_push, hs1]; decide, ?_⟩
    rw [ht0] at h2 ⊢
    exact VClock.le_trans h2 (hcl 0 (by decide))

/-! ## `main`: the acquire load and the read of the node -/

theorem decode_none : (Enc.decode noneBytes : Result (Option Ptr)) = pure none :=
  LawfulEnc.decode_encode _

theorem decode_some : (Enc.decode someBytes : Result (Option Ptr)) = pure (some nPtr) :=
  LawfulEnc.decode_encode _

/-- A message's pointer: `null` or the node, from its bytes. -/
theorem decode_eq {bs : Array Byte} {v : Option Ptr} {w : Option Ptr}
    (hb : (Enc.decode bs : Result (Option Ptr)) = pure w)
    (hv : (Enc.decode bs : Result (Option Ptr)).run = some (.ok v)) : v = w := by
  rw [hb] at hv
  simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at hv
  exact hv.symm

/-- `main`'s acquire load of the slot: `null`, or the node, and then A has ended, the node is
live, holds 42, and every write to it happened before `main`. -/
theorem step_acq {G : ThreadId → Gh} {m m' : Mem} {c : Nat} {v : Option Ptr} (hi : Inv G m)
    (hg : G 0 = .run) (hc : m.current = 0)
    (h : ((atomicLoadPtrAt (Option Ptr) c .acquire 8 sPtr).run m).run = some (.ok (v, m'))) :
    m'.current = 0 ∧ m'.threads = m.threads ∧ Inv G m' ∧
      (v = none ∨ (v = some nPtr ∧ G 1 = .fin ∧ NodeAt m' ∧ U32At m' 1 42 ∧
        NodeLe m' (m'.clocks[0]!))) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hv, rfl⟩ := atomicLoadPtrAt_ok h
  obtain ⟨rfl, rfl, -⟩ := acc_slot hi.b0 hacc
  have hsz := (thr_of hi.thr (.inl hg)).1
  have ht : m.current < m.threads.size := by rw [hc, hsz]; decide
  have hir := hi.record (b := 0) (o := 0) (len := intSize 64) (k := .atomicRead) ht
    (fun h => by cases h) (.inr (.inr (.inr ⟨rfl, rfl⟩)))
  have hcur : (m.recordAt 0 0 (intSize 64) .atomicRead).current = 0 := hc
  have hcs : 0 < (m.recordAt 0 0 (intSize 64) .atomicRead).clocks.size := by
    show 0 < (m.clocks.set! _ _).size; simp [hi.thr.2.1, hsz]
  have hthr : (m.recordAt 0 0 (intSize 64) .atomicRead).threads = m.threads := rfl
  generalize m.recordAt 0 0 (intSize 64) .atomicRead = mr at hir hl hcur hcs hthr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_slot hir.slot hl
  have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hiM := hir.setLoc hfl k
  have hg' := grows_loadM { mr with atomics := #[l], nextMsg := k } 0 .acquire
    ((({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[pos]!)
  refine ⟨by rw [loadM_current]; exact hcur, hg'.threads.trans hthr, hiM.grow hg', ?_⟩
  have hlt := readOpts_lt hpos
  rw [hl0] at hlt hv
  obtain ⟨-, -, -, -, ⟨m0, hms, h0⟩ | ⟨m0, m1, hms, h0, h1, hfin, hn, h42, hle, -⟩⟩ := hfl
  · rw [hms] at hlt hv
    have : pos = 0 := by simp at hlt; omega
    subst this
    left
    exact decode_eq (by rw [show (#[m0] : Array Msg)[0]! = m0 from rfl, h0]; exact decode_none) hv
  · rw [hms] at hlt hv
    have : pos = 0 ∨ pos = 1 := by simp at hlt; omega
    rcases this with rfl | rfl
    · left
      exact decode_eq (by rw [show (#[m0, m1] : Array Msg)[0]! = m0 from rfl, h0]; exact decode_none) hv
    · right
      refine ⟨decode_eq (by rw [show (#[m0, m1] : Array Msg)[1]! = m1 from rfl, h1]; exact decode_some) hv,
        hfin, hn.congr hg'.blocks, by unfold U32At; rw [curBytes_congr hg'.blocks]; exact h42,
        fun e he hb1 hkw => ?_⟩
      rw [hg'.footprint] at he
      have hmsg : (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[1]! = m1 := by
        rw [hl0, hms]; rfl
      rw [hmsg]
      exact VClock.le_trans (hle e he hb1 hkw) (loadM_acq_le _ _ _ hcur hcs)

/-- A load of the slot gives no error: each message it can read holds `null` or the node. -/
theorem slotLoad_noErr {G : ThreadId → Gh} {m : Mem} {c : Nat} {ord : AtomicOrder} (hi : Inv G m)
    (ht : m.current < m.threads.size)
    (hcr : c < loadCount 64 ord 8 sPtr m ∨ loadCount 64 ord 8 sPtr m = 0 ∧ c = 0)
    (e : Error) : ((atomicLoadPtrAt (Option Ptr) c ord 8 sPtr).run m).run ≠ some (.error e) := by
  obtain ⟨blk₀, hb₀, -, -, hacc₀⟩ := access_blk (p := sPtr) (a := 8) (len := intSize 64) (o := 0)
    hi.b0 (by decide) (fun A hA => by omega) rfl
  have hir := hi.record (b := 0) (o := 0) (len := intSize 64) (k := .atomicRead) ht
    (fun h => by cases h) (.inr (.inr (.inr ⟨rfl, rfl⟩)))
  refine atomicLoadPtrAt_noErr (loadPrep_noErr (rmw := false) (by simpa using hacc₀)
    (by simpa using noRace_slot (k := .atomicRead) rfl hi ht)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact slot_locIdx_noErr hir.slot))
    (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at hacc' hl
  obtain ⟨rfl, rfl, -⟩ := acc_slot hi.b0 hacc'
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_slot hir.slot hl
  have hl0 : ({ m.recordAt 0 0 (intSize 64) .atomicRead with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hcount : loadCount 64 ord 8 sPtr m = (readOpts { m.recordAt 0 0 (intSize 64) .atomicRead with
      atomics := #[l], nextMsg := k } 0 false).size := optCount_eq hp
  have hne : 0 < (readOpts { m.recordAt 0 0 (intSize 64) .atomicRead with
      atomics := #[l], nextMsg := k } 0 false).size := readOpts_ne (by rw [hl0]; exact hfl.pos)
  rw [hcount] at hcr
  have hc : c < (readOpts { m.recordAt 0 0 (intSize 64) .atomicRead with atomics := #[l], nextMsg := k } 0 false).size := by
    rcases hcr with h | ⟨h0, -⟩
    · exact h
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp hne)
  obtain ⟨pos, hpos⟩ : ∃ pos, (readOpts { m.recordAt 0 0 (intSize 64) .atomicRead with
      atomics := #[l], nextMsg := k } 0 false)[c]? = some pos := ⟨_, Array.getElem?_eq_getElem hc⟩
  refine ⟨pos, hpos, ?_⟩
  have hlt := readOpts_lt hpos
  rw [hl0] at hlt ⊢
  obtain ⟨-, -, -, -, ⟨m0, hms, h0⟩ | ⟨m0, m1, hms, h0, h1, -⟩⟩ := hfl
  · rw [hms] at hlt ⊢
    have : pos = 0 := by simp at hlt; omega
    subst this
    exact ⟨none, by rw [show (#[m0] : Array Msg)[0]! = m0 from rfl, h0, decode_none]; rfl⟩
  · rw [hms] at hlt ⊢
    have : pos = 0 ∨ pos = 1 := by simp at hlt; omega
    rcases this with rfl | rfl
    · exact ⟨none, by rw [show (#[m0, m1] : Array Msg)[0]! = m0 from rfl, h0, decode_none]; rfl⟩
    · exact ⟨some nPtr, by rw [show (#[m0, m1] : Array Msg)[1]! = m1 from rfl, h1, decode_some]; rfl⟩

/-- An access to the node, through the pointer that `main` read. -/
theorem acc_node {m : Mem} (hn : NodeAt m) (n a : Nat) (hn4 : n ≤ 4) (ha : 4 % a = 0) :
    ∃ blk, m.blocks[1]? = some blk ∧ blk.kind = .heap ∧ blk.bytes.size = 4 ∧
      m.access nPtr n a = pure (1, blk, 0) := by
  obtain ⟨blk, hb, hl, hs, hk, hadd⟩ := hn
  refine ⟨blk, hb, hk, hs, access_of rfl hb hl (by simp [nPtr]) (by simp [nPtr, hs]; omega) ?_⟩
  simp only [nPtr, Int.toNat_zero, Nat.add_zero]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero ha)
    (Nat.dvd_of_mod_eq_zero hadd))

/-- `main`'s read of the node after it read its pointer: 42, no race. -/
theorem step_read {G : ThreadId → Gh} {m m' : Mem} {v : BitVec 32} (hi : Inv G m)
    (hfin : G 1 = .fin) (hn : NodeAt m) (h42 : U32At m 1 42)
    (h : ((load (BitVec 32) 4 nPtr).run m).run = some (.ok (v, m')))
    (ht : m.current < m.threads.size) :
    v = 42 ∧ m' = m.recordAt 1 0 4 .read ∧ Inv G m' := by
  obtain ⟨b, blk, o, hacc, -, hdec, rfl⟩ := load_ok h
  obtain ⟨blk₁, hb₁, -, -, hacc₁⟩ := acc_node hn (Enc.size (BitVec 32)) 4 (by decide) (by decide)
  rw [hacc₁] at hacc
  cases hacc
  unfold U32At curBytes at h42
  rw [hb₁] at h42
  have : (Enc.decode (blk.bytes.extract 0 (0 + Enc.size (BitVec 32))) : Result (BitVec 32)).run =
      some (.ok 42) := h42
  rw [this] at hdec
  simp only [Option.some.injEq, Except.ok.injEq] at hdec
  exact ⟨hdec.symm, rfl, hi.record ht (fun _ h => by cases h) (.inr (.inr (.inl ⟨rfl, rfl, hfin⟩)))⟩

theorem read_noErr {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hn : NodeAt m)
    (h42 : U32At m 1 42) (hle : NodeLe m (m.clocks[m.current]!)) (ht : m.current < m.threads.size)
    (e : Error) : ((load (BitVec 32) 4 nPtr).run m).run ≠ some (.error e) := by
  obtain ⟨blk₁, hb₁, -, -, hacc₁⟩ := acc_node hn (Enc.size (BitVec 32)) 4 (by decide) (by decide)
  unfold U32At curBytes at h42
  rw [hb₁] at h42
  have hnr : NoRace m 1 0 (Enc.size (BitVec 32)) .read := noRace_inv hi ht fun e he hb hf => by
    rcases hf with h | ⟨-, hk, -⟩ | ⟨-, hk, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr (.inl (hle e he hb hk))
    · exact .inr (.inr (by rw [hk]; rfl))
    · exact (blk_ne h hb (by decide)).elim
  exact MemM.noErr_of_run (load_run hacc₁ h42 hnr) e

/-! ## `main`: the join, the load after it and the free -/

/-- A change of `main`'s ghost value from `run` to `joins`. -/
theorem Inv.retag0 {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hg : G 0 = .run) :
    Inv (upd G 0 .joins) m := by
  have h1 : upd G 0 Gh.joins 1 = G 1 := upd_ne _ _ (by decide)
  have h0 : upd G 0 Gh.joins 0 = .joins := upd_self _ _ _
  obtain ⟨t0, tc, ⟨-, hp, -⟩ | ⟨hs2, ⟨r, hr, hsp, hj⟩, -, g1, gp, g2⟩⟩ := hi.thr
  · rw [hg] at hp; cases hp
  exact {
    thr := ⟨t0, tc, .inr ⟨hs2, ⟨r, hr, hsp, by rw [hj, hg, h0]; decide⟩, .inr (.inl h0), by rw [h1]; exact g1,
      fun hp => absurd (h0.symm.trans hp) (by decide),
      fun u hu => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact g2 u hu⟩⟩
    b0 := hi.b0
    start := by rw [h1]; exact hi.start
    wrote := by rw [h1]; exact hi.wrote
    slot := by
      unfold SlotOk SlotLoc
      rw [h1, h0]
      rcases hi.slot with h | ⟨l, ha, hlb, hlo, hll, hlast, h1' | ⟨m0, m1, hms, a, b, c, d, e, f, g, -⟩⟩
      · exact .inl h
      · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, .inl h1'⟩
      · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, .inr ⟨m0, m1, hms, a, b, c, d, e, f, g,
          fun h => by cases h⟩⟩
    fp := by intro e he; unfold FpOk; rw [h1]; exact hi.fp e he
    own := hi.own }

/-- `main`'s join of A is possible: thread 1, spawned by `main`, not joined. -/
theorem join_ok {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (h0 : G 0 = .joins) :
    ∃ m', ((Thread.join 1).run { m with current := 0 }).run = some (.ok ((), m')) := by
  obtain ⟨-, -, ⟨-, hp, -⟩ | ⟨-, ⟨r, hr, hs, hj⟩, -⟩⟩ := hi.thr
  · rw [h0] at hp; cases hp
  · rw [h0] at hj
    exact join_run (m := { m with current := 0 }) hr hs (by rw [hj]; rfl)

/-- After the join: `main` is at `post`, and its clock is above A's. -/
theorem inv_join {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (h0 : G 0 = .joins)
    (hfin : G 1 = .fin)
    (hj : ((Thread.join 1).run { m with current := 0 }).run = some (.ok ((), m'))) :
    m'.current = 0 ∧ Inv (upd G 0 .post) m' := by
  obtain ⟨jr, hr, hjf, rfl⟩ := join_eq hj
  obtain ⟨h00, hcs, ⟨-, hp, -⟩ | ⟨hs2, ⟨r, hr', hsp, hj'⟩, -, -, -, g2⟩⟩ := hi.thr
  · rw [h0] at hp; cases hp
  have hrr : r = jr := Option.some.inj (hr'.symm.trans hr)
  have hsp' : jr.spawner = 0 := hrr ▸ hsp
  have e1 : upd G 0 Gh.post 1 = G 1 := upd_ne _ _ (by decide)
  have e0 : upd G 0 Gh.post 0 = .post := upd_self _ _ _
  have hc0 : 0 < m.clocks.size := by rw [hcs, hs2]; decide
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) ((m.clocks.set! 0
      (VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[1]!)))[u]!) = true := by
    intro u
    rw [getElem!_set!_ite]
    split
    · rename_i h; rw [h.1]
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _
  have hc1 : (m.clocks.set! 0 (VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[1]!)))[1]! =
      m.clocks[1]! := by rw [getElem!_set!_ite]; simp
  have hcm : VClock.le (m.clocks[1]!) ((m.clocks.set! 0
      (VClock.merge (VClock.bump (m.clocks[0]!) 0) (m.clocks[1]!)))[0]!) = true := by
    rw [getElem!_set!_ite]; simp only [true_and, hc0, ↓reduceIte]
    exact VClock.le_merge_right _ _
  have hthr0 : (m.threads.set! 1 { jr with joined := true })[0]? = m.threads[0]? := by
    simp [Array.set!_eq_setIfInBounds]
  refine ⟨rfl, {
    thr := ⟨by rw [hthr0]; exact h00, by simp [hcs], .inr ⟨by simp [hs2],
      ⟨{ jr with joined := true }, by
        simp only [Array.set!_eq_setIfInBounds]
        exact Array.getElem?_setIfInBounds_self_of_lt (by omega), hsp', by rw [e0]; rfl⟩,
      .inr (.inr e0), by rw [e1, hfin]; exact .inr (.inr rfl), fun _ => by rw [e1]; exact hfin,
      fun u hu => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact g2 u hu⟩⟩
    b0 := hi.b0
    start := fun h => by rw [e1, hfin] at h; cases h
    wrote := fun h => by rw [e1, hfin] at h; cases h
    slot := by
      rcases hi.slot with h | ⟨l, ha, hlb, hlo, hll, hlast, h1' |
          ⟨m0, m1, hms, a, b, -, d, e, f, hl1, -⟩⟩
      · exact .inl h
      · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, .inl h1'⟩
      · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, .inr ⟨m0, m1, hms, a, b, by rw [e1]; exact hfin,
          d, e, f, by show VClock.le _ ((m.clocks.set! 0 _)[1]!) = true; rw [hc1]; exact hl1,
          fun _ => VClock.le_trans hl1 hcm⟩⟩
    fp := by
      intro e he
      rcases hi.fp e he with ⟨hk, hb⟩ | h | ⟨a, b, -⟩ | h
      · refine .inl ⟨hk, fun (u : Nat) hu => VClock.le_trans (hb u ?_) (hcl u)⟩
        simpa [Array.size_set!] using hu
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl ⟨a, b, by rw [e1]; exact hfin⟩))
      · exact .inr (.inr (.inr h))
    own := by
      intro e he
      obtain ⟨h1, h2⟩ := hi.own e he
      exact ⟨by simpa using h1, VClock.le_trans h2 (hcl _)⟩ }⟩

/-- At `post`, `main` joined every thread. -/
theorem joinedAll_post {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (h0 : G 0 = .post) :
    joinedAll 0 m := by
  intro r hr _
  obtain ⟨t0, -, ⟨-, hp, -⟩ | ⟨hs2, ⟨r₁, hr₁, -, hj⟩, -⟩⟩ := hi.thr
  · rw [h0] at hp; cases hp
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [Array.getElem?_eq_getElem hi'] at t0; rw [Option.some.inj t0]
  · rw [Array.getElem?_eq_getElem hi'] at hr₁; rw [Option.some.inj hr₁, hj, h0]; rfl

/-- `main`'s load of the slot after the join: the newest message (the join put A's store before
`main`): `null` if A published nothing, else the node, live. -/
theorem step_last {G : ThreadId → Gh} {m m' : Mem} {c : Nat} {v : Option Ptr} (hi : Inv G m)
    (hg : G 0 = .post) (hc : m.current = 0)
    (h : ((atomicLoadPtrAt (Option Ptr) c .relaxed 8 sPtr).run m).run = some (.ok (v, m'))) :
    m'.threads = m.threads ∧ m'.blocks = m.blocks ∧ (v = none ∨ (v = some nPtr ∧ NodeAt m)) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hv, rfl⟩ := atomicLoadPtrAt_ok h
  obtain ⟨rfl, rfl, -⟩ := acc_slot hi.b0 hacc
  have hsz := (thr_of hi.thr (.inr (.inr (.inl hg)))).1
  have ht : m.current < m.threads.size := by rw [hc, hsz]; decide
  have hir := hi.record (b := 0) (o := 0) (len := intSize 64) (k := .atomicRead) ht
    (fun h => by cases h) (.inr (.inr (.inr ⟨rfl, rfl⟩)))
  have hcl0 : VClock.le (m.clocks[0]!) ((m.recordAt 0 0 (intSize 64) .atomicRead).clocks[0]!) = true :=
    recordAt_le' _ _ _ _ _ _
  have hcur : (m.recordAt 0 0 (intSize 64) .atomicRead).current = 0 := hc
  have hthr : (m.recordAt 0 0 (intSize 64) .atomicRead).threads = m.threads := rfl
  have hblk : (m.recordAt 0 0 (intSize 64) .atomicRead).blocks = m.blocks := rfl
  generalize m.recordAt 0 0 (intSize 64) .atomicRead = mr at hir hl hcur hthr hblk hcl0
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_slot hir.slot hl
  have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hg' := grows_loadM { mr with atomics := #[l], nextMsg := k } 0 .relaxed
    ((({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[pos]!)
  refine ⟨hg'.threads.trans hthr, hg'.blocks.trans hblk, ?_⟩
  have hlt := readOpts_lt hpos
  obtain ⟨-, -, -, -, ⟨m0, hms, h0⟩ | ⟨m0, m1, hms, h0, h1, -, hn, -, -, -, hpost⟩⟩ := hfl
  · rw [hl0, hms] at hlt hv
    have : pos = 0 := by simp at hlt; omega
    subst this
    exact .inl (decode_eq (by rw [show (#[m0] : Array Msg)[0]! = m0 from rfl, h0]; exact decode_none) hv)
  · -- the floor is the newest message: `main`'s clock is above A's message
    have hsz2 : (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs.size = 2 := by
      rw [hl0, hms]; rfl
    have hfl1 : 1 ≤ floorPos { mr with atomics := #[l], nextMsg := k } 0 := by
      refine le_floorPos (by rw [hsz2]; decide) ?_
      have e : ((({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[1]'(by rw [hsz2]; decide)) = m1 := by
        simp only [hl0, hms]; rfl
      rw [e]
      show VClock.le m1.clock (mr.clocks[mr.current]!) = true
      rw [hcur]
      exact hpost hg
    have hflt := floorPos_lt (m := { mr with atomics := #[l], nextMsg := k }) (li := 0) (by rw [hsz2]; decide)
    rw [hsz2] at hflt
    have hro := readOpts_floor (m := { mr with atomics := #[l], nextMsg := k }) (li := 0)
      (by rw [hsz2]; decide) (by rw [hsz2]; omega)
    rw [hro, hsz2] at hpos
    have : pos = 1 := by
      rcases c with _ | c
      · simpa using hpos.symm
      · simp at hpos
    subst this
    rw [hl0, hms] at hv
    exact .inr ⟨decode_eq (by rw [show (#[m0, m1] : Array Msg)[1]! = m1 from rfl, h1]; exact decode_some) hv,
      hn.congr hblk.symm⟩

/-- `destroy(node)`: a free of the live heap block. -/
theorem destroy_ok {m m' : Mem} (h : ((Allocator.destroy ⟨⟩ 4 nPtr).run m).run = some (.ok ((), m'))) :
    m'.threads = m.threads ∧ ∀ b, b ≠ 1 → m'.blocks[b]? = m.blocks[b]? := by
  simp only [Allocator.destroy, show ((4 : Nat) = 0) = False from by decide, if_false] at h
  unfold rawFree at h
  obtain ⟨a, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨⟨b, blk, o⟩, m₂, ha, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨ha, rfl⟩ := MemM.lift_ok ha
  dsimp only at h₂
  split at h₂
  · obtain ⟨b', blk', hb', -, rfl⟩ := free_ok h₂
    cases hb'
    refine ⟨rfl, fun b hb => ?_⟩
    simp only [Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_ne (Ne.symm hb)
  · exact (MemM.throw_ok h₂).elim

theorem destroy_noErr {m : Mem} (hn : NodeAt m) (e : Error) :
    ((Allocator.destroy ⟨⟩ 4 nPtr).run m).run ≠ some (.error e) := by
  obtain ⟨blk, hb, hk, hs, hacc⟩ := acc_node hn 4 1 (by decide) (by decide)
  have hl : blk.live = true := by
    obtain ⟨b', hb', hl', -⟩ := hn; rw [hb] at hb'; cases hb'; exact hl'
  intro h
  simp only [Allocator.destroy, show ((4 : Nat) = 0) = False from by decide, if_false] at h
  unfold rawFree at h
  rcases MemM.bind_err h with h | ⟨a, m₁, hg, h₁⟩
  · exact MemM.get_err h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  rcases MemM.bind_err h₁ with h | ⟨r, m₂, ha, h₂⟩
  · have := MemM.lift_err h
    rw [hacc] at this
    simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at this
  obtain ⟨ha, rfl⟩ := MemM.lift_ok ha
  rw [hacc] at ha
  simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at ha
  subst ha
  dsimp only at h₂
  rw [if_pos ⟨hk, rfl, hs⟩] at h₂
  exact free_noErr hb hl e h₂

/-- `main`: the slot, the store of `null`, the spawn, the acquire load (a stop), the read of the
node, the join (a stop), the load after the join (a stop), the destroy, the free. -/
theorem main_spec (d : Nat) : proto.WP 0 publishRead QM G0 { mem0 with current := 0 } d := by
  unfold publishRead
  -- the slot
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s0 m₁ ha₁ => ?_)
  obtain ⟨hq₁, hm₁⟩ := alloc_ok ha₁
  have e0 : s0 = sPtr := by rw [hq₁]; rfl
  subst e0
  refine ⟨by rw [hm₁] <;> rfl, ?_⟩
  have hp₁ : Pre m₁ := by
    rw [hm₁]
    exact { toSolo := ⟨rfl, rfl, rfl, rfl, fun e he => by simp [mem0] at he⟩
            b0 := ⟨_, rfl, rfl, rfl, rfl, by decide⟩
            one := rfl }
  clear hm₁ ha₁ hq₁
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  -- `slot = null`
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₁ e he).elim) fun _ m₂ hs₂ => ?_)
  obtain ⟨hp₂, hb₂⟩ := pre_store hp₁ hs₂
  refine ⟨by rw [hp₂.thr, hp₁.thr], ?_⟩
  have hi₂ : Inv G0 m₂ := pre_inv hp₂ hb₂
  have hG0 : upd G0 0 .pre = G0 := by
    funext u; unfold upd G0; split <;> simp_all
  -- the spawn
  refine WP.bind (WP.spawnC fun k hk => ⟨.pre, by rw [hG0]; exact hi₂, fun G₁ m₃ hg₁ hi₃ =>
    ⟨.start, by simp [proto], fun child m₄ hf => ?_⟩⟩)
  obtain ⟨rfl, hc₄, hi₄⟩ := inv_fork ((hi₃ : Inv G₁ m₃).grow (grows_current m₃ 0)) hg₁ rfl hf
  dsimp only
  simp only [StateT.run_bind, bind_assoc, atomicLoadPtrC]
  -- the acquire load
  refine WP.bind (WP.pickC fun k₁ hk₁ => ⟨.run, hi₄, fun G₂ m₅ hg₂ hi₅ c hcr => ?_⟩)
  have hi₅' : Inv G₂ { m₅ with current := 0 } := (hi₅ : Inv G₂ m₅).grow (grows_current _ _)
  have ht₅ : ({ m₅ with current := 0 } : Mem).current <
      ({ m₅ with current := 0 } : Mem).threads.size := by
    show 0 < _; rw [(thr_of hi₅'.thr (.inl hg₂)).1]; decide
  refine WP.bind (WP.callMC (fun e he => (slotLoad_noErr hi₅' ht₅ hcr e he).elim) fun v m₆ hl => ?_)
  obtain ⟨hc₆, hth₆, hi₆, hv⟩ := step_acq hi₅' hg₂ rfl hl
  refine ⟨by rw [hth₆], ?_⟩
  dsimp only
  have ht₆ : m₆.current < m₆.threads.size := by rw [hc₆, hth₆]; exact ht₅
  -- the read of the node, if the slot held it: 0 or 42
  refine WP.bind (WP.mono (Q := fun (p : BitVec 32 × Unit) G m _ =>
      (p.1 = 0 ∨ p.1 = 42) ∧ m.current = 0 ∧ Inv G m ∧ G 0 = .run) ?_ ?_)
  rotate_left
  · rcases hv with rfl | ⟨rfl, hfin, hn, h42, hle⟩
    · simp only [StateT.run_pure]
      exact WP.pure' ⟨.inl rfl, hc₆, hi₆, hg₂⟩
    · refine WP.liftM (fun e he => (read_noErr hi₆ hn h42 (by rw [hc₆]; exact hle) ht₆ e he).elim)
        fun v' m₇ hl' => ?_
      obtain ⟨rfl, rfl, hi₇⟩ := step_read hi₆ hfin hn h42 hl' ht₆
      exact ⟨rfl, .inr rfl, hc₆, hi₇, hg₂⟩
  rintro ⟨r, _⟩ G₃ m₇ d₃ ⟨hr, -, hi₇, hg₃⟩
  dsimp only
  try simp only [StateT.run_bind]
  -- the join
  refine WP.bind (WP.joinC fun k₂ hk₂ => ⟨.joins, hi₇.retag0 hg₃, fun G₄ m₈ hg₄ hi₈ =>
    ⟨fun _ => ⟨by decide, by rw [(thr_of hi₈.thr (.inr (.inl hg₄))).1]; decide, rfl, by
      obtain ⟨m', hj⟩ := join_ok hi₈ hg₄
      exact Proto.join_valid hj⟩, fun hfin =>
      ⟨fun _ => join_ok hi₈ hg₄, fun m₉ hj => ?_⟩⟩⟩)
  obtain ⟨hc₉, hi₉⟩ := inv_join hi₈ hg₄ hfin hj
  dsimp only
  try simp only [StateT.run_bind, bind_assoc, atomicLoadPtrC]
  -- the load after the join
  refine WP.bind (WP.pickC fun k₃ hk₃ => ⟨.post, hi₉, fun G₅ m₁₀ hg₅ hi₁₀ c' hcr' => ?_⟩)
  have hi₁₀' : Inv G₅ { m₁₀ with current := 0 } := (hi₁₀ : Inv G₅ m₁₀).grow (grows_current _ _)
  have ht₁₀ : ({ m₁₀ with current := 0 } : Mem).current <
      ({ m₁₀ with current := 0 } : Mem).threads.size := by
    show 0 < _; rw [(thr_of hi₁₀'.thr (.inr (.inr (.inl hg₅)))).1]; decide
  refine WP.bind (WP.callMC (fun e he => (slotLoad_noErr hi₁₀' ht₁₀ hcr' e he).elim)
    fun w m₁₁ hl₂ => ?_)
  obtain ⟨hth₁₁, hb₁₁, hw⟩ := step_last hi₁₀' hg₅ rfl hl₂
  refine ⟨by rw [hth₁₁], ?_⟩
  have hja : joinedAll 0 m₁₁ := by
    have := joinedAll_post hi₁₀' hg₅; unfold joinedAll at this ⊢; rw [hth₁₁]; exact this
  have hb0 : ∃ blk, m₁₁.blocks[0]? = some blk ∧ blk.live = true := by
    obtain ⟨blk, hb, hl, -⟩ := hi₁₀'.b0
    exact ⟨blk, by rw [hb₁₁]; exact hb, hl⟩
  dsimp only
  -- the destroy of the node, if the slot held it
  refine WP.bind (WP.mono (Q := fun (p : Unit × Unit) G m _ =>
      joinedAll 0 m ∧ ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true) ?_ ?_)
  rotate_left
  · rcases hw with rfl | ⟨rfl, hn⟩
    · simp only [StateT.run_pure]
      exact WP.pure' ⟨hja, hb0⟩
    · refine WP.callMC (fun e he => (destroy_noErr (hn.congr hb₁₁) e he).elim) fun _ m₁₂ hd => ?_
      obtain ⟨hth, hbk⟩ := destroy_ok hd
      exact ⟨by rw [hth], by unfold joinedAll at hja ⊢; rw [hth]; exact hja,
        by rw [hbk 0 (by decide)]; exact hb0⟩
  rintro ⟨_, _⟩ G₆ m₁₂ d₆ ⟨hja', blk, hb, hl⟩
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- the free of the slot
  refine WP.bind (WP.liftMem (fun e he => (free_noErr hb hl e he).elim) fun _ m₁₃ hf => ?_)
  obtain ⟨b, blk', hb', -, rfl⟩ := free_ok hf
  refine ⟨rfl, WP.pure' ⟨hr, ?_⟩⟩
  unfold joinedAll at hja' ⊢
  exact hja'

/-! ## The results -/

/-- **Visibility.** `publishRead` gives 0 or 42 under every schedule (every oracle `o`, every
`fuel`): when B reads A's pointer, it reads the 42 that A wrote before publishing it. -/
theorem publishRead_spec {fuel : Nat} {o : Nat → Nat} {v : BitVec 32} {m : Mem}
    (h : (Sched.run dispatch fuel o publishRead mem0).run = some (.ok (v, m))) :
    v = 0 ∨ v = 42 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl main_spec h
  exact hv

/-- **Lifetime.** No run of `publishRead` gives an error under any schedule: no data race, no
access to a dead block, no invalid or double free, no undecodable pointer. -/
theorem publishRead_safe {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run dispatch fuel o publishRead mem0).run ≠ some (.error e) :=
  proto.run_safe dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl main_spec

end Atomics.PtrPublish
