import ZigLean.Sep.Owned

/-!
# A request-scoped arena client (M01)

The usual use of `std.heap.ArenaAllocator`: a server opens an arena for a session; each request
copies its fields into the arena (`dupe`), reads them back to compute a checksum, and resets
the arena on both outcomes (`defer arena.reset(...)`); the session ends with `deinit`.

`session_spec` holds for every memory, every allocation-failure policy and every request
list: the run returns one outcome per request, each the request's checksum or
`error.OutOfMemory`, nothing throws, and the final heap is the initial heap without the
session arena's blocks, which is the initial heap when no block claims the new arena
(`session_restores`).
-/

namespace Zig

/-! ## The client -/

/-- `r.dupe(u8, bs)`. -/
def dupeBytes (r : AllocRef) (bs : Array (BitVec 8)) : MemM (Except ErrName Slice) := do
  match ← r.alloc 1 1 (BitVec.ofNat 64 bs.size) with
  | .error e => pure (.error e)
  | .ok s =>
    if bs.size ≠ 0 then storeBytes s.ptr 1 (bs.map .int)
    pure (.ok s)

/-- Copy every field; stop at the first failure. -/
def dupeAll (r : AllocRef) : List (Array (BitVec 8)) → MemM (Except ErrName (List Slice))
  | [] => pure (.ok [])
  | f :: fs => do
    match ← dupeBytes r f with
    | .error e => pure (.error e)
    | .ok s =>
      match ← dupeAll r fs with
      | .error e => pure (.error e)
      | .ok ss => pure (.ok (s :: ss))

/-- The sum of the defined bytes. -/
def byteSum (bs : Array Byte) : Nat :=
  bs.foldl (fun acc b => match b with | .int x => acc + x.toNat | _ => acc) 0

/-- The bytes of a byte slice. -/
def readBytes (s : Slice) : MemM (Array Byte) :=
  if s.len.toNat = 0 then pure #[] else loadBytes s.ptr s.len.toNat 1

/-- Read every slice back and sum its bytes. -/
def sumAll : List Slice → MemM Nat
  | [] => pure 0
  | s :: ss => do
    let bs ← readBytes s
    let t ← sumAll ss
    pure (byteSum bs + t)

/-- The answer to one request, from arena `a`. -/
def answer (a : AllocId) (fields : List (Array (BitVec 8))) : MemM (Except ErrName Nat) := do
  match ← dupeAll (.owned a) fields with
  | .error e => pure (.error e)
  | .ok ss => Except.ok <$> sumAll ss

/-- One request on arena `a`; the arena is reset on both outcomes. -/
def handleRequest (a : AllocId) (fields : List (Array (BitVec 8))) :
    MemM (Except ErrName Nat) := do
  let out ← answer a fields
  Owned.reset a
  pure out

def serve (a : AllocId) : List (List (Array (BitVec 8))) → MemM (List (Except ErrName Nat))
  | [] => pure []
  | req :: reqs => do
    let r ← handleRequest a req
    let rs ← serve a reqs
    pure (r :: rs)

/-- A session: a new arena for all requests, deinitialized at the end. -/
def session (reqs : List (List (Array (BitVec 8)))) : MemM (List (Except ErrName Nat)) := do
  let a ← Arena.init
  let rs ← serve a reqs
  Arena.deinit a
  pure rs

/-- The checksum of a request. -/
def requestSum (fields : List (Array (BitVec 8))) : Nat :=
  (fields.map fun f => f.foldl (fun acc x => acc + x.toNat) 0).sum

/-- A permitted outcome of a request. -/
def RequestOutcome (r : Except ErrName Nat) (fields : List (Array (BitVec 8))) : Prop :=
  r = .ok (requestSum fields) ∨ r = .error "OutOfMemory"

/-! ## Invariants -/

/-- `m'` is `m` with more blocks, all of arena `a`, and the same allocators. -/
structure Grows (a : AllocId) (m m' : Mem) : Prop where
  size : m.blocks.size ≤ m'.blocks.size
  old : ∀ b, b < m.blocks.size → m'.blocks[b]? = m.blocks[b]?
  new : ∀ b blk, m.blocks.size ≤ b → m'.blocks[b]? = some blk → blk.kind = .owned a
  allocators : m'.allocators = m.allocators

theorem Grows.refl (a : AllocId) (m : Mem) : Grows a m m := by
  refine ⟨Nat.le_refl _, fun _ _ => rfl, fun b blk hb h => ?_, rfl⟩
  rw [Array.getElem?_eq_none hb] at h; cases h

theorem Grows.of_blocks {a : AllocId} {m m' : Mem} (hb : m'.blocks = m.blocks)
    (ha : m'.allocators = m.allocators) : Grows a m m' := by
  refine ⟨by rw [hb]; exact Nat.le_refl _, fun b _ => by rw [hb], fun b blk h h' => ?_, ha⟩
  rw [hb, Array.getElem?_eq_none h] at h'; cases h'

theorem Grows.trans {a : AllocId} {m₁ m₂ m₃ : Mem} (h₁ : Grows a m₁ m₂) (h₂ : Grows a m₂ m₃) :
    Grows a m₁ m₃ := by
  refine ⟨Nat.le_trans h₁.size h₂.size, fun b hb => ?_, fun b blk hb h => ?_,
    h₂.allocators.trans h₁.allocators⟩
  · rw [h₂.old b (Nat.lt_of_lt_of_le hb h₁.size), h₁.old b hb]
  · by_cases hb₂ : b < m₂.blocks.size
    · rw [h₂.old b hb₂] at h; exact h₁.new b blk hb h
    · exact h₂.new b blk (by omega) h

/-- Growth with arena blocks keeps the heap without the arena. -/
theorem Grows.dropOwned {a : AllocId} {m m' : Mem} (h : Grows a m m') :
    m'.heap.dropOwned a = m.heap.dropOwned a := by
  funext ⟨b, o⟩
  by_cases hb : b < m.blocks.size
  · simp only [Heap.dropOwned, Mem.heap, h.old b hb]
  · have hb := Nat.le_of_not_lt hb
    have e : m.blocks[b]? = none := Array.getElem?_eq_none hb
    simp only [Heap.dropOwned, Mem.heap, e]
    cases hb' : m'.blocks[b]? with
    | none => rfl
    | some blk =>
      have hk := h.new b blk hb hb'
      by_cases hc : blk.live ∧ o < blk.bytes.size <;> simp [hc, hk]

/-- Slice `s` holds the bytes of `f` in a live block. -/
def Holds (m : Mem) (s : Slice) (f : Array (BitVec 8)) : Prop :=
  s.len.toNat = f.size ∧ (f.size ≠ 0 → ∃ b blk, s.ptr = ⟨some b, 0⟩ ∧ m.blocks[b]? = some blk ∧
    blk.live ∧ blk.bytes = f.map .int ∧ blk.kind.mappedLo = 0)

theorem Holds.grow {a : AllocId} {m m' : Mem} {s : Slice} {f : Array (BitVec 8)}
    (h : Holds m s f) (hg : Grows a m m') : Holds m' s f := by
  refine ⟨h.1, fun hf => ?_⟩
  obtain ⟨b, blk, hp, hblk, hl, hbs⟩ := h.2 hf
  refine ⟨b, blk, hp, ?_, hl, hbs⟩
  rw [hg.old b (Array.getElem?_eq_some_iff.mp hblk).1, hblk]

/-- Each slice holds its field. -/
def HoldsAll (m : Mem) : List Slice → List (Array (BitVec 8)) → Prop
  | [], [] => True
  | s :: ss, f :: fs => Holds m s f ∧ HoldsAll m ss fs
  | _, _ => False

theorem HoldsAll.grow {a : AllocId} {m m' : Mem} {ss : List Slice} {fs : List (Array (BitVec 8))}
    (h : HoldsAll m ss fs) (hg : Grows a m m') : HoldsAll m' ss fs := by
  induction ss generalizing fs with
  | nil => cases fs <;> simp_all [HoldsAll]
  | cons s ss ih =>
    cases fs with
    | nil => simp [HoldsAll] at h
    | cons f fs => exact ⟨h.1.grow hg, ih h.2⟩

theorem Mem.Seq.write {m : Mem} (hst : m.Seq) {b : BlockId} {blk : Block} {o : Nat}
    {bs : Array Byte} (hblk : m.blocks[b]? = some blk) (hl : blk.live)
    (hn : o + bs.size ≤ blk.bytes.size) : (m.write b blk o bs).Seq := by
  refine ⟨hst.single, hst.addr.of_heap rfl fun l c hc => ?_⟩
  obtain ⟨c', hc', ha, hs⟩ := Mem.heap_write_cell hblk hn hc
  exact ⟨l, c', hc', ha, hs⟩

theorem byteSum_map (f : Array (BitVec 8)) :
    byteSum (f.map .int) = f.foldl (fun acc x => acc + x.toNat) 0 := by
  unfold byteSum; rw [Array.foldl_map]

/-! ## Steps -/

theorem dupeBytes_spec {m : Mem} {a : AllocId} {st : OwnedAlloc}
    (hs : m.allocators[a]? = some st) (hl : st.live) (hp : st.policy = .arena) (hst : m.Seq)
    (bs : Array (BitVec 8)) (hn : bs.size < 2 ^ 64) :
    ∃ r m', (dupeBytes (.owned a) bs).run m = pure (r, m') ∧ Grows a m m' ∧ m'.Seq ∧
      match r with
      | .error e => e = "OutOfMemory"
      | .ok s => Holds m' s bs := by
  have hlen : (BitVec.ofNat 64 bs.size).toNat = bs.size := by simp [Nat.mod_eq_of_lt hn]
  have hov : ¬ 18446744073709551616 ≤ bs.size := by omega
  have hmod : bs.size % 18446744073709551616 = bs.size := Nat.mod_eq_of_lt hn
  by_cases h0 : bs.size = 0
  · refine ⟨.ok ⟨zeroAllocPtr 1, BitVec.ofNat 64 bs.size⟩, m, ?_, Grows.refl a m, hst,
      by rw [hlen], fun h => absurd h0 h⟩
    simp [dupeBytes, AllocRef.alloc, ownedAllocBytes, h0, zig_unfold]
  · have hA := ownedRawAlloc_arena_run hs hl hp bs.size
    let m₁ : Mem := { m with allocs := m.allocs + 1 }
    have hst₁ : m₁.Seq := ⟨hst.single, hst.addr⟩
    have hg₁ : Grows a m m₁ := Grows.of_blocks rfl rfl
    by_cases hc : m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < bs.size ∨
        m.allocs ∈ m.allocPolicy.failures
    · simp only [hc, ↓reduceIte] at hA
      refine ⟨.error "OutOfMemory", m₁, ?_, hg₁, hst₁, rfl⟩
      simp only [StateT.run] at hA
      simp [dupeBytes, AllocRef.alloc, ownedAllocBytes, h0, hmod, hov, zig_unfold, hA, m₁]
    · simp only [hc, ↓reduceIte] at hA
      let B := m.blocks.size
      let m₂ := m₁.afterAlloc (.owned a) bs.size 1
      let nb : Block :=
        { bytes := Array.replicate bs.size .undef, align := 1, kind := .owned a, live := true,
          addr := m₁.newAddr (.owned a) bs.size 1 }
      have hblk₂ : m₂.blocks[B]? = some nb := by simp [m₂, Mem.afterAlloc, B, m₁, nb]
      have hacc : m₂.access ⟨some B, 0⟩ (bs.map Byte.int).size 1 = pure (B, nb, 0) := by
        simpa using access_of (p := ⟨some B, 0⟩) (n := (bs.map Byte.int).size) (a := 1) rfl hblk₂
          rfl (by simp) (by simp [nb]) (Nat.mod_one _)
      have hst₂ : m₂.Seq := hst₁.alloc _ _ _
      have hS := storeBytes_run (kind := .write) hacc (by simp [nb])
        (noRace_of_singleThread hst₂.single _ _ _ _)
      let m₃ := (m₂.recordAt B 0 (bs.map Byte.int).size .write).write B nb 0 (bs.map .int)
      have hblk₃ : m₃.blocks[B]? = some { nb with bytes := bs.map .int } := by
        have hlt : B < m₂.blocks.size := (Array.getElem?_eq_some_iff.mp hblk₂).1
        simp only [m₃, Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_self_of_lt hlt]
        simp [nb, writeBytes_all (a := Array.replicate bs.size .undef)]
      refine ⟨.ok ⟨⟨some B, 0⟩, BitVec.ofNat 64 bs.size⟩, m₃, ?_, ⟨?_, ?_, ?_, rfl⟩, ?_,
        hlen, fun _ => ⟨B, _, rfl, hblk₃, rfl, rfl, rfl⟩⟩
      · simp only [StateT.run] at hA hS
        simp [dupeBytes, AllocRef.alloc, ownedAllocBytes, h0, hmod, hov, zig_unfold, hA, hS, m₃, m₂, m₁, B]
      · simp [m₃, Mem.write, Mem.recordAt, m₂, Mem.afterAlloc, m₁]
      · intro b hb
        have hne : B ≠ b := by omega
        simp [m₃, Mem.write, Mem.recordAt, m₂, Mem.afterAlloc, m₁, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne hne, Array.getElem?_push, show b ≠ m.blocks.size by omega]
      · intro b blk hb h
        have hsz : m₃.blocks.size = m.blocks.size + 1 := by
          simp [m₃, Mem.write, Mem.recordAt, m₂, Mem.afterAlloc, m₁]
        have hbB : b = B := by
          have := (Array.getElem?_eq_some_iff.mp h).1; omega
        subst hbB
        rw [hblk₃] at h; cases h; rfl
      · exact (Mem.Seq.recordAt hst₂ B 0 _ .write).write
          (by simpa [Mem.recordAt] using hblk₂) rfl (by simp [nb])

theorem dupeAll_spec {a : AllocId} {st : OwnedAlloc} (hl : st.live) (hp : st.policy = .arena)
    (fs : List (Array (BitVec 8))) (hn : ∀ f ∈ fs, f.size < 2 ^ 64) (m : Mem)
    (hs : m.allocators[a]? = some st) (hst : m.Seq) :
    ∃ r m', (dupeAll (.owned a) fs).run m = pure (r, m') ∧ Grows a m m' ∧ m'.Seq ∧
      match r with
      | .error e => e = "OutOfMemory"
      | .ok ss => HoldsAll m' ss fs := by
  induction fs generalizing m with
  | nil => exact ⟨.ok [], m, rfl, Grows.refl a m, hst, trivial⟩
  | cons f fs ih =>
    obtain ⟨r, m₁, hr, hg₁, hst₁, hpost⟩ := dupeBytes_spec hs hl hp hst f (hn f (by simp))
    simp only [StateT.run] at hr
    cases r with
    | error e =>
      refine ⟨.error e, m₁, ?_, hg₁, hst₁, hpost⟩
      simp [dupeAll, zig_unfold, hr]
    | ok s =>
      have hs₁ : m₁.allocators[a]? = some st := by rw [hg₁.allocators]; exact hs
      obtain ⟨r₂, m₂, hr₂, hg₂, hst₂, hpost₂⟩ :=
        ih (fun f hf => hn f (by simp [hf])) m₁ hs₁ hst₁
      simp only [StateT.run] at hr₂
      cases r₂ with
      | error e =>
        refine ⟨.error e, m₂, ?_, hg₁.trans hg₂, hst₂, hpost₂⟩
        simp [dupeAll, zig_unfold, hr, hr₂]
      | ok ss =>
        refine ⟨.ok (s :: ss), m₂, ?_, hg₁.trans hg₂, hst₂, Holds.grow hpost hg₂, hpost₂⟩
        simp [dupeAll, zig_unfold, hr, hr₂]

theorem sumAll_spec (a : AllocId) (ss : List Slice) (fs : List (Array (BitVec 8))) (m : Mem)
    (h : HoldsAll m ss fs) (hst : m.Seq) :
    ∃ m', (sumAll ss).run m = pure (requestSum fs, m') ∧ Grows a m m' ∧ m'.Seq := by
  induction ss generalizing fs m with
  | nil =>
    cases fs with
    | nil => exact ⟨m, rfl, Grows.refl a m, hst⟩
    | cons => simp [HoldsAll] at h
  | cons s ss ih =>
    cases fs with
    | nil => simp [HoldsAll] at h
    | cons f fs => ?_
    obtain ⟨hh, htail⟩ := h
    -- The read of `s`.
    obtain ⟨bs, m₁, hr, hbs, hg₁, hst₁⟩ : ∃ bs m₁,
        (readBytes s).run m = pure (bs, m₁) ∧
        byteSum bs = f.foldl (fun acc x => acc + x.toNat) 0 ∧ Grows a m m₁ ∧ m₁.Seq := by
      by_cases h0 : s.len.toNat = 0
      · have hf : f = #[] := Array.eq_empty_of_size_eq_zero (by rw [← hh.1, h0])
        subst hf
        exact ⟨#[], m, by simp [readBytes, h0, zig_unfold], by simp [byteSum], Grows.refl a m, hst⟩
      · obtain ⟨b, blk, hpb, hblk, hl, hbytes, hblo⟩ := hh.2 (by rw [← hh.1]; exact h0)
        have hacc : m.access s.ptr s.len.toNat 1 = pure (b, blk, 0) := by
          rw [hpb]
          simpa using access_of (p := ⟨some b, 0⟩) (n := s.len.toNat) (a := 1) rfl hblk hl
            (by simp) (by simp [hbytes, hh.1]) (Nat.mod_one _) (by simp [hblo])
        have hL := loadBytes_run (kind := .read) hacc (noRace_of_singleThread hst.single _ _ _ _)
        refine ⟨f.map .int, m.recordAt b 0 s.len.toNat .read, ?_, byteSum_map f,
          Grows.of_blocks rfl rfl, hst.recordAt _ _ _ _⟩
        have hx : (f.map Byte.int).extract 0 (0 + f.size) = f.map Byte.int := by
          rw [Nat.zero_add, show f.size = (f.map Byte.int).size by simp, Array.extract_size]
        simp only [readBytes, h0, ↓reduceIte]
        rw [hL, hbytes, hh.1, hx]
    have hh' : HoldsAll m₁ ss fs := htail.grow hg₁
    obtain ⟨m₂, hr₂, hg₂, hst₂⟩ := ih fs m₁ hh' hst₁
    refine ⟨m₂, ?_, hg₁.trans hg₂, hst₂⟩
    rw [sumAll, StateT.run_bind, hr, pure_bind, StateT.run_bind, hr₂, pure_bind, StateT.run_pure]
    simp [requestSum, hbs]

theorem answer_spec {m : Mem} {a : AllocId} {st : OwnedAlloc}
    (hs : m.allocators[a]? = some st) (hl : st.live) (hp : st.policy = .arena) (hst : m.Seq)
    (fields : List (Array (BitVec 8))) (hn : ∀ f ∈ fields, f.size < 2 ^ 64) :
    ∃ r m', (answer a fields).run m = pure (r, m') ∧ RequestOutcome r fields ∧ Grows a m m' ∧
      m'.Seq := by
  obtain ⟨r₁, m₁, hr₁, hg₁, hst₁, hpost₁⟩ := dupeAll_spec hl hp fields hn m hs hst
  cases r₁ with
  | error e =>
    refine ⟨.error e, m₁, ?_, .inr (by rw [hpost₁]), hg₁, hst₁⟩
    rw [answer, StateT.run_bind, hr₁, pure_bind]
    rfl
  | ok ss =>
    obtain ⟨m₂, hr₂, hg₂, hst₂⟩ := sumAll_spec a ss fields m₁ hpost₁ hst₁
    refine ⟨.ok (requestSum fields), m₂, ?_, .inl rfl, hg₁.trans hg₂, hst₂⟩
    rw [answer, StateT.run_bind, hr₁, pure_bind]
    simp only [StateT.run_map, hr₂]
    rfl

/-- (M01) One request: one permitted outcome, nothing throws, and the arena's reset leaves
the heap without exactly the arena's blocks, whatever the failure policy. -/
theorem handleRequest_spec {m : Mem} {a : AllocId} {st : OwnedAlloc}
    (hs : m.allocators[a]? = some st) (hl : st.live) (hp : st.policy = .arena) (hst : m.Seq)
    (fields : List (Array (BitVec 8))) (hn : ∀ f ∈ fields, f.size < 2 ^ 64) :
    ∃ r m', (handleRequest a fields).run m = pure (r, m') ∧ RequestOutcome r fields ∧
      m'.heap = m.heap.dropOwned a ∧ m'.Seq ∧
      m'.allocators[a]? = some { st with used := 0, starts := [] } := by
  obtain ⟨r, m₁, hr, hout, hg, hst₁⟩ := answer_spec hs hl hp hst fields hn
  have hs₁ : m₁.allocators[a]? = some st := by rw [hg.allocators]; exact hs
  obtain ⟨hR, hheap, hstR, hsR⟩ := Owned.reset_spec hs₁ hl hst₁
  refine ⟨r, m₁.afterReset a st, ?_, hout, by rw [hheap, hg.dropOwned], hstR, hsR⟩
  rw [handleRequest, StateT.run_bind, hr, pure_bind, StateT.run_bind, hR, pure_bind,
    StateT.run_pure]

/-- One permitted outcome per request. -/
def Outcomes : List (Except ErrName Nat) → List (List (Array (BitVec 8))) → Prop
  | [], [] => True
  | r :: rs, req :: reqs => RequestOutcome r req ∧ Outcomes rs reqs
  | _, _ => False

theorem serve_spec {a : AllocId} (reqs : List (List (Array (BitVec 8))))
    (hn : ∀ req ∈ reqs, ∀ f ∈ req, f.size < 2 ^ 64) (m : Mem) (st : OwnedAlloc)
    (hs : m.allocators[a]? = some st) (hl : st.live) (hp : st.policy = .arena) (hst : m.Seq) :
    ∃ rs m' st', (serve a reqs).run m = pure (rs, m') ∧ Outcomes rs reqs ∧
      m'.heap.dropOwned a = m.heap.dropOwned a ∧ m'.Seq ∧ m'.allocators[a]? = some st' ∧
      st'.live ∧ st'.policy = .arena := by
  induction reqs generalizing m st with
  | nil => exact ⟨[], m, st, rfl, trivial, rfl, hst, hs, hl, hp⟩
  | cons req reqs ih =>
    obtain ⟨r, m₁, hr, hout, hheap, hst₁, hs₁⟩ :=
      handleRequest_spec hs hl hp hst req (hn req (by simp))
    obtain ⟨rs, m₂, st₂, hr₂, houts, hheap₂, hst₂, hs₂, hl₂, hp₂⟩ :=
      ih (fun r h => hn r (by simp [h])) m₁ _ hs₁ hl hp hst₁
    refine ⟨r :: rs, m₂, st₂, ?_, ⟨hout, houts⟩, ?_, hst₂, hs₂, hl₂, hp₂⟩
    · rw [serve, StateT.run_bind, hr, pure_bind, StateT.run_bind, hr₂, pure_bind, StateT.run_pure]
    · rw [hheap₂, hheap, Heap.dropOwned_idem]

/-- (M01, the production-style client) A session over any memory, any allocation-failure
policy and any requests: one permitted outcome per request, nothing throws, and the final
heap is the initial heap without the session arena's blocks. -/
theorem session_spec (reqs : List (List (Array (BitVec 8))))
    (hn : ∀ req ∈ reqs, ∀ f ∈ req, f.size < 2 ^ 64) (m : Mem) (hst : m.Seq) :
    ∃ rs m', (session reqs).run m = pure (rs, m') ∧ Outcomes rs reqs ∧
      m'.heap = m.heap.dropOwned m.allocators.size ∧ m'.Seq := by
  let a := m.allocators.size
  let m₀ : Mem := { m with allocators := m.allocators.push { policy := .arena } }
  have hs₀ : m₀.allocators[a]? = some { policy := .arena } := by simp [m₀, a]
  obtain ⟨rs, m₁, st₁, hr₁, houts, hheap₁, hst₁, hs₁, hl₁, -⟩ :=
    serve_spec reqs hn m₀ _ hs₀ rfl rfl ⟨hst.single, hst.addr⟩
  obtain ⟨m₂, hr₂, hheap₂, hst₂, -⟩ := Arena.deinit_spec hs₁ hl₁ hst₁
  refine ⟨rs, m₂, ?_, houts, ?_, hst₂⟩
  · rw [session, StateT.run_bind, Arena.init_run, pure_bind, StateT.run_bind, hr₁, pure_bind,
      StateT.run_bind, hr₂, pure_bind, StateT.run_pure]
  · rw [hheap₂, hheap₁]
    rfl

/-- (M01) When no block of `m` claims the session's new arena (any memory that the model's
operations reach from `{}`), a session restores the heap exactly. -/
theorem session_restores (reqs : List (List (Array (BitVec 8))))
    (hn : ∀ req ∈ reqs, ∀ f ∈ req, f.size < 2 ^ 64) (m : Mem) (hst : m.Seq)
    (hfresh : ∀ l c, m.heap l = some c → c.kind ≠ .owned m.allocators.size) :
    ∃ rs m', (session reqs).run m = pure (rs, m') ∧ Outcomes rs reqs ∧ m'.heap = m.heap ∧
      m'.Seq := by
  obtain ⟨rs, m', hr, houts, hheap, hst'⟩ := session_spec reqs hn m hst
  exact ⟨rs, m', hr, houts, hheap.trans (Heap.dropOwned_of_none hfresh), hst'⟩

end Zig
