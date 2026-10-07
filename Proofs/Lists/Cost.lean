import Proofs.Lists.Sep
import Proofs.Lists.Append
import ZigLean.Sep.Cost

/-!
# Resource bounds for `examples/lists/lists.zig` (P06)

Allocation and loop-step counts (`ZigLean/Sep/Cost.lean`) for the generated list code. The
counts are model counts: `Mem.allocs` allocation requests, `Mem.liveHeap` retained heap blocks
and `LoopRuns` body runs. They say nothing about CPU time or native memory use.

* (a) Retained allocations. `push_cost`: one allocation request; one more retained block on
  success, none on `error.OutOfMemory`. `pushAll_cost`: after `n` successful pushes, exactly
  `n` more requests and `n` more retained blocks. `freeAll_cost`: freeing a list of `n` nodes
  releases exactly `n` retained blocks and allocates nothing.
* (b) Operation bound. `sum_cost`: `sum` over `n` items runs its loop body exactly `n + 1`
  times (`sum_count_unique`), allocates nothing and returns the sum. `freeAll_cost` has the
  same exact count.
* (c) Capacity premises. `sum_count_capacity`: under `n ≤ C` the loop body runs at most
  `C + 1` times. `pushAll_capacity`: with at most `C` items, at most `C` requests and `C` new
  retained blocks. `append_capacity`: `ArrayListUnmanaged(u32).append` with spare capacity
  (`xs.length < cap`) makes no allocation request and retains no new block.
-/

namespace Lists
open Zig Assn

/-- (a) `push` is one allocation request; it retains one new block on success and none on
`error.OutOfMemory`. -/
theorem push_cost (a : Allocator) (q : Option Ptr) (v : BitVec 32) {m : Mem} (hst : m.Seq) :
    ∃ r m', (push a q v).run m = pure (r, m') ∧ m'.Seq ∧ m'.allocs = m.allocs + 1 ∧
      m'.liveHeap = m.liveHeap + allocated r := by
  have hd : Heap.Disjoint Heap.empty m.heap := (Heap.disjoint_empty _).symm
  have hm : m.heap = Heap.empty ∪ m.heap := by simp
  obtain ⟨r, m₁, h₁, hc, hd₁, hm₁, -, hst₁, hnew⟩ :=
    create_run hd hm a 16 8 (by decide) (by decide) hst
  obtain ⟨ha₁, hl₁⟩ := create_cost (by decide) hc
  simp only [Heap.empty_union] at hd₁ hm₁
  simp only [StateT.run] at hc
  cases r with
  | error e =>
    refine ⟨.error e, m₁, ?_, hst₁, ha₁, hl₁⟩
    simp [push, zig_unfold, hc, Zig.unwrapErr]
  | ok p =>
    obtain ⟨h0, A, hA, hb⟩ := hnew
    obtain ⟨m₂, hs₁, hst₂, h₂, hd₂, hm₂, hb₂⟩ := bytesAt_store (q := p.add 8) (k := 8) (a := 4)
      (bs' := Enc.encode v) hb hm₁ hd₁ (by simp) (by rw [enc_val_size]; decide)
      (by rw [enc_val_size]; simp) (by simp [h0]; omega) hst₁ (by decide)
    have hw : (writeBytes (Array.replicate 16 Byte.undef) 8 (Enc.encode v)).size = 16 := by
      rw [writeBytes_size _ _ _ (by rw [enc_val_size]; simp)]; simp
    obtain ⟨m₃, hs₂, hst₃, -, -, -, -⟩ := bytesAt_store (q := p.add 0) (k := 0) (a := 8)
      (bs' := Enc.encode q) hb₂ hm₂ hd₂ (by simp) (by rw [enc_next_size]; decide)
      (by rw [enc_next_size, hw]; decide) (by simp [h0]; omega) hst₂ (by decide)
    have c₂ := storeBytes_cost hs₁
    have c₃ := storeBytes_cost hs₂
    refine ⟨.ok p, m₃, ?_, hst₃, by rw [c₃.allocs, c₂.allocs, ha₁],
      by rw [c₃.liveHeap, c₂.liveHeap, hl₁]⟩
    simp only [StateT.run] at hs₁ hs₂
    simp [push, zig_unfold, hc, Zig.store, hs₁, hs₂]

/-- Every successful run of `push` from a sequential memory has `push_cost`'s cost. -/
theorem push_cost_of_run {a : Allocator} {q : Option Ptr} {v : BitVec 32} {m m' : Mem}
    {r : Except ErrName Ptr} (hst : m.Seq) (h : (push a q v).run m = pure (r, m')) :
    m'.allocs = m.allocs + 1 ∧ m'.liveHeap = m.liveHeap + allocated r := by
  obtain ⟨r₀, m₀, h₀, -, ha, hl⟩ := push_cost a q v hst
  rw [h₀] at h; simp only [pure, ExceptT.pure, ExceptT.mk] at h; cases h
  exact ⟨ha, hl⟩

/-- A client that pushes `vs` one at a time with the generated `push` and stops at the first
error. -/
def pushAll (a : Allocator) : Option Ptr → List (BitVec 32) → MemM (Except ErrName (Option Ptr))
  | hd, [] => pure (.ok hd)
  | hd, v :: vs => do
    match ← push a hd v with
    | .ok p => pushAll a (some p) vs
    | .error e => pure (.error e)

/-- (a) `pushAll` makes at most one request and retains at most one block per item; on
success, exactly one of each. -/
theorem pushAll_cost (a : Allocator) (hd : Option Ptr) (vs : List (BitVec 32)) {m : Mem}
    (hst : m.Seq) :
    ∃ r m', (pushAll a hd vs).run m = pure (r, m') ∧ m'.Seq ∧
      m'.allocs ≤ m.allocs + vs.length ∧ m'.liveHeap ≤ m.liveHeap + vs.length ∧
      (∀ hd', r = .ok hd' → m'.allocs = m.allocs + vs.length ∧
        m'.liveHeap = m.liveHeap + vs.length) := by
  induction vs generalizing hd m with
  | nil =>
    refine ⟨.ok hd, m, rfl, hst, by simp, by simp, fun _ _ => by simp⟩
  | cons v vs ih =>
    obtain ⟨r, m₁, hp, hst₁, ha₁, hl₁⟩ := push_cost a hd v hst
    simp only [StateT.run] at hp
    cases r with
    | error e =>
      refine ⟨.error e, m₁, ?_, hst₁, by simp [ha₁], by simp [hl₁, allocated],
        fun _ h => by cases h⟩
      simp [pushAll, zig_unfold, hp]
    | ok p =>
      obtain ⟨r', m', hr, hst', ha, hl, hok⟩ := ih (some p) hst₁
      refine ⟨r', m', ?_, hst', by simp [ha₁] at ha; simp; omega,
        by simp [hl₁, allocated] at hl; simp; omega, fun hd' h => ?_⟩
      · simp only [StateT.run] at hr
        simp [pushAll, zig_unfold, hp, hr]
      · obtain ⟨e1, e2⟩ := hok hd' h
        simp [ha₁, hl₁, allocated] at e1 e2; simp; omega

/-- (c) The capacity form: with at most `C` items to push, the client retains at most `C` new
blocks and makes at most `C` allocation requests. -/
theorem pushAll_capacity (a : Allocator) (hd : Option Ptr) (vs : List (BitVec 32)) (C : Nat)
    (hC : vs.length ≤ C) {m : Mem} (hst : m.Seq) :
    ∃ r m', (pushAll a hd vs).run m = pure (r, m') ∧
      m'.allocs ≤ m.allocs + C ∧ m'.liveHeap ≤ m.liveHeap + C := by
  obtain ⟨r, m', hr, -, ha, hl, -⟩ := pushAll_cost a hd vs hst
  exact ⟨r, m', hr, by omega, by omega⟩

/-- The invariant of `sum`'s loop: the memory is the start memory `m₀` (bytes, allocations),
`p` is a list of `n` items in a part `h` of it, and `s` plus their sum is `total`. -/
def sumInv (m₀ : Mem) (total : Nat) (s : sumLocals) (m : Mem) (n : Nat) : Prop :=
  m.heap = m₀.heap ∧ m.Seq ∧ m₀.SameAllocs m ∧
    ∃ zs h hG, zs.length = n ∧ Heap.Disjoint h hG ∧ m₀.heap = h ∪ hG ∧ list s.p zs h ∧
      s.s.toNat + (zs.map BitVec.toNat).sum = total

/-- One body run of `sum`'s loop: a node lowers the ghost count by one. -/
theorem sum_count_step (m₀ : Mem) (total : Nat) (htot : total < 2 ^ 64) (s : sumLocals) (m : Mem)
    (n : Nat) (hi : sumInv m₀ total s m n) :
    ∃ e s' m', (sum.loop6.run s).run m = pure ((e, s'), m') ∧
      (if sum.again6 e then ∃ n', n = n' + 1 ∧ sumInv m₀ total s' m' n'
       else n = 0 ∧ (e = .br5 ∧ s'.s.toNat = total ∧ m'.heap = m₀.heap ∧ m'.Seq ∧
         m₀.SameAllocs m')) := by
  obtain ⟨hH, hst, hc, zs, h, hG, hn, d, hm0, hl, hsum⟩ := hi
  cases zs with
  | nil =>
    obtain ⟨hp, rfl⟩ := hl
    refine ⟨.br5, s, m, by simp [sum.loop6, zig_unfold, hp], ?_⟩
    simp only [sum.again6, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by simpa using hn.symm, trivial, by simpa using hsum, hH, hst, hc⟩
  | cons z zs =>
    obtain ⟨p, q, hp, hn₁, hr, dnr, rfl, hnode, hrest⟩ := hl
    have hm : m.heap = hn₁ ∪ (hr ∪ hG) := by rw [hH, hm0, Heap.union_assoc]
    obtain ⟨mA, hv, hmA, hstA⟩ := node_val_run hnode hm hst
    obtain ⟨mB, hq, hmB, hstB⟩ := node_next_run hnode hmA hstA
    have cA := load_cost hv
    have cB := load_cost hq
    have hz := z.isLt
    have hno : ¬ (18446744073709551616 ≤ s.s.toNat + z.toNat % 18446744073709551616) := by
      simp only [List.map_cons, List.sum_cons] at hsum
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    refine ⟨.rep6, { s with s := s.s + z.setWidth 64, p := q }, mB, ?_, ?_⟩
    · simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hv hq
      simp [sum.loop6, zig_unfold, hp, Zig.optPayload, hv, hq, hno]
    · simp only [sum.again6, ↓reduceIte]
      obtain ⟨-, dGr⟩ := Heap.disjoint_union_left.mp d
      refine ⟨zs.length, by simpa using hn.symm, by rw [hmB, ← hm, hH], hstB,
        hc.trans (cA.trans cB), zs, hr, hn₁ ∪ hG, rfl,
        Heap.disjoint_union_right.mpr ⟨dnr.symm, dGr⟩,
        by rw [hm0, Heap.union_comm dnr, Heap.union_assoc], hrest, ?_⟩
      simp only [List.map_cons, List.sum_cons] at hsum
      rw [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (a := z.toNat) (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega

/-- The locals at the start of `sum`'s loop. -/
abbrev sumStart (hd : Option Ptr) : sumLocals := { (default : sumLocals) with s := 0, p := hd }

/-- (b) `sum` over a list of `xs.length` items runs its loop body exactly `xs.length + 1` times
(one per node and the final null test), returns the sum, and neither allocates nor frees. -/
theorem sum_cost (hd : Option Ptr) (xs : List (BitVec 32)) {m : Mem} {h hF : Heap}
    (hl : list hd xs h) (hm : m.heap = h ∪ hF) (hdj : Heap.Disjoint h hF) (hst : m.Seq)
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) :
    ∃ s' m', LoopRuns sum.loop6 sum.again6 (sumStart hd) m (xs.length + 1) .br5 s' m' ∧
      (sum hd).run m = pure (BitVec.ofNat 64 (xs.map BitVec.toNat).sum, m') ∧
      m.SameAllocs m' ∧ m'.heap = m.heap ∧ m'.Seq := by
  obtain ⟨e, s', m', hrun, he, hs, hH, hst', hc⟩ :=
    loopRuns_exact sum.loop6 sum.again6 (sumInv m (xs.map BitVec.toNat).sum)
      (fun e s m' => e = .br5 ∧ s.s.toNat = (xs.map BitVec.toNat).sum ∧ m'.heap = m.heap ∧
        m'.Seq ∧ m.SameAllocs m')
      (sum_count_step m _ htot) (sumStart hd) m xs.length
      ⟨rfl, hst, .refl m, xs, h, hF, rfl, hdj, hm, hl, by simp⟩
  subst he
  have hv : s'.s = BitVec.ofNat 64 (xs.map BitVec.toNat).sum := by
    apply BitVec.eq_of_toNat_eq; rw [hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htot]
  refine ⟨s', m', hrun, ?_, hc, hH, hst'⟩
  have hr := hrun.run
  simp only [StateT.run, sumStart] at hr
  simp only [BitVec.ofNat_eq_ofNat] at hr
  simp [sum, zig_unfold, hr, hv]

/-- The count is exact: every counted run of `sum`'s loop from the same start has
`xs.length + 1` body runs. -/
theorem sum_count_unique (hd : Option Ptr) (xs : List (BitVec 32)) {m : Mem} {h hF : Heap}
    (hl : list hd xs h) (hm : m.heap = h ∪ hF) (hdj : Heap.Disjoint h hF) (hst : m.Seq)
    (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) {k : Nat} {e : sumExit} {s' : sumLocals}
    {m' : Mem} (hk : LoopRuns sum.loop6 sum.again6 (sumStart hd) m k e s' m') :
    k = xs.length + 1 := by
  obtain ⟨_, _, h₀, -⟩ := sum_cost hd xs hl hm hdj hst htot
  exact (hk.unique h₀).1

/-- (c) The capacity form: under the premise `xs.length ≤ C`, `sum`'s loop runs its body at
most `C + 1` times. -/
theorem sum_count_capacity (hd : Option Ptr) (xs : List (BitVec 32)) (C : Nat)
    (hC : xs.length ≤ C) {m : Mem} {h hF : Heap} (hl : list hd xs h) (hm : m.heap = h ∪ hF)
    (hdj : Heap.Disjoint h hF) (hst : m.Seq) (htot : (xs.map BitVec.toNat).sum < 2 ^ 64)
    {k : Nat} {e : sumExit} {s' : sumLocals} {m' : Mem}
    (hk : LoopRuns sum.loop6 sum.again6 (sumStart hd) m k e s' m') : k ≤ C + 1 := by
  have := sum_count_unique hd xs hl hm hdj hst htot hk
  omega

/-- The invariant of `freeAll`'s loop: `p` is a list of `n` items in the owned part `h`, and
`N - n` blocks are freed so far. -/
def freeCostInv (m₀ : Mem) (N : Nat) (hF : Heap) (s : freeAllLocals) (m : Mem) (n : Nat) : Prop :=
  m.Seq ∧ m.allocs = m₀.allocs ∧ m.liveHeap + N = m₀.liveHeap + n ∧
    ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ ∃ zs, zs.length = n ∧ list s.p zs h

/-- One body run of `freeAll`'s loop: a node lowers the ghost count by one and frees one
block. -/
theorem freeAll_count_step (a : Allocator) (m₀ : Mem) (N : Nat) (hF : Heap) (s : freeAllLocals)
    (m : Mem) (n : Nat) (hi : freeCostInv m₀ N hF s m n) :
    ∃ e s' m', ((freeAll.loop5 a).run s).run m = pure ((e, s'), m') ∧
      (if freeAll.again5 e then ∃ n', n = n' + 1 ∧ freeCostInv m₀ N hF s' m' n'
       else n = 0 ∧ (e = .br4 ∧ m'.Seq ∧ m'.allocs = m₀.allocs ∧ m'.liveHeap + N = m₀.liveHeap ∧
         m'.heap = hF)) := by
  obtain ⟨hst, ha, hl0, h, hd, hm, zs, hn, hl⟩ := hi
  cases zs with
  | nil =>
    obtain ⟨hp, rfl⟩ := hl
    refine ⟨.br4, s, m, by simp [freeAll.loop5, zig_unfold, hp], ?_⟩
    simp only [freeAll.again5, Bool.false_eq_true, ↓reduceIte]
    simp only [List.length_nil] at hn; subst hn
    exact ⟨rfl, trivial, hst, ha, by simpa using hl0, by simpa using hm⟩
  | cons z zs =>
    obtain ⟨p, q, hp, hn₁, hr, d, rfl, hnode, hrest⟩ := hl
    obtain ⟨dnF, drF⟩ := Heap.disjoint_union_left.mp hd
    have hm' : m.heap = hn₁ ∪ (hr ∪ hF) := by rw [hm, Heap.union_assoc]
    have dN : Heap.Disjoint hn₁ (hr ∪ hF) := Heap.disjoint_union_right.mpr ⟨d, dnF⟩
    obtain ⟨mA, hq, hmA, hstA⟩ := node_next_run hnode hm' hst
    obtain ⟨m', hf, hm'', hst'⟩ := node_free_run hnode hmA dN hstA a
    have cA := load_cost hq
    obtain ⟨ca, cl⟩ := destroy_cost (by decide) hf
    refine ⟨.rep5, { s with p := q }, m', ?_, ?_⟩
    · simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hq hf
      simp [freeAll.loop5, zig_unfold, hp, Zig.optPayload, hq, hf]
    · simp only [freeAll.again5, ↓reduceIte]
      simp only [List.length_cons] at hn
      refine ⟨zs.length, by omega, hst', by rw [ca, cA.allocs, ha],
        by rw [cA.liveHeap] at cl; omega,
        hr, drF, by simpa using hm'', zs, rfl, hrest⟩

/-- (a, b) `freeAll` over a list of `xs.length` nodes runs its loop body exactly
`xs.length + 1` times, frees exactly `xs.length` retained blocks, allocates nothing, and leaves
the frame. -/
theorem freeAll_cost (a : Allocator) (hd : Option Ptr) (xs : List (BitVec 32)) {m : Mem}
    {h hF : Heap} (hl : list hd xs h) (hm : m.heap = h ∪ hF) (hdj : Heap.Disjoint h hF)
    (hst : m.Seq) :
    ∃ s' m', LoopRuns (freeAll.loop5 a) freeAll.again5 { (default : freeAllLocals) with p := hd } m
        (xs.length + 1) .br4 s' m' ∧ (freeAll a hd).run m = pure ((), m') ∧
      m'.allocs = m.allocs ∧ m'.liveHeap + xs.length = m.liveHeap ∧ m'.heap = hF ∧ m'.Seq := by
  obtain ⟨e, s', m', hrun, he, hst', ha, hl', hH⟩ :=
    loopRuns_exact (freeAll.loop5 a) freeAll.again5 (freeCostInv m xs.length hF)
      (fun e _ m' => e = .br4 ∧ m'.Seq ∧ m'.allocs = m.allocs ∧
        m'.liveHeap + xs.length = m.liveHeap ∧ m'.heap = hF)
      (freeAll_count_step a m xs.length hF) { (default : freeAllLocals) with p := hd } m xs.length
      ⟨hst, rfl, rfl, h, hdj, hm, xs, rfl, hl⟩
  subst he
  refine ⟨s', m', hrun, ?_, ha, hl', hH, hst'⟩
  have hr := hrun.run
  simp only [StateT.run] at hr
  simp [freeAll, zig_unfold, hr]

/-- (c) `ArrayListUnmanaged(u32).append` under the capacity premise `xs.length < cap`: no
allocation request and no new retained block, whatever the allocator policy. -/
theorem append_capacity (a : Allocator) (v : BitVec 32) {p ptr : Ptr} {cap : BitVec 64}
    {xs : List (BitVec 32)} {m : Mem} {hL hF : Heap} (hl : alist p ptr cap xs hL)
    (hm : m.heap = hL ∪ hF) (hd : Heap.Disjoint hL hF) (hst : m.Seq) (hok : ptrOk m ptr)
    (hroom : xs.length < cap.toNat) :
    ∃ r m', (array_list_Aligned_u32_null_append p a v).run m = pure (r, m') ∧
      m'.allocs = m.allocs ∧ m'.liveHeap = m.liveHeap ∧
      ∃ hL', Heap.Disjoint hL' hF ∧ m'.heap = hL' ∪ hF ∧ Appended p ptr cap xs v m' hL' r := by
  obtain ⟨r, m', hr, -, hc, hpost⟩ := append_cost_run a v hl hm hd hst hok
  exact ⟨r, m', hr, (hc hroom).allocs, (hc hroom).liveHeap, hpost⟩

end Lists
