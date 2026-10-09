import ZigLean.Sep.Alloc
import ZigLean.Sep.Loop

/-!
# Model cost: allocation counters and counted loops

A qualified cost layer over the existing semantics. It adds no state to `Mem` and changes no
generated code; each count is read off a run that the semantics already defines.

* Allocation events: `Mem.allocs`, the allocator's own count of `rawAlloc` requests
  (successful or failed).
* Retained allocations: `Mem.liveHeap`, the number of live `.heap` blocks.
* Loop steps: `LoopRuns body again s m k e s' m'`, a run of `loop body again` with exactly `k`
  body runs (each repeat and the final exit). `LoopRuns.run` turns it into the loop's run;
  `LoopRuns.unique` makes `k` a function of the start, so a proved count is exact.

The instrumentation lemmas (`store_cost`, `load_cost`, `create_cost`, `destroy_cost`) hold for
every successful run of a primitive, from any memory. `loopRuns_exact` and `loopRuns_bound`
are `loopMM_ghost` with the count.

These are counts in the model. A body run, a load or an allocation request has no time or
byte cost here, and nothing relates a count to measured CPU time, cache behavior or a native
allocator's memory use. Such a claim needs a separate calibration argument
(`docs/proof-tools.md`, premise SEM-05).
-/

namespace Zig

/-! ## Retained allocations -/

/-- A live block of kind `.heap`: an allocator block that nothing has freed yet. -/
def Block.retained (blk : Block) : Bool := blk.live && blk.kind == .heap

/-- The number of retained allocator blocks of `m`. -/
def Mem.liveHeap (m : Mem) : Nat := m.blocks.toList.countP Block.retained

private theorem countP_set_same {α : Type} (p : α → Bool) (l : List α) (i : Nat) (a : α)
    (h : ∀ x, l[i]? = some x → p a = p x) : (l.set i a).countP p = l.countP p := by
  induction l generalizing i with
  | nil => simp
  | cons y ys ih =>
    cases i with
    | zero => simp at h; simp [List.countP_cons, h]
    | succ i => simp [List.countP_cons, ih i (by simpa using h)]

private theorem countP_set_drop {α : Type} (p : α → Bool) (l : List α) (i : Nat) (a x : α)
    (hx : l[i]? = some x) (hpx : p x = true) (hpa : p a = false) :
    (l.set i a).countP p + 1 = l.countP p := by
  induction l generalizing i with
  | nil => simp at hx
  | cons y ys ih =>
    cases i with
    | zero => simp at hx; subst hx; simp [hpx, hpa]
    | succ i =>
      have := ih i (by simpa using hx)
      simp only [List.set_cons_succ, List.countP_cons]
      omega

theorem Mem.liveHeap_set (m : Mem) {b : BlockId} {blk : Block} (x : Block)
    (hb : m.blocks[b]? = some blk) (hx : x.retained = blk.retained) :
    ({ m with blocks := m.blocks.set! b x } : Mem).liveHeap = m.liveHeap := by
  unfold Mem.liveHeap
  simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  apply countP_set_same
  intro y hy
  rw [Array.getElem?_toList, hb] at hy
  cases hy; exact hx

theorem Mem.liveHeap_kill (m : Mem) {b : BlockId} {blk : Block} (x : Block)
    (hb : m.blocks[b]? = some blk) (hblk : blk.retained = true) (hx : x.retained = false) :
    ({ m with blocks := m.blocks.set! b x } : Mem).liveHeap + 1 = m.liveHeap := by
  unfold Mem.liveHeap
  simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  exact countP_set_drop _ _ _ _ blk (by rw [Array.getElem?_toList, hb]) hblk hx

/-- `m'` has the allocation count and the retained blocks of `m`. -/
structure Mem.SameAllocs (m m' : Mem) : Prop where
  allocs : m'.allocs = m.allocs
  liveHeap : m'.liveHeap = m.liveHeap

theorem Mem.SameAllocs.refl (m : Mem) : m.SameAllocs m := ⟨rfl, rfl⟩

theorem Mem.SameAllocs.trans {m₁ m₂ m₃ : Mem} (h₁ : m₁.SameAllocs m₂) (h₂ : m₂.SameAllocs m₃) :
    m₁.SameAllocs m₃ := ⟨h₂.allocs.trans h₁.allocs, h₂.liveHeap.trans h₁.liveHeap⟩

/-! ## Instrumentation lemmas: every successful run of a primitive -/

private theorem access_ok_of_accessW {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block}
    {o : Nat} (hw : m.accessW p n a = some (.ok (b, blk, o))) :
    m.access p n a = pure (b, blk, o) ∧ blk.kind ≠ .constGlobal := by
  unfold Mem.accessW at hw
  cases ha : m.access p n a with
  | none => simp [ha, zig_unfold] at hw
  | some r => cases r with
    | error e => simp [ha, zig_unfold] at hw; cases hw
    | ok r =>
      simp [ha, zig_unfold] at hw
      split at hw
      · cases hw
      · rename_i hk; cases hw; exact ⟨rfl, hk⟩

/-- A store never allocates or frees. -/
theorem storeBytes_cost {p : Ptr} {a : Nat} {bs : Array Byte} {kind : AccessKind} {m m' : Mem}
    {u : Unit} (h : (storeBytes p a bs kind).run m = pure (u, m')) : m.SameAllocs m' := by
  cases hw : m.accessW p bs.size a with
  | none => simp [storeBytes, zig_unfold, hw] at h
  | some r =>
    cases r with
    | error e => simp [storeBytes, zig_unfold, hw] at h; cases h
    | ok r =>
      obtain ⟨b, blk, o⟩ := r
      obtain ⟨hacc, hK⟩ := access_ok_of_accessW hw
      obtain ⟨-, hblk, -⟩ := access_eq hacc
      by_cases hnr : NoRace m b o bs.size kind
      · rw [storeBytes_run hacc hK hnr] at h
        simp only [pure, ExceptT.pure, ExceptT.mk] at h
        cases h
        exact ⟨rfl, Mem.liveHeap_set (m.recordAt b o bs.size kind) _ hblk rfl⟩
      · unfold NoRace at hnr
        obtain ⟨err, herr⟩ := Option.ne_none_iff_exists'.mp hnr
        simp [storeBytes, recordAccess, zig_unfold, hw, herr] at h; cases h

theorem store_cost {α : Type} [Enc α] {a : Nat} {p : Ptr} {v : α} {m m' : Mem} {u : Unit}
    (h : (store a p v).run m = pure (u, m')) : m.SameAllocs m' := storeBytes_cost h

/-- A load never allocates or frees. -/
theorem load_cost {α : Type} [Enc α] {a : Nat} {p : Ptr} {v : α} {m m' : Mem}
    (h : (load α a p).run m = pure (v, m')) : m.SameAllocs m' := by
  cases ha : m.access p (Enc.size α) a with
  | none => simp [load, loadBytes, zig_unfold, ha] at h
  | some r =>
    cases r with
    | error e => simp [load, loadBytes, zig_unfold, ha] at h; cases h
    | ok r =>
      obtain ⟨b, blk, o⟩ := r
      by_cases hnr : NoRace m b o (Enc.size α) .read
      · simp only [load, StateT.run_bind, loadBytes_run ha hnr] at h
        cases hd : (Enc.decode (blk.bytes.extract o (o + Enc.size α)) : Result α) with
        | none => simp [zig_unfold, hd] at h
        | some r => cases r with
          | error e => simp [zig_unfold, hd] at h; cases h
          | ok w => simp [zig_unfold, hd] at h; cases h; exact ⟨rfl, rfl⟩
      · unfold NoRace at hnr
        obtain ⟨err, herr⟩ := Option.ne_none_iff_exists'.mp hnr
        simp [load, loadBytes, recordAccess, zig_unfold, ha, herr] at h; cases h

/-- The number of blocks a successful allocation result adds: one, or none for an error. -/
def allocated {α : Type} : Except ErrName α → Nat
  | .ok _ => 1
  | .error _ => 0

/-- `create` of `size > 0` bytes is one allocation event. It retains exactly one new block on
success and none on `error.OutOfMemory`. -/
theorem create_cost {a : Allocator} {size align : Nat} {m m' : Mem} {r : Except ErrName Ptr}
    (hs : 0 < size) (h : (a.create size align).run m = pure (r, m')) :
    m'.allocs = m.allocs + 1 ∧ m'.liveHeap = m.liveHeap + allocated r := by
  have hns : ¬ size = 0 := by omega
  by_cases hc : m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < size ∨
      m.allocs ∈ m.allocPolicy.failures
  · simp [Allocator.create, allocBytes, rawAlloc, hns, hc, zig_unfold, set, StateT.set,
      MonadStateOf.set] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  by_cases ho : m.oracleDenies size = true
  · simp [Allocator.create, allocBytes, rawAlloc, hns, hc, ho, zig_unfold, set, StateT.set,
      MonadStateOf.set] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · simp [Allocator.create, allocBytes, rawAlloc, alloc, hns, hc, ho, zig_unfold, set, StateT.set,
      MonadStateOf.set] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [Mem.liveHeap, List.countP_append, Block.retained, allocated]⟩

/-- `destroy` of `size > 0` bytes frees exactly one retained block and is no allocation
event. -/
theorem destroy_cost {a : Allocator} {size : Nat} {p : Ptr} {m m' : Mem} {u : Unit}
    (hs : 0 < size) (h : (a.destroy size p).run m = pure (u, m')) :
    m'.allocs = m.allocs ∧ m'.liveHeap + 1 = m.liveHeap := by
  have hns : ¬ size = 0 := by omega
  simp only [Allocator.destroy, hns, ↓reduceIte] at h
  cases ha : m.access p size 1 with
  | none => simp [rawFree, zig_unfold, ha] at h
  | some r =>
    cases r with
    | error e => simp [rawFree, zig_unfold, ha] at h; cases h
    | ok r =>
      obtain ⟨b, blk, o⟩ := r
      obtain ⟨hpb, hblk, hl, h0, -, -, rfl⟩ := access_eq ha
      by_cases hc : blk.kind = .heap ∧ p.off.toNat = 0 ∧ blk.bytes.size = size
      · have hp0 : p.off = 0 := by omega
        cases hfr : m.freeRaces b size
        · simp [rawFree, free, zig_unfold, ha, hc, hpb, hblk, hl, hp0, hfr, set, StateT.set,
            MonadStateOf.set] at h
          obtain ⟨-, rfl⟩ := h
          exact ⟨rfl, Mem.liveHeap_kill m _ hblk (by simp [Block.retained, hl, hc.1])
            (by simp [Block.retained])⟩
        · simp [rawFree, free, zig_unfold, ha, hc, hpb, hblk, hl, hp0, hfr, StateT.lift] at h
          cases h
      · unfold rawFree at h
        simp only [zig_unfold, ha] at h
        rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
        simp [StateT.lift, zig_unfold] at h; cases h

/-! ## Counted loops -/

/-- `LoopRuns body again s m k e s' m'`: the loop `loop body again` from the locals `s` and the
memory `m` runs its body exactly `k` times (every repeat and the final exit) and ends with the
exit `e`, the locals `s'` and the memory `m'`. -/
inductive LoopRuns {σ ε : Type} (body : MM σ ε) (again : ε → Bool) :
    σ → Mem → Nat → ε → σ → Mem → Prop
  | exit {s m e s' m'} : (body.run s).run m = pure ((e, s'), m') → again e = false →
      LoopRuns body again s m 1 e s' m'
  | next {s m e₁ s₁ m₁ k e s' m'} : (body.run s).run m = pure ((e₁, s₁), m₁) → again e₁ = true →
      LoopRuns body again s₁ m₁ k e s' m' → LoopRuns body again s m (k + 1) e s' m'

namespace LoopRuns

variable {σ ε : Type} {body : MM σ ε} {again : ε → Bool}

/-- The counted run is the run of the loop. -/
theorem run {s : σ} {m : Mem} {k : Nat} {e : ε} {s' : σ} {m' : Mem}
    (h : LoopRuns body again s m k e s' m') :
    ((loop body again).run s).run m = pure ((e, s'), m') := by
  induction h with
  | exit hb ha =>
    rw [loopMM_run]
    simp [hb, ha, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure]
  | next hb ha _ ih =>
    rw [loopMM_run]
    simp [hb, ha, ih, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure]

/-- The count is a function of the start: the body is deterministic. -/
theorem unique {s : σ} {m : Mem} {k₁ k₂ : Nat} {e₁ e₂ : ε} {s₁ s₂ : σ} {m₁ m₂ : Mem}
    (h₁ : LoopRuns body again s m k₁ e₁ s₁ m₁) (h₂ : LoopRuns body again s m k₂ e₂ s₂ m₂) :
    k₁ = k₂ ∧ e₁ = e₂ ∧ s₁ = s₂ ∧ m₁ = m₂ := by
  induction h₁ generalizing k₂ with
  | exit hb ha =>
    cases h₂ with
    | exit hb' ha' =>
      rw [hb] at hb'; simp only [pure, ExceptT.pure, ExceptT.mk] at hb'; cases hb'
      exact ⟨rfl, rfl, rfl, rfl⟩
    | next hb' ha' _ =>
      rw [hb] at hb'; simp only [pure, ExceptT.pure, ExceptT.mk] at hb'; cases hb'
      rw [ha] at ha'; cases ha'
  | next hb ha _ ih =>
    cases h₂ with
    | exit hb' ha' =>
      rw [hb] at hb'; simp only [pure, ExceptT.pure, ExceptT.mk] at hb'; cases hb'
      rw [ha] at ha'; cases ha'
    | next hb' ha' h' =>
      rw [hb] at hb'; simp only [pure, ExceptT.pure, ExceptT.mk] at hb'; cases hb'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih h'
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem pos {s : σ} {m : Mem} {k : Nat} {e : ε} {s' : σ} {m' : Mem}
    (h : LoopRuns body again s m k e s' m') : 0 < k := by
  cases h <;> omega

end LoopRuns

/-- An exact count: a ghost number `n` that each repeat lowers by exactly one and that is `0`
at the exit. The loop runs its body `n + 1` times. -/
theorem loopRuns_exact {σ ε : Type} (body : MM σ ε) (again : ε → Bool)
    (inv : σ → Mem → Nat → Prop) (post : ε → σ → Mem → Prop)
    (step : ∀ s m n, inv s m n → ∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
      (if again e then ∃ n', n = n' + 1 ∧ inv s' m' n' else n = 0 ∧ post e s' m')) :
    ∀ s m n, inv s m n → ∃ e s' m', LoopRuns body again s m (n + 1) e s' m' ∧ post e s' m' := by
  intro s m n
  induction n generalizing s m with
  | zero =>
    intro hi
    obtain ⟨e, s', m', hr, hn⟩ := step s m 0 hi
    cases ha : again e
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hn
      exact ⟨e, s', m', .exit hr ha, hn.2⟩
    · simp only [ha, ↓reduceIte] at hn
      obtain ⟨n', h0, -⟩ := hn; omega
  | succ n ih =>
    intro hi
    obtain ⟨e, s', m', hr, hn⟩ := step s m (n + 1) hi
    cases ha : again e
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hn; omega
    · simp only [ha, ↓reduceIte] at hn
      obtain ⟨n', hnn, hi'⟩ := hn
      obtain rfl : n' = n := by omega
      obtain ⟨e₂, s₂, m₂, hl, hp⟩ := ih s' m' hi'
      exact ⟨e₂, s₂, m₂, .next hr ha hl, hp⟩

/-- A bound: `loopMM_ghost`'s decreasing ghost number `n` bounds the count by `n + 1`. -/
theorem loopRuns_bound {σ ε : Type} (body : MM σ ε) (again : ε → Bool)
    (inv : σ → Mem → Nat → Prop) (post : ε → σ → Mem → Prop)
    (step : ∀ s m n, inv s m n → ∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
      (if again e then ∃ n' < n, inv s' m' n' else post e s' m')) :
    ∀ s m n, inv s m n → ∃ k e s' m', k ≤ n + 1 ∧ LoopRuns body again s m k e s' m' ∧
      post e s' m' := by
  intro s m n
  induction n using Nat.strongRecOn generalizing s m with
  | _ n ih =>
    intro hi
    obtain ⟨e, s', m', hr, hn⟩ := step s m n hi
    cases ha : again e
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hn
      exact ⟨1, e, s', m', by omega, .exit hr ha, hn⟩
    · simp only [ha, ↓reduceIte] at hn
      obtain ⟨n', hlt, hi'⟩ := hn
      obtain ⟨k, e₂, s₂, m₂, hk, hl, hp⟩ := ih n' hlt s' m' hi'
      exact ⟨k + 1, e₂, s₂, m₂, by omega, .next hr ha hl, hp⟩

end Zig
