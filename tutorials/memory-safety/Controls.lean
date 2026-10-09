import Proofs.Lists.Sep
import ZigLean.Sep.AddrReuse

/-!
# Refuted clients for the memory-safety tutorial

From the repository root (Lean accepts this file; `Negative.lean` is the control Lean must
reject):

    lake build Proofs.Lists.Sep
    lake env lean tutorials/memory-safety/Controls.lean

`Main.lean` proves that `buildThenFree` throws no `.illegal` and leaks nothing. These are the
same properties for three wrong clients of the generated `push`, `freeAll` and `sum`. Each
theorem proves the bug, so the properties of `Main.lean` are not vacuous:

* `doubleFree`: `freeAll` the node, then `destroy` it again: the second free throws `.illegal`;
* `useAfterFree`: `freeAll` the node, then `sum` the list: the read of `val` throws `.illegal`;
* `forgetFree`: allocate a node and never free it: the live heap grows, so the no-leak
  property of `Main.lean` is false.

Each holds whenever the allocation succeeds (`Room m`); `{}` (the default memory, no failure)
is such a memory, so the safety property of `Main.lean` is refuted for each client. The bugs
stay bugs under address reuse (`doubleFree_reuse`, `useAfterFree_reuse`): the stale node
pointer names the freed block, whatever block now has its address.
-/

namespace MemorySafety.Controls

open Zig Assn Lists

/-- `Main.lean`'s property: from every single-threaded memory, `c` returns (no `.illegal`) and
the live heap after it is exactly the live heap before it. -/
def SafeNoLeak {α : Type} (c : MemM α) : Prop :=
  ∀ m : Mem, m.Seq → ∃ r m', c.run m = pure (r, m') ∧ m'.heap = m.heap

/-- The next allocation of 16 bytes (`create(Node)`) succeeds under `m`'s policy: no legacy
index, cap or listed failure, and neither the failure oracle nor the budget denies it. -/
def Room (m : Mem) : Prop :=
  ¬(m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < 16 ∨ m.allocs ∈ m.allocPolicy.failures) ∧
    m.oracleDenies 16 = false

/-! ## The wrong clients -/

/-- `const n = try push(a, null, v); freeAll(a, n); a.destroy(n);` -/
def doubleFree (a : Allocator) (v : BitVec 32) : MemM (Except ErrName Unit) := do
  match ← push a none v with
  | .error e => pure (.error e)
  | .ok p => do freeAll a (some p); a.destroy 16 p; pure (.ok ())

/-- `const n = try push(a, null, v); freeAll(a, n); return sum(n);` -/
def useAfterFree (a : Allocator) (v : BitVec 32) : MemM (Except ErrName (BitVec 64)) := do
  match ← push a none v with
  | .error e => pure (.error e)
  | .ok p => do freeAll a (some p); let s ← sum (some p); pure (.ok s)

/-- `_ = try push(a, null, v);`: `Main.lean`'s client for one item, without the free. -/
def forgetFree (a : Allocator) (v : BitVec 32) : MemM (Except ErrName Unit) := do
  match ← push a none v with
  | .error e => pure (.error e)
  | .ok _ => pure (.ok ())

/-! ## Lemmas -/

/-- With room for the allocation, `create(Node)` succeeds. -/
theorem create_ok (a : Allocator) {m : Mem} (hc : Room m) :
    ∃ p m', (a.create 16 8).run m = pure (.ok p, m') := by
  obtain ⟨hc, ho⟩ := hc
  simp only [not_or] at hc
  simp [Allocator.create, allocBytes, rawAlloc, alloc, zig_unfold, hc, ho, set, StateT.set,
    MonadStateOf.set, StateT.get]
  exact ⟨_, _, rfl⟩

/-- With room for the allocation, `push` returns a new node in a new part of the heap. -/
theorem push_ok (a : Allocator) (q : Option Ptr) (v : BitVec 32) {m : Mem} (hs : m.Seq)
    (hc : Room m) :
    ∃ p m₁ h₁, (push a q v).run m = pure (.ok p, m₁) ∧ Heap.Disjoint h₁ m.heap ∧
      m₁.heap = h₁ ∪ m.heap ∧ node p v q h₁ ∧ m₁.Seq := by
  obtain ⟨p', m', hok⟩ := create_ok a hc
  have hd : Heap.Disjoint Heap.empty m.heap := (Heap.disjoint_empty _).symm
  obtain ⟨r, m₁, h₁, hcr, hd₁, hm₁, -, hst₁, hnew⟩ :=
    create_run hd (by simp) a 16 8 (by decide) (by decide) hs
  rw [hok] at hcr
  cases hcr
  simp only [Heap.empty_union] at hd₁ hm₁
  obtain ⟨h0, A, hA, hb⟩ := hnew
  obtain ⟨m₂, hs₁, hst₂, h₂, hd₂, hm₂, hb₂⟩ := bytesAt_store (q := p'.add 8) (k := 8) (a := 4)
    (bs' := Enc.encode v) hb hm₁ hd₁ (by simp) (by rw [enc_val_size]; decide)
    (by rw [enc_val_size]; simp) (by simp [h0]; omega) hst₁ (by decide)
  have hw : (writeBytes (Array.replicate 16 Byte.undef) 8 (Enc.encode v)).size = 16 := by
    rw [writeBytes_size _ _ _ (by rw [enc_val_size]; simp)]; simp
  obtain ⟨m₃, hs₂, hst₃, h₃, hd₃, hm₃, hb₃⟩ := bytesAt_store (q := p'.add 0) (k := 0) (a := 8)
    (bs' := Enc.encode q) hb₂ hm₂ hd₂ (by simp) (by rw [enc_next_size]; decide)
    (by rw [enc_next_size, hw]; decide) (by simp [h0]; omega) hst₂ (by decide)
  rw [nodeBytes_new] at hb₃
  refine ⟨p', m₃, h₃, ?_, hd₃, hm₃, ⟨h0, A, hA, hb₃⟩, hst₃⟩
  simp only [StateT.run] at hs₁ hs₂ hok
  simp [push, zig_unfold, hok, Zig.store, hs₁, hs₂]

/-- A node owns its 16 bytes. -/
theorem node_cell {p : Ptr} {v : BitVec 32} {q : Option Ptr} {h : Heap} (hn : node p v q h) :
    ∃ b, p.block = some b ∧ ∀ o < 16, h (b, o) ≠ none := by
  obtain ⟨h0, A, -, b, hpb, -, hcell⟩ := hn
  refine ⟨b, hpb, fun o ho => ?_⟩
  rw [hcell]
  simp [h0, nodeBytes_size, ho]

/-- An access whose first byte is not live throws `.illegal`. -/
theorem access_dead {m : Mem} {p : Ptr} {b : BlockId} {n a : Nat} (hb : p.block = some b)
    (h0 : 0 ≤ p.off) (hn : 0 < n) (hh : m.heap (b, p.off.toNat) = none) :
    m.access p n a = throw .illegal := by
  unfold Mem.access
  simp only [hb]
  cases hblk : m.blocks[b]? with
  | none => rfl
  | some blk =>
    simp only
    by_cases hc : blk.live = true ∧ 0 ≤ p.off ∧ p.off + n ≤ blk.bytes.size ∧
        (blk.addr + p.off.toNat) % a = 0 ∧ blk.kind.mappedLo ≤ p.off.toNat
    · exfalso
      simp only [Mem.heap, hblk] at hh
      simp [hc.1, hc.2.2.2.2, show p.off.toNat < blk.bytes.size by omega] at hh
    · simp only [hc, ↓reduceIte]

/-- After `push` then `freeAll`, the node's 16 bytes are dead. -/
theorem push_free (a : Allocator) (v : BitVec 32) {m : Mem} (hs : m.Seq) (hc : Room m) :
    ∃ p b m₁ m₂, (push a none v).run m = pure (.ok p, m₁) ∧
      (freeAll a (some p)).run m₁ = pure ((), m₂) ∧ p.block = some b ∧ p.off = 0 ∧
      (∀ o < 16, m₂.heap (b, o) = none) ∧ m₂.Seq := by
  obtain ⟨p, m₁, h₁, hpush, hd₁, hm₁, hnode, hs₁⟩ := push_ok a none v hs hc
  have hl : list (some p) [v] h₁ :=
    ⟨p, none, rfl, h₁, Heap.empty, Heap.disjoint_empty _, by simp, hnode, rfl, rfl⟩
  obtain ⟨u, m₂, h₂, hfree, -, hm₂, rfl, hs₂⟩ :=
    freeAll_total a (some p) [v] m₁ h₁ m.heap hd₁ hm₁ hl hs₁
  obtain ⟨b, hpb, hcell⟩ := node_cell hnode
  refine ⟨p, b, m₁, m₂, hpush, hfree, hpb, hnode.1, fun o ho => ?_, hs₂⟩
  rw [hm₂, Heap.empty_union]
  exact (hd₁ (b, o)).resolve_left (hcell o ho)

/-- A loop whose first iteration throws throws. -/
theorem loop_throw {σ ε : Type} (body : MM σ ε) (again : ε → Bool) (s : σ) (m : Mem) (e : Error)
    (h : (body.run s).run m = throw e) : ((Zig.loop body again).run s).run m = throw e := by
  rw [loopMM_run, h]
  rfl

/-! ## The controls -/

/-- Double free: the second free of the node throws `.illegal`. -/
theorem doubleFree_illegal (a : Allocator) (v : BitVec 32) {m : Mem} (hs : m.Seq) (hc : Room m) :
    (doubleFree a v).run m = throw .illegal := by
  obtain ⟨p, b, m₁, m₂, hpush, hfree, hpb, h0, hdead, -⟩ := push_free a v hs hc
  have hacc : m₂.access p 16 1 = throw .illegal :=
    access_dead hpb (by simp [h0]) (by decide) (by simpa [h0] using hdead 0 (by decide))
  have hdes : (a.destroy 16 p).run m₂ = throw .illegal := by
    simp [Allocator.destroy, rawFree, zig_unfold, hacc]
  simp only [StateT.run] at hpush hfree hdes
  simp [doubleFree, zig_unfold, hpush, hfree, hdes]

/-- Use after free: `sum` reads the freed node's `val` and throws `.illegal`. -/
theorem useAfterFree_illegal (a : Allocator) (v : BitVec 32) {m : Mem} (hs : m.Seq)
    (hc : Room m) : (useAfterFree a v).run m = throw .illegal := by
  obtain ⟨p, b, m₁, m₂, hpush, hfree, hpb, h0, hdead, -⟩ := push_free a v hs hc
  have hacc : m₂.access (p.add 8) (Enc.size (BitVec 32)) 4 = throw .illegal :=
    access_dead (by simpa [Ptr.add] using hpb) (by simp [Ptr.add, h0]) (by decide)
      (by simpa [Ptr.add, h0] using hdead 8 (by decide))
  have hloop : ∀ s : sumLocals, s.p = some p →
      ((Zig.loop sum.loop6 sum.again6).run s).run m₂ = throw .illegal := by
    intro s hsp
    apply loop_throw
    simp [sum.loop6, zig_unfold, hsp, Zig.optPayload, Zig.load, loadBytes, hacc]
  simp only [StateT.run] at hpush hfree hloop
  simp [useAfterFree, sum, zig_unfold, hpush, hfree, hloop]

/-- A missing free: the node stays live, so the heap after the run is not the heap before. -/
theorem forgetFree_leaks (a : Allocator) (v : BitVec 32) {m : Mem} (hs : m.Seq) (hc : Room m) :
    ∃ m', (forgetFree a v).run m = pure (.ok (), m') ∧ m'.heap ≠ m.heap := by
  obtain ⟨p, m₁, h₁, hpush, hd₁, hm₁, hnode, -⟩ := push_ok a none v hs hc
  obtain ⟨b, -, hcell⟩ := node_cell hnode
  refine ⟨m₁, ?_, fun he => hcell 0 (by decide) ?_⟩
  · simp only [StateT.run] at hpush
    simp [forgetFree, zig_unfold, hpush]
  · have hl := congrFun (hm₁.symm.trans he) (b, 0)
    have hn := (hd₁ (b, 0)).resolve_left (hcell 0 (by decide))
    simpa [Heap.union, hn] using hl

/-- Address reuse (M05) does not hide either bug: with any reuse oracle and provenance mode,
the stale pointer still throws `.illegal`. -/
theorem doubleFree_reuse (a : Allocator) (v : BitVec 32) {m : Mem} (hs : m.Seq) (hc : Room m)
    (pick : BlockId → Option Nat) (pm : ProvenanceMode) :
    (doubleFree a v).run (m.withReuse pick pm) = throw .illegal :=
  doubleFree_illegal a v (hs.withReuse pick pm) hc

theorem useAfterFree_reuse (a : Allocator) (v : BitVec 32) {m : Mem} (hs : m.Seq) (hc : Room m)
    (pick : BlockId → Option Nat) (pm : ProvenanceMode) :
    (useAfterFree a v).run (m.withReuse pick pm) = throw .illegal :=
  useAfterFree_illegal a v (hs.withReuse pick pm) hc

/-- The default memory (`{}`: one thread, no allocation fails) has room for a node. -/
theorem default_seq : ({} : Mem).Seq :=
  ⟨⟨by decide, by simp⟩, fun l c h => by simp [Mem.heap] at h⟩

theorem default_room : Room {} := by unfold Room; decide

/-- None of the three clients has `Main.lean`'s property. -/
theorem doubleFree_unsafe (a : Allocator) (v : BitVec 32) : ¬SafeNoLeak (doubleFree a v) := by
  intro h
  obtain ⟨r, m', hr, -⟩ := h {} default_seq
  rw [doubleFree_illegal a v default_seq default_room] at hr
  cases hr

theorem useAfterFree_unsafe (a : Allocator) (v : BitVec 32) : ¬SafeNoLeak (useAfterFree a v) := by
  intro h
  obtain ⟨r, m', hr, -⟩ := h {} default_seq
  rw [useAfterFree_illegal a v default_seq default_room] at hr
  cases hr

theorem forgetFree_unsafe (a : Allocator) (v : BitVec 32) : ¬SafeNoLeak (forgetFree a v) := by
  intro h
  obtain ⟨r, m', hr, hh⟩ := h {} default_seq
  obtain ⟨m'', hr', hne⟩ := forgetFree_leaks a v default_seq default_room
  rw [hr'] at hr
  cases hr
  exact hne hh

end MemorySafety.Controls
