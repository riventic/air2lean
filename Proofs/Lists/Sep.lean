import Proofs.Lists.Gen
import ZigLean.Sep

/-!
# Separation-logic proofs about `examples/lists/lists.zig`

A node (`node p v q`) is a heap block of 16 bytes from `create(Node)`: `next` at offset 0, `val`
at offset 8, 4 bytes of padding. `list hd xs`: the nodes from `hd` hold the items `xs`.

* `push_spec`: `push` gives a new node, or `error.OutOfMemory` and no bytes.
* `reverse_spec`: `reverse` turns the list into the list of the items in the other order.
* `freeAll_spec`: after `freeAll`, the function owns no bytes: every node is freed.
-/

namespace Lists
open Zig Assn

/-- The bytes of a node. -/
def nodeBytes (v : BitVec 32) (next : Option Ptr) : Array Byte :=
  Enc.encode next ++ Enc.encode v ++ Array.replicate 4 .undef

theorem enc_next_size (q : Option Ptr) : (Enc.encode q).size = 8 := LawfulEnc.size_encode q
theorem enc_val_size (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v
theorem enc_next_empty (q : Option Ptr) : (Enc.encode q).extract 8 8 = #[] := by simp; omega
theorem enc_val_all (v : BitVec 32) : (Enc.encode v).extract 0 4 = Enc.encode v := by
  rw [show (4 : Nat) = (Enc.encode v).size from (enc_val_size v).symm]; exact Array.extract_size

theorem nodeBytes_size (v : BitVec 32) (q : Option Ptr) : (nodeBytes v q).size = 16 := by
  simp [nodeBytes, enc_next_size, enc_val_size]

/-- The bytes of `next` and of `val`, a store of `next`, and the bytes after `push`'s stores. -/
theorem nodeBytes_next (v : BitVec 32) (q : Option Ptr) :
    (nodeBytes v q).extract 0 (0 + 8) = Enc.encode q := by
  simp [nodeBytes, Array.extract_append, enc_next_size, enc_val_size]

theorem nodeBytes_val (v : BitVec 32) (q : Option Ptr) :
    (nodeBytes v q).extract 8 (8 + 4) = Enc.encode v := by
  simp [nodeBytes, Array.extract_append, enc_next_size, enc_val_size, enc_next_empty, enc_val_all]

theorem nodeBytes_set_next (v : BitVec 32) (q q' : Option Ptr) :
    writeBytes (nodeBytes v q) 0 (Enc.encode q') = nodeBytes v q' := by
  simp [writeBytes, nodeBytes, Array.extract_append, enc_next_size, enc_val_size, enc_next_empty,
    enc_val_all]

theorem nodeBytes_new (v : BitVec 32) (q : Option Ptr) :
    writeBytes (writeBytes (Array.replicate 16 .undef) 8 (Enc.encode v)) 0 (Enc.encode q) =
      nodeBytes v q := by
  simp [writeBytes, nodeBytes, Array.extract_append, enc_next_size, enc_val_size, enc_val_all]

/-- A node at `p`: a heap block of 16 bytes (`create(Node)`), `next` at offset 0, `val` at 8. -/
def node (p : Ptr) (v : BitVec 32) (q : Option Ptr) : Assn := fun h =>
  p.off = 0 ∧ ∃ A, A % 8 = 0 ∧ bytesAt p A 16 .heap (nodeBytes v q) h

section Node
variable {m : Mem} {h hF : Heap} {p : Ptr} {v : BitVec 32} {q : Option Ptr}

/-- The operations on a node that the list functions run: a load of `next` and of `val`, a store
of `next`, and `destroy`. -/
theorem node_next_run (hn : node p v q h) (hm : m.heap = h ∪ hF) :
    (load (Option Ptr) 8 (p.add 0)).run m = pure (q, m) := by
  obtain ⟨h0, A, hA, hb⟩ := hn
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ := bytesAt_access (q := p.add 0) (k := 0) (n := 8) (a := 8)
    hb hm (by simp) (by decide) (by rw [nodeBytes_size]; decide) (by simp [h0]; omega)
  simp only [h0, Int.toNat_zero, Nat.zero_add] at hacc hx
  apply load_run (o := 0) hacc
  rw [show Enc.size (Option Ptr) = 8 from rfl, hx, nodeBytes_next]; exact LawfulEnc.decode_encode q

theorem node_val_run (hn : node p v q h) (hm : m.heap = h ∪ hF) :
    (load (BitVec 32) 4 (p.add 8)).run m = pure (v, m) := by
  obtain ⟨h0, A, hA, hb⟩ := hn
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ := bytesAt_access (q := p.add 8) (k := 8) (n := 4) (a := 4)
    hb hm (by simp) (by decide) (by rw [nodeBytes_size]; decide) (by simp [h0]; omega)
  simp only [h0, Int.toNat_zero, Nat.zero_add] at hacc hx
  apply load_run (o := 8) hacc
  rw [show Enc.size (BitVec 32) = 4 from rfl, hx, nodeBytes_val]; exact LawfulEnc.decode_encode v

theorem node_set_next_run (hn : node p v q h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (q' : Option Ptr) :
    ∃ m', (store 8 (p.add 0) q').run m = pure ((), m') ∧
      ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ node p v q' h' := by
  obtain ⟨h0, A, hA, hb⟩ := hn
  obtain ⟨m', hr, h', hd', hm', hb'⟩ := bytesAt_store (q := p.add 0) (k := 0) (a := 8)
    (bs' := Enc.encode q') hb hm hd (by simp) (by rw [enc_next_size]; decide)
    (by rw [enc_next_size, nodeBytes_size]; decide) (by simp [h0]; omega)
  rw [nodeBytes_set_next] at hb'
  exact ⟨m', hr, h', hd', hm', h0, A, hA, hb'⟩

theorem node_free_run (hn : node p v q h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (a : Allocator) :
    ∃ m', (a.destroy 16 p).run m = pure ((), m') ∧ m'.heap = Heap.empty ∪ hF := by
  obtain ⟨h0, A, -, hb⟩ := hn
  obtain ⟨m', hr, hm'⟩ := rawFree_run hb hm hd (nodeBytes_size v q) h0 (by decide)
  exact ⟨m', by simpa [Allocator.destroy] using hr, hm'⟩

end Node

/-- The list at `hd` has the items `xs`. -/
def list (hd : Option Ptr) : List (BitVec 32) → Assn
  | [] => ⌜hd = none⌝
  | v :: vs => fun h => ∃ p q, hd = some p ∧ (node p v q ∗ list q vs) h

/-- The middle part `h₂` of `h₁ ∪ (h₂ ∪ h₃)`, with the rest and the frame as its frame. -/
theorem focus_mid {h₁ h₂ h₃ hF : Heap} (d12 : Heap.Disjoint h₁ (h₂ ∪ h₃)) (d23 : Heap.Disjoint h₂ h₃)
    (dF : Heap.Disjoint (h₁ ∪ (h₂ ∪ h₃)) hF) :
    (h₁ ∪ (h₂ ∪ h₃)) ∪ hF = h₂ ∪ ((h₁ ∪ h₃) ∪ hF) ∧ Heap.Disjoint h₂ ((h₁ ∪ h₃) ∪ hF) := by
  obtain ⟨d12', -⟩ := Heap.disjoint_union_right.mp d12
  obtain ⟨-, d23F⟩ := Heap.disjoint_union_left.mp dF
  obtain ⟨d2F, -⟩ := Heap.disjoint_union_left.mp d23F
  refine ⟨?_, Heap.disjoint_union_right.mpr ⟨Heap.disjoint_union_right.mpr ⟨d12'.symm, d23⟩, d2F⟩⟩
  simp only [Heap.union_assoc]
  exact Heap.union_left_comm d12'

/-- The invariant of `reverse`: `prev` has the first items of `xs`, reversed, and `cur` the
rest, `n` items. -/
def revInv (xs : List (BitVec 32)) (s : reverseLocals) (n : Nat) : Assn := fun h =>
  ∃ ys zs, xs = ys.reverse ++ zs ∧ zs.length = n ∧ (list s.prev ys ∗ list s.cur zs) h

theorem reverse_step (xs : List (BitVec 32)) (hF : Heap) (s : reverseLocals) (n : Nat) (m : Mem)
    (h : Heap) (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF) (hi : revInv xs s n h) :
    ∃ e s' m' h', (reverse.loop6.run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
      m'.heap = h' ∪ hF ∧
      (if reverse.again6 e then ∃ n' < n, revInv xs s' n' h'
       else e = .br5 ∧ list s'.prev xs.reverse h') := by
  obtain ⟨ys, zs, hxs, hn, h₁, h₂, d12, rfl, hl₁, hl₂⟩ := hi
  cases zs with
  | nil =>
    obtain ⟨hcur, rfl⟩ := hl₂
    refine ⟨.br5, s, m, h₁ ∪ Heap.empty, ?_, hd, hm, ?_⟩
    · simp [reverse.loop6, zig_unfold, hcur]
    · simp only [reverse.again6, Bool.false_eq_true, ↓reduceIte, true_and, Heap.union_empty]
      simpa [hxs] using hl₁
  | cons z zs =>
    obtain ⟨p, q, hcur, hn₂, hr, d2, rfl, hnode, hrest⟩ := hl₂
    obtain ⟨hm', dN⟩ := focus_mid d12 d2 hd
    replace hm' := hm.trans hm'
    have hl := node_next_run hnode hm'
    obtain ⟨m₁, hs, hn', dN', hm₁, hnode'⟩ := node_set_next_run hnode hm' dN s.prev
    simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hl hs
    obtain ⟨-, d1r⟩ := Heap.disjoint_union_right.mp d12
    obtain ⟨dn'1r, dn'F⟩ := Heap.disjoint_union_right.mp dN'
    obtain ⟨dn'1, dn'r⟩ := Heap.disjoint_union_right.mp dn'1r
    obtain ⟨d1F, d2rF⟩ := Heap.disjoint_union_left.mp hd
    obtain ⟨-, drF⟩ := Heap.disjoint_union_left.mp d2rF
    refine ⟨.rep6, { s with cur := q, prev := some p }, m₁, (hn' ∪ h₁) ∪ hr, ?_, ?_, ?_, ?_⟩
    · simp [reverse.loop6, zig_unfold, hcur, Zig.optPayload, hl, hs]
    · exact Heap.disjoint_union_left.mpr ⟨Heap.disjoint_union_left.mpr ⟨dn'F, d1F⟩, drF⟩
    · rw [hm₁]; simp only [Heap.union_assoc]
    · simp only [reverse.again6, ↓reduceIte]
      refine ⟨zs.length, by simp at hn; omega, z :: ys, zs, by simp [hxs], rfl,
        hn' ∪ h₁, hr, Heap.disjoint_union_left.mpr ⟨dn'r, d1r⟩, rfl,
        ⟨p, s.prev, rfl, hn', h₁, dn'1, rfl, hnode', hl₁⟩, hrest⟩

/-- `reverse` turns the list at `hd` into the list of the items in the other order. -/
theorem reverse_spec (hd : Option Ptr) (xs : List (BitVec 32)) :
    Triple (list hd xs) (reverse hd) (fun r => list r xs.reverse) := by
  apply Triple.of_run
  intro m hP hF hdj hm hl
  obtain ⟨e, s', m', h', hr, hd', hm', he, hpost⟩ :=
    loop_sep_ghost reverse.loop6 reverse.again6 (revInv xs)
      (fun e s h => e = .br5 ∧ list s.prev xs.reverse h) hF
      (fun s n m h hd hm hi => reverse_step xs hF s n m h hd hm hi)
      { (default : reverseLocals) with prev := none, cur := hd } xs.length m hP hdj hm
      ⟨[], xs, by simp, rfl, Heap.empty, hP, (Heap.disjoint_empty hP).symm, by simp, ⟨rfl, rfl⟩, hl⟩
  refine ⟨s'.prev, m', h', ?_, hd', hm', hpost⟩
  simp only [StateT.run] at hr
  simp [reverse, zig_unfold, hr, he]

/-- What `push` returns: a new node in front of `q`, or `error.OutOfMemory` and no bytes. -/
def pushed (v : BitVec 32) (q : Option Ptr) : Except ErrName Ptr → Assn
  | .ok p => node p v q
  | .error e => ⌜e = "OutOfMemory"⌝

theorem push_spec (a : Allocator) (q : Option Ptr) (v : BitVec 32) :
    Triple emp (push a q v) (pushed v q) := by
  apply Triple.of_run
  intro m hP hF hd hm hp
  have hP0 : hP = Heap.empty := hp
  subst hP0
  obtain ⟨r, m₁, h₁, hc, hd₁, hm₁, -, hnew⟩ := create_run hd hm a 16 8 (by decide) (by decide)
  simp only [Heap.empty_union] at hd₁ hm₁
  simp only [StateT.run] at hc
  cases r with
  | error e =>
    obtain ⟨rfl, rfl⟩ := hnew
    refine ⟨.error "OutOfMemory", m₁, Heap.empty, ?_, hd₁, hm₁, rfl, rfl⟩
    simp [push, zig_unfold, hc, Zig.unwrapErr]
  | ok p =>
    obtain ⟨h0, A, hA, hb⟩ := hnew
    obtain ⟨m₂, hs₁, h₂, hd₂, hm₂, hb₂⟩ := bytesAt_store (q := p.add 8) (k := 8) (a := 4)
      (bs' := Enc.encode v) hb hm₁ hd₁ (by simp) (by rw [enc_val_size]; decide)
      (by rw [enc_val_size]; simp) (by simp [h0]; omega)
    have hw : (writeBytes (Array.replicate 16 Byte.undef) 8 (Enc.encode v)).size = 16 := by
      rw [writeBytes_size _ _ _ (by rw [enc_val_size]; simp)]; simp
    obtain ⟨m₃, hs₂, h₃, hd₃, hm₃, hb₃⟩ := bytesAt_store (q := p.add 0) (k := 0) (a := 8)
      (bs' := Enc.encode q) hb₂ hm₂ hd₂ (by simp) (by rw [enc_next_size]; decide)
      (by rw [enc_next_size, hw]; decide) (by simp [h0]; omega)
    rw [nodeBytes_new] at hb₃
    refine ⟨.ok p, m₃, h₃, ?_, hd₃, hm₃, h0, A, hA, hb₃⟩
    simp only [StateT.run] at hs₁ hs₂
    simp [push, zig_unfold, hc, Zig.store, hs₁, hs₂]

/-- The invariant of `freeAll`: `p` is a list of `n` items. -/
def freeInv (s : freeAllLocals) (n : Nat) : Assn := fun h => ∃ zs, zs.length = n ∧ list s.p zs h

theorem freeAll_step (a : Allocator) (hF : Heap) (s : freeAllLocals) (n : Nat) (m : Mem) (h : Heap)
    (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF) (hi : freeInv s n h) :
    ∃ e s' m' h', ((freeAll.loop5 a).run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
      m'.heap = h' ∪ hF ∧
      (if freeAll.again5 e then ∃ n' < n, freeInv s' n' h' else e = .br4 ∧ emp h') := by
  obtain ⟨zs, hn, hl⟩ := hi
  cases zs with
  | nil =>
    obtain ⟨hp, rfl⟩ := hl
    refine ⟨.br4, s, m, Heap.empty, ?_, hd, hm, ?_⟩
    · simp [freeAll.loop5, zig_unfold, hp]
    · simp [freeAll.again5, emp]
  | cons z zs =>
    obtain ⟨p, q, hp, hn₁, hr, d, rfl, hnode, hrest⟩ := hl
    obtain ⟨dnF, drF⟩ := Heap.disjoint_union_left.mp hd
    have hm' : m.heap = hn₁ ∪ (hr ∪ hF) := by rw [hm, Heap.union_assoc]
    have dN : Heap.Disjoint hn₁ (hr ∪ hF) := Heap.disjoint_union_right.mpr ⟨d, dnF⟩
    have hl := node_next_run hnode hm'
    obtain ⟨m', hf, hm''⟩ := node_free_run hnode hm' dN a
    simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hl hf
    refine ⟨.rep5, { s with p := q }, m', hr, ?_, drF, by simpa using hm'', ?_⟩
    · simp [freeAll.loop5, zig_unfold, hp, Zig.optPayload, hl, hf]
    · simp only [freeAll.again5, ↓reduceIte]
      exact ⟨zs.length, by simp at hn; omega, zs, rfl, hrest⟩

/-- `freeAll` frees every node of the list: after it, the function owns no bytes. -/
theorem freeAll_spec (a : Allocator) (hd : Option Ptr) (xs : List (BitVec 32)) :
    Triple (list hd xs) (freeAll a hd) (fun _ => emp) := by
  apply Triple.of_run
  intro m hP hF hdj hm hl
  obtain ⟨e, s', m', h', hr, hd', hm', he, hpost⟩ :=
    loop_sep_ghost (freeAll.loop5 a) freeAll.again5 freeInv (fun e _ h => e = .br4 ∧ emp h) hF
      (fun s n m h hd hm hi => freeAll_step a hF s n m h hd hm hi)
      { (default : freeAllLocals) with p := hd } xs.length m hP hdj hm ⟨xs, rfl, hl⟩
  refine ⟨(), m', h', ?_, hd', hm', hpost⟩
  simp only [StateT.run] at hr
  simp [freeAll, zig_unfold, hr, he]

end Lists
