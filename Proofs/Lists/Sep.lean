import Proofs.Lists.Gen
import ZigLean.Sep
import ZigLean.Sep.Total
import ZigLean.Sep.Step

/-!
# Separation-logic proofs about `examples/lists/lists.zig`

A node (`node p v q`) is a heap block of 16 bytes from `create(Node)`: `next` at offset 0, `val`
at offset 8, 4 bytes of padding. `list hd xs`: the nodes from `hd` hold the items `xs`.

* `push_spec`: `push` gives a new node, or `error.OutOfMemory` and no bytes.
* `reverse_spec`: `reverse` turns the list into the list of the items in the other order.
* `freeAll_spec`: after `freeAll`, the function owns no bytes: every node is freed.

Each is the partial form (`Triple.toPartial`) of a total one (`push_total`, `reverse_total`,
`freeAll_total`): the run returns, so a client can compose them into a total triple
(`tutorials/memory-safety`). The loop steps `reverse_step` and `freeAll_step` execute the
generated bodies with the `sep_*` tactics of `ZigLean.Sep.Step` and the node triples
`node_next_total`, `node_set_next_total` and `node_free_total`.
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
theorem node_next_run (hn : node p v q h) (hm : m.heap = h ∪ hF) (hst : m.Seq) :
    ∃ m', (load (Option Ptr) 8 (p.add 0)).run m = pure (q, m') ∧ m'.heap = h ∪ hF ∧
      m'.Seq := by
  obtain ⟨h0, A, hA, hb⟩ := hn
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ := bytesAt_access (q := p.add 0) (k := 0) (n := 8) (a := 8)
    hb hm (by simp) (by decide) (by rw [nodeBytes_size]; decide) (by simp [h0]; omega)
  simp only [h0, Int.toNat_zero, Nat.zero_add] at hacc hx
  have hv' : Enc.decode (blk.bytes.extract 0 (0 + Enc.size (Option Ptr))) = pure q := by
    rw [show Enc.size (Option Ptr) = 8 from rfl, hx, nodeBytes_next]; exact LawfulEnc.decode_encode q
  refine ⟨_, load_run hacc hv' (noRace_of_singleThread hst.single _ _ _ _), ?_, ?_⟩
  · funext l; rw [Mem.heap_recordAt]; exact congrFun hm l
  · exact hst.recordAt _ _ _ _

theorem node_val_run (hn : node p v q h) (hm : m.heap = h ∪ hF) (hst : m.Seq) :
    ∃ m', (load (BitVec 32) 4 (p.add 8)).run m = pure (v, m') ∧ m'.heap = h ∪ hF ∧
      m'.Seq := by
  obtain ⟨h0, A, hA, hb⟩ := hn
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ := bytesAt_access (q := p.add 8) (k := 8) (n := 4) (a := 4)
    hb hm (by simp) (by decide) (by rw [nodeBytes_size]; decide) (by simp [h0]; omega)
  simp only [h0, Int.toNat_zero, Nat.zero_add] at hacc hx
  have hv' : Enc.decode (blk.bytes.extract 8 (8 + Enc.size (BitVec 32))) = pure v := by
    rw [show Enc.size (BitVec 32) = 4 from rfl, hx, nodeBytes_val]; exact LawfulEnc.decode_encode v
  refine ⟨_, load_run hacc hv' (noRace_of_singleThread hst.single _ _ _ _), ?_, ?_⟩
  · funext l; rw [Mem.heap_recordAt]; exact congrFun hm l
  · exact hst.recordAt _ _ _ _

theorem node_set_next_run (hn : node p v q h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hst : m.Seq) (q' : Option Ptr) :
    ∃ m', (store 8 (p.add 0) q').run m = pure ((), m') ∧ m'.Seq ∧
      ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ node p v q' h' := by
  obtain ⟨h0, A, hA, hb⟩ := hn
  obtain ⟨m', hr, hst', h', hd', hm', hb'⟩ := bytesAt_store (q := p.add 0) (k := 0) (a := 8)
    (bs' := Enc.encode q') hb hm hd (by simp) (by rw [enc_next_size]; decide)
    (by rw [enc_next_size, nodeBytes_size]; decide) (by simp [h0]; omega) hst (by decide)
  rw [nodeBytes_set_next] at hb'
  exact ⟨m', hr, hst', h', hd', hm', h0, A, hA, hb'⟩

theorem node_free_run (hn : node p v q h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hst : m.Seq) (a : Allocator) :
    ∃ m', (a.destroy 16 p).run m = pure ((), m') ∧ m'.heap = Heap.empty ∪ hF ∧ m'.Seq := by
  obtain ⟨h0, A, -, hb⟩ := hn
  obtain ⟨m', hr, hm', hst', -⟩ := rawFree_run hb hm hd (nodeBytes_size v q) h0 (by decide) hst
  exact ⟨m', by simpa [Allocator.destroy] using hr, hm', hst'⟩

end Node

/-! The node operations as total triples, the rules `sep_step using` applies. -/

theorem node_next_total {p : Ptr} {v : BitVec 32} {q : Option Ptr} :
    TotalTriple (node p v q) (load (Option Ptr) 8 (p.add 0)) (fun r => ⌜r = q⌝ ∗ node p v q) :=
  fun _ h _ hd hm hn hst => by
    obtain ⟨m', hr, hm', hst'⟩ := node_next_run hn hm hst
    exact ⟨q, m', h, hr, hd, hm', sep_lift.mpr ⟨rfl, hn⟩, hst'⟩

theorem node_set_next_total {p : Ptr} {v : BitVec 32} {q q' : Option Ptr} :
    TotalTriple (node p v q) (store 8 (p.add 0) q') (fun _ => node p v q') :=
  fun _ _ _ hd hm hn hst => by
    obtain ⟨m', hr, hst', h', hd', hm', hn'⟩ := node_set_next_run hn hm hd hst q'
    exact ⟨(), m', h', hr, hd', hm', hn', hst'⟩

theorem node_free_total {p : Ptr} {v : BitVec 32} {q : Option Ptr} {a : Allocator} :
    TotalTriple (node p v q) (a.destroy 16 p) (fun _ => emp) :=
  fun _ _ _ hd hm hn hst => by
    obtain ⟨m', hr, hm', hst'⟩ := node_free_run hn hm hd hst a
    exact ⟨(), m', Heap.empty, hr, (Heap.disjoint_empty _).symm, hm', rfl, hst'⟩

/-- The list at `hd` has the items `xs`. -/
def list (hd : Option Ptr) : List (BitVec 32) → Assn
  | [] => ⌜hd = none⌝
  | v :: vs => fun h => ∃ p q, hd = some p ∧ (node p v q ∗ list q vs) h

/-- A nonempty list as separation connectives, for `sep_intro` and `sep_close`. -/
theorem list_cons_eq {hd : Option Ptr} {v : BitVec 32} {vs : List (BitVec 32)} :
    list hd (v :: vs) = Assn.ex fun p => Assn.ex fun q => ⌜hd = some p⌝ ∗ (node p v q ∗ list q vs) := by
  funext h; simp only [list, Assn.ex, sep_lift]

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
    (h : Heap) (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF) (hi : revInv xs s n h)
    (hst : m.Seq) :
    ∃ e s' m' h', (reverse.loop6.run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
      m'.heap = h' ∪ hF ∧ m'.Seq ∧
      (if reverse.again6 e then ∃ n' < n, revInv xs s' n' h'
       else e = .br5 ∧ list s'.prev xs.reverse h') := by
  obtain ⟨ys, zs, hxs, hn, hl⟩ := hi
  refine TotalTriple.step_run ?_ hd hm hl hst
  cases zs with
  | nil =>
    simp only [list]
    sep_intro hcur
    sep_unfold [reverse.loop6, hcur]
    sep_ret
    exact fun _ hl' => by simpa [reverse.again6, hxs] using hl'
  | cons z zs =>
    rw [list_cons_eq]
    sep_intro p q hcur
    sep_unfold [reverse.loop6, hcur]
    sep_steps using node_next_total, node_set_next_total
    sep_ret
    intro _ hp
    refine ⟨zs.length, by simp at hn; omega, z :: ys, zs, by simp [hxs], rfl, ?_⟩
    rw [list_cons_eq]
    sep_close hp p s.prev

/-- `reverse` turns the list at `hd` into the list of the items in the other order. It
returns. -/
theorem reverse_total (hd : Option Ptr) (xs : List (BitVec 32)) :
    TotalTriple (list hd xs) (reverse hd) (fun r => list r xs.reverse) := by
  apply TotalTriple.of_run
  intro m hP hF hdj hm hl hst
  obtain ⟨e, s', m', h', hr, hd', hm', ⟨he, hpost⟩, hst'⟩ :=
    loop_sep_ghost reverse.loop6 reverse.again6 (revInv xs)
      (fun e s h => e = .br5 ∧ list s.prev xs.reverse h) hF
      (fun s n m h hd hm hi hst => reverse_step xs hF s n m h hd hm hi hst)
      { (default : reverseLocals) with prev := none, cur := hd } xs.length m hP hdj hm
      ⟨[], xs, by simp, rfl, Heap.empty, hP, (Heap.disjoint_empty hP).symm, by simp, ⟨rfl, rfl⟩, hl⟩
      hst
  refine ⟨s'.prev, m', h', ?_, hd', hm', hpost, hst'⟩
  simp only [StateT.run] at hr
  simp [reverse, zig_unfold, hr, he]

theorem reverse_spec (hd : Option Ptr) (xs : List (BitVec 32)) :
    Triple (list hd xs) (reverse hd) (fun r => list r xs.reverse) :=
  (reverse_total hd xs).toPartial

/-- What `push` returns: a new node in front of `q`, or `error.OutOfMemory` and no bytes. -/
def pushed (v : BitVec 32) (q : Option Ptr) : Except ErrName Ptr → Assn
  | .ok p => node p v q
  | .error e => ⌜e = "OutOfMemory"⌝

/-- `push` returns, with a new node or `error.OutOfMemory`, for every allocation policy. -/
theorem push_total (a : Allocator) (q : Option Ptr) (v : BitVec 32) :
    TotalTriple emp (push a q v) (pushed v q) := by
  apply TotalTriple.of_run
  intro m hP hF hd hm hp hst
  have hP0 : hP = Heap.empty := hp
  subst hP0
  obtain ⟨r, m₁, h₁, hc, hd₁, hm₁, -, hst₁, hnew⟩ :=
    create_run hd hm a 16 8 (by decide) (by decide) hst
  simp only [Heap.empty_union] at hd₁ hm₁
  simp only [StateT.run] at hc
  cases r with
  | error e =>
    obtain ⟨rfl, rfl⟩ := hnew
    refine ⟨.error "OutOfMemory", m₁, Heap.empty, ?_, hd₁, hm₁, ⟨rfl, rfl⟩, hst₁⟩
    simp [push, zig_unfold, hc, Zig.unwrapErr]
  | ok p =>
    obtain ⟨h0, A, hA, hb⟩ := hnew
    obtain ⟨m₂, hs₁, hst₂, h₂, hd₂, hm₂, hb₂⟩ := bytesAt_store (q := p.add 8) (k := 8) (a := 4)
      (bs' := Enc.encode v) hb hm₁ hd₁ (by simp) (by rw [enc_val_size]; decide)
      (by rw [enc_val_size]; simp) (by simp [h0]; omega) hst₁ (by decide)
    have hw : (writeBytes (Array.replicate 16 Byte.undef) 8 (Enc.encode v)).size = 16 := by
      rw [writeBytes_size _ _ _ (by rw [enc_val_size]; simp)]; simp
    obtain ⟨m₃, hs₂, hst₃, h₃, hd₃, hm₃, hb₃⟩ := bytesAt_store (q := p.add 0) (k := 0) (a := 8)
      (bs' := Enc.encode q) hb₂ hm₂ hd₂ (by simp) (by rw [enc_next_size]; decide)
      (by rw [enc_next_size, hw]; decide) (by simp [h0]; omega) hst₂ (by decide)
    rw [nodeBytes_new] at hb₃
    refine ⟨.ok p, m₃, h₃, ?_, hd₃, hm₃, ⟨h0, A, hA, hb₃⟩, hst₃⟩
    simp only [StateT.run] at hs₁ hs₂
    simp [push, zig_unfold, hc, Zig.store, hs₁, hs₂]

theorem push_spec (a : Allocator) (q : Option Ptr) (v : BitVec 32) :
    Triple emp (push a q v) (pushed v q) :=
  (push_total a q v).toPartial

/-- The invariant of `freeAll`: `p` is a list of `n` items. -/
def freeInv (s : freeAllLocals) (n : Nat) : Assn := fun h => ∃ zs, zs.length = n ∧ list s.p zs h

theorem freeAll_step (a : Allocator) (hF : Heap) (s : freeAllLocals) (n : Nat) (m : Mem) (h : Heap)
    (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF) (hi : freeInv s n h) (hst : m.Seq) :
    ∃ e s' m' h', ((freeAll.loop5 a).run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
      m'.heap = h' ∪ hF ∧ m'.Seq ∧
      (if freeAll.again5 e then ∃ n' < n, freeInv s' n' h' else e = .br4 ∧ emp h') := by
  obtain ⟨zs, hn, hl⟩ := hi
  refine TotalTriple.step_run (P := list s.p zs) ?_ hd hm hl hst
  cases zs with
  | nil =>
    simp only [list]
    sep_intro hp
    sep_unfold [freeAll.loop5, hp]
    sep_ret
    exact fun _ he => ⟨rfl, he⟩
  | cons z zs =>
    rw [list_cons_eq]
    sep_intro p q hp
    sep_unfold [freeAll.loop5, hp]
    sep_steps using node_next_total, node_free_total
    sep_ret
    exact fun _ hr => ⟨zs.length, by simp at hn; omega, zs, rfl, sep_emp.mp (sep_comm hr)⟩

/-- `freeAll` frees every node of the list: after it, the function owns no bytes. It
returns. -/
theorem freeAll_total (a : Allocator) (hd : Option Ptr) (xs : List (BitVec 32)) :
    TotalTriple (list hd xs) (freeAll a hd) (fun _ => emp) := by
  apply TotalTriple.of_run
  intro m hP hF hdj hm hl hst
  obtain ⟨e, s', m', h', hr, hd', hm', ⟨he, hpost⟩, hst'⟩ :=
    loop_sep_ghost (freeAll.loop5 a) freeAll.again5 freeInv (fun e _ h => e = .br4 ∧ emp h) hF
      (fun s n m h hd hm hi hst => freeAll_step a hF s n m h hd hm hi hst)
      { (default : freeAllLocals) with p := hd } xs.length m hP hdj hm ⟨xs, rfl, hl⟩ hst
  refine ⟨(), m', h', ?_, hd', hm', hpost, hst'⟩
  simp only [StateT.run] at hr
  simp [freeAll, zig_unfold, hr, he]

theorem freeAll_spec (a : Allocator) (hd : Option Ptr) (xs : List (BitVec 32)) :
    Triple (list hd xs) (freeAll a hd) (fun _ => emp) :=
  (freeAll_total a hd xs).toPartial

end Lists
