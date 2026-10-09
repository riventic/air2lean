import ZigLean.Sep.Full.Res
import ZigLean.Conc.Lemmas
import ZigLean.Sep.Block

/-!
# Full-state triples (prototype, `docs/sep-full-state.md`)

`FTriple P c Q` is `Triple` (`ZigLean/Sep/Triple.lean`) over full-state resources
(`ZigLean/Sep/Full/Res.lean`): a memory holds a resource `r` with the frame `rF` (`Holds`) if its
full heap (live bytes **with their atomic tags**) is exactly the disjoint union of the two, and
**the knowledge of both is true in it** (every `known b A` names an existing block at its address).
The memory invariant is `Mem.FSeq`: `Mem.Seq` and a well-formed atomic layout.

* **Structural rules**: `conseq`, `frame`, `ret`, `bind`, `ex`, `lift`; `drop` forgets knowledge.
  The frame is in the definition, so the frame rule holds for every program; the frame now
  includes the tags of its bytes and its knowledge.
* **Lifting** (`ofTriple`): a legacy `Triple P c Q` of a program that keeps the atomic layout and
  every block's address (`Tame`) is a full triple of `up P` and `up Q`. Every primitive of plain
  generated code is `Tame` (`Tame.load`, `.store`, `.alloc`, `.free`, `.ptrAddr`,
  `.ptrFromAddr`, closed under `pure` and `bind`), so the legacy rules carry over unchanged.
* **Knowledge** (`know_intro`): owning a byte of block `b` gives `known b A` for its address `A`;
  `ptrAddr` (`@intFromPtr`) of a pointer into `b` needs only `known b A`, so it works after `free`
  (`FTriple.ptrAddr`, obstruction O1).
-/

namespace Zig
namespace Full

open FAssn Conc

/-- The memory invariant of `FTriple`: one thread, blocks below `nextAddr` (`Mem.Seq`), and a
well-formed atomic layout. -/
def _root_.Zig.Mem.FSeq (m : Mem) : Prop := m.Seq ∧ ShapesWF (shapes m)

/-- `m` holds the resource `r` and the frame `rF`: its full heap is exactly their disjoint union,
and their knowledge is true in `m`. -/
structure Holds (m : Mem) (r rF : Res) : Prop where
  disj : FHeap.Disjoint r.heap rF.heap
  heap : m.fheap = r.heap ∪ rF.heap
  know : Know.Sub r.know m.kn
  knowF : Know.Sub rF.know m.kn

/-- Partial correctness without a panic, over full-state resources (module doc). -/
def FTriple {α : Type} (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FSeq →
    match (c.run m).run with
    | none => True
    | some (.error _) => False
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq

namespace FTriple

variable {α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {c : MemM α}

theorem of_run
    (h : ∀ m r rF, Holds m r rF → P r → m.FSeq →
      ∃ v m' r', c.run m = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FSeq) :
    FTriple P c Q := by
  intro m r rF hh hp hs
  obtain ⟨v, m', r', hr, hh', hq, hs'⟩ := h m r rF hh hp hs
  rw [hr]; exact ⟨r', hh', hq, hs'⟩

theorem conseq (ht : FTriple P c Q) (hp : ∀ r, P' r → P r) (hq : ∀ v r, Q v r → Q' v r) :
    FTriple P' c Q' := by
  intro m r rF hh hp' hs
  have := ht m r rF hh (hp _ hp') hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', a, b, s⟩ := this; exact ⟨r', a, hq _ _ b, s⟩

theorem pre (ht : FTriple P c Q) (hp : ∀ r, P' r → P r) : FTriple P' c Q := conseq ht hp (fun _ _ h => h)

theorem post (ht : FTriple P c Q) (hq : ∀ v r, Q v r → Q' v r) : FTriple P c Q' :=
  conseq ht (fun _ h => h) hq

/-- **The frame rule.** The frame's bytes, their atomic tags and its knowledge stay. -/
theorem frame (ht : FTriple P c Q) : FTriple (P ⋆ R) c (fun v => Q v ⋆ R) := by
  intro m r rF hh hpr hs
  obtain ⟨rP, rR, hd, rfl, hp, hr⟩ := hpr
  obtain ⟨hdisj, hheap, hk, hkF⟩ := hh
  obtain ⟨hPF, hRF⟩ := FHeap.disjoint_union_left.mp hdisj
  have := ht m rP ⟨rR.heap ∪ rF.heap, rR.know.union rF.know⟩
    ⟨FHeap.disjoint_union_right.mpr ⟨hd, hPF⟩, by rw [hheap]; exact FHeap.union_assoc .., hk.left,
      hk.right.union hkF⟩ hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', ⟨hd', hh', hk', hkF'⟩, hq, hs'⟩ := this
    obtain ⟨hQR, hQF⟩ := FHeap.disjoint_union_right.mp hd'
    exact ⟨⟨r'.heap ∪ rR.heap, r'.know.union rR.know⟩,
      ⟨FHeap.disjoint_union_left.mpr ⟨hQF, hRF⟩, by rw [hh', FHeap.union_assoc],
        hk'.union hkF'.left, hkF'.right⟩, ⟨r', rR, hQR, rfl, hq, hr⟩, hs'⟩

/-- Frame on the left. -/
theorem frameL (ht : FTriple P c Q) : FTriple (R ⋆ P) c (fun v => R ⋆ Q v) :=
  conseq (frame (R := R) ht) (fun _ h => sep_comm h) (fun _ _ h => sep_comm h)

theorem ret (v : α) : FTriple (Q v) (pure v : MemM α) Q :=
  of_run fun m r _ hh hq hs => ⟨v, m, r, rfl, hh, hq, hs⟩

theorem ret' (v : α) (hq : ∀ r, P r → Q v r) : FTriple P (pure v : MemM α) Q :=
  pre (ret v) hq

theorem bind {S : β → FAssn} {f : α → MemM β} (hc : FTriple P c Q)
    (hf : ∀ v, FTriple (Q v) (f v) S) : FTriple P (c >>= f) S := by
  intro m r rF hh hp hs
  have h1 := hc m r rF hh hp hs
  simp only [StateT.run_bind, ExceptT.run_bind]
  revert h1
  cases (c.run m).run with
  | none => intro; trivial
  | some x =>
    cases x with
    | error e => intro h1; exact h1.elim
    | ok x =>
      obtain ⟨v, m'⟩ := x
      rintro ⟨r', hh', hq, hs'⟩
      exact hf v m' r' rF hh' hq hs'

theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ x, FTriple (P x) c Q) : FTriple (FAssn.ex P) c Q := by
  intro m r rF hh ⟨x, hp⟩ hs
  exact h x m r rF hh hp hs

theorem lift {φ : Prop} (h : φ → FTriple P c Q) : FTriple (⟪φ⟫ ⋆ P) c Q := by
  intro m r rF hh hp hs
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m r rF hh hp hs

/-- Knowledge (anything that owns no bytes) can be forgotten. -/
theorem drop {K : α → FAssn} (ht : FTriple P c (fun v => Q v ⋆ K v))
    (hK : ∀ v r, K v r → r.heap = FHeap.empty) : FTriple P c Q := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', ⟨hd, hm, hk, hkF⟩, ⟨r₁, r₂, -, rfl, hq, hk2⟩, hs'⟩ := this
    have e := hK _ _ hk2
    simp only [e, FHeap.union_empty] at hd hm
    exact ⟨r₁, ⟨hd, hm, hk.left, hkF⟩, hq, hs'⟩

/-- A step that does not change the memory and returns: every assertion stays. -/
theorem of_pure_run (h : ∀ m, m.FSeq → ∃ v, c.run m = pure (v, m)) (hq : ∀ v r, P r → Q v r) :
    FTriple P c Q :=
  of_run fun m r _ hh hp hs => by
    obtain ⟨v, hv⟩ := h m hs
    exact ⟨v, m, r, hv, hh, hq v r hp, hs⟩

end FTriple

/-! ## Knowledge rules -/

/-- A cell of an owned full heap is a cell of the memory. -/
theorem Holds.cell {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc} {c : FCell}
    (hc : r.heap l = some c) : m.heap l = some c.cell := by
  have := congrFun hh.heap l
  rw [FHeap.union_apply, hc, Option.some_or] at this
  have e := congrArg (Option.map (·.cell)) this
  simpa [Mem.fheap, Option.map_map] using e

/-- **Knowledge from ownership.** Owning a byte of block `b`, whose cell has the address `A`,
gives `known b A`. -/
theorem FTriple.know_intro {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {b : BlockId}
    {A : Nat} (hc : ∀ r, P r → ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A)
    (ht : FTriple (P ⋆ known b A) c Q) : FTriple P c Q := by
  intro m r rF hh hp hs
  obtain ⟨x, fc, hx, hA⟩ := hc r hp
  have hkn : m.kn b A := by
    obtain ⟨blk, hblk, _, _, he⟩ := Mem.heap_some (hh.cell hx)
    exact ⟨blk, hblk, by rw [← hA, he]⟩
  have hres : (P ⋆ known b A) ⟨r.heap, r.know.union fun b' A' => b' = b ∧ A' = A⟩ :=
    ⟨r, ⟨FHeap.empty, fun b' A' => b' = b ∧ A' = A⟩, FHeap.disjoint_empty _,
      by rw [FHeap.union_empty], hp, rfl, rfl⟩
  have hk : Know.Sub (r.know.union fun b' A' => b' = b ∧ A' = A) m.kn :=
    hh.know.union fun b' A' h => by obtain ⟨rfl, rfl⟩ := h; exact hkn
  exact ht m ⟨r.heap, r.know.union fun b' A' => b' = b ∧ A' = A⟩ rF
    ⟨hh.disj, hh.heap, hk, hh.knowF⟩ hres hs

theorem ptrAddr_run {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (off : Int) : (ptrAddr ⟨some b, off⟩).run m = pure ((blk.addr : Int) + off, m) := by
  simp [ptrAddr, hb, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont]

/-- **`@intFromPtr` of a pointer into block `b`, live or freed** (O1): only the knowledge of its
address is needed. -/
theorem FTriple.ptrAddr {b : BlockId} {A : Nat} (off : Int) :
    FTriple (known b A) (Zig.ptrAddr ⟨some b, off⟩) (fun a => ⟪a = (A : Int) + off⟫ ⋆ known b A) :=
  FTriple.of_run fun m r _ hh hp hs => by
    obtain ⟨blk, hblk, hA⟩ := hh.know b A (by rw [hp.2]; exact ⟨rfl, rfl⟩)
    exact ⟨_, m, r, ptrAddr_run hblk off, hh, sep_lift.mpr ⟨by rw [hA], hp⟩, hs⟩

theorem ptrAddr_none_run (m : Mem) (off : Int) : (Zig.ptrAddr ⟨none, off⟩).run m = pure (off, m) := rfl

/-- `@intFromPtr` of a pointer without a block (an integer handle): no knowledge needed. -/
theorem FTriple.ptrAddr_none {P : FAssn} (off : Int) :
    FTriple P (Zig.ptrAddr ⟨none, off⟩) (fun a => ⟪a = off⟫ ⋆ P) :=
  FTriple.of_run fun m r _ hh hp hs =>
    ⟨off, m, r, ptrAddr_none_run m off, hh, sep_lift.mpr ⟨rfl, hp⟩, hs⟩

/-- `@ptrFromInt` never fails and changes nothing: its result may point into a dead block (or a
frame block), which a later access checks. -/
theorem ptrFromAddr_run (n : Nat) (m : Mem) : ∃ v, (Zig.ptrFromAddr n).run m = pure (v, m) := by
  unfold Zig.ptrFromAddr
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, StateT.pure, Option.bind_some]
  generalize Array.findSome? _ m.blocks.zipIdx = x
  rcases x with _ | ⟨b, a⟩ <;> exact ⟨_, rfl⟩

theorem FTriple.ptrFromAddr {P : FAssn} (n : Nat) : FTriple P (Zig.ptrFromAddr n) (fun _ => P) :=
  FTriple.of_pure_run (fun m _ => ptrFromAddr_run n m) fun _ _ h => h

/-! ## Lifting legacy triples -/

/-- `c` keeps the atomic layout and every block's address. -/
def Tame {α : Type} (c : MemM α) : Prop :=
  ∀ m v m', (c.run m).run = some (.ok (v, m')) → shapes m' = shapes m ∧ KMono m m'

namespace Tame

variable {α β : Type}

theorem pure' (v : α) : Tame (pure v : MemM α) := fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h; exact ⟨rfl, KMono.refl _⟩

theorem bind {c : MemM α} {f : α → MemM β} (hc : Tame c) (hf : ∀ v, Tame (f v)) :
    Tame (c >>= f) := fun m v m'' h => by
  obtain ⟨a, m', h1, h2⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨s1, k1⟩ := hc m a m' h1
  obtain ⟨s2, k2⟩ := hf a m' v m'' h2
  exact ⟨s2.trans s1, k1.trans k2⟩

/-- A step that changes only clocks, footprint and bytes or liveness of blocks. -/
theorem of_eq {c : MemM α}
    (h : ∀ m v m', (c.run m).run = some (.ok (v, m')) → m'.atomics = m.atomics ∧ KMono m m') :
    Tame c := fun m v m' hr => by
  obtain ⟨ha, hk⟩ := h m v m' hr
  exact ⟨by simp [shapes, ha], hk⟩

theorem loadBytes (p : Ptr) (n a : Nat) (k : AccessKind) : Tame (Zig.loadBytes p n a k) :=
  of_eq fun _ _ _ h => by
    obtain ⟨-, -, -, -, -, -, rfl⟩ := Conc.Proto.loadBytes_ok h
    exact ⟨rfl, KMono.of_blocks rfl⟩

theorem lift (r : Result α) : Tame (StateT.lift r : MemM α) := of_eq fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.lift_ok h; exact ⟨rfl, KMono.refl _⟩

theorem load (T : Type) [Enc T] (a : Nat) (p : Ptr) : Tame (Zig.load T a p) :=
  bind (loadBytes p _ a .read) fun bs => lift (Enc.decode bs)

theorem storeBytes (p : Ptr) (a : Nat) (bs : Array Byte) (k : AccessKind) :
    Tame (Zig.storeBytes p a bs k) := of_eq fun _ _ _ h => by
  obtain ⟨b, blk, o, hacc, -, -, rfl⟩ := Conc.Proto.storeBytes_ok h
  exact ⟨rfl, KMono.set (blk' := { blk with bytes := writeBytes blk.bytes o bs })
    (access_eq hacc).2.1 rfl rfl⟩

theorem store {T : Type} [Enc T] (a : Nat) (p : Ptr) (v : T) : Tame (Zig.store a p v) :=
  storeBytes p a _ .write

theorem alloc (kind : BlockKind) (size align : Nat) : Tame (Zig.alloc kind size align) :=
  of_eq fun m v m' h => by
    rw [alloc_run_eq] at h
    obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h
    exact ⟨rfl, KMono.push rfl⟩

theorem free (p : Ptr) : Tame (Zig.free p) := of_eq fun m v m' h => by
  unfold Zig.free at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
  split at h₁
  · exact (Conc.Proto.MemM.throw_ok h₁).elim
  · split at h₁
    · rename_i b _ blk hblk
      split at h₁
      · have := Conc.Proto.MemM.set_ok h₁
        subst this
        exact ⟨rfl, KMono.set (blk' := { blk with live := false }) hblk rfl rfl⟩
      · exact (Conc.Proto.MemM.throw_ok h₁).elim
    · exact (Conc.Proto.MemM.throw_ok h₁).elim

theorem ptrAddr (p : Ptr) : Tame (Zig.ptrAddr p) := of_eq fun m v m' h => by
  unfold Zig.ptrAddr at h
  split at h
  · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h; exact ⟨rfl, KMono.refl _⟩
  · obtain ⟨a₁, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
    split at h₁
    · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h₁; exact ⟨rfl, KMono.refl _⟩
    · exact (Conc.Proto.MemM.throw_ok h₁).elim

end Tame

/-- **Lifting.** A legacy triple of a program that keeps the atomic layout and the block addresses
is a full triple: the legacy frame is the full frame without its tags, and the tags of the frame
stay because the layout stays. -/
theorem FTriple.ofTriple {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} (ht : Triple P c Q)
    (hc : Tame c) : FTriple (up P) c (fun v => up (Q v)) := by
  intro m r rF hh hp hs
  obtain ⟨hd, hm, hk, hkF⟩ := hh
  have hm' : m.heap = r.heap.erase ∪ rF.heap.erase := by
    rw [← fheap_erase, hm, FHeap.erase_union]
  have := ht m _ _ (FHeap.erase_disjoint hd) hm' hp.1 hs.1
  revert this
  cases hrun : (c.run m).run with
  | none => intro; trivial
  | some x =>
    cases x with
    | error e => intro h; exact h
    | ok x =>
      obtain ⟨v, m'⟩ := x
      rintro ⟨hQ, hdQ, hmQ, hq, hs'⟩
      obtain ⟨hsh, hkm⟩ := hc m v m' hrun
      -- The frame's cells carry `m`'s tags, which are `m'`'s.
      have hF : ∀ l fc, rF.heap l = some fc → fc.atom = tagOf (shapes m') l.1 l.2 := by
        intro l fc hl
        have e := congrFun hm l
        rcases hd l with h1 | h1
        · rw [FHeap.union_apply, h1, Option.none_or, hl] at e
          simp only [Mem.fheap, Option.map_eq_some_iff] at e
          obtain ⟨c0, -, rfl⟩ := e
          rw [hsh]
        · rw [h1] at hl; cases hl
      let hQ' : FHeap := fun l => (hQ l).map fun c => ⟨c, tagOf (shapes m') l.1 l.2⟩
      refine ⟨⟨hQ', Know.none⟩, ⟨fun l => ?_, ?_, Know.sub_none _, hkF.trans hkm⟩,
        ⟨?_, rfl⟩, ⟨hs', by rw [hsh]; exact hs.2⟩⟩
      · rcases hdQ l with e | e
        · left; simp [hQ', e]
        · right
          cases h2 : rF.heap l with
          | none => rfl
          | some fc => simp [FHeap.erase, h2] at e
      · funext l
        simp only [Mem.fheap, hmQ, FHeap.union_apply, Heap.union_apply, hQ']
        cases hql : hQ l with
        | some c => rfl
        | none =>
          simp only [Option.none_or, Option.map_none]
          cases h2 : rF.heap l with
          | none => simp [FHeap.erase, h2]
          | some fc =>
            simp only [FHeap.erase, h2, Option.map_some]
            rw [← hF l fc h2]
      · show Q v (fun l => (hQ' l).map (·.cell))
        have : (fun l => (hQ' l).map (·.cell)) = hQ := by
          funext l; simp only [hQ', Option.map_map]; cases hQ l <;> rfl
        rw [this]; exact hq

end Full
end Zig
