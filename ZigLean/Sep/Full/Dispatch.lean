import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.AllocSpec.Dispatch

/-!
# Indirect calls through a read-only vtable, read in one thread

The translator emits an indirect call (`Air2Lean/Emit.lean`, M20/L11) as a test of the loaded
function pointer against every address-taken function of the callee's type, in a fixed order, and
`.illegal` for any other pointer:

    if f == ⟨some b₁, 0⟩ then call₁ else if f == ⟨some b₂, 0⟩ then call₂ else … else throw .illegal

`callIndirect f arms` is that chain over the list `arms` of (function pointer, call) pairs. The
`dispatch_fold` simp set folds a generated chain into it (the lemmas are `rfl`), and
`CTriple.callIndirect` reads it: if the arm that `f` selects (`arms.lookup f`) meets a triple, so
does the call. A `Table` is the program's candidates for one function type, as functions of the
call's arguments.

The function pointer comes from a vtable, a `const` global: `vtR vtp fns` holds its entries `fns`
(at `vtp`, `vtp + 8`, …) read-only (`ptsR`). `vtR_load` and `vtR_project` read entry `i`. This is
`Dispatch.vtR` of the legacy logic (`ZigLean/Sep/AllocSpec/Dispatch.lean`) for any interface: the
list has one entry per function of the interface.

For `std.mem.Allocator` (`CVTable`, `CAllocSpec`, `CVTable.dispatch`): an allocator whose entries
are concurrent functions meets `FAllocSpec` in the one-thread reading at every depth
(`CAllocSpec`); the allocator that a call site reaches through a vtable holding `fns` is the
dispatch of the program's tables at `fns` (`CVTable.dispatch`); if each entry of `fns` selects the
corresponding function of an implementation `impl`, the dispatch meets `impl`'s specification
(`CAllocSpec.dispatch`). Other interfaces (`Io`, …) use `callIndirect`, `Table` and `vtR` the same
way.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

open FAssn

variable {Tgt α A : Type}

/-- The arms of a generated indirect call on the function pointer `f` (module doc). -/
def callIndirect {m : Type → Type} [MonadExceptOf Error m] (f : Ptr) :
    List (Ptr × m α) → m α
  | [] => throw .illegal
  | (c, x) :: arms => if f == c then x else callIndirect f arms

section Fold

variable {m : Type → Type} [MonadExceptOf Error m] {f c : Ptr} {x : m α}

/-- The innermost arm of a generated chain. -/
@[simp] theorem callIndirect_fold_one :
    (if f == c then x else (throw .illegal : m α)) = callIndirect f [(c, x)] := rfl

/-- One more arm of a generated chain. -/
@[simp] theorem callIndirect_fold_cons {arms : List (Ptr × m α)} :
    (if f == c then x else callIndirect f arms) = callIndirect f ((c, x) :: arms) := rfl

end Fold

/-- The arm that `f` selects. -/
theorem callIndirect_of_lookup {m : Type → Type} [MonadExceptOf Error m] {f : Ptr}
    {arms : List (Ptr × m α)} {x : m α} (h : arms.lookup f = some x) : callIndirect f arms = x := by
  induction arms with
  | nil => cases h
  | cons a arms ih =>
    obtain ⟨c, y⟩ := a
    by_cases hc : f = c
    · subst hc
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      simp [callIndirect, h]
    · have hc' : (f == c) = false := beq_false_of_ne hc
      simp only [List.lookup, hc'] at h
      simp only [callIndirect, hc', Bool.false_eq_true, ↓reduceIte]
      exact ih h

/-- The chain under the locals of a generated function (`CM`). -/
theorem callIndirect_run {σ : Type} {f : Ptr} (arms : List (Ptr × CM Tgt σ α)) (s : σ) :
    (callIndirect f arms).run s = callIndirect f (arms.map fun a => (a.1, a.2.run s)) := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
    simp only [callIndirect, List.map_cons]
    split
    · rfl
    · exact ih

/-- A continuation after the call is a continuation of every arm. -/
theorem callIndirect_bind {β : Type} {f : Ptr} (arms : List (Ptr × ConcM Tgt α))
    (k : α → ConcM Tgt β) :
    callIndirect f arms >>= k = callIndirect f (arms.map fun a => (a.1, a.2 >>= k)) := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
    simp only [callIndirect, List.map_cons]
    split
    · rfl
    · exact ih

/-- **An indirect call** meets the triple of the arm that its function pointer selects. -/
theorem CTriple.callIndirect {P : FAssn} {Q : α → FAssn} {f : Ptr}
    {arms : List (Ptr × ConcM Tgt α)} {x : ConcM Tgt α} (h : arms.lookup f = some x)
    (hx : CTriple P x Q) : CTriple P (Full.callIndirect f arms) Q := by
  rw [callIndirect_of_lookup h]; exact hx

/-- The program's candidates for an indirect call of one function type, as functions of the
call's arguments `A` (module doc). -/
abbrev Table (Tgt A α : Type) := List (Ptr × (A → ConcM Tgt α))

/-- The indirect call through `f` with arguments `a`. -/
def Table.call (t : Table Tgt A α) (f : Ptr) (a : A) : ConcM Tgt α :=
  callIndirect f (t.map fun g => (g.1, g.2 a))

/-- `f` selects `g` in `t`. -/
def Table.Sel (t : Table Tgt A α) (f : Ptr) (g : A → ConcM Tgt α) : Prop := t.lookup f = some g

theorem Table.call_of_sel {t : Table Tgt A α} {f : Ptr} {g : A → ConcM Tgt α} (h : t.Sel f g)
    (a : A) : t.call f a = g a := by
  unfold Table.call
  refine callIndirect_of_lookup ?_
  unfold Table.Sel at h
  induction t with
  | nil => cases h
  | cons c t ih =>
    obtain ⟨c, g'⟩ := c
    by_cases hc : f = c
    · subst hc
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      simp [h]
    · have hc' : (f == c) = false := beq_false_of_ne hc
      simp only [List.lookup, hc'] at h
      simp only [List.map_cons, List.lookup, hc']
      exact ih h

/-- **A call through a table, then a continuation**: the form of a generated call site after
`conc_norm` (the continuation is pushed into every arm). -/
theorem CTriple.tableCall {β : Type} {P : FAssn} {Q : α → FAssn} {S : β → FAssn}
    {t : Table Tgt A α} {f : Ptr} {a : A} {g : α → ConcM Tgt β} (h : CTriple P (t.call f a) Q)
    (hg : ∀ v, CTriple (Q v) (g v) S) :
    CTriple P (Full.callIndirect f (t.map fun x => (x.1, x.2 a >>= g))) S := by
  have e : Full.callIndirect f (t.map fun x => (x.1, x.2 a >>= g)) = t.call f a >>= g := by
    rw [Table.call, callIndirect_bind, List.map_map]; rfl
  rw [e]; exact CTriple.bind h hg

/-! ## The read-only vtable -/

open Assn in
/-- The vtable at `vtp` holds the function pointers `fns` (read-only: a `const` global). -/
def vtR (vtp : Ptr) : List Ptr → Assn
  | [] => Assn.emp
  | f :: fns => ptsR vtp 8 f ∗ vtR (vtp.add 8) fns

open Assn in
/-- Entry `i` of the vtable, and the rest. -/
theorem vtR_split {vtp : Ptr} {fns : List Ptr} {i : Nat} (hi : i < fns.length) {h : Heap}
    (hv : vtR vtp fns h) :
    ∃ R : Assn, (ptsR (vtp.add (8 * i)) 8 fns[i] ∗ R) h ∧
      ∀ h', (ptsR (vtp.add (8 * i)) 8 fns[i] ∗ R) h' → vtR vtp fns h' := by
  induction fns generalizing vtp i h with
  | nil => cases hi
  | cons f fns ih =>
    cases i with
    | zero =>
      refine ⟨vtR (vtp.add 8) fns, ?_, fun h' x => ?_⟩
      · simpa [vtR, Ptr.add] using hv
      · simpa [vtR, Ptr.add] using x
    | succ i =>
      obtain ⟨h₁, h₂, hd, rfl, h1, h2⟩ := hv
      obtain ⟨R, hR, back⟩ := ih (vtp := vtp.add 8) (i := i) (by simp at hi; omega) h2
      have e : (vtp.add 8).add (8 * i) = vtp.add (8 * (i + 1)) := by
        simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega
      rw [e] at hR back
      refine ⟨ptsR vtp 8 f ∗ R, ?_, fun h' x => ?_⟩
      · simp only [List.getElem_cons_succ]
        rw [Zig.sep_left_comm_eq]; exact ⟨h₁, h₂, hd, rfl, h1, hR⟩
      · simp only [List.getElem_cons_succ] at x
        rw [Zig.sep_left_comm_eq] at x
        obtain ⟨h₁', h₂', hd', rfl, h1', h2'⟩ := x
        exact ⟨h₁', h₂', hd', rfl, h1', back _ h2'⟩

/-- Load entry `i` of the vtable: the function pointer `fns[i]`; the vtable stays. -/
theorem vtR_load {vtp : Ptr} {fns : List Ptr} {i : Nat} (hi : i < fns.length) :
    FTriple (up (vtR vtp fns)) (load Ptr 8 (vtp.add (8 * i)))
      (fun f => ⟪f = fns[i]⟫ ⋆ up (vtR vtp fns)) := by
  intro m r rF hh hp hs
  obtain ⟨R, hR, back⟩ := vtR_split hi hp.1
  refine (((FTotalTriple.ofTotal ((ptsR_load (p := vtp.add (8 * i)) (a := 8) (v := fns[i])
    (by decide)).frame (R := R)) (Tame.load Ptr 8 _)).toPartial).post fun f r' hq => ?_)
    m r rF hh ⟨hR, hp.2⟩ hs
  obtain ⟨hq, hk, hg⟩ := hq
  obtain ⟨hv, hq⟩ := Zig.sep_lift.mp (Zig.sep_assoc hq)
  exact sep_lift.mpr ⟨hv, back _ hq, hk, hg⟩

open Assn in
/-- The pointer to entry `i` of a vtable that the precondition holds: formed (MM-3), no effect. -/
theorem vtR_project {vtp : Ptr} {fns : List Ptr} {i : Nat} (hi : i < fns.length)
    (hv : 0 ≤ vtp.off) :
    FTriple (up (vtR vtp fns)) (ptrProject vtp (·.add (8 * i)))
      (fun q => ⟪q = vtp.add (8 * i)⟫ ⋆ up (vtR vtp fns)) := by
  refine FTriple.of_run fun m r rF hh hp hs => ?_
  obtain ⟨R, hR, -⟩ := vtR_split hi hp.1
  obtain ⟨h₁, h₂, -, he, ⟨A, S, K, bs, -, hsz, -, hb⟩, -⟩ := hR
  have hm : m.heap = h₁ ∪ (h₂ ∪ rF.heap.erase) := by
    rw [← fheap_erase, hh.heap, FHeap.erase_union, he, Heap.union_assoc]
  obtain ⟨b, blk, hacc, -⟩ := bytesAt_access (q := vtp.add (8 * i)) (k := 0) (n := 8) (a := 1) hb hm
    (by simp [Ptr.add]) (by decide) (by rw [hsz]; decide) (Nat.mod_one _)
  obtain ⟨hqb, hblk, -, h0, hn, -⟩ := access_eq hacc
  have hvb : vtp.block = some b := by simpa [Ptr.add] using hqb
  exact ⟨_, m, r, ptrProject_add_run (inBounds_of hvb hblk hv (by simp [Ptr.add] at hn; omega))
    (inBounds_of hqb hblk h0 (by omega)), hh, sep_lift.mpr ⟨rfl, hp⟩, hs⟩

/-! ## `std.mem.Allocator` -/

/-- An allocator's four entries as concurrent functions (a translated implementation of
`std.mem.Allocator.VTable`; the alignment as its log2). -/
structure CVTable (Tgt : Type) where
  alloc : Ptr → BitVec 64 → Nat → BitVec 64 → ConcM Tgt (Option Ptr)
  resize : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → ConcM Tgt Bool
  remap : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → ConcM Tgt (Option Ptr)
  free : Ptr → Slice → Nat → BitVec 64 → ConcM Tgt Unit

/-- The entries read in one thread at depth `fuel` (`Sched.soloRun`). -/
def CVTable.solo (vt : CVTable Tgt) (fuel : Nat) : RawVTable where
  alloc c n k ra := Sched.soloRun fuel (vt.alloc c n k ra)
  resize c s k n ra := Sched.soloRun fuel (vt.resize c s k n ra)
  remap c s k n ra := Sched.soloRun fuel (vt.remap c s k n ra)
  free c s k ra := Sched.soloRun fuel (vt.free c s k ra)

/-- `FAllocSpec` for concurrent entries read in one thread, at every depth. -/
def CAllocSpec (vt : CVTable Tgt) (ctx : Ptr) (I : FAllocInv) : Prop :=
  ∀ fuel, FAllocSpec FLogic.partial (vt.solo fuel) ctx I

/-- `CAllocSpec` from `CTriple`s of the four entries. -/
theorem CAllocSpec.of_ctriples {vt : CVTable Tgt} {ctx : Ptr} {I : FAllocInv}
    (ha : ∀ len k ra, 0 < len.toNat → k < 64 → I.fits len.toNat k →
      CTriple I.own (vt.alloc ctx len k ra) (I.allocPost len.toNat k))
    (hr : ∀ s k n ra bs, k < 64 → 0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size →
      0 < bs.size → CTriple (I.own ⋆ I.granted s.ptr k bs) (vt.resize ctx s k n ra)
        (I.resizePost s.ptr k bs n.toNat))
    (hm : ∀ s k n ra bs, k < 64 → 0 < n.toNat → I.fits n.toNat k → s.len.toNat = bs.size →
      0 < bs.size → CTriple (I.own ⋆ I.granted s.ptr k bs) (vt.remap ctx s k n ra)
        (I.remapPost s.ptr k bs n.toNat))
    (hf : ∀ s k ra bs, k < 64 → s.len.toNat = bs.size → 0 < bs.size →
      CTriple (I.own ⋆ I.granted s.ptr k bs) (vt.free ctx s k ra) (fun _ => I.own)) :
    CAllocSpec vt ctx I := fun fuel =>
  { alloc := fun len k ra h1 h2 h3 => ha len k ra h1 h2 h3 fuel
    resize := fun s k n ra bs h1 h2 h3 h4 h5 => hr s k n ra bs h1 h2 h3 h4 h5 fuel
    remap := fun s k n ra bs h1 h2 h3 h4 h5 => hm s k n ra bs h1 h2 h3 h4 h5 fuel
    free := fun s k ra bs h1 h2 h3 => hf s k ra bs h1 h2 h3 fuel }

section CAllocSpec

variable {vt : CVTable Tgt} {ctx : Ptr} {I : FAllocInv} (h : CAllocSpec vt ctx I)
include h

theorem CAllocSpec.alloc (len : BitVec 64) (k : Nat) (ra : BitVec 64) (h1 : 0 < len.toNat)
    (h2 : k < 64) (h3 : I.fits len.toNat k) :
    CTriple I.own (vt.alloc ctx len k ra) (I.allocPost len.toNat k) :=
  fun fuel => (h fuel).alloc len k ra h1 h2 h3

theorem CAllocSpec.resize (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte) (h1 : k < 64)
    (h2 : 0 < n.toNat) (h3 : I.fits n.toNat k) (h4 : s.len.toNat = bs.size) (h5 : 0 < bs.size) :
    CTriple (I.own ⋆ I.granted s.ptr k bs) (vt.resize ctx s k n ra)
      (I.resizePost s.ptr k bs n.toNat) :=
  fun fuel => (h fuel).resize s k n ra bs h1 h2 h3 h4 h5

theorem CAllocSpec.remap (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte) (h1 : k < 64)
    (h2 : 0 < n.toNat) (h3 : I.fits n.toNat k) (h4 : s.len.toNat = bs.size) (h5 : 0 < bs.size) :
    CTriple (I.own ⋆ I.granted s.ptr k bs) (vt.remap ctx s k n ra)
      (I.remapPost s.ptr k bs n.toNat) :=
  fun fuel => (h fuel).remap s k n ra bs h1 h2 h3 h4 h5

theorem CAllocSpec.free (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte) (h1 : k < 64)
    (h2 : s.len.toNat = bs.size) (h3 : 0 < bs.size) :
    CTriple (I.own ⋆ I.granted s.ptr k bs) (vt.free ctx s k ra) (fun _ => I.own) :=
  fun fuel => (h fuel).free s k ra bs h1 h2 h3

end CAllocSpec

/-- The program's candidates for the four entries of `std.mem.Allocator.VTable`: one `Table` per
function type. -/
structure AllocTables (Tgt : Type) where
  alloc : Table Tgt (Ptr × BitVec 64 × Nat × BitVec 64) (Option Ptr)
  resize : Table Tgt (Ptr × Slice × Nat × BitVec 64 × BitVec 64) Bool
  remap : Table Tgt (Ptr × Slice × Nat × BitVec 64 × BitVec 64) (Option Ptr)
  free : Table Tgt (Ptr × Slice × Nat × BitVec 64) Unit

/-- The allocator that a call site reaches through a vtable holding `fns`: each entry is the
indirect call through the entry's function pointer. -/
def CVTable.dispatch (t : AllocTables Tgt) (fns : VTableFns) : CVTable Tgt where
  alloc c n k ra := t.alloc.call fns.alloc (c, n, k, ra)
  resize c s k n ra := t.resize.call fns.resize (c, s, k, n, ra)
  remap c s k n ra := t.remap.call fns.remap (c, s, k, n, ra)
  free c s k ra := t.free.call fns.free (c, s, k, ra)

/-- The vtable `fns` selects the entries of `impl` in the program's tables. -/
structure Selects (t : AllocTables Tgt) (fns : VTableFns) (impl : CVTable Tgt) : Prop where
  alloc : t.alloc.Sel fns.alloc fun a => impl.alloc a.1 a.2.1 a.2.2.1 a.2.2.2
  resize : t.resize.Sel fns.resize fun a => impl.resize a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
  remap : t.remap.Sel fns.remap fun a => impl.remap a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
  free : t.free.Sel fns.free fun a => impl.free a.1 a.2.1 a.2.2.1 a.2.2.2

/-- **The dispatch through a vtable meets the specification of the implementation it selects.** -/
theorem CAllocSpec.dispatch {t : AllocTables Tgt} {fns : VTableFns} {impl : CVTable Tgt}
    {ctx : Ptr} {I : FAllocInv} (hs : Selects t fns impl) (h : CAllocSpec impl ctx I) :
    CAllocSpec (CVTable.dispatch t fns) ctx I := by
  refine CAllocSpec.of_ctriples (fun len k ra h1 h2 h3 => ?_) (fun s k n ra bs h1 h2 h3 h4 h5 => ?_)
    (fun s k n ra bs h1 h2 h3 h4 h5 => ?_) fun s k ra bs h1 h2 h3 => ?_
  · show CTriple _ (t.alloc.call _ _) _
    rw [Table.call_of_sel hs.alloc]; exact h.alloc len k ra h1 h2 h3
  · show CTriple _ (t.resize.call _ _) _
    rw [Table.call_of_sel hs.resize]; exact h.resize s k n ra bs h1 h2 h3 h4 h5
  · show CTriple _ (t.remap.call _ _) _
    rw [Table.call_of_sel hs.remap]; exact h.remap s k n ra bs h1 h2 h3 h4 h5
  · show CTriple _ (t.free.call _ _) _
    rw [Table.call_of_sel hs.free]; exact h.free s k ra bs h1 h2 h3

/-- The four entries of a `std.mem.Allocator.VTable` in field order, for `vtR`. -/
def VTableFns.toList (fns : VTableFns) : List Ptr := [fns.alloc, fns.resize, fns.remap, fns.free]

end Full
end Zig
