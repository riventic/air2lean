import ZigLean.Sep.AllocSpec.Wrappers

/-!
# The vtable dispatch of a translated `std.mem.Allocator`

A translated wrapper calls a vtable entry the way the compiler does: it loads the function
pointer from the `VTable` (a `const` global) at `vtable + 8 * i` and calls it. The translator
emits the indirect call as a test against each function the program can reach, and `.illegal`
for any other pointer. `dispatch impl fns vtp` is that: the `RawVTable` whose entries load the
pointer at `vtp` and, if it is the function `fns.*` of the allocator `impl`, run `impl`.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig

/-- The function pointers of the four entries of one allocator's `VTable`. -/
structure VTableFns where
  alloc : Ptr
  resize : Ptr
  remap : Ptr
  free : Ptr

/-- The entries of the vtable at `vtp`, dispatched to `impl` (module doc). -/
def dispatch (impl : RawVTable) (fns : VTableFns) (vtp : Ptr) : RawVTable where
  alloc ctx len k ra := load Ptr 8 (vtp.add 0) >>= fun f =>
    if f = fns.alloc then impl.alloc ctx len k ra else throw .illegal
  resize ctx s k n ra := load Ptr 8 (vtp.add 8) >>= fun f =>
    if f = fns.resize then impl.resize ctx s k n ra else throw .illegal
  remap ctx s k n ra := load Ptr 8 (vtp.add 16) >>= fun f =>
    if f = fns.remap then impl.remap ctx s k n ra else throw .illegal
  free ctx s k ra := load Ptr 8 (vtp.add 24) >>= fun f =>
    if f = fns.free then impl.free ctx s k ra else throw .illegal

open Assn

/-- The vtable at `vtp` holds `fns` (read-only: it is a `const` global). -/
def vtR (vtp : Ptr) (fns : VTableFns) : Assn :=
  ptsR (vtp.add 0) 8 fns.alloc ∗ (ptsR (vtp.add 8) 8 fns.resize ∗
    (ptsR (vtp.add 16) 8 fns.remap ∗ ptsR (vtp.add 24) 8 fns.free))

/-- The invariant of an allocator reached through its vtable: its own invariant and the vtable. -/
def AllocInv.withVTable (I : AllocInv) (vtp : Ptr) (fns : VTableFns) : AllocInv :=
  { I with own := I.own ∗ vtR vtp fns }

variable {L : Logic}

/-- Load a function pointer from the vtable and call it if it is `v`. -/
theorem load_dispatch {α : Type} {R : Assn} {p v : Ptr} {c : MemM α} {Q : α → Assn}
    (hc : L.T (ptsR p 8 v ∗ R) c Q) :
    L.T (ptsR p 8 v ∗ R) (load Ptr 8 p >>= fun f => if f = v then c else throw .illegal) Q := by
  refine L.bind (L.frame (L.ofTotal (ptsR_load (p := p) (a := 8) (v := v) (by decide)))) fun f => ?_
  refine L.pre (L.lift fun hf => ?_) fun h hp => sep_assoc hp
  subst hf
  rw [if_pos rfl]
  exact hc

/-- Run an entry of `impl` with the vtable framed: the dispatch through the vtable. -/
theorem dispatch_entry {α : Type} {P : Assn} {p v : Ptr} {R R' : Assn} {c : MemM α}
    {Q Q' : α → Assn} (hc : L.T P c Q) (hpre : ∀ h, (ptsR p 8 v ∗ R) h → (P ∗ R') h)
    (hpost : ∀ r h, (Q r ∗ R') h → Q' r h) :
    L.T (ptsR p 8 v ∗ R) (load Ptr 8 p >>= fun f => if f = v then c else throw .illegal) Q' :=
  load_dispatch (L.conseq (L.frame (R := R') hc) hpre hpost)

theorem withVTable_own {I : AllocInv} {vtp : Ptr} {fns : VTableFns} :
    (I.withVTable vtp fns).own = (I.own ∗ vtR vtp fns) := rfl

theorem withVTable_tok {I : AllocInv} {vtp : Ptr} {fns : VTableFns} :
    (I.withVTable vtp fns).tok = I.tok := rfl

theorem withVTable_granted {I : AllocInv} {vtp : Ptr} {fns : VTableFns} {p : Ptr} {k : Nat}
    {bs : Array Byte} : granted (I.withVTable vtp fns) p k bs = granted I p k bs := rfl

/-- An allocator called through the vtable at `vtp` satisfies the specification of the
allocator itself, with the vtable added to the invariant. -/
theorem dispatch_allocSpec {impl : RawVTable} {fns : VTableFns} {vtp ctx : Ptr} {I : AllocInv}
    (h : AllocSpec L impl ctx I) :
    AllocSpec L (dispatch impl fns vtp) ctx (I.withVTable vtp fns) where
  alloc len k ra h1 h2 h3 := by
    refine L.pre (dispatch_entry (R := ptsR (vtp.add 8) 8 fns.resize ∗
      (ptsR (vtp.add 16) 8 fns.remap ∗ (ptsR (vtp.add 24) 8 fns.free ∗ I.own)))
      (R' := vtR vtp fns) (h.alloc len k ra h1 h2 h3) (fun hh hp => by unfold vtR; sep_from hp)
      fun r hh hp => ?_) fun hh hp => by rw [withVTable_own] at hp; unfold vtR at hp; sep_from hp
    cases r with
    | none => exact hp
    | some p =>
      show ((I.own ∗ vtR vtp fns) ∗ Assn.ex fun bs => ⌜bs.size = len.toNat⌝ ∗ granted I p k bs) hh
      simp only [allocPost] at hp; sep_from hp
  resize s k n ra bs h1 h2 h3 h4 h5 := by
    refine L.pre (dispatch_entry (R := ptsR (vtp.add 0) 8 fns.alloc ∗
      (ptsR (vtp.add 16) 8 fns.remap ∗ (ptsR (vtp.add 24) 8 fns.free ∗ (I.own ∗ granted I s.ptr k bs))))
      (R' := vtR vtp fns) (h.resize s k n ra bs h1 h2 h3 h4 h5)
      (fun hh hp => by unfold vtR; sep_from hp) fun r hh hp => ?_)
      fun hh hp => by rw [withVTable_own, withVTable_granted] at hp; unfold vtR at hp; sep_from hp
    cases r with
    | true =>
      show ((I.own ∗ vtR vtp fns) ∗ Assn.ex fun bs' => ⌜bs'.size = n.toNat ∧ keepsPrefix bs bs'⌝ ∗
        granted I s.ptr k bs') hh
      simp only [resizePost] at hp; sep_from hp
    | false =>
      show ((I.own ∗ vtR vtp fns) ∗ granted I s.ptr k bs) hh
      simp only [resizePost] at hp; sep_from hp
  remap s k n ra bs h1 h2 h3 h4 h5 := by
    refine L.pre (dispatch_entry (R := ptsR (vtp.add 0) 8 fns.alloc ∗
      (ptsR (vtp.add 8) 8 fns.resize ∗ (ptsR (vtp.add 24) 8 fns.free ∗ (I.own ∗ granted I s.ptr k bs))))
      (R' := vtR vtp fns) (h.remap s k n ra bs h1 h2 h3 h4 h5)
      (fun hh hp => by unfold vtR; sep_from hp) fun r hh hp => ?_)
      fun hh hp => by rw [withVTable_own, withVTable_granted] at hp; unfold vtR at hp; sep_from hp
    cases r with
    | none =>
      show ((I.own ∗ vtR vtp fns) ∗ granted I s.ptr k bs) hh
      simp only [remapPost] at hp; sep_from hp
    | some q =>
      show ((I.own ∗ vtR vtp fns) ∗ Assn.ex fun bs' => ⌜bs'.size = n.toNat ∧ keepsPrefix bs bs'⌝ ∗
        granted I q k bs') hh
      simp only [remapPost] at hp; sep_from hp
  free s k ra bs h1 h2 h3 := by
    refine L.pre (dispatch_entry (R := ptsR (vtp.add 0) 8 fns.alloc ∗
      (ptsR (vtp.add 8) 8 fns.resize ∗ (ptsR (vtp.add 16) 8 fns.remap ∗ (I.own ∗ granted I s.ptr k bs))))
      (R' := vtR vtp fns) (h.free s k ra bs h1 h2 h3)
      (fun hh hp => by unfold vtR; sep_from hp) fun r hh hp => hp)
      fun hh hp => by rw [withVTable_own, withVTable_granted] at hp; unfold vtR at hp; sep_from hp

end Zig
