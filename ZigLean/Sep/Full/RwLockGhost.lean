import ZigLean.Sep.Full.RwLockBase

/-!
# The reader/writer lock over a product ghost value

`FRw.Base.fits` gives the reader/writer protocol to every client whose ghost value, locks,
condition and semaphore satisfy the laws of the places next to each other. This file is the
instance every client can take, as `FLock.prod` is for one lock: the ghost value
`FLG2 × RwX Xc` (the two mutexes' places and held resources and the common part, `FLG2`; the
thread's places in the rwlock's, the condition's and the semaphore's code and the client's part,
`RwX`), for a reader/writer lock at byte `o` of block `b` in the layout of `Io.RwLock` (the state
word at `o`, the semaphore at `o + 8`: its count at `o + 8`, its mutex at `o + 16`, its
condition's state and epoch at `o + 20` and `o + 24`; the outer mutex at `o + 32`) that protects
any resource `R` of the client parts.

- `RwProd.M`, `RwProd.L`: the outer mutex (`FLock.prodA`; it protects nothing, and its holder may
  sleep at the semaphore's mutex and at the epoch) and the semaphore's mutex (`FLock.prodB`; the
  count and the pool).
- `RwProd.C`, `RwProd.S`, `RwProd.W`: the condition, the semaphore (count `1` and the pool `R`
  exactly while the resource is posted, `RwPosted`; only the writer at `ww` waits) and the
  reader/writer lock.
- `RwProd.fits`: `FRw.Fits` for every protocol whose invariant is the two-lock product at
  `FRw.Base` (`FRw.Base.fits`; the laws of the places hold by `rfl`), with the program's own
  facts `E` (`FClient`: its threads, the bytes every thread reads). The client gives where an
  ended or joining thread is, that `R` has no byte of the condition's words, and that its
  read-shared bytes are none of the bytes the lock's code changes.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-- A thread's places in the rwlock's, the condition's and the semaphore's code, and the client's
part. -/
structure RwX (Xc : Type) where
  w : RwPh := .out
  c : CPh := .out
  sp : SPh := .out
  x : Xc

namespace RwProd

variable {Xc : Type}

/-- The ghost value (module doc). -/
abbrev Gh (Xc : Type) := FLG2 × RwX Xc

/-- What the semaphore's count and pool read: the rwlock's place and the client's part. -/
abbrev sx (g : RwX Xc) : RwPh × Xc := (g.w, g.x)

open Classical in
/-- The count: `1` exactly while the resource is posted. -/
noncomputable def pv (Y : ThreadId → RwPh × Xc) : BitVec 64 :=
  if RwPosted Prod.fst Y then 1 else 0

open Classical in
/-- The pool: the resource exactly while it is posted. -/
noncomputable def Pool (R : (ThreadId → Xc) → FAssn) (Y : ThreadId → RwPh × Xc) : FAssn :=
  if RwPosted Prod.fst Y then R fun u => (Y u).2 else emp

/-- The rwlock's address. -/
def p (b o : Nat) : Ptr := ⟨some b, (o : Int)⟩

/-- The semaphore's mutex's resource: the count and the pool. -/
noncomputable def RL (b o : Nat) (R : (ThreadId → Xc) → FAssn) (Y : ThreadId → RwX Xc) : FAssn :=
  up (pts ((p b o).add 8) 8 (pv fun u => sx (Y u))) ⋆ Pool R fun u => sx (Y u)

/-- The outer mutex: it protects nothing; its holder may sleep at the semaphore's mutex and at
the epoch. -/
abbrev M (b o : Nat) : FLock (Gh Xc) :=
  FLock.prodA b (o + 32) (fun _ => emp)
    (fun q => q = ⟨some b, ((o + 16 : Nat) : Int)⟩ ∨ q = ⟨some b, ((o + 24 : Nat) : Int)⟩)

/-- The semaphore's mutex. -/
noncomputable abbrev L (b o : Nat) (R : (ThreadId → Xc) → FAssn) : FLock (Gh Xc) :=
  FLock.prodB b (o + 16) (RL b o R)

/-- The condition: its place is `RwX.c`; the threads at `pst` signal. -/
def C (b o : Nat) : FCond (Gh Xc) where
  S := { b := b, o := o + 20 }
  Ep := { b := b, o := o + 24 }
  ep_b := rfl
  ep_o := rfl
  ph g := g.2.c
  set g q := (g.1, { g.2 with c := q })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  sx g := g.2.sp.isPst = true
  sx_set _ _ := Iff.rfl

/-- The semaphore: its place is `RwX.sp`; only the writer at `ww` waits. -/
noncomputable def S (b o : Nat) (R : (ThreadId → Xc) → FAssn) :
    FSem (Gh Xc) (RwPh × Xc) (L b o R) (C b o) where
  ph g := g.2.sp
  set g s := (g.1, { g.2 with sp := s })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  p := (p b o).add 8
  ptr_l := by
    show (⟨some b, ((o + 16 : Nat) : Int)⟩ : Ptr) = ⟨some b, (o : Int) + 8 + 8⟩
    exact congrArg (Ptr.mk (some b)) (by omega)
  ptr_c := by
    show (⟨some b, ((o + 20 : Nat) : Int)⟩ : Ptr) = ⟨some b, (o : Int) + 8 + 12⟩
    exact congrArg (Ptr.mk (some b)) (by omega)
  off := by show 8 ≤ o + 16; omega
  x g := sx g.2
  pv := pv
  Pool := Pool R
  R_eq _ := rfl
  x_l _ _ _ := rfl
  x_part _ _ := rfl
  x_c _ _ := rfl
  x_s _ _ := rfl
  wx g := g.2.w = .ww
  wx_l _ _ _ := Iff.rfl
  wx_part _ _ := Iff.rfl
  wx_c _ _ := Iff.rfl
  wx_s _ _ := Iff.rfl
  cph_set _ _ := rfl
  ph_cset _ _ := rfl
  set_cset _ _ _ := rfl
  sx_iff _ := Iff.rfl

/-- The reader/writer lock: its place is `RwX.w`, the client's part `RwX.x`. -/
noncomputable def W (b o : Nat) (R : (ThreadId → Xc) → FAssn)
    (R_plain : ∀ xs r, R xs r → r.know = Know.none ∧ r.gh = Ghost.unit)
    (R_fixed : ∀ xs, (R xs).FixedDom) :
    FRw (Gh Xc) Xc (RwPh × Xc) (M b o) (L b o R) (C b o) (S b o R) where
  ph g := g.2.w
  set g a := (g.1, { g.2 with w := a })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  p := p b o
  st := { b := b, o := o }
  ptr_st := rfl
  ptr_s := rfl
  ptr_m := by
    show (⟨some b, ((o + 32 : Nat) : Int)⟩ : Ptr) = ⟨some b, (o : Int) + 32⟩
    exact congrArg (Ptr.mk (some b)) (by omega)
  pair := FLock.prodPair (.inr (.inr (by show o + 16 + 4 ≤ o + 32; omega)))
  mR _ := rfl
  x g := g.2.x
  R := R
  R_plain := R_plain
  R_fixed := R_fixed
  x_set _ _ := rfl
  x_m _ _ _ := rfl
  x_part _ _ := rfl
  x_l _ _ _ := rfl
  x_c _ _ := rfl
  x_s _ _ := rfl
  lph _ _ := rfl
  lheld _ _ := rfl
  ph_l _ _ _ := rfl
  set_l _ _ _ _ := rfl
  ph_sp _ _ := rfl
  sp_ph _ _ := rfl
  set_sp _ _ _ := rfl
  cnt_posted _ h := ite_eq_left h
  cnt_idle _ h := ite_eq_right h
  pool_posted _ h := ite_eq_left h
  pool_idle _ h := ite_eq_right h
  wx_iff _ := Iff.rfl

/-- The threads that run the semaphore's mutex's code: out of the condition's busy code and out
of the semaphore's `pst`. -/
def okS (g : Gh Xc) : Prop := g.2.c.busy = false ∧ (g.2.sp = .out ∨ g.2.sp = .wt)

variable {b o : Nat} {R : (ThreadId → Xc) → FAssn}
  {R_plain : ∀ xs r, R xs r → r.know = Know.none ∧ r.gh = Ghost.unit}
  {R_fixed : ∀ xs, (R xs).FixedDom} {E : FClient Xc} {Sz : Nat} {K : BlockKind} {Tgt : Type}
  {P : Proto Tgt (Gh Xc)}

/-- **The reader/writer protocol over the product ghost value** (module doc): `FRw.Base.fits`
with the laws of the places by `rfl`. -/
theorem fits
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, (M b o).Inv G rX m ∧
      FLock.Pair.U (L b o R) ((W b o R R_plain R_fixed).Base E Sz K) G rX m)
    (fin : ∀ g, P.fin g → g.1.phA = .gone ∧ g.1.phB = .gone ∧ g.2.w = .out ∧ g.2.c = .out ∧
      g.2.sp = .out)
    (joins : ∀ g, P.joins g → g.1.phA = .out ∧ g.1.phB = .out ∧ g.2.w = .out ∧ g.2.c = .out ∧
      g.2.sp = .out)
    (hRoff : ∀ xs r l, R xs r → ((C b o (Xc := Xc)).S.In l ∨ (C b o (Xc := Xc)).Ep.In l) →
      r.heap l = none)
    (hIo : ∀ r l, E.Io r → (W b o R R_plain R_fixed).Lk l → r.heap l = none) :
    (W b o R R_plain R_fixed).Fits P
      (FLock.Pair.U (L b o R) ((W b o R R_plain R_fixed).Base E Sz K))
      (FLock.Pair.U (M b o) ((W b o R R_plain R_fixed).Base E Sz K)) (fun _ => True) okS := by
  have hpl : ∀ g : Gh Xc, g.2.c = .out → g.2.sp = .out →
      (S b o R).place.ph g = (.out, .out) := fun g hc hs => Prod.ext hc hs
  refine FRw.Base.fits inv (fun g h => (fin g h).1) (fun g h => (joins g h).1)
    (fun g h => (fin g h).2.1) (fun g h => (joins g h).2.1)
    (fun g h => ⟨(fin g h).2.2.1, hpl g (fin g h).2.2.2.1 (fin g h).2.2.2.2⟩)
    (fun g h => ⟨(joins g h).2.2.1, hpl g (joins g h).2.2.2.1 (joins g h).2.2.2.2⟩)
    (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) (fun _ h => h.1) (fun _ h => h.2)
    (fun _ _ _ hp hq => ⟨fun _ => hq, fun _ => hp⟩)
    (.inl rfl) (.inr rfl) (fun _ h => h) (fun _ h => h) hRoff hIo
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun G t q r h => ?_)
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)
  have e : (fun u => (upd G t ((S b o R).place.set (G t) q) u).2.w) = fun u => (G u).2.w := by
    funext u; unfold upd; split
    · rename_i e; subst e; rfl
    · rfl
  have e' : (fun u => (upd G t ((S b o R).place.set (G t) q) u).2.x) = fun u => (G u).2.x := by
    funext u; unfold upd; split
    · rename_i e; subst e; rfl
    · rfl
  have e2 : (fun u => sx (upd G t ((S b o R).place.set (G t) q) u).2) = fun u => sx (G u).2 :=
    funext fun u => Prod.ext (congrFun e u) (congrFun e' u)
  show RL b o R (fun u => (upd G t ((S b o R).place.set (G t) q) u).2) r
  unfold RL
  rw [e2]
  exact h

end RwProd

end Full
end Zig
