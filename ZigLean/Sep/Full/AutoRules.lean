import ZigLean.Sep.Full.AutoAttr
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.AllocSpec.Norm

/-!
# The rule library of the full-state symbolic executor (`fsym`, `docs/proof-automation.md`)

General lemmas that `fsym` (`ZigLean/Sep/Full/Auto.lean`) applies; nothing here is about one std
module.

* **Structural steps** over any `FLogic` (`FLogic.total`: `FTotalTriple`, `FLogic.partial`:
  `FTriple`): a step by a total rule on a framed part (`step`) or on the whole precondition
  (`stepAll`), a return through a frame-preserving update (`ret`), existentials and facts of the
  precondition (`ex_sep`, `lift_sep`).
* **Step rules** (`@[fsym]`): pointer operations from the providers of `Ops.lean`, loads and
  stores of `pts`, the fields of a stored slice, the overflow-checked arithmetic of generated code.
* **Providers from atoms**: `AddrOf`/`Reaches` of a precondition from one of its atoms
  (`known`, `bshare`, an owned `pts` or region), up to associativity and commutativity of `⋆`.
* **`junk`**: bytes an allocator gave up (padding, leaked frees); an `up` part is absorbed.
* **`fsym_norm`** and **`fsym_arith`**: the simp sets for programs and side goals.
-/

namespace Zig.Full.Auto

open FAssn

/-! ## Structural steps over any `FLogic` -/

section Steps

variable (L : FLogic) {α β γ : Type} {P P' P₀ R : FAssn} {Q : β → FAssn} {c : MemM β}

theorem pre (h : ∀ r, P r → P' r) (t : L.T P' c Q) : L.T P c Q := L.pre t h

theorem pre_eq (h : P = P') (t : L.T P' c Q) : L.T P c Q := h ▸ t

theorem bind_pure (t : L.T P (c >>= pure) Q) : L.T P c Q := by
  simpa only [_root_.bind_pure] using t

/-- A command proved by a total rule on the part `P₀`, framed by `R`. -/
theorem step {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTotalTriple P₀ c Q₀)
    (k : ∀ v, L.T (Q₀ v ⋆ R) (f v) Q) : L.T (P₀ ⋆ R) (c >>= f) Q :=
  L.bind (L.frame (L.ofTotal r)) k

/-- A command proved by a total rule on the whole precondition. -/
theorem stepAll {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : FTotalTriple P c Q₀)
    (k : ∀ v, L.T (Q₀ v) (f v) Q) : L.T P (c >>= f) Q :=
  L.bind (L.ofTotal r) k

/-- A command proved by a rule of the logic itself (a partial rule in the partial logic). -/
theorem stepL {c : MemM α} {f : α → MemM β} {Q₀ : α → FAssn} (r : L.T P₀ c Q₀)
    (k : ∀ v, L.T (Q₀ v ⋆ R) (f v) Q) : L.T (P₀ ⋆ R) (c >>= f) Q :=
  L.bind (L.frame r) k

/-- **A return**, after a frame-preserving update into the postcondition. -/
theorem ret {v : β} (h : EUpd P (Q v)) : L.T P (pure v) Q :=
  L.ofTotal (FTotalTriple.eupd h (FTotalTriple.ret v))

theorem ex_sep {F : γ → FAssn} (t : ∀ x, L.T (F x ⋆ R) c Q) : L.T (FAssn.ex F ⋆ R) c Q :=
  L.pre (L.ex (P := fun x => F x ⋆ R) t) fun _ h => sep_ex.mp h

theorem lift_sep {φ : Prop} (t : φ → L.T R c Q) : L.T (⟪φ⟫ ⋆ R) c Q := L.lift t

theorem of_false (h : False) : L.T P c Q := h.elim

end Steps

/-! ## Providers from atoms -/

section Providers

variable {b : BlockId} {A k : Nat} {P X R : FAssn}

theorem AddrOf.of_atom (h : AddrOf b A X) (e : P = (X ⋆ R)) : AddrOf b A P := e ▸ h.sepL

theorem Reaches.of_atom (h : Reaches b k X) (e : P = (X ⋆ R)) : Reaches b k P := e ▸ h.sepL

/-- The cells of a legacy assertion are the resource's. -/
theorem up_cell {Y : Assn} {r : Res} (hr : up Y r) {l : Loc} {c : Cell} (hc : r.heap.erase l = some c) :
    ∃ fc, r.heap l = some fc ∧ fc.cell = c := erase_cell hc

/-- A nonempty owned byte range at `p` (in block `b`): the block's address. -/
theorem AddrOf.bytes {Y : Assn} {p : Ptr} (hpb : p.block = some b)
    (hy : ∀ h, Y h → ∃ S K bs, 0 < bs.size ∧ bytesAt p A S K bs h) : AddrOf b A (up Y) :=
  AddrOf.owned fun r hr => by
    obtain ⟨S, K, bs, hpos, hb⟩ := hy _ hr.1
    obtain ⟨b', hb', h0, hl⟩ := id hb
    rw [hpb] at hb'; cases hb'
    have hc : r.heap.erase (b, p.off.toNat + (bs.size - 1)) = some ⟨bs[bs.size - 1]!, A, S, K⟩ := by
      rw [hl]; simp only [true_and]; rw [if_pos ⟨by omega, by omega⟩]; congr 3; omega
    obtain ⟨fc, hfc, he⟩ := erase_cell hc
    exact ⟨_, fc, hfc, by rw [he]⟩

/-- A nonempty owned byte range at `p` (in block `b`): the block reaches its end. -/
theorem Reaches.bytes {Y : Assn} {p : Ptr} {n : Nat} (hpb : p.block = some b)
    (hy : ∀ h, Y h → ∃ A S K bs, 0 < bs.size ∧ n ≤ bs.size ∧ bytesAt p A S K bs h) :
    Reaches b (p.off.toNat + n) (up Y) := fun m r rF hh hr => by
  obtain ⟨A, S, K, bs, hpos, hn, hb⟩ := hy _ hr.1
  obtain ⟨b', hb', h0, c, hc⟩ := bytesAt_ownsAt hb hpos
  rw [hpb] at hb'; cases hb'
  obtain ⟨fc, hfc, -⟩ := erase_cell hc
  obtain ⟨blk, hblk, -, hj, -⟩ := hh.block hfc
  exact ⟨blk, hblk, by omega⟩

/-- A typed value at `p` owns its bytes: its block reaches one past it. -/
theorem Reaches.pts {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} (hpb : p.block = some b)
    (hn : 0 < Enc.size T) : Reaches b (p.off.toNat + Enc.size T) (up (Zig.pts p a v)) :=
  Reaches.bytes hpb fun _ hp => by
    obtain ⟨A, S, K, bs, -, hs, -, hb, -⟩ := hp
    exact ⟨A, S, K, bs, by omega, by omega, hb⟩

/-- A nonempty region owns its bytes: its block reaches its end. -/
theorem Reaches.region {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    (hpb : p.block = some b) (hpos : 0 < bs.size) :
    Reaches b (p.off.toNat + bs.size) (up (regionIn p A S K a bs)) :=
  Reaches.bytes hpb fun _ hr => ⟨A, S, K, bs, hpos, Nat.le_refl _, hr.2.2⟩

/-- A nonempty region: its block's address. -/
theorem AddrOf.region {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    (hpb : p.block = some b) (hpos : 0 < bs.size) : AddrOf b A (up (regionIn p A S K a bs)) :=
  AddrOf.bytes hpb fun _ hr => ⟨S, K, bs, hpos, hr.2.2⟩

end Providers

/-! ## The fields of a stored slice -/

theorem result_bind_eq_pure {α β : Type} {x : Result α} {f : α → Result β} {b : β}
    (h : x >>= f = pure b) : ∃ a, x = pure a ∧ f a = pure b := by
  have : ∀ y : Option (Except Error α), (ExceptT.mk y : Result α) >>= f = pure b →
      ∃ a, y = some (.ok a) ∧ f a = pure b := by
    intro y hy
    rcases y with _ | e | a
    · cases hy
    · cases hy
    · exact ⟨a, rfl, hy⟩
  obtain ⟨a, ha, hf⟩ := this x h
  exact ⟨a, ha, hf⟩

theorem pts_slice_parts {q : Ptr} {s : Slice} {h : Heap} (hp : Zig.pts q 8 s h) :
    ∃ A S K bs, (A + q.off.toNat) % 8 = 0 ∧ bs.size = 16 ∧
      Enc.decode (bs.extract 0 8) = (pure s.ptr : Result Ptr) ∧
      Enc.decode (bs.extract 8 16) = (pure s.len : Result (BitVec 64)) ∧ bytesAt q A S K bs h := by
  obtain ⟨A, S, K, bs, ha, hs, hv, hb, -⟩ := hp
  change (do pure ⟨← Enc.decode (bs.extract 0 8), ← Enc.decode (bs.extract 8 16)⟩ : Result Slice) =
    pure s at hv
  obtain ⟨p, h1, hv⟩ := result_bind_eq_pure hv
  obtain ⟨l, h2, hv⟩ := result_bind_eq_pure hv
  have : (⟨p, l⟩ : Slice) = s := by
    have := congrArg (fun r : Result Slice => r.run) hv
    simpa [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using this
  subst this
  exact ⟨A, S, K, bs, ha, hs, h1, h2, hb⟩

theorem pts_slice_field_load {T : Type} [Enc T] {q : Ptr} {s : Slice} {o : Nat} {v : T}
    (hsz : Enc.size T = 8) (ho : o = 0 ∨ o = 8)
    (hv : ∀ bs : Array Byte, Enc.decode (bs.extract 0 8) = (pure s.ptr : Result Ptr) →
      Enc.decode (bs.extract 8 16) = (pure s.len : Result (BitVec 64)) →
      Enc.decode (bs.extract o (o + 8)) = (pure v : Result T)) :
    TotalTriple (Zig.pts q 8 s) (load T 8 (q.add o)) (fun r => ⌜r = v⌝ ∗ Zig.pts q 8 s) := by
  intro m hP hF hd hm hp hst
  obtain ⟨A, S, K, bs, ha, hs, h1, h2, hb⟩ := pts_slice_parts hp
  have hao : (A + q.off.toNat + o) % 8 = 0 := by rcases ho with rfl | rfl <;> omega
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (q := q.add o) (k := o) (n := Enc.size T) (a := 8) hb hm rfl
      (by omega) (by rcases ho with rfl | rfl <;> omega) hao
  have hv' : Enc.decode (blk.bytes.extract (q.off.toNat + o) (q.off.toNat + o + Enc.size T)) =
      pure v := by rw [hx, hsz]; exact hv bs h1 h2
  refine ⟨v, _, hP, load_run hacc hv' (noRace_of_singleThread hst.single _ _ _ _), hd, ?_,
    Zig.sep_lift.mpr ⟨rfl, hp⟩, hst.recordAt _ _ _ _⟩
  funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

theorem slice_field {T : Type} [Enc T] {q : Ptr} {s : Slice} {o : Nat} {v : T}
    (hsz : Enc.size T = 8) (ho : o = 0 ∨ o = 8)
    (hv : ∀ bs : Array Byte, Enc.decode (bs.extract 0 8) = (pure s.ptr : Result Ptr) →
      Enc.decode (bs.extract 8 16) = (pure s.len : Result (BitVec 64)) →
      Enc.decode (bs.extract o (o + 8)) = (pure v : Result T)) :
    FTotalTriple (up (Zig.pts q 8 s)) (load T 8 (q.add o)) (fun r => ⟪r = v⟫ ⋆ up (Zig.pts q 8 s)) :=
  (FTotalTriple.ofTotal_up (pts_slice_field_load hsz ho hv) (Tame.load T 8 _) (SizeFree.pts q 8 s)
    (Keeps.load T 8 _)).post fun _ _ h => sep_lift.mpr (up_lift.mp h)

/-- **The pointer field** of a stored slice. -/
@[fsym] theorem load_slice_ptr {q : Ptr} {s : Slice} :
    FTotalTriple (up (Zig.pts q 8 s)) (load Ptr 8 q) (fun r => ⟪r = s.ptr⟫ ⋆ up (Zig.pts q 8 s)) := by
  have t := slice_field (T := Ptr) (q := q) (s := s) (o := 0) (v := s.ptr) rfl (Or.inl rfl)
    (fun bs h1 _ => by simpa using h1)
  push_cast at t
  simpa only [Norm.add_zero_ptr] using t

/-- **The length field** of a stored slice. -/
@[fsym] theorem load_slice_len {q : Ptr} {s : Slice} :
    FTotalTriple (up (Zig.pts q 8 s)) (load (BitVec 64) 8 (q.add 8))
      (fun r => ⟪r = s.len⟫ ⋆ up (Zig.pts q 8 s)) := by
  have t := slice_field (T := BitVec 64) (q := q) (s := s) (o := 8) (v := s.len) rfl (Or.inr rfl)
    (fun bs _ h2 => h2)
  push_cast at t
  exact t

/-! ## Memory and pointer rules -/

attribute [fsym] FTotalTriple.load FTotalTriple.store FTotalTriple.ptrAddr_of
  FTotalTriple.checkAlign_of FTotalTriple.ptrEqAddr_of FTotalTriple.ptrProject_elem_of
  FTotalTriple.ptrProject_of

/-! ## Overflow-checked arithmetic -/

section Arith

variable {w : Nat} {P : FAssn}

theorem read_pure {α : Type} {v : α} : FTotalTriple P (pure v : MemM α) (fun r => ⟪r = v⟫ ⋆ P) :=
  (FTotalTriple.ret (Q := fun r => ⟪r = v⟫ ⋆ P) v).pre fun _ h => sep_lift.mpr ⟨rfl, h⟩

/-- A checked unsigned `+` that does not overflow. -/
@[fsym] theorem add_step {a b : BitVec w} (h : a.toNat + b.toNat < 2 ^ w) :
    FTotalTriple P (StateT.lift (Zig.add false a b) : MemM (BitVec w)) (fun r => ⟪r = a + b⟫ ⋆ P) := by
  have e : Zig.add false a b = pure (a + b) := by
    simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by simp; omega)]
  rw [e]; exact read_pure

/-- A checked unsigned `-` that does not overflow. -/
@[fsym] theorem sub_step {a b : BitVec w} (h : b.toNat ≤ a.toNat) :
    FTotalTriple P (StateT.lift (Zig.sub false a b) : MemM (BitVec w)) (fun r => ⟪r = a - b⟫ ⋆ P) := by
  have e : Zig.sub false a b = pure (a - b) := by
    simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by simp; omega)]
  rw [e]; exact read_pure

end Arith

/-! ## Junk -/

/-- Bytes that an allocator gave up (padding, the bytes of frees it cannot reuse). -/
def junk : FAssn := FAssn.ex fun h : Heap => up (fun h' => h' = h)

attribute [fsym_atom] junk

theorem junk_absorb {X : Assn} {r : Res} (h : (up X ⋆ junk) r) : junk r := by
  obtain ⟨r₁, r₂, hd, rfl, h1, ⟨hj, h2⟩⟩ := h
  refine ⟨r₁.heap.erase ∪ hj, ?_⟩
  obtain ⟨-, k1, g1⟩ := h1
  obtain ⟨e2, k2, g2⟩ := h2
  refine ⟨?_, by simp [k1, k2, Know.union_none], by simp [g1, g2]⟩
  show (FHeap.union r₁.heap r₂.heap).erase = _
  rw [← e2]; exact FHeap.erase_union _ _

theorem junk_emp {r : Res} (h : emp r) : junk r := ⟨Heap.empty, Full.up_emp.mpr h⟩

/-! ## Entailment combinators (the proofs `fsym` builds for returns) -/

section Imp

variable {P X Y A B A' B' : FAssn}

theorem imp_refl : ∀ r, P r → P r := fun _ h => h

theorem imp_sep (ha : ∀ r, A' r → A r) (hb : ∀ r, B' r → B r) : ∀ r, (A' ⋆ B') r → (A ⋆ B) r :=
  fun _ h => sep_mono ha hb h

theorem imp_ex {γ : Type} {F : γ → FAssn} (w : γ) (h : ∀ r, X r → F w r) : ∀ r, X r → FAssn.ex F r :=
  fun r hx => ⟨w, h r hx⟩

theorem imp_trans (h₁ : ∀ r, X r → Y r) (h₂ : ∀ r, Y r → P r) : ∀ r, X r → P r :=
  fun r h => h₂ r (h₁ r h)

theorem imp_eq (e : X = Y) : ∀ r, X r → Y r := fun _ h => e ▸ h

theorem imp_lift {φ : Prop} (hφ : φ) (h : ∀ r, X r → Y r) : ∀ r, X r → (⟪φ⟫ ⋆ Y) r :=
  fun r hx => sep_lift.mpr ⟨hφ, h r hx⟩

theorem imp_junk_emp : ∀ r, emp r → junk r := fun _ h => junk_emp h

theorem imp_junk_up {Z : Assn} (h : ∀ r, X r → junk r) : ∀ r, (up Z ⋆ X) r → junk r :=
  fun _ hx => junk_absorb (sep_mono_right h hx)

theorem imp_junk_one {Z : Assn} : ∀ r, up Z r → junk r :=
  fun _ hx => junk_absorb (sep_emp.mpr hx |> sep_mono_right fun _ h => junk_emp h)

theorem imp_junk_junk (h : ∀ r, X r → junk r) : ∀ r, (junk ⋆ X) r → junk r := by
  intro r hx
  obtain ⟨r₁, r₂, hd, rfl, ⟨j1, h1⟩, h2⟩ := hx
  obtain ⟨j2, h2⟩ := h _ h2
  exact junk_absorb ⟨r₁, r₂, hd, rfl, h1, ⟨j2, h2⟩⟩

theorem eupd_of_imp (h : ∀ r, P r → X r) : EUpd P X := EUpd.of_imp h

/-- A local update, reordered: the planner's step. -/
theorem eupd_frame_ac {R P' : FAssn} (h : EUpd X Y) (e1 : P = (X ⋆ R)) (e2 : (Y ⋆ R) = P') :
    EUpd P P' := e1 ▸ e2 ▸ h.frame

theorem eupd_ac {P' : FAssn} (h : EUpd X Y) (e1 : P = X) (e2 : Y = P') : EUpd P P' := e1 ▸ e2 ▸ h

end Imp

/-! ## Regions and shares (the planner's local steps) -/

section Plan

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a a' : Nat} {bs bs' : Array Byte}

theorem up_region_split {k : Nat} (hk : k ≤ bs.size) (ha : (A + p.off.toNat + k) % a' = 0) :
    EUpd (up (regionIn p A S K a bs))
      (up (regionIn p A S K a (bs.extract 0 k)) ⋆ up (regionIn (p.add k) A S K a' (bs.extract k bs.size))) :=
  EUpd.of_imp fun _ h => Full.up_sep ⟨Region.regionIn_split h.1 hk ha, h.2⟩

theorem up_region_join :
    EUpd (up (regionIn p A S K a bs) ⋆ up (regionIn (p.add bs.size) A S K a' bs'))
      (up (regionIn p A S K a (bs ++ bs'))) :=
  EUpd.of_imp fun _ h => by
    have h' := Full.sep_up h
    exact ⟨Region.regionIn_join h'.1, h'.2⟩

theorem up_region_weaken (hd : a' ∣ a) :
    EUpd (up (regionIn p A S K a bs)) (up (regionIn p A S K a' bs)) :=
  EUpd.of_imp fun _ h => ⟨Region.regionIn_weaken h.1 hd, h.2⟩

variable {b : BlockId} {q : Frac} {k k' : Nat} {t : STag}

theorem share_halves : EUpd (bshare b q k t) (bshare b q.half k t ⋆ bshare b q.half k t) :=
  EUpd.of_imp fun _ h => (bshare_split (Frac.half_pos h.1) (Frac.half_pos h.1)).mp
    (by rw [Frac.half_add_half]; exact h)

theorem share_weaken (h : k' ≤ k) : EUpd (bshare b q k t) (bshare b q k' t) := EUpd.weaken h

theorem share_join {q₂ : Frac} {k₂ : Nat} :
    EUpd (bshare b q k t ⋆ bshare b q₂ k₂ t) (bshare b (q.add q₂) (Max.max k k₂) t) := EUpd.join

end Plan

theorem sep_emp_eq' (P : FAssn) : (P ⋆ emp) = P := funext fun _ => propext sep_emp
theorem emp_sep_eq' (P : FAssn) : (emp ⋆ P) = P := by rw [sep_comm_eq]; exact sep_emp_eq' P

theorem atom_eq {X Y : FAssn} (e : X = Y) : EUpd X Y := e ▸ EUpd.of_imp fun _ h => h

theorem ptr_ext' {p q : Ptr} (h1 : p.block = q.block) (h2 : p.off = q.off) : p = q := by
  cases p; cases q; simp_all

/-! ## Simp sets -/

theorem lift_bind {α β : Type} (x : Result α) (g : α → Result β) :
    (StateT.lift (x >>= g) : MemM β) = StateT.lift x >>= fun a => StateT.lift (g a) := by
  funext m
  show ((x >>= g) >>= fun a => pure (a, m)) =
    ((x >>= fun a => pure (a, m)) >>= fun p => (g p.1 >>= fun a => pure (a, p.2)))
  simp only [bind_assoc, pure_bind]

theorem lift_ite {α : Type} {c : Prop} [Decidable c] (x y : Result α) :
    (StateT.lift (if c then x else y) : MemM α) = if c then StateT.lift x else StateT.lift y := by
  split <;> rfl

theorem lift_optPayload_some {α : Type} (a : α) :
    (StateT.lift (optPayload (some a)) : MemM α) = pure a := rfl

theorem run_ite' {σ α : Type} {m : Type → Type} [Monad m] {c : Prop} [Decidable c]
    (x y : StateT σ m α) (s : σ) : (if c then x else y).run s = if c then x.run s else y.run s := by
  split <;> rfl

theorem run_throw' {σ α : Type} (e : Error) (s : σ) : (throw e : StateT σ Result α).run s = throw e := rfl

theorem result_throw_bind {α β : Type} (e : Error) (f : α → Result β) : (throw e : Result α) >>= f = throw e :=
  rfl

attribute [fsym_norm] run_ite' run_throw' result_throw_bind lift_bind lift_ite lift_optPayload_some Option.elim_none Option.elim_some
  Zig.call StateT.run_monadLift StateT.run_lift liftM monadLift MonadLift.monadLift

attribute [fsym_norm] StateT.run'_eq StateT.run_bind StateT.run_pure Norm.run_callM Norm.run_callR
  Norm.run_liftM Norm.run_liftR Norm.run_ite Norm.ite_bind Norm.run_throw Norm.throw_bind
  Norm.lift_pure Norm.lift_throw Norm.sub_zero Norm.elem_zero Norm.run_get Norm.run_modify
  Norm.add_zero_ptr bind_assoc pure_bind map_pure bind_map_left map_bind Norm.beq_true_iff
  bind_pure_unit Zig.isNonErr Zig.isErr Bool.not_false Bool.not_true Bool.false_eq_true
  Norm.isSome_ite Norm.elim_bind

/-- `Zig` comparisons of unsigned words, as comparisons of their values. -/
@[fsym_arith] theorem lt_false {n : Nat} (a b : BitVec n) : Zig.lt false a b = decide (a.toNat < b.toNat) := by
  simp [Zig.lt, BitVec.ult]
@[fsym_arith] theorem le_false {n : Nat} (a b : BitVec n) : Zig.le false a b = decide (a.toNat ≤ b.toNat) := by
  simp [Zig.le, BitVec.ule]
@[fsym_arith] theorem gt_false {n : Nat} (a b : BitVec n) : Zig.gt false a b = decide (b.toNat < a.toNat) := by
  simp [Zig.gt, Zig.lt, BitVec.ult]
@[fsym_arith] theorem ge_false {n : Nat} (a b : BitVec n) : Zig.ge false a b = decide (b.toNat ≤ a.toNat) := by
  simp [Zig.ge, Zig.le, BitVec.ule]

@[fsym_arith] theorem off_add (p : Ptr) (k : Int) : (p.add k).off = p.off + k := rfl
@[fsym_arith] theorem block_add (p : Ptr) (k : Int) : (p.add k).block = p.block := rfl
@[fsym_arith] theorem off_elem (p : Ptr) (s : Nat) (i : BitVec 64) :
    (p.elem s i).off = p.off + ((s * i.toNat : Nat) : Int) := rfl
@[fsym_arith] theorem block_elem (p : Ptr) (s : Nat) (i : BitVec 64) : (p.elem s i).block = p.block := rfl

attribute [fsym_arith] BitVec.toNat_ofNat BitVec.toNat_ofInt BitVec.toNat_add BitVec.toNat_eq
  BitVec.lt_def BitVec.le_def decide_eq_true_eq decide_eq_false_iff_not Bool.not_eq_true
  Bool.not_eq_true' beq_iff_eq bne_iff_ne Int.natCast_add Int.natCast_mul Int.toNat_natCast

open Lean Meta Simp in
/-- `x &&& m` for a literal mask `m = 2 ^ k - 1`: `x % 2 ^ k` (for `omega`). -/
simproc [fsym_arith] reduceLandMask ((_ : Nat) &&& _) := fun e => do
  let_expr HAnd.hAnd _ _ _ _ x m := e | return .continue
  let some n := m.nat? | return .continue
  let n1 := n + 1
  if n1 &&& n != 0 then return .continue
  let k := n1.log2
  let pf := mkApp2 (mkConst ``Nat.and_two_pow_sub_one_eq_mod) x (mkNatLit k)
  let rhs ← mkAppM ``HMod.hMod #[x, mkNatLit n1]
  return .done { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

attribute [fsym_arith] Array.size_append Array.size_extract BitVec.ofNat_eq_ofNat BitVec.toNat_and BitVec.toNat_sub BitVec.toNat_mul Nat.one_mul Nat.mul_one

/-! ## Sizes of the library's encodings -/

@[fsym_arith] theorem enc_size_bv64 : Enc.size (BitVec 64) = 8 := rfl
@[fsym_arith] theorem enc_size_bv32 : Enc.size (BitVec 32) = 4 := rfl
@[fsym_arith] theorem enc_size_bv16 : Enc.size (BitVec 16) = 2 := rfl
@[fsym_arith] theorem enc_size_bv8 : Enc.size (BitVec 8) = 1 := rfl
@[fsym_arith] theorem enc_size_ptr : Enc.size Ptr = 8 := rfl
@[fsym_arith] theorem enc_size_slice : Enc.size Slice = 16 := rfl

/-! ## Facts about byte arrays (`keepsPrefix` of `resizePost`/`remapPost`) -/

theorem kp_refl (bs : Array Byte) : keepsPrefix bs bs := rfl

theorem kp_extract (bs : Array Byte) (n : Nat) : keepsPrefix bs (bs.extract 0 n) := by
  unfold keepsPrefix; simp only [Array.extract_extract, Nat.zero_add, Array.size_extract]
  congr 1; omega

theorem kp_append (bs t : Array Byte) : keepsPrefix bs (bs ++ t) := by
  unfold keepsPrefix
  rw [Array.extract_append_left]
  simp only [Array.size_append, Array.extract_size]
  exact (Array.extract_eq_self_of_le (by omega)).symm

theorem kp_extract_append (bs t : Array Byte) (n : Nat) : keepsPrefix bs ((bs ++ t).extract 0 n) := by
  unfold keepsPrefix
  apply Array.ext
  · simp only [Array.size_extract, Array.size_append]; omega
  · intro i h1 h2
    simp only [Array.size_extract, Array.size_append] at h1 h2
    simp only [Array.getElem_extract, Nat.zero_add]
    rw [Array.getElem_append_left (by omega)]

end Zig.Full.Auto

/-- Library facts that are not arithmetic; extend with `macro_rules`. -/
syntax "fsym_fact" : tactic
macro_rules
  | `(tactic| fsym_fact) => `(tactic| first
      | exact Zig.Full.Auto.kp_refl _
      | exact Zig.Full.Auto.kp_extract _ _
      | exact Zig.Full.Auto.kp_append _ _
      | exact Zig.Full.Auto.kp_extract_append _ _ _)
