import ZigLean.Sep.Full.AutoAttr
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.AllocSpec.Ops
import ZigLean.Sep.AllocSpec.Norm
import ZigLean.Range

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
* **`Junk`** (the library's, `Full/AllocSpec.lean`): bytes an allocator gave up (padding, leaked
  frees); an `up` part is absorbed.
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

/-- **A return**, after a frame-preserving update into the postcondition. -/
theorem ret {v : β} (h : EUpd P (Q v)) : L.T P (pure v) Q :=
  L.ofTotal (FTotalTriple.eupd h (FTotalTriple.ret v))

theorem ex_sep {F : γ → FAssn} (t : ∀ x, L.T (F x ⋆ R) c Q) : L.T (FAssn.ex F ⋆ R) c Q :=
  L.pre (L.ex (P := fun x => F x ⋆ R) t) fun _ h => sep_ex.mp h

theorem lift_sep {φ : Prop} (t : φ → L.T R c Q) : L.T (⟪φ⟫ ⋆ R) c Q := L.lift t

theorem of_false (h : False) : L.T P c Q := h.elim

end Steps

/-! ## Facts of atoms -/

/-- The assertion `X` implies the fact `φ` (a facts lemma, `@[fsym_facts]`). -/
def AtomFacts (X : FAssn) (φ : Prop) : Prop := ∀ r, X r → φ

theorem AtomFacts.sepL {X R : FAssn} {φ : Prop} (h : AtomFacts X φ) {r : Res} (hr : (X ⋆ R) r) : φ := by
  obtain ⟨r₁, -, -, -, h1, -⟩ := hr; exact h r₁ h1

/-- A fact of a part `X` of the precondition, in the context. -/
theorem pre_fact (L : FLogic) {β : Type} {R : FAssn} {Q : β → FAssn} {c : MemM β} {X : FAssn} {φ : Prop}
    (hX : AtomFacts X φ) (t : φ → L.T (X ⋆ R) c Q) : L.T (X ⋆ R) c Q :=
  L.pre (L.lift t) fun _ h => sep_lift.mpr ⟨hX.sepL h, h⟩

/-- The assertion `X`, held in a memory, implies the fact `φ` (a facts lemma, `@[fsym_facts]`):
facts that need the memory or the whole ghost state, such as a token's grant in its authority's
map (`gauthP γ e M t ⋆ gfrag γ e i g`, `gfrag_mem`) or two owned regions apart. `X` is one atom
or a pair `X₁ ⋆ X₂` of atoms. -/
def MemFacts (X : FAssn) (φ : Prop) : Prop := ∀ m r rF, Holds m r rF → X r → m.FSeq → φ

theorem AtomFacts.mem {X : FAssn} {φ : Prop} (h : AtomFacts X φ) : MemFacts X φ :=
  fun _ r _ _ hx _ => h r hx

theorem MemFacts.sepL {X R : FAssn} {φ : Prop} (h : MemFacts X φ) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hr : (X ⋆ R) r) (hs : m.FSeq) : φ := by
  obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hr
  exact h m r₁ _ (Holds.split hd hh) h1 hs

/-- The facts of a part `X` of the precondition, as an update that keeps it. -/
theorem MemFacts.eupd {X R : FAssn} {φ : Prop} (h : MemFacts X φ) : EUpd (X ⋆ R) (⟪φ⟫ ⋆ (X ⋆ R)) :=
  fun _ r _ hh hp hs => ⟨r, hh, sep_lift.mpr ⟨h.sepL hh hp hs, hp⟩⟩

/-- An update of the precondition, in any logic (a return of `()` bound to the program). -/
theorem pre_eupd (L : FLogic) {β : Type} {P P' : FAssn} {Q : β → FAssn} {c : MemM β}
    (h : EUpd P P') (t : L.T P' c Q) : L.T P c Q :=
  L.congr (fun _ _ => rfl) (L.bind (ret L (Q := fun _ => P') (v := ()) h) fun _ => t)

/-- A fact of a part `X` of the precondition that needs the memory, in the context. -/
theorem pre_mfact (L : FLogic) {β : Type} {R : FAssn} {Q : β → FAssn} {c : MemM β} {X : FAssn} {φ : Prop}
    (hX : MemFacts X φ) (t : φ → L.T (X ⋆ R) c Q) : L.T (X ⋆ R) c Q :=
  pre_eupd L hX.eupd (L.lift t)

section Facts

variable {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte}

/-- An owned region: the block of its pointer, a nonnegative offset, its alignment. -/
@[fsym_facts] theorem facts_region :
    AtomFacts (up (regionIn p A S K a bs)) ((∃ b, p.block = some b) ∧ 0 ≤ p.off ∧ (A + p.off.toNat) % a = 0) := by
  rintro r ⟨⟨ha, -, b, hb, h0, -⟩, -⟩; exact ⟨⟨b, hb⟩, h0, ha⟩

/-- Owned bytes: the block of their pointer, a nonnegative offset. -/
@[fsym_facts] theorem facts_bytes :
    AtomFacts (up (bytesAt p A S K bs)) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨⟨b, hb, h0, -⟩, -⟩; exact ⟨⟨b, hb⟩, h0⟩

/-- A typed value: the block of its pointer, a nonnegative offset. -/
@[fsym_facts] theorem facts_pts {T : Type} [Enc T] {v : T} :
    AtomFacts (up (pts p a v)) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨⟨-, -, -, -, -, -, -, ⟨b, hb, h0, -⟩, -⟩, -⟩; exact ⟨⟨b, hb⟩, h0⟩

/-- An atomic word: the block of its pointer, a nonnegative offset. -/
@[fsym_facts] theorem facts_apts {v : BitVec 64} :
    AtomFacts (apts p v) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨-, -, -, -, -, -, -, -, -, -, b, hb, h0, -⟩; exact ⟨⟨b, hb⟩, h0⟩

end Facts

/-! ## Providers from atoms -/

section Providers

variable {b : BlockId} {A k : Nat} {P X R : FAssn}

theorem AddrOf.of_atom (h : AddrOf b A X) (e : P = (X ⋆ R)) : AddrOf b A P := e ▸ h.sepL

theorem Reaches.of_atom (h : Reaches b k X) (e : P = (X ⋆ R)) : Reaches b k P := e ▸ h.sepL

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

attribute [fsym_provider] AddrOf.known AddrOf.region Reaches.share Reaches.pts Reaches.region

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

/-- A word result with its value: the step rules below leave `r` opaque with the fact
`r.toNat = …` (a symbolic execution in SSA form), so later terms mention `r` and not the
growing expression that computed it. -/
theorem read_val {v : BitVec w} {n : Nat} (h : v.toNat = n) :
    FTotalTriple P (pure v : MemM (BitVec w)) (fun r => ⟪r.toNat = n⟫ ⋆ P) :=
  (FTotalTriple.ret (Q := fun r => ⟪r.toNat = n⟫ ⋆ P) v).pre fun _ hp => sep_lift.mpr ⟨h, hp⟩

/-- A checked unsigned `+` that does not overflow. -/
@[fsym] theorem add_step {a b : BitVec w} (h : a.toNat + b.toNat < 2 ^ w) :
    FTotalTriple P (StateT.lift (Zig.add false a b) : MemM (BitVec w))
      (fun r => ⟪r.toNat = a.toNat + b.toNat⟫ ⋆ P) := by
  have e : Zig.add false a b = pure (a + b) := by
    simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by simp; omega)]
  rw [e]; exact read_val (BitVec.toNat_add_of_lt h)

/-- A checked unsigned `-` that does not overflow (its value stated without truncated
subtraction, which `omega` would case-split on). -/
@[fsym] theorem sub_step {a b : BitVec w} (h : b.toNat ≤ a.toNat) :
    FTotalTriple P (StateT.lift (Zig.sub false a b) : MemM (BitVec w))
      (fun r => ⟪r.toNat + b.toNat = a.toNat⟫ ⋆ P) := by
  have e : Zig.sub false a b = pure (a - b) := by
    simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by simp; omega)]
  have hv : (a - b).toNat + b.toNat = a.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]; omega
  rw [e]
  exact (FTotalTriple.ret (Q := fun r => ⟪r.toNat + b.toNat = a.toNat⟫ ⋆ P) (a - b)).pre
    fun _ hp => sep_lift.mpr ⟨hv, hp⟩

/-- The payload of an optional that is not null (`.?`, `orelse unreachable`): some `v` with
`o = some v`. -/
@[fsym] theorem optPayload_step {α : Type} {o : Option α} (h : o.isSome = true) :
    FTotalTriple P (StateT.lift (optPayload o) : MemM α) (fun v => ⟪o = some v⟫ ⋆ P) := by
  obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp h
  exact (FTotalTriple.ret (Q := fun r => ⟪some v = some r⟫ ⋆ P) v).pre fun _ hp => sep_lift.mpr ⟨rfl, hp⟩

/-! Tests of an optional as constructor equations (facts of `if o != null`, `orelse`), so a
`match o` of the precondition reduces (`destruct`, `substCtor`). -/

theorem opt_isSome_true {α : Type _} {o : Option α} (h : o.isSome = true) : ∃ a, o = some a :=
  Option.isSome_iff_exists.mp h

theorem opt_not_isSome {α : Type _} {o : Option α} (h : ¬o.isSome = true) : o = none :=
  Option.not_isSome_iff_eq_none.mp h

theorem opt_isSome_false {α : Type _} {o : Option α} (h : o.isSome = false) : o = none :=
  Option.not_isSome_iff_eq_none.mp (by simp [h])

theorem opt_isNone_true {α : Type _} {o : Option α} (h : o.isNone = true) : o = none :=
  Option.isNone_iff_eq_none.mp h

theorem opt_not_isNone {α : Type _} {o : Option α} (h : ¬o.isNone = true) : ∃ a, o = some a :=
  Option.isSome_iff_exists.mp (by cases o <;> simp_all)

theorem opt_isNone_false {α : Type _} {o : Option α} (h : o.isNone = false) : ∃ a, o = some a :=
  Option.isSome_iff_exists.mp (by cases o <;> simp_all)

/-- A slice's end check (`s[start..][0..len]`) within the source's length. -/
@[fsym] theorem checkSliceEnd_of {srcLen start len : BitVec 64} {extra : Nat}
    (h : start.toNat + len.toNat + extra ≤ srcLen.toNat) :
    FTotalTriple P (checkSliceEnd srcLen start len extra) (fun _ => P) := by
  unfold checkSliceEnd; rw [if_pos h]; exact FTotalTriple.ret (Q := fun _ => P) ()

/-- A checked unsigned `%` by a nonzero divisor. -/
@[fsym] theorem rem_step {a b : BitVec w} (h : b ≠ 0) :
    FTotalTriple P (StateT.lift (Zig.rem false a b) : MemM (BitVec w))
      (fun r => ⟪r.toNat = a.toNat % b.toNat⟫ ⋆ P) := by
  have e : Zig.rem false a b = pure (a % b) := by
    simp only [Zig.rem, h, Bool.false_eq_true, ↓reduceIte]; rfl
  rw [e]; exact read_val BitVec.toNat_umod

/-- A checked unsigned `/` by a nonzero divisor. -/
@[fsym] theorem divTrunc_step {a b : BitVec w} (h : b ≠ 0) :
    FTotalTriple P (StateT.lift (Zig.divTrunc false a b) : MemM (BitVec w))
      (fun r => ⟪r.toNat = a.toNat / b.toNat⟫ ⋆ P) := by
  have e : Zig.divTrunc false a b = pure (a / b) := by
    simp only [Zig.divTrunc, h, Bool.false_eq_true, ↓reduceIte]; rfl
  rw [e]; exact read_val BitVec.toNat_udiv

/-- An unsigned `@intCast` whose value fits in the target width (widening always does). -/
@[fsym] theorem intCast_step {n : Nat} {a : BitVec w} (h : a.toNat < 2 ^ n) :
    FTotalTriple P (StateT.lift (Zig.intCast false false n a) : MemM (BitVec n))
      (fun r => ⟪r.toNat = a.toNat⟫ ⋆ P) := by
  rw [Zig.intCast_unsigned_of_lt h]; exact read_val (Zig.toNat_ofNat_of_lt h)

end Arith

section Values

variable {w : Nat}

/-! The overflow bits of `@addWithOverflow` and friends, and shifts, as values. -/

theorem addWithOverflow_fst {s : Bool} (a b : BitVec w) : (Zig.addWithOverflow s a b).fst = a + b := rfl
theorem subWithOverflow_fst {s : Bool} (a b : BitVec w) : (Zig.subWithOverflow s a b).fst = a - b := rfl
theorem mulWithOverflow_fst {s : Bool} (a b : BitVec w) : (Zig.mulWithOverflow s a b).fst = a * b := rfl

theorem ovbit_ne (c : Bool) : ((if c = true then (1 : BitVec 1) else 0) != 0#1) = c := by
  cases c <;> rfl

theorem addWithOverflow_snd (a b : BitVec w) :
    ((Zig.addWithOverflow false a b).snd != 0#1) = decide (2 ^ w ≤ a.toNat + b.toNat) := by
  simp only [Zig.addWithOverflow, Bool.false_eq_true, ↓reduceIte, ovbit_ne, BitVec.uaddOverflow]
theorem subWithOverflow_snd (a b : BitVec w) :
    ((Zig.subWithOverflow false a b).snd != 0#1) = decide (a.toNat < b.toNat) := by
  simp only [Zig.subWithOverflow, Bool.false_eq_true, ↓reduceIte, ovbit_ne, BitVec.usubOverflow]
theorem mulWithOverflow_snd (a b : BitVec w) :
    ((Zig.mulWithOverflow false a b).snd != 0#1) = decide (2 ^ w ≤ a.toNat * b.toNat) := by
  simp only [Zig.mulWithOverflow, Bool.false_eq_true, ↓reduceIte, ovbit_ne, BitVec.umulOverflow]

theorem ovbit_eq (c : Bool) : ((if c = true then (1 : BitVec 1) else 0) = 0#1) = (c = false) := by
  cases c <;> decide
theorem addWithOverflow_snd_eq (a b : BitVec w) :
    ((Zig.addWithOverflow false a b).snd = 0#1) = (a.toNat + b.toNat < 2 ^ w) := by
  simp only [Zig.addWithOverflow, Bool.false_eq_true, ↓reduceIte, ovbit_eq, BitVec.uaddOverflow]
  simp
theorem subWithOverflow_snd_eq (a b : BitVec w) :
    ((Zig.subWithOverflow false a b).snd = 0#1) = (b.toNat ≤ a.toNat) := by
  simp only [Zig.subWithOverflow, Bool.false_eq_true, ↓reduceIte, ovbit_eq, BitVec.usubOverflow]
  simp
theorem mulWithOverflow_snd_eq (a b : BitVec w) :
    ((Zig.mulWithOverflow false a b).snd = 0#1) = (a.toNat * b.toNat < 2 ^ w) := by
  simp only [Zig.mulWithOverflow, Bool.false_eq_true, ↓reduceIte, ovbit_eq, BitVec.umulOverflow]
  simp
theorem shl_eq {m : Nat} (a : BitVec w) (b : BitVec m) : Zig.shl a b = BitVec.ofNat w (a.toNat * 2 ^ b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [Zig.shl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem sub_one_mod {W J : Nat} (hW : 0 < W) (hJ : 0 < J) : (W - 1 + J % W) % W = (J - 1) % W := by
  have hd := Nat.div_add_mod J W
  have hr := Nat.mod_lt J hW
  generalize J / W = q at hd
  generalize J % W = r at hd hr ⊢
  subst hd
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hJ)
    have := Nat.le_mul_of_pos_right W hq
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega : W - 1 < W),
      show W * q + 0 - 1 = W * (q - 1) + (W - 1) by rw [Nat.mul_sub_one]; omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  · rw [show W - 1 + r = W + (r - 1) by omega, Nat.add_mod_left, show W * q + r - 1 = W * q + (r - 1) by omega,
      Nat.mul_add_mod]

/-- The low mask `2 ^ j - 1` of width `w`. -/
theorem toNat_lowMask (j : Nat) : (BitVec.ofNat w (2 ^ j) - BitVec.ofNat w 1).toNat = (2 ^ j - 1) % 2 ^ w := by
  rcases w with _ | w
  · simp [Nat.mod_one]
  have h1 : 1 % 2 ^ (w + 1) = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1]
  exact sub_one_mod (Nat.two_pow_pos _) (Nat.two_pow_pos _)

theorem mask_mod (x j : Nat) (hx : x < 2 ^ w) : x &&& ((2 ^ j - 1) % 2 ^ w) = x % 2 ^ j := by
  rcases Nat.lt_or_ge j w with h | h
  · rw [Nat.mod_eq_of_lt (by have := Nat.pow_lt_pow_right (by omega : 1 < 2) h; omega),
      Nat.and_two_pow_sub_one_eq_mod]
  · have e : (2 ^ j - 1) % 2 ^ w = 2 ^ w - 1 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have hd := Nat.two_pow_pos d
      have hw := Nat.two_pow_pos w
      rw [Nat.pow_add, show 2 ^ w * 2 ^ d - 1 = 2 ^ w * (2 ^ d - 1) + (2 ^ w - 1) by
        rw [Nat.mul_sub_one]; have := Nat.le_mul_of_pos_right (2 ^ w) hd; omega]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h))]

theorem and_not_add_and (z m : BitVec w) : (z &&& ~~~m).toNat + (z &&& m).toNat = z.toNat := by
  have h0 : (z &&& ~~~m) &&& (z &&& m) = 0#w := by
    ext i; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases z[i] <;> cases m[i] <;> rfl
  rw [← BitVec.toNat_add_of_and_eq_zero h0, BitVec.add_eq_or_of_and_eq_zero _ _ h0]
  congr 1
  ext i; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
  cases z[i] <;> cases m[i] <;> rfl

/-! **Masks** (`std.mem.alignForward`, `isPowerOfTwo`): `x &&& (2 ^ j - 1)` is `x % 2 ^ j` and
`x &&& ~~~(2 ^ j - 1)` is `x - x % 2 ^ j`, for any width and any `j`. -/

theorem and_lowMask (x : BitVec w) (j : Nat) :
    (x &&& (BitVec.ofNat w (2 ^ j) - BitVec.ofNat w 1)).toNat = x.toNat % 2 ^ j := by
  rw [BitVec.toNat_and, toNat_lowMask, mask_mod _ _ x.isLt]
theorem and_lowMask' (x : BitVec w) (j : Nat) :
    (x &&& BitVec.ofNat w (2 ^ j - 1)).toNat = x.toNat % 2 ^ j := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, mask_mod _ _ x.isLt]
theorem and_not_lowMask (x : BitVec w) (j : Nat) :
    (x &&& ~~~(BitVec.ofNat w (2 ^ j) - BitVec.ofNat w 1)).toNat = x.toNat - x.toNat % 2 ^ j := by
  have := and_not_add_and x (BitVec.ofNat w (2 ^ j) - BitVec.ofNat w 1)
  rw [and_lowMask] at this; omega
theorem and_not_lowMask' (x : BitVec w) (j : Nat) :
    (x &&& ~~~BitVec.ofNat w (2 ^ j - 1)).toNat = x.toNat - x.toNat % 2 ^ j := by
  have := and_not_add_and x (BitVec.ofNat w (2 ^ j - 1))
  rw [and_lowMask'] at this; omega

/-- An exponent reduced modulo a bound it is below (`2 ^ (k % 64)` from a `u6` shift count). -/
theorem pow_mod_elim {b x m : Nat} (h : x < m) : b ^ (x % m) = b ^ x := by rw [Nat.mod_eq_of_lt h]

/-- Masks of natural numbers known by facts (the arithmetic solver's `addFacts`). -/
theorem land_low {a b j : Nat} (h : b = 2 ^ j - 1) : a &&& b = a % 2 ^ j := by
  subst h; exact Nat.and_two_pow_sub_one_eq_mod a j
theorem land_high' {a b j w : Nat} (ha : a < 2 ^ w) (hj : j ≤ w) (h : b = 2 ^ w - 2 ^ j) :
    a &&& b = a - a % 2 ^ j := by
  have hjw : 2 ^ j ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hj
  have hp := Nat.two_pow_pos j
  have t := and_not_lowMask' (BitVec.ofNat w a) j
  rw [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : 2 ^ j - 1 < 2 ^ w)] at t
  rw [h, ← t]; congr 1; omega

/-- `land_high'` without truncated subtraction. -/
theorem land_high {a b j w : Nat} (ha : a < 2 ^ w) (hj : j ≤ w) (h : b = 2 ^ w - 2 ^ j) :
    (a &&& b) + a % 2 ^ j = a := by
  rw [land_high' ha hj h]; have := Nat.mod_le a (2 ^ j); omega

/-! **Atoms for `omega`**: a truncated subtraction, `Int.toNat`, `min` or `max` whose case is
known, as an opaque atom with a linear defining fact (no case split). -/

/-- `a - b` as an atom for `omega` where `b ≤ a` is known (no case split). -/
@[irreducible] def subAtom (a b : Nat) : Nat := a - b
theorem subAtom_add {a b : Nat} (h : b ≤ a) : subAtom a b + b = a := by unfold subAtom; omega
theorem subAtom_zero {a b : Nat} (h : a ≤ b) : subAtom a b = 0 := by unfold subAtom; omega
/-- `x.toNat` as an atom for `omega` where `0 ≤ x` is known. -/
@[irreducible] def toNatAtom (x : Int) : Nat := x.toNat
theorem toNatAtom_eq {x : Int} (h : 0 ≤ x) : (toNatAtom x : Int) = x := by unfold toNatAtom; omega
/-- `min a b`/`max a b` as an atom where the order is known. -/
@[irreducible] def minAtom (a b : Nat) : Nat := Min.min a b
theorem minAtom_left {a b : Nat} (h : a ≤ b) : minAtom a b = a := by unfold minAtom; omega
theorem minAtom_right {a b : Nat} (h : b ≤ a) : minAtom a b = b := by unfold minAtom; omega
@[irreducible] def maxAtom (a b : Nat) : Nat := Max.max a b
theorem maxAtom_left {a b : Nat} (h : b ≤ a) : maxAtom a b = a := by unfold maxAtom; omega
theorem maxAtom_right {a b : Nat} (h : a ≤ b) : maxAtom a b = b := by unfold maxAtom; omega

/-! **No wrap-around**: the value of a word operation whose result fits (conditional rewrites of
the arithmetic solver, side conditions by `omega`; `+ - *` are `Zig.toNat_add_of_lt`,
`Zig.toNat_sub_of_le`, `BitVec.toNat_mul_of_lt`). -/

theorem toNat_ofNat_nowrap {n : Nat} (h : n < 2 ^ w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem toNat_ofInt_nowrap {i : Int} (h0 : 0 ≤ i) (h : i < 2 ^ w) : (BitVec.ofInt w i).toNat = i.toNat := by
  rw [BitVec.toNat_ofInt]; congr 1; exact Int.emod_eq_of_lt h0 (by exact_mod_cast h)
theorem sub_wrap {M a b : Nat} (hb : b ≤ a) (ha : a < M) : (M - b + a) % M = a - b := by
  rw [show M - b + a = M + (a - b) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
theorem mod_eq_zero_of_eq {z M : Nat} (h : z = M) : z % M = 0 := by subst h; exact Nat.mod_self z

/-- `z` rounded down to a multiple of `M` is one. -/
theorem sub_mod_self_mod (z M : Nat) : (z - z % M) % M = 0 := Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm

end Values

/-! ## Junk -/

-- The library's `Junk` (`Full/AllocSpec.lean`) stays opaque: `fsym` absorbs `up` parts into it.
attribute [fsym_atom] Junk

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

theorem imp_junk_emp : ∀ r, emp r → Junk r := fun _ h => junk_emp h

theorem imp_junk_up {Z : Assn} (h : ∀ r, X r → Junk r) : ∀ r, (up Z ⋆ X) r → Junk r :=
  fun _ hx => junk_absorb (sep_mono_right h hx)

theorem imp_junk_one {Z : Assn} : ∀ r, up Z r → Junk r :=
  fun _ hx => junk_absorb (sep_emp.mpr hx |> sep_mono_right fun _ h => junk_emp h)

theorem imp_junk_junk (h : ∀ r, X r → Junk r) : ∀ r, (Junk ⋆ X) r → Junk r := by
  intro r hx
  obtain ⟨r₁, r₂, hd, rfl, ⟨j1, h1⟩, h2⟩ := hx
  obtain ⟨j2, h2⟩ := h _ h2
  exact junk_absorb ⟨r₁, r₂, hd, rfl, h1, ⟨j2, h2⟩⟩

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

/-- **Raise a share's bound** with another share of the block: both at the higher bound, the
fractions unchanged (join, then split back). A grant that grows in place takes its new bound
from the allocator's share of the block. -/
theorem share_raise {q₂ : Frac} {k₂ : Nat} :
    EUpd (bshare b q k t ⋆ bshare b q₂ k₂ t)
      (bshare b q (Max.max k k₂) t ⋆ bshare b q₂ (Max.max k k₂) t) := fun m r rF hh hp hs => by
  obtain ⟨r₁, r₂, -, -, h1, h2⟩ := id hp
  obtain ⟨r', hh', hp'⟩ := EUpd.join m r rF hh hp hs
  exact ⟨r', hh', (bshare_split h1.1 h2.1).mp hp'⟩

/-! The authority over a block's extent (`bauth`; `bext` is the fraction `Frac.one`): untagged
shares go back into it (`EUpd.unlend`) and come out of it (`EUpd.lend`); a share's bound rises up
to the block's size. -/

theorem auth_unlend {S : Nat} {K : BlockKind} {q₁ q₂ : Frac} :
    EUpd (bauth b S K q₁ ⋆ bshare b q₂ k) (bauth b S K (q₁.add q₂)) := EUpd.unlend

theorem auth_lend {S : Nat} {K : BlockKind} {q₁ q₂ : Frac} (hk : k ≤ S) (hq : 0 < q₂.val) :
    EUpd (bauth b S K (q₁.add q₂)) (bauth b S K q₁ ⋆ bshare b q₂ k) := EUpd.lend hk hq

/-- **Raise a share's bound** with the authority of its block: up to the block's size. -/
theorem auth_raise {S : Nat} {K : BlockKind} {q₁ q₂ : Frac} (hk : k' ≤ S) :
    EUpd (bauth b S K q₁ ⋆ bshare b q₂ k) (bauth b S K q₁ ⋆ bshare b q₂ k') := fun m r rF hh hp hs => by
  have hq : 0 < q₂.val := by obtain ⟨_, _, _, _, _, h2⟩ := hp; exact h2.1
  exact (EUpd.unlend.trans (EUpd.lend hk hq)) m r rF hh hp hs

/-- An authority whose fraction is known otherwise. -/
theorem auth_eq {S : Nat} {K : BlockKind} {q₁ q₂ : Frac} (h : q₁ = q₂) :
    bauth b S K q₁ = bauth b S K q₂ := h ▸ rfl

theorem one_half_pos : 0 < Frac.one.half.val := Frac.half_pos (by decide)

theorem frac_pos_of_eq {a c : Frac} (h : a = c) (ha : 0 < a.val) : 0 < c.val := h ▸ ha

/-- **Knowledge from ownership**, as an update: a nonempty region of block `b` whose cells have
the address `A` gives `known b A`. -/
theorem known_of_region {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte}
    (hpb : p.block = some b) (hpos : 0 < bs.size) :
    EUpd (up (regionIn p A S K a bs)) (up (regionIn p A S K a bs) ⋆ known b A) := by
  intro m r rF hh hp _
  obtain ⟨hr, hk, hg⟩ := id hp
  obtain ⟨-, -, b', hb', -, hl⟩ := id hr
  rw [hpb] at hb'; cases hb'
  have e := hl (b, p.off.toNat)
  rw [if_pos ⟨rfl, Nat.le_refl _, by omega⟩] at e
  simp only [FHeap.erase, Option.map_eq_some_iff] at e
  obtain ⟨fc, hfc, hfe⟩ := e
  have hkn : m.kn (.addr b A) := by
    obtain ⟨blk, hblk, -, -, -, ha, -⟩ := hh.block hfc
    exact ⟨blk, hblk, by rw [← ha, hfe]⟩
  exact ⟨⟨r.heap, r.know.union (Know.single (.addr b A)), r.gh⟩,
    ⟨hh.disj, hh.heap, hh.know.union (Know.sub_single hkn),
      hh.knowF, hh.ghost⟩,
    ⟨r, ⟨FHeap.empty, Know.single (.addr b A), Ghost.unit⟩, FHeap.disjoint_empty _,
      by rw [FHeap.union_empty, Ghost.add_unit], hp, rfl, rfl, rfl⟩⟩

/-- Knowledge can be forgotten. -/
@[fsym_drop] theorem known_drop {A : Nat} {R : FAssn} : EUpd (known b A ⋆ R) R := by
  rintro m _ rF hh ⟨r₁, r₂, -, rfl, ⟨e1, -, e3⟩, hp⟩ -
  obtain ⟨hd, hm, hkn, hkF, hg⟩ := hh
  simp only [e1, e3, FHeap.empty_union, Ghost.unit_add] at hd hm hg
  exact ⟨r₂, ⟨hd, hm, Know.Sub.right hkn, hkF, hg⟩, hp⟩

theorem ite_pos_eq {c : Prop} [Decidable c] (h : c) (X Y : FAssn) : (if c then X else Y) = X := if_pos h
theorem ite_neg_eq {c : Prop} [Decidable c] (h : ¬c) (X Y : FAssn) : (if c then X else Y) = Y := if_neg h

end Plan

theorem sep_emp_eq' (P : FAssn) : (P ⋆ emp) = P := funext fun _ => propext sep_emp
theorem emp_sep_eq' (P : FAssn) : (emp ⋆ P) = P := by rw [sep_comm_eq]; exact sep_emp_eq' P

theorem atom_eq {X Y : FAssn} (e : X = Y) : EUpd X Y := e ▸ EUpd.of_imp fun _ h => h

/-- A fact of the state of an update goes into the context. -/
theorem eupd_lift_pre {φ : Prop} {R Q : FAssn} (h : φ → EUpd R Q) : EUpd (⟪φ⟫ ⋆ R) Q :=
  fun m r rF hh hp hs => (h (sep_lift.mp hp).1) m r rF hh (sep_lift.mp hp).2 hs

/-- An existential of the state of an update is opened. -/
theorem eupd_ex_pre {β : Type} {F : β → FAssn} {R Q : FAssn} (h : ∀ x, EUpd (F x ⋆ R) Q) :
    EUpd (FAssn.ex F ⋆ R) Q := fun m r rF hh hp hs => by
  obtain ⟨x, hx⟩ := sep_ex.mp hp
  exact h x m r rF hh hx hs

theorem eupd_pre_eq {P P' Q : FAssn} (e : P = P') (h : EUpd P' Q) : EUpd P Q := e ▸ h

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
  Zig.call StateT.run_monadLift StateT.run_lift liftM monadLift MonadLift.monadLift StateT.run_get StateT.run_modify

/-- The payload and the error of an error union whose tag is known. -/
theorem unwrapPayload_ok {α : Type} (v : α) : Zig.unwrapPayload (.ok v : Except ErrName α) = pure v := rfl
theorem unwrapErr_error {α : Type} (e : ErrName) : Zig.unwrapErr (.error e : Except ErrName α) = pure e := rfl

attribute [fsym_norm] StateT.run'_eq StateT.run_bind StateT.run_pure Norm.run_callM Norm.run_callR
  Norm.run_liftM Norm.run_liftR Norm.run_ite Norm.ite_bind Norm.run_throw Norm.throw_bind
  Norm.lift_pure Norm.lift_throw Norm.sub_zero Norm.elem_zero Norm.run_get Norm.run_modify
  Norm.add_zero_ptr bind_assoc pure_bind map_pure bind_map_left map_bind Norm.beq_true_iff
  bind_pure_unit Zig.isNonErr Zig.isErr Bool.not_false Bool.not_true Bool.false_eq_true
  Norm.isSome_ite Norm.elim_bind unwrapPayload_ok unwrapErr_error

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
  Bool.or_eq_true Bool.and_eq_true Nat.not_lt Nat.not_le BlockKind.mapped.injEq

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

attribute [fsym_arith] LawfulEnc.size_encode Array.size_append Array.size_extract BitVec.ofNat_eq_ofNat BitVec.toNat_and BitVec.toNat_sub BitVec.toNat_mul Nat.one_mul Nat.mul_one

attribute [fsym_arith] addWithOverflow_fst subWithOverflow_fst mulWithOverflow_fst addWithOverflow_snd
  subWithOverflow_snd mulWithOverflow_snd shl_eq BitVec.toNat_umod BitVec.toNat_udiv BitVec.toNat_not
attribute [fsym_arith high] addWithOverflow_snd_eq subWithOverflow_snd_eq mulWithOverflow_snd_eq
attribute [fsym_arith high] and_lowMask and_lowMask' and_not_lowMask and_not_lowMask'

theorem add_lit {n : Nat} {a b : BitVec n} (h : decide (a.toNat + b.toNat < 2 ^ n) = true) :
    Zig.add false a b = pure (a + b) := by
  simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp at h ⊢; omega)]
theorem sub_lit {n : Nat} {a b : BitVec n} (h : decide (b.toNat ≤ a.toNat) = true) :
    Zig.sub false a b = pure (a - b) := by
  simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp at h ⊢; omega)]
theorem mul_lit {n : Nat} {a b : BitVec n} (h : decide (a.toNat * b.toNat < 2 ^ n) = true) :
    Zig.mul false a b = pure (a * b) := by
  simp only [Zig.mul, BitVec.umulOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp at h ⊢; omega)]

open Lean Meta Simp in
/-- Unsigned `+ - *` of two word literals that does not overflow: its value (`pure (a - b)`,
then evaluated by Lean's `BitVec` simprocs). Generated code computes constants such as
`alignment - 1` at run time. The side condition is decided on the literals. -/
def reduceLitArithCore (op lem : Name) : Simproc := fun e => do
  unless e.isAppOfArity op 4 do return .continue
  let args := e.getAppArgs
  unless args[1]!.isConstOf ``Bool.false do return .continue
  let some ⟨w, a⟩ ← getBitVecValue? args[2]! | return .continue
  let some ⟨_, b⟩ ← getBitVecValue? args[3]! | return .continue
  let ok := if op == ``Zig.add then a.toNat + b.toNat < 2 ^ w
    else if op == ``Zig.sub then b.toNat ≤ a.toNat
    else a.toNat * b.toNat < 2 ^ w
  unless ok do return .continue
  let f ← mkAppOptM lem #[none, args[2]!, args[3]!]
  let hTy := (← whnfR (← inferType f)).bindingDomain!
  let pf := mkApp f (← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) hTy)
  let rhs := (← inferType pf).appArg!
  return .visit { expr := rhs, proof? := some pf }

simproc [fsym_norm] reduceLitAdd (Zig.add false _ _) := reduceLitArithCore ``Zig.add ``add_lit
simproc [fsym_norm] reduceLitSub (Zig.sub false _ _) := reduceLitArithCore ``Zig.sub ``sub_lit
simproc [fsym_norm] reduceLitMul (Zig.mul false _ _) := reduceLitArithCore ``Zig.mul ``mul_lit

open Lean Meta Simp in
/-- The size `Enc.size T` of a closed type's encoding, as a literal (with `LawfulEnc.size_encode`:
the size of an encoded value, `(Enc.encode v).size`). -/
dsimproc [fsym_arith] reduceEncSize (Enc.size _) := fun e => do
  unless e.isAppOfArity ``Enc.size 2 && !e.hasFVar && !e.hasMVar do return .continue
  let v ← whnfD e
  let some n := v.nat? <|> v.rawNatLit? | return .continue
  return .done (mkNatLit n)

open Lean Meta Simp in
/-- A field accessor of generated code applied to a structure value (`mem_Alignment.toBits ⟨x⟩`
is `x`): a user definition whose body is a projection of one of its parameters. -/
dsimproc [fsym_norm, fsym_arith] reduceAccessor (_) := fun e => do
  let .const c _ := e.getAppFn | return .continue
  if e.getAppNumArgs == 0 then return .continue
  let env ← getEnv
  if let some idx := env.getModuleIdxFor? c then
    if [`ZigLean, `Init, `Std, `Lean].contains env.header.moduleNames[idx.toNat]!.getRoot then
      return .continue
  let some (.defnInfo info) := env.find? c | return .continue
  let isAccessor ← lambdaTelescope info.value fun xs body => do
    let body := body.consumeMData
    if xs.size != e.getAppNumArgs then return false
    match body with
    | .proj _ _ s => return s.isFVar && xs.contains s
    | _ =>
      let .const f _ := body.getAppFn | return false
      let some pi ← getProjectionFnInfo? f | return false
      let some s := body.getAppArgs[pi.numParams]? | return false
      return body.getAppNumArgs == pi.numParams + 1 && s.isFVar && xs.contains s
  unless isAccessor do return .continue
  let some e' ← withTransparency .default (unfoldDefinition? e) | return .continue
  let e' ← withTransparency .default (whnfCore e'.headBeta)
  if e' != e && (e.find? (· == e')).isSome then return .done e'
  return .continue

open Lean Meta Simp in
/-- A user definition (an invariant's, generated code's) with an arithmetic or logical value
(`Nat`, `Int`, `BitVec`, `Bool`, `Prop`) is transparent to the arithmetic solver: unfolded
(`bnd B`, `FOk …`). Monadic generated code is not touched (its value is a program). -/
dsimproc [fsym_arith] unfoldUserValue (_) := fun e => do
  let .const c _ := e.getAppFn | return .continue
  let env ← getEnv
  if let some idx := env.getModuleIdxFor? c then
    if [`ZigLean, `Init, `Std, `Lean].contains env.header.moduleNames[idx.toNat]!.getRoot then
      return .continue
  let some (.defnInfo info) := env.find? c | return .continue
  if (← getProjectionFnInfo? c).isSome || isMatcherCore env c || isAuxRecursor env c then return .continue
  if info.value.getUsedConstants.contains c then return .continue
  if (← isInstance c) then return .continue
  let ty ← whnfR (← inferType e)
  let ok := ty.isProp || ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isConstOf ``Bool ||
    ty.isAppOfArity ``BitVec 1
  unless ok do return .continue
  let some e' ← withTransparency .default (unfoldDefinition? e) | return .continue
  return .visit e'.headBeta

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

theorem kp_extract_append_append (bs t u : Array Byte) (n : Nat) :
    keepsPrefix bs ((bs ++ t ++ u).extract 0 n) := by
  rw [Array.append_assoc]; exact kp_extract_append bs (t ++ u) n

/-- A prefix of a prefix of `bs ++ t` keeps `bs`'s prefix. -/
theorem kp_extract_extract_append (bs t : Array Byte) (m n : Nat) :
    keepsPrefix bs (((bs ++ t).extract 0 m).extract 0 n) := by
  rw [Array.extract_extract]; simp only [Nat.zero_add]
  exact kp_extract_append bs t (Nat.min n m)

/-- A power of two divides a literal power of two exactly when its exponent is at most the
literal's. -/
theorem two_pow_dvd_iff {k j L : Nat} (h : L = 2 ^ j) : 2 ^ k ∣ L ↔ k ≤ j := by
  subst h; exact Nat.pow_dvd_pow_iff_le_right (by decide)

/-- An exponent bounded by a power of two's literal bound. -/
theorem le_of_two_pow_le {x c j : Nat} (h : 2 ^ x ≤ c) (hc : c < 2 ^ (j + 1)) : x ≤ j := by
  rcases Nat.lt_or_ge j x with hx | hx
  · have : 2 ^ (j + 1) ≤ 2 ^ x := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · exact hx

open Lean Meta Simp in
/-- `2 ^ k ∣ L` for a literal power of two `L = 2 ^ j`: `k ≤ j` (for `omega`). -/
simproc [fsym_arith] reduceTwoPowDvd ((2 : Nat) ^ _ ∣ _) := fun e => do
  let_expr Dvd.dvd _ _ p L := e | return .continue
  let some l := L.nat? | return .continue
  unless l > 0 && l &&& (l - 1) == 0 do return .continue
  let_expr HPow.hPow _ _ _ _ two k := p | return .continue
  unless two.nat? == some 2 do return .continue
  let j := l.log2
  let h ← mkDecideProof (← mkEq L (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit j]))
  let pf ← mkAppOptM ``two_pow_dvd_iff #[k, mkNatLit j, L, h]
  let rhs ← mkAppM ``LE.le #[k, mkNatLit j]
  return .done { expr := rhs, proof? := some (← mkPropExt pf) }

end Zig.Full.Auto

/-- Library facts that are not arithmetic; extend with `macro_rules`. -/
syntax "fsym_fact" : tactic
macro_rules
  | `(tactic| fsym_fact) => `(tactic| first
      | with_reducible exact Zig.Full.Auto.kp_refl _
      | with_reducible exact Zig.Full.Auto.kp_extract _ _
      | with_reducible exact Zig.Full.Auto.kp_append _ _
      | with_reducible exact Zig.Full.Auto.kp_extract_append _ _ _
      | with_reducible exact Zig.Full.Auto.kp_extract_extract_append _ _ _ _
      | with_reducible exact Zig.Full.Auto.kp_extract_append_append _ _ _ _
      | with_reducible exact Zig.Full.Frac.half_add_half _
      | with_reducible exact Zig.Full.Auto.one_half_pos
      | with_reducible assumption
      | (apply Eq.symm; with_reducible assumption))
