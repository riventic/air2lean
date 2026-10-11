import AllocFba.Fba
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AllocSpec

/-!
# The translated `FixedBufferAllocator` satisfies the full-state `FAllocSpec`

`FBA.fallocSpec`: the four vtable entries of the translated `FixedBufferAllocator` (`Gen.lean`)
satisfy `FAllocSpec FLogic.total impl ctx (finv ctx B)` for every allocator struct `ctx` and every
buffer `B`, proved natively in the full-state logic (`ZigLean/Sep/Full`) from the generated code.
The legacy proof (`Fba.lean`) is not lifted: its invariant owns a pin byte of the buffer's block,
because there a cell is the only source of the block's size. Here the size comes from the
buffer's **extent share** (`docs/sep-full-state.md` §Block extents):

* The invariant `fown ctx B` owns the struct (`end_index = e` and the buffer slice, as two typed
  words), the free tail `[e, cap)` of the buffer, junk (padding and the bytes of non-last frees),
  the knowledge of the addresses of the buffer's and the struct's blocks, and a share
  `bshare b q (ptr.off + cap)` of the buffer block's extent: the block reaches the buffer's end
  even when every byte of the buffer is lent out, so `buffer.ptr + end_index` is formed
  (`ptrProject`, MM-3). A share, not the full extent: the buffer may itself lie in a grant of
  another allocator.
* A grant gets half of the invariant's share, weakened to its own end (`EUpd.weaken`), as the
  stronger `FAllocSpec` requires; `free` and `resize` take it back (`EUpd.join` at the buffer's
  bound). The token says that the grant lies in the buffer, with the buffer's address and its
  cells' labels `S`, `K` (a full-state cell's size is a label: `FMatch` ignores it).

`fits n k := cap + 2^k + n ≤ 2^64`, as in the legacy proof.
-/

namespace AllocFba

open Zig Zig.Full Zig.Full.FAssn Gen

namespace FBA

open Zig.Wrap (toNat_ofNat_lt)
open Zig.Ops (two_pow_lt toNat_two_pow add_ok gt_eq)

/-! ## The invariant -/

/-- The buffer: its pointer and length, the address of its block, the size and kind labels of
its region cells, and the address of the struct's block. -/
structure FBuf where
  ptr : Ptr
  cap : Nat
  A : Nat
  S : Nat
  K : BlockKind
  cA : Nat

/-- The struct word `end_index = e`. -/
def wEnd (ctx : Ptr) (e : Nat) : FAssn := up (pts ctx 8 (BitVec.ofNat 64 e))

/-- The struct's buffer slice. -/
def wBuf (ctx : Ptr) (B : FBuf) : FAssn := up (pts (ctx.add 8) 8 (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice))

/-- The buffer's bound: its block reaches the buffer's end. -/
def bnd (B : FBuf) : Nat := B.ptr.off.toNat + B.cap

def FOk (ctx : Ptr) (B : FBuf) (e : Nat) (tail : Array Byte) : Prop :=
  e ≤ B.cap ∧ tail.size = B.cap - e ∧ B.A + B.ptr.off.toNat + B.cap < 2 ^ 64 ∧ 0 ≤ B.ptr.off ∧
    (B.cA + ctx.off.toNat) % 8 = 0 ∧ 0 ≤ ctx.off

/-- The parts of the invariant that do not depend on `end_index`: the buffer slice, the
knowledge of the two blocks' addresses, the extent share of the buffer's block, junk. -/
def fparts (ctx : Ptr) (B : FBuf) (q : Frac) (b cb : BlockId) : FAssn :=
  wBuf ctx B ⋆ (known cb B.cA ⋆ (known b B.A ⋆ (bshare b q (bnd B) ⋆ Junk)))

/-- The struct with `end_index = e`, and the other parts. -/
def fst (ctx : Ptr) (B : FBuf) (e : Nat) (q : Frac) (b cb : BlockId) : FAssn :=
  wEnd ctx e ⋆ fparts ctx B q b cb

/-- The free tail `[e, cap)` of the buffer. -/
def ftail (B : FBuf) (e : Nat) (tail : Array Byte) : FAssn :=
  up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail)

/-- The invariant's parts, with the block ids `b` (buffer) and `cb` (struct) named. -/
def fbody (ctx : Ptr) (B : FBuf) (e : Nat) (tail : Array Byte) (q : Frac) (b cb : BlockId) : FAssn :=
  fst ctx B e q b cb ⋆ ftail B e tail

def fown (ctx : Ptr) (B : FBuf) : FAssn :=
  FAssn.ex fun e => FAssn.ex fun tail => FAssn.ex fun q => FAssn.ex fun b => FAssn.ex fun cb =>
    ⟪FOk ctx B e tail ∧ B.ptr.block = some b ∧ ctx.block = some cb⟫ ⋆ fbody ctx B e tail q b cb

/-- The allocator issued the region: it lies in the buffer, with the buffer's address and labels. -/
def ftok (B : FBuf) (p : Ptr) (n _k A S : Nat) (K : BlockKind) (_q : Frac) : FAssn :=
  ⟪p.block = B.ptr.block ∧ A = B.A ∧ S = B.S ∧ K = B.K ∧ B.ptr.off ≤ p.off ∧
    p.off + n ≤ B.ptr.off + B.cap⟫

def ffits (B : FBuf) (n k : Nat) : Prop := B.cap + 2 ^ k + n ≤ 2 ^ 64

def finv (ctx : Ptr) (B : FBuf) : FAllocInv where
  own := fown ctx B
  tok := ftok B
  fits := ffits B

theorem fown_intro {ctx : Ptr} {B : FBuf} {e : Nat} {tail : Array Byte} {q : Frac} {b cb : BlockId}
    {r : Res} (hok : FOk ctx B e tail) (hb : B.ptr.block = some b) (hc : ctx.block = some cb)
    (h : fbody ctx B e tail q b cb r) : fown ctx B r :=
  ⟨e, tail, q, b, cb, sep_lift.mpr ⟨⟨hok, hb, hc⟩, h⟩⟩

/-! ## Providers of the body -/

section Providers

variable {ctx : Ptr} {B : FBuf} {e : Nat} {tail : Array Byte} {q : Frac} {b cb : BlockId} {R : FAssn}

theorem body_addrC : AddrOf cb B.cA (fst ctx B e q b cb ⋆ R) := by
  unfold fst fparts; exact AddrOf.known.sepL.sepR.sepR.sepL

theorem body_addrB : AddrOf b B.A (fst ctx B e q b cb ⋆ R) := by
  unfold fst fparts; exact AddrOf.known.sepL.sepR.sepR.sepR.sepL

theorem body_reach : Reaches b (bnd B) (fst ctx B e q b cb ⋆ R) := by
  unfold fst fparts; exact Reaches.share.sepL.sepR.sepR.sepR.sepR.sepL

/-- A nonempty typed value owns its last byte: its block reaches one past it. -/
theorem Reaches.pts {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} {b : BlockId}
    (hpb : p.block = some b) (hn : 0 < Enc.size T) :
    Reaches b (p.off.toNat + Enc.size T) (up (Zig.pts p a v)) := by
  have := Reaches.owned (P := up (Zig.pts p a v)) (b := b) (j := p.off.toNat + (Enc.size T - 1))
    fun r hr => by
      obtain ⟨A, S, K, bs, -, hs, -, hb, -⟩ := hr.1
      obtain ⟨b', hb', -, c, hc⟩ := bytesAt_ownsAt hb (by omega)
      rw [hpb] at hb'; cases hb'
      obtain ⟨fc, hfc, -⟩ := erase_cell hc
      exact ⟨fc, by rw [← hs]; exact hfc⟩
  exact this.mono (by omega)

theorem body_reachC (hc : ctx.block = some cb) (h0 : 0 ≤ ctx.off) :
    Reaches cb (ctx.off.toNat + 24) (fst ctx B e q b cb ⋆ R) := by
  have hc8 : (ctx.add 8).block = some cb := by simp [Ptr.add, hc]
  have := Reaches.pts (T := Slice) (p := ctx.add 8) (a := 8) (v := ⟨B.ptr, BitVec.ofNat 64 B.cap⟩)
    hc8 (by decide)
  have e : (ctx.add 8).off.toNat + Enc.size Slice = ctx.off.toNat + 24 := by
    rw [show Enc.size Slice = 16 from rfl]; simp [Ptr.add]; omega
  rw [e] at this
  unfold fst fparts; exact this.sepL.sepR.sepL

end Providers

/-! ## Steps on the struct -/

/-- A step that reads the left part. -/
theorem FTotalTriple.readL {α : Type} {X R : FAssn} {c : MemM α} {φ : α → Prop}
    (ht : FTotalTriple X c (fun v => ⟪φ v⟫ ⋆ X)) :
    FTotalTriple (X ⋆ R) c (fun v => ⟪φ v⟫ ⋆ (X ⋆ R)) :=
  ht.frame.post fun _ _ h => sep_assoc h

/-- A step that reads the right part. -/
theorem FTotalTriple.readR {α : Type} {X P : FAssn} {c : MemM α} {φ : α → Prop}
    (ht : FTotalTriple P c (fun v => ⟪φ v⟫ ⋆ P)) :
    FTotalTriple (X ⋆ P) c (fun v => ⟪φ v⟫ ⋆ (X ⋆ P)) :=
  ht.frame.conseq (fun _ h => sep_comm h) fun _ _ h => Full.sep_mono_right (fun _ h => Full.sep_comm h) (Full.sep_assoc h)

theorem pts_slice_field_load' {T : Type} [Enc T] {q : Ptr} {s : Slice} {o : Nat} {v : T}
    (hsz : Enc.size T = 8) (ho : o = 0 ∨ o = 8)
    (hv : ∀ bs : Array Byte, Enc.decode (bs.extract 0 8) = (pure s.ptr : Result Ptr) →
      Enc.decode (bs.extract 8 16) = (pure s.len : Result (BitVec 64)) →
      Enc.decode (bs.extract o (o + 8)) = (pure v : Result T)) :
    TotalTriple (pts q 8 s) (load T 8 (q.add o)) (fun r => ⌜r = v⌝ ∗ pts q 8 s) := by
  intro m hP hF hd hm hp hst
  obtain ⟨A, S, K, bs, ha, hs, h1, h2, hb⟩ := pts_slice_parts hp
  have hao : (A + q.off.toNat + o) % 8 = 0 := by rcases ho with rfl | rfl <;> omega
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (q := q.add o) (k := o) (n := Enc.size T) (a := 8) hb hm rfl
      (by omega) (by rcases ho with rfl | rfl <;> omega) hao
  have hv' : Enc.decode (blk.bytes.extract (q.off.toNat + o) (q.off.toNat + o + Enc.size T)) =
      pure v := by rw [hx, hsz]; exact hv bs h1 h2
  refine ⟨v, _, hP, load_run hacc hv' (noRace_of_singleThread hst.single _ _ _ _), hd, ?_,
    sep_lift.mpr ⟨rfl, hp⟩, hst.recordAt _ _ _ _⟩
  funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

/-- A load of a field of the struct's slice. -/
theorem fload_field {T : Type} [Enc T] {q : Ptr} {s : Slice} {o : Nat} {v : T}
    (hsz : Enc.size T = 8) (ho : o = 0 ∨ o = 8)
    (hv : ∀ bs : Array Byte, Enc.decode (bs.extract 0 8) = (pure s.ptr : Result Ptr) →
      Enc.decode (bs.extract 8 16) = (pure s.len : Result (BitVec 64)) →
      Enc.decode (bs.extract o (o + 8)) = (pure v : Result T)) :
    FTotalTriple (up (pts q 8 s)) (load T 8 (q.add o)) (fun r => ⟪r = v⟫ ⋆ up (pts q 8 s)) :=
  (FTotalTriple.ofTotal_up (pts_slice_field_load' hsz ho hv) (Tame.load T 8 _) (SizeFree.pts q 8 s)
    (Keeps.load T 8 _)).post fun _ _ h => sep_lift.mpr (up_lift.mp h)

section Struct

variable {ctx : Ptr} {B : FBuf} {e : Nat} {q : Frac} {b cb : BlockId} {R : FAssn}

theorem fload_end : FTotalTriple (fst ctx B e q b cb ⋆ R) (load (BitVec 64) 8 ctx)
    (fun r => ⟪r = BitVec.ofNat 64 e⟫ ⋆ (fst ctx B e q b cb ⋆ R)) := by
  unfold fst; exact FTotalTriple.readL (FTotalTriple.readL (FTotalTriple.load (by decide)))

theorem fload_ptr : FTotalTriple (fst ctx B e q b cb ⋆ R) (load Ptr 8 (ctx.add 8))
    (fun r => ⟪r = B.ptr⟫ ⋆ (fst ctx B e q b cb ⋆ R)) := by
  have t := fload_field (T := Ptr) (q := ctx.add 8) (s := ⟨B.ptr, BitVec.ofNat 64 B.cap⟩) (o := 0)
    (v := B.ptr) rfl (Or.inl rfl) (fun bs h1 _ => by simpa using h1)
  push_cast at t
  simp only [Norm.add_zero_ptr] at t
  unfold fst fparts
  exact FTotalTriple.readL (FTotalTriple.readR (FTotalTriple.readL t))

theorem fload_len : FTotalTriple (fst ctx B e q b cb ⋆ R) (load (BitVec 64) 8 ((ctx.add 8).add 8))
    (fun r => ⟪r = BitVec.ofNat 64 B.cap⟫ ⋆ (fst ctx B e q b cb ⋆ R)) := by
  have t := fload_field (T := BitVec 64) (q := ctx.add 8) (s := ⟨B.ptr, BitVec.ofNat 64 B.cap⟩)
    (o := 8) (v := BitVec.ofNat 64 B.cap) rfl (Or.inr rfl) (fun bs _ h2 => h2)
  push_cast at t
  unfold fst fparts
  exact FTotalTriple.readL (FTotalTriple.readR (FTotalTriple.readL t))

theorem fload_slice : FTotalTriple (fst ctx B e q b cb ⋆ R) (load Slice 8 (ctx.add 8))
    (fun r => ⟪r = ⟨B.ptr, BitVec.ofNat 64 B.cap⟩⟫ ⋆ (fst ctx B e q b cb ⋆ R)) := by
  unfold fst fparts
  exact FTotalTriple.readL (FTotalTriple.readR (FTotalTriple.readL (FTotalTriple.load (by decide))))

theorem fstore_end (e' : Nat) : FTotalTriple (fst ctx B e q b cb ⋆ R) (store 8 ctx (BitVec.ofNat 64 e'))
    (fun _ => fst ctx B e' q b cb ⋆ R) := by
  unfold fst; exact (FTotalTriple.store (by decide) _).frame.frame

/-- The `@alignCast` of the context pointer passes. -/
theorem fptrAddr_ctx (hc : ctx.block = some cb) (hal : (B.cA + ctx.off.toNat) % 8 = 0)
    (h0 : 0 ≤ ctx.off) : FTotalTriple (fst ctx B e q b cb ⋆ R) (ptrAddr ctx)
      (fun r => ⟪(BitVec.ofInt 64 r &&& 7) = 0⟫ ⋆ (fst ctx B e q b cb ⋆ R)) := by
  refine (FTotalTriple.ptrAddr_of hc body_addrC).post fun r x h => ?_
  obtain ⟨hr, h⟩ := Full.sep_lift.mp h
  refine Full.sep_lift.mpr ⟨?_, h⟩
  subst hr
  have hx : ((B.cA : Int) + ctx.off) % 2 ^ 3 = 0 := by
    have : ((B.cA + ctx.off.toNat : Nat) : Int) % ((2 ^ 3 : Nat) : Int) = 0 := by exact_mod_cast hal
    rw [Int.natCast_add, Int.toNat_of_nonneg h0] at this
    exact_mod_cast this
  exact Ops.and_mask_eq_zero (k := 3) (by decide) (by omega) hx

theorem fcheckAlign_ctx (hc : ctx.block = some cb) (hal : (B.cA + ctx.off.toNat) % 8 = 0)
    (h0 : 0 ≤ ctx.off) : FTotalTriple (fst ctx B e q b cb ⋆ R) (checkAlign 8 ctx)
      (fun _ => fst ctx B e q b cb ⋆ R) :=
  FTotalTriple.checkAlign_of hc body_addrC (by
    have : ((B.cA + ctx.off.toNat : Nat) : Int) % ((8 : Nat) : Int) = 0 := by exact_mod_cast hal
    rw [Int.natCast_add, Int.toNat_of_nonneg h0] at this
    exact_mod_cast this)

theorem fproject_ctx8 (hc : ctx.block = some cb) (h0 : 0 ≤ ctx.off) :
    FTotalTriple (fst ctx B e q b cb ⋆ R) (ptrProject ctx (·.add 8))
      (fun r => ⟪r = ctx.add 8⟫ ⋆ (fst ctx B e q b cb ⋆ R)) :=
  FTotalTriple.ptrProject_of hc (body_reachC hc h0) h0 (by omega) (by omega) (by omega)

theorem fproject_ctx16 (hc : ctx.block = some cb) (h0 : 0 ≤ ctx.off) :
    FTotalTriple (fst ctx B e q b cb ⋆ R) (ptrProject (ctx.add 8) (·.add 8))
      (fun r => ⟪r = (ctx.add 8).add 8⟫ ⋆ (fst ctx B e q b cb ⋆ R)) :=
  FTotalTriple.ptrProject_of (by simp [Ptr.add, hc]) (body_reachC hc h0) (by simp [Ptr.add]; omega)
    (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega)

end Struct

/-! ## The helpers -/

/-- `alignPointerOffset(q, 2 ^ k)` (`alignPointerOffset_spec`), with the address of `q`'s block
from a provider. -/
theorem falignPointerOffset_spec {P : FAssn} {q : Ptr} {b : BlockId} {A k : Nat} (hk : k < 64)
    (hqb : q.block = some b) (hown : AddrOf b A P) (h0 : 0 ≤ q.off) :
    FTotalTriple P (mem_alignPointerOffset__anon_1fdb4fd23aee q (BitVec.ofNat 64 (2 ^ k)))
      (fun r => ⟪AlignRes k ((A : Int) + q.off) r⟫ ⋆ P) := by
  simp only [mem_alignPointerOffset__anon_1fdb4fd23aee]
  gen_norm
  simp only [isValidAlign_eq hk, debug_assert_true, Norm.lift_pure, pure_bind, le_eq,
    toNat_two_pow hk]
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos (by simp only [decide_eq_true_eq]; exact Nat.le_refl 1)]
    exact FTotalTriple.conseq (FTotalTriple.ret (Q := fun r => ⟪AlignRes 0 ((A : Int) + q.off) r⟫ ⋆ P)
      (some 0)) (fun _ hp => Full.sep_lift.mpr ⟨by simp [AlignRes, Nat.mod_one], hp⟩) (fun _ _ h => h)
  have hk1 : ¬ 2 ^ k ≤ 1 := by
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    simp at this; omega
  rw [if_neg (by simp only [decide_eq_true_eq]; exact hk1)]
  simp only [sub_one_eq hk, Norm.lift_pure, pure_bind]
  refine FTotalTriple.bind (FTotalTriple.ptrAddr_of hqb hown) fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  have hxnat : (BitVec.ofInt 64 ((A : Int) + q.off)).toNat = ((A : Int) + q.off).toNat % 2 ^ 64 :=
    ofInt_toNat (by omega)
  generalize hX : BitVec.ofInt 64 ((A : Int) + q.off) = X at hxnat ⊢
  have hm := toNat_mask hk
  have hpk := Nat.two_pow_pos k
  by_cases hov : X.toNat + (2 ^ k - 1) < 2 ^ 64
  · have hnov : (Zig.addWithOverflow false X (BitVec.ofNat 64 (2 ^ k - 1))).snd = 0 := by
      simp only [Zig.addWithOverflow, Bool.false_eq_true, ↓reduceIte, BitVec.uaddOverflow, hm]
      rw [if_neg (by simp; omega)]
    obtain ⟨hle, hlt, hal⟩ := alignOffset_facts hk X hov
    simp only [Zig.addWithOverflow, Bool.false_eq_true, ↓reduceIte] at hnov ⊢
    rw [hnov]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [sub_ok hle, Norm.lift_pure, pure_bind, rem_one, Norm.lift_pure, pure_bind]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, divTrunc_one, Norm.lift_pure,
      pure_bind]
    refine FTotalTriple.conseq (FTotalTriple.ret (Q := fun r => ⟪AlignRes k ((A : Int) + q.off) r⟫ ⋆ P)
      _) (fun _ hp => Full.sep_lift.mpr ⟨?_, hp⟩) (fun _ _ h => h)
    simp only [AlignRes]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hle)]
    have hdvd : 2 ^ k ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (Nat.le_of_lt hk)
    refine ⟨by omega, ?_⟩
    have e1 : ((A : Int) + q.off).toNat % 2 ^ 64 % 2 ^ k = ((A : Int) + q.off).toNat % 2 ^ k :=
      Nat.mod_mod_of_dvd _ hdvd
    rw [← hxnat] at e1
    have e2 : (X.toNat + ((X + BitVec.ofNat 64 (2 ^ k - 1) &&& ~~~BitVec.ofNat 64 (2 ^ k - 1)).toNat -
        X.toNat)) % 2 ^ k = 0 := by
      rw [Nat.add_sub_cancel' hle]; exact hal
    rw [Nat.add_mod, ← e1, ← Nat.add_mod]; exact e2
  · have hov' : (Zig.addWithOverflow false X (BitVec.ofNat 64 (2 ^ k - 1))).snd = 1 := by
      simp only [Zig.addWithOverflow, Bool.false_eq_true, ↓reduceIte, BitVec.uaddOverflow, hm]
      rw [if_pos (by simp; omega)]
    simp only [Zig.addWithOverflow, Bool.false_eq_true, ↓reduceIte] at hov' ⊢
    rw [hov']
    exact FTotalTriple.conseq (FTotalTriple.ret (Q := fun r => ⟪AlignRes k ((A : Int) + q.off) r⟫ ⋆ P)
      none) (fun _ hp => Full.sep_lift.mpr ⟨trivial, hp⟩) (fun _ _ h => h)

section Helpers

variable {ctx : Ptr} {B : FBuf} {e : Nat} {q : Frac} {b cb : BlockId} {R : FAssn}

/-- `ownsSlice(s)` of a slice inside the buffer is `true`. -/
theorem fownsSlice_spec {s : Slice} (hb : B.ptr.block = some b) (hc : ctx.block = some cb)
    (hc0 : 0 ≤ ctx.off) (hsb : s.ptr.block = B.ptr.block) (h0 : 0 ≤ B.ptr.off)
    (hlo : B.ptr.off ≤ s.ptr.off) (hhi : s.ptr.off + s.len.toNat ≤ B.ptr.off + B.cap)
    (hA : B.A + B.ptr.off.toNat + B.cap < 2 ^ 64) :
    FTotalTriple (fst ctx B e q b cb ⋆ R) (heap_FixedBufferAllocator_ownsSlice ctx s)
      (fun r => ⟪r = true⟫ ⋆ (fst ctx B e q b cb ⋆ R)) := by
  simp only [heap_FixedBufferAllocator_ownsSlice, heap_FixedBufferAllocator_sliceContainsSlice]
  gen_norm
  have hcap : B.cap < 2 ^ 64 := by omega
  refine FTotalTriple.bind (fproject_ctx8 hc hc0) fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  refine FTotalTriple.bind fload_slice fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  have hsb' : s.ptr.block = some b := by rw [hsb, hb]
  refine FTotalTriple.bind (FTotalTriple.ptrAddr_of hsb' body_addrB) fun x₁ =>
    FTotalTriple.lift fun hx₁ => ?_
  subst hx₁
  refine FTotalTriple.bind (FTotalTriple.ptrAddr_of hb body_addrB) fun x₂ =>
    FTotalTriple.lift fun hx₂ => ?_
  subst hx₂
  have e1 : (BitVec.ofInt 64 ((B.A : Int) + s.ptr.off)).toNat = B.A + s.ptr.off.toNat := by
    rw [ofInt_toNat_lt (by omega) (by omega)]; omega
  have e2 : (BitVec.ofInt 64 ((B.A : Int) + B.ptr.off)).toNat = B.A + B.ptr.off.toNat := by
    rw [ofInt_toNat_lt (by omega) (by omega)]; omega
  have hge : Zig.ge false (BitVec.ofInt 64 ((B.A : Int) + s.ptr.off))
      (BitVec.ofInt 64 ((B.A : Int) + B.ptr.off)) = true := by
    simp only [Zig.ge, le_eq, e1, e2, decide_eq_true_eq]; omega
  rw [if_pos hge]
  refine FTotalTriple.bind (FTotalTriple.ptrAddr_of hsb' body_addrB) fun x₃ =>
    FTotalTriple.lift fun hx₃ => ?_
  subst hx₃
  rw [add_ok (by rw [e1]; omega), Norm.lift_pure, pure_bind]
  refine FTotalTriple.bind (FTotalTriple.ptrAddr_of hb body_addrB) fun x₅ =>
    FTotalTriple.lift fun hx₅ => ?_
  subst hx₅
  rw [add_ok (by rw [e2, toNat_ofNat_lt hcap]; omega), Norm.lift_pure, pure_bind]
  refine FTotalTriple.conseq (FTotalTriple.ret (Q := fun r => ⟪r = true⟫ ⋆ (fst ctx B e q b cb ⋆ R)) _)
    (fun _ hp => Full.sep_lift.mpr ⟨?_, hp⟩) (fun _ _ h => h)
  rw [le_eq, toNat_add_ok (by rw [e1]; omega), toNat_add_ok (by rw [e2, toNat_ofNat_lt hcap]; omega),
    e1, e2, toNat_ofNat_lt hcap]
  simp only [decide_eq_true_eq]; omega

/-- `isLastAllocation(s)`: the end of the slice (in bounds by the grant's share, `hS`) and of the
used part (by the invariant's share) are formed and compared. -/
theorem fisLast_spec {s : Slice} (hb : B.ptr.block = some b) (hc : ctx.block = some cb)
    (hc0 : 0 ≤ ctx.off) (hsb : s.ptr.block = B.ptr.block)
    (hS : Reaches b (s.ptr.off.toNat + s.len.toNat) (fst ctx B e q b cb ⋆ R)) (he : e ≤ B.cap)
    (hcap : B.cap < 2 ^ 64) (h0 : 0 ≤ B.ptr.off) (hlo : B.ptr.off ≤ s.ptr.off) :
    FTotalTriple (fst ctx B e q b cb ⋆ R) (heap_FixedBufferAllocator_isLastAllocation ctx s)
      (fun r => ⟪r = decide (s.ptr.off + s.len.toNat = B.ptr.off + e)⟫ ⋆ (fst ctx B e q b cb ⋆ R)) := by
  simp only [heap_FixedBufferAllocator_isLastAllocation]
  gen_norm
  have hsb' : s.ptr.block = some b := by rw [hsb, hb]
  refine FTotalTriple.bind (FTotalTriple.ptrProject_elem_of (size := 1) (i := s.len) hsb' hS
    (by omega) (by push_cast; omega)) fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  refine FTotalTriple.bind (fproject_ctx8 hc hc0) fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  refine FTotalTriple.bind fload_ptr fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  refine FTotalTriple.bind fload_end fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  have heN : (BitVec.ofNat 64 e).toNat = e := toNat_ofNat_lt (by omega)
  refine FTotalTriple.bind (FTotalTriple.ptrProject_elem_of (size := 1) (i := BitVec.ofNat 64 e) hb
    body_reach h0 (by rw [heN]; simp only [bnd]; push_cast; omega)) fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  rw [bind_pure]
  refine FTotalTriple.conseq (FTotalTriple.ptrEqAddr_of (p := s.ptr.elem 1 s.len)
    (q := B.ptr.elem 1 (BitVec.ofNat 64 e)) hsb' hb body_addrB) (fun _ hp => hp) fun r _ hp => ?_
  obtain ⟨hr, hp⟩ := Full.sep_lift.mp hp
  refine Full.sep_lift.mpr ⟨?_, hp⟩
  rw [hr]
  simp only [Ptr.elem_eq, Ptr.add, heN, Nat.one_mul]

end Helpers

/-! ## Opening and closing the invariant, grants -/

section Inv

variable {ctx : Ptr} {B : FBuf} {e : Nat} {tail : Array Byte} {q : Frac} {b cb : BlockId}

/-- Half of the invariant's share splits off. -/
theorem fparts_split {r : Res} (h : fparts ctx B q b cb r) :
    (fparts ctx B q.half b cb ⋆ bshare b q.half (bnd B)) r := by
  unfold fparts at h ⊢
  have h1 : (wBuf ctx B ⋆ (known cb B.cA ⋆ (known b B.A ⋆ (Junk ⋆ bshare b q (bnd B))))) r :=
    Full.of_eq (by ac_rfl) h
  have h2 : (wBuf ctx B ⋆ (known cb B.cA ⋆ (known b B.A ⋆ (Junk ⋆
      (bshare b q.half (bnd B) ⋆ bshare b q.half (bnd B)))))) r :=
    Full.sep_mono_right (fun _ x => Full.sep_mono_right (fun _ y => Full.sep_mono_right
      (fun _ z => Full.sep_mono_right (fun _ w => (bshare_split (Frac.half_pos w.1)
        (Frac.half_pos w.1)).mp (by rw [Frac.half_add_half]; exact w)) z) y) x) h1
  exact Full.of_eq (by ac_rfl) h2

/-- Bytes go to junk. -/
theorem fparts_absorb {X : Assn} {r : Res} (h : (up X ⋆ fparts ctx B q b cb) r) : fparts ctx B q b cb r := by
  unfold fparts at h ⊢
  have h1 : (wBuf ctx B ⋆ (known cb B.cA ⋆ (known b B.A ⋆ (bshare b q (bnd B) ⋆ (up X ⋆ Junk))))) r :=
    Full.of_eq (by ac_rfl) h
  exact Full.sep_mono_right (fun _ x => Full.sep_mono_right (fun _ y => Full.sep_mono_right
    (fun _ z => Full.sep_mono_right (fun _ w => junk_absorb w) z) y) x) h1

/-- A share at a bound up to the buffer's end joins the invariant's. -/
theorem fparts_join {q' : Frac} {k : Nat} (hk : k ≤ bnd B) :
    EUpd (fparts ctx B q b cb ⋆ bshare b q' k) (fparts ctx B (q.add q') b cb) := by
  unfold fparts
  refine EUpd.trans (EUpd.of_imp (P' := (wBuf ctx B ⋆ (known cb B.cA ⋆ (known b B.A ⋆ Junk))) ⋆
    (bshare b q (bnd B) ⋆ bshare b q' k)) fun _ h => Full.of_eq (by ac_rfl) h)
    (EUpd.trans (EUpd.frameL EUpd.join) (EUpd.of_imp fun _ h => ?_))
  rw [Nat.max_eq_left hk] at h
  exact Full.of_eq (by ac_rfl) h

theorem fclose {R : FAssn} {r : Res} (hok : FOk ctx B e tail) (hb : B.ptr.block = some b)
    (hc : ctx.block = some cb) (h : (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ R)) r)
    (hR : ∀ r, R r → ∃ X, up X r) : fown ctx B r := by
  refine fown_intro (q := q) hok hb hc ?_
  unfold fbody
  have h1 : ((wEnd ctx e ⋆ (R ⋆ fparts ctx B q b cb)) ⋆ ftail B e tail) r := by
    unfold fst at h; exact Full.of_eq (by ac_rfl) h
  refine Full.sep_mono_left (fun _ x => Full.sep_mono_right (fun r y => ?_) x) h1
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := y
  obtain ⟨X, hX⟩ := hR r₁ h1
  exact fparts_absorb ⟨r₁, r₂, hd, rfl, hX, h2⟩

/-- Open the invariant with a frame. -/
theorem fown_open {α : Type} {c : MemM α} {Q : α → FAssn} {R : FAssn}
    (ht : ∀ e tail q b cb, FOk ctx B e tail → B.ptr.block = some b → ctx.block = some cb →
      FTotalTriple (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ R)) c Q) :
    FTotalTriple (fown ctx B ⋆ R) c Q := by
  refine FTotalTriple.pre (P := FAssn.ex fun e => FAssn.ex fun tail => FAssn.ex fun q =>
    FAssn.ex fun b => FAssn.ex fun cb =>
      ⟪FOk ctx B e tail ∧ B.ptr.block = some b ∧ ctx.block = some cb⟫ ⋆
        (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ R))) ?_ fun r h => ?_
  · exact FTotalTriple.ex fun e => FTotalTriple.ex fun tail => FTotalTriple.ex fun q =>
      FTotalTriple.ex fun b => FTotalTriple.ex fun cb => FTotalTriple.lift fun ⟨hok, hb, hc⟩ =>
        ht e tail q b cb hok hb hc
  · obtain ⟨r₁, r₂, hd, rfl, ⟨e, tail, q, b, cb, h1⟩, h2⟩ := h
    obtain ⟨hf, h1⟩ := Full.sep_lift.mp h1
    refine ⟨e, tail, q, b, cb, Full.sep_lift.mpr ⟨hf, ?_⟩⟩
    unfold fbody at h1
    exact Full.sep_assoc ⟨r₁, r₂, hd, rfl, h1, h2⟩

/-- A grant of the buffer. -/
theorem fgrant_intro {p : Ptr} {k : Nat} {bs : Array Byte} {q' : Frac} {r : Res}
    (hpb : p.block = some b) (hb : B.ptr.block = some b) (hlo : B.ptr.off ≤ p.off)
    (hhi : p.off + bs.size ≤ B.ptr.off + B.cap)
    (h : (up (regionIn p B.A B.S B.K (2 ^ k) bs) ⋆ bshare b q' (p.off.toNat + bs.size)) r) :
    (finv ctx B).granted p k bs r :=
  ⟨B.A, B.S, B.K, q', Full.sep_mono_right (fun _ x => Full.sep_lift.mpr
    ⟨⟨by rw [hpb, hb], rfl, rfl, rfl, hlo, hhi⟩, ⟨b, Full.sep_lift.mpr ⟨hpb, x⟩⟩⟩) h⟩

end Inv

/-! ## `alloc` -/

/-- After `alloc` has moved `end_index` from `e` to `e + d + n`: the padding `d` is junk, the
next `n` bytes are a grant with half of the invariant's share (weakened to the grant's end), the
rest is the new tail. -/
theorem fcarve {ctx : Ptr} {B : FBuf} {e d n k : Nat} {tail : Array Byte} {q : Frac} {b cb : BlockId}
    (hok : FOk ctx B e tail) (hb : B.ptr.block = some b) (hc : ctx.block = some cb)
    (hfit : e + d + n ≤ B.cap) (hal : (B.A + B.ptr.off.toNat + e + d) % 2 ^ k = 0) :
    EUpd (fst ctx B (e + d + n) q b cb ⋆ (ftail B e tail ⋆ emp))
      ((finv ctx B).allocPost n k (some (B.ptr.add ((e + d : Nat) : Int)))) := by
  obtain ⟨he, hts, hA, h0, hal8, hc0⟩ := hok
  have hq0 : (B.ptr.add (e : Int)).off.toNat = B.ptr.off.toNat + e := off_add_nat h0
  have hpd : (B.ptr.add (e : Int)).add ((d : Nat) : Int) = B.ptr.add ((e + d : Nat) : Int) :=
    Region.Ptr.add_add_nat _ _ _
  have hpdn : (B.ptr.add (e : Int)).add ((d + n : Nat) : Int) = B.ptr.add ((e + d + n : Nat) : Int) := by
    rw [Region.Ptr.add_add_nat, Nat.add_assoc]
  let p := B.ptr.add ((e + d : Nat) : Int)
  let gbs := (tail.extract d tail.size).extract 0 n
  let ntail := (tail.extract d tail.size).extract n (tail.extract d tail.size).size
  have hcarve : ∀ h', regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail h' →
      (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 (tail.extract 0 d) ∗
        (regionIn p B.A B.S B.K (2 ^ k) gbs ∗
          regionIn (B.ptr.add ((e + d + n : Nat) : Int)) B.A B.S B.K 1 ntail)) h' := by
    intro h' x
    have hc := Region.regionIn_carve x (pad := d) (len := n) (a := 2 ^ k) (by omega)
      (by rw [hq0, ← Nat.add_assoc]; exact hal)
    rw [hpd, hpdn] at hc
    exact hc
  have hpb : p.block = some b := by simp [p, Ptr.add, hb]
  have hgs : gbs.size = n := by simp only [gbs, Array.size_extract]; omega
  have hpo : p.off.toNat = B.ptr.off.toNat + (e + d) := off_add_nat h0
  refine EUpd.trans (EUpd.of_imp (P' := ((fst ctx B (e + d + n) q.half b cb ⋆ ftail B (e + d + n) ntail) ⋆
      up (regionIn p B.A B.S B.K (2 ^ k) gbs)) ⋆ bshare b q.half (bnd B)) fun r h => ?_)
    (EUpd.trans (EUpd.frameL (EUpd.weaken (k' := p.off.toNat + gbs.size) (by
      simp only [bnd]; omega))) (EUpd.of_imp fun r h => ?_))
  · have h1 : (fst ctx B (e + d + n) q b cb ⋆ ftail B e tail) r :=
      Full.sep_mono_right (fun _ x => Full.sep_emp.mp x) h
    have h2 : (fst ctx B (e + d + n) q b cb ⋆
        (up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 (tail.extract 0 d)) ⋆
          (up (regionIn p B.A B.S B.K (2 ^ k) gbs) ⋆
            up (regionIn (B.ptr.add ((e + d + n : Nat) : Int)) B.A B.S B.K 1 ntail)))) r :=
      Full.sep_mono_right (fun r x => Full.sep_mono_right (fun _ y => Full.up_sep y)
        (Full.up_sep ⟨hcarve _ x.1, x.2⟩)) h1
    unfold fst at h2
    have h3 : ((wEnd ctx (e + d + n) ⋆
        (up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 (tail.extract 0 d)) ⋆ fparts ctx B q b cb)) ⋆
        (up (regionIn p B.A B.S B.K (2 ^ k) gbs) ⋆
          up (regionIn (B.ptr.add ((e + d + n : Nat) : Int)) B.A B.S B.K 1 ntail))) r :=
      Full.of_eq (by ac_rfl) h2
    have h4 : ((wEnd ctx (e + d + n) ⋆ (fparts ctx B q.half b cb ⋆ bshare b q.half (bnd B))) ⋆
        (up (regionIn p B.A B.S B.K (2 ^ k) gbs) ⋆
          up (regionIn (B.ptr.add ((e + d + n : Nat) : Int)) B.A B.S B.K 1 ntail))) r :=
      Full.sep_mono_left (fun _ x => Full.sep_mono_right
        (fun _ y => fparts_split (fparts_absorb y)) x) h3
    unfold fst ftail
    exact Full.of_eq (by ac_rfl) h4
  · have h1 : ((fst ctx B (e + d + n) q.half b cb ⋆ ftail B (e + d + n) ntail) ⋆
        (up (regionIn p B.A B.S B.K (2 ^ k) gbs) ⋆ bshare b q.half (p.off.toNat + gbs.size))) r :=
      Full.of_eq (by ac_rfl) h
    show (fown ctx B ⋆ FAssn.ex fun bs => ⟪bs.size = n⟫ ⋆ (finv ctx B).granted p k bs) r
    refine Full.sep_mono (fun r x => fown_intro (e := e + d + n) (tail := ntail) (q := q.half)
      ⟨by omega, by simp only [ntail, Array.size_extract]; omega, hA, h0, hal8, hc0⟩ hb hc
      (by unfold fbody; exact x))
      (fun r x => ⟨gbs, Full.sep_lift.mpr ⟨hgs, fgrant_intro hpb hb (by simp [p, Ptr.add]; omega)
        (by rw [hgs]; simp [p, Ptr.add]; omega) x⟩⟩) h1

theorem emp_up {r : Res} (h : emp r) : ∃ X, up X r := ⟨Assn.emp, Full.up_emp.mpr h⟩

theorem falloc_spec (ctx : Ptr) (B : FBuf) (n : BitVec 64) (k : Nat) (ra : BitVec 64)
    (hn : 0 < n.toNat) (hk : k < 64) (hfit : ffits B n.toNat k) :
    FTotalTriple (fown ctx B) (impl.alloc ctx n k ra) ((finv ctx B).allocPost n.toNat k) := by
  refine FTotalTriple.pre (P := fown ctx B ⋆ emp) ?_ (fun _ h => Full.sep_emp.mpr h)
  refine fown_open fun e tail q b cb hok hb hc => ?_
  have hok' := hok
  obtain ⟨he, hts, hA, h0, hal8, hc0⟩ := hok
  unfold impl
  simp only [heap_FixedBufferAllocator_alloc]
  gen_norm
  have hpk := Nat.two_pow_pos k
  have hcap : B.cap < 2 ^ 64 := by unfold ffits at hfit; omega
  have heN : (BitVec.ofNat 64 e).toNat = e := toNat_ofNat_lt (by omega)
  have hclose : ∀ r, (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ emp)) r →
      (finv ctx B).allocPost n.toNat k none r := fun r h => fclose hok' hb hc h fun _ => emp_up
  refine FTotalTriple.bind (fptrAddr_ctx hc hal8 hc0) fun x => FTotalTriple.lift fun hx => ?_
  rw [if_pos hx, toByteUnits_eq hk, Norm.lift_pure, pure_bind]
  refine FTotalTriple.bind (fcheckAlign_ctx hc hal8 hc0) fun _ => ?_
  refine FTotalTriple.bind (fproject_ctx8 hc hc0) fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  refine FTotalTriple.bind fload_ptr fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  refine FTotalTriple.bind fload_end fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  refine FTotalTriple.bind (FTotalTriple.ptrProject_elem_of (size := 1) (i := BitVec.ofNat 64 e) hb
    body_reach h0 (by rw [heN]; simp only [bnd]; push_cast; omega)) fun x => FTotalTriple.lift fun hx => ?_
  subst hx
  refine FTotalTriple.bind (falignPointerOffset_spec (A := B.A) hk (by simp [Ptr.elem, Ptr.add, hb])
    body_addrB (by simp [Ptr.elem, Ptr.add]; omega)) fun r => FTotalTriple.lift fun hr => ?_
  cases r with
  | none =>
    exact FTotalTriple.conseq (FTotalTriple.ret (Q := (finv ctx B).allocPost n.toNat k) none) hclose
      (fun _ _ h => h)
  | some d =>
    obtain ⟨hd, hal⟩ := hr
    simp only [Option.elim]
    refine FTotalTriple.bind fload_end fun x => FTotalTriple.lift fun hx => ?_
    subst hx
    have hed : (BitVec.ofNat 64 e).toNat + d.toNat < 2 ^ 64 := by
      rw [heN]; unfold ffits at hfit; omega
    rw [add_ok hed, Norm.lift_pure, pure_bind]
    have hedn : (BitVec.ofNat 64 e + d).toNat + n.toNat < 2 ^ 64 := by
      rw [toNat_add_ok hed, heN]; unfold ffits at hfit; omega
    rw [add_ok hedn, Norm.lift_pure, pure_bind]
    refine FTotalTriple.bind (fproject_ctx8 hc hc0) fun x => FTotalTriple.lift fun hx => ?_
    subst hx
    refine FTotalTriple.bind (fproject_ctx16 hc hc0) fun x => FTotalTriple.lift fun hx => ?_
    subst hx
    refine FTotalTriple.bind fload_len fun x => FTotalTriple.lift fun hx => ?_
    subst hx
    have hv : (BitVec.ofNat 64 e + d + n).toNat = e + d.toNat + n.toNat := by
      rw [toNat_add_ok hedn, toNat_add_ok hed, heN]
    rw [gt_eq, hv, toNat_ofNat_lt hcap]
    by_cases hroom : B.cap < e + d.toNat + n.toNat
    · rw [if_pos (by simpa using hroom)]
      exact FTotalTriple.conseq (FTotalTriple.ret (Q := (finv ctx B).allocPost n.toNat k) none) hclose
        (fun _ _ h => h)
    rw [if_neg (by simpa using hroom)]
    have hst : BitVec.ofNat 64 e + d + n = BitVec.ofNat 64 (e + d.toNat + n.toNat) := by
      apply BitVec.eq_of_toNat_eq; rw [hv, toNat_ofNat_lt (by omega)]
    rw [hst]
    refine FTotalTriple.bind (fstore_end (e + d.toNat + n.toNat)) fun _ => ?_
    refine FTotalTriple.bind (fproject_ctx8 hc hc0) fun x => FTotalTriple.lift fun hx => ?_
    subst hx
    refine FTotalTriple.bind fload_ptr fun x => FTotalTriple.lift fun hx => ?_
    subst hx
    have hed' : (BitVec.ofNat 64 e + d).toNat = e + d.toNat := by rw [toNat_add_ok hed, heN]
    refine FTotalTriple.bind (FTotalTriple.ptrProject_elem_of (size := 1) (i := BitVec.ofNat 64 e + d)
      hb body_reach h0 (by rw [hed']; simp only [bnd]; push_cast; omega))
      fun x => FTotalTriple.lift fun hx => ?_
    subst hx
    have hptr : B.ptr.elem 1 (BitVec.ofNat 64 e + d) = B.ptr.add ((e + d.toNat : Nat) : Int) := by
      rw [Ptr.elem_eq, toNat_add_ok hed, heN, Nat.one_mul]
    rw [hptr]
    have hal' : (B.A + B.ptr.off.toNat + e + d.toNat) % 2 ^ k = 0 := by
      have : ((B.A : Int) + (B.ptr.elem 1 (BitVec.ofNat 64 e)).off).toNat = B.A + B.ptr.off.toNat + e := by
        simp [Ptr.elem, Ptr.add, heN]; omega
      rw [this] at hal; omega
    exact FTotalTriple.eupd (fcarve hok' hb hc (by omega) hal')
      (FTotalTriple.ret (Q := (finv ctx B).allocPost n.toNat k) _)

/-! ## `resize`, `remap`, `free` -/

/-- The grant's facts from its token. -/
def FInBuf (B : FBuf) (s : Ptr) (n : Nat) : Prop :=
  s.block = B.ptr.block ∧ B.ptr.off ≤ s.off ∧ s.off + n ≤ B.ptr.off + B.cap

/-- A grant held by the client: its bytes and its share. -/
def fgr (B : FBuf) (b : BlockId) (s : Ptr) (k : Nat) (bs : Array Byte) (q' : Frac) : FAssn :=
  up (regionIn s B.A B.S B.K (2 ^ k) bs) ⋆ bshare b q' (s.off.toNat + bs.size)

section Grant

variable {ctx : Ptr} {B : FBuf} {e : Nat} {tail : Array Byte} {q q' : Frac} {b cb : BlockId}
  {s : Ptr} {k : Nat} {bs : Array Byte}

theorem fst_absorb {X : Assn} {r : Res} (h : (up X ⋆ fst ctx B e q b cb) r) : fst ctx B e q b cb r := by
  unfold fst at h ⊢
  have h1 : (wEnd ctx e ⋆ (up X ⋆ fparts ctx B q b cb)) r := Full.of_eq (by ac_rfl) h
  exact Full.sep_mono_right (fun _ x => fparts_absorb x) h1

theorem fst_split {r : Res} (h : fst ctx B e q b cb r) :
    (fst ctx B e q.half b cb ⋆ bshare b q.half (bnd B)) r := by
  unfold fst at h ⊢
  have h1 : (wEnd ctx e ⋆ (fparts ctx B q.half b cb ⋆ bshare b q.half (bnd B))) r :=
    Full.sep_mono_right (fun _ x => fparts_split x) h
  exact Full.sep_assoc' h1

theorem fst_join {k : Nat} (hk : k ≤ bnd B) :
    EUpd (fst ctx B e q b cb ⋆ bshare b q' k) (fst ctx B e (q.add q') b cb) := by
  unfold fst
  exact EUpd.trans (EUpd.of_imp fun _ h => Full.sep_assoc h) (EUpd.frameL (fparts_join hk))

/-- Open the invariant and the grant. -/
theorem fopen_grant {α : Type} {c : MemM α} {Q : α → FAssn}
    (ht : ∀ e tail q b cb q', FOk ctx B e tail → B.ptr.block = some b → ctx.block = some cb →
      FInBuf B s bs.size → s.block = some b →
      FTotalTriple (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ fgr B b s k bs q')) c Q) :
    FTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s k bs) c Q := by
  refine fown_open fun e tail q b cb hok hb hc => ?_
  refine FTotalTriple.pre (P := FAssn.ex fun q' => ⟪FInBuf B s bs.size ∧ s.block = some b⟫ ⋆
      (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ fgr B b s k bs q')))
    (FTotalTriple.ex fun q' => FTotalTriple.lift fun ⟨hin, hsb⟩ => ht e tail q b cb q' hok hb hc hin hsb)
    fun r h => ?_
  obtain ⟨r1, r2, hd, rfl, h1, r3, r4, hd', rfl, h3, A, S, K, q', r5, r6, hd'', rfl, h5, h6⟩ := h
  obtain ⟨⟨hsb, rfl, rfl, rfl, hlo, hhi⟩, b', h6⟩ := Full.sep_lift.mp h6
  obtain ⟨hsb', h6⟩ := Full.sep_lift.mp h6
  have hsb2 : s.block = some b := by rw [hsb, hb]
  rw [hsb2] at hsb'; cases hsb'
  exact ⟨q', Full.sep_lift.mpr ⟨⟨⟨hsb, hlo, hhi⟩, hsb2⟩,
    ⟨r1, _, hd, rfl, h1, r3, _, hd', rfl, h3, r5, r6, hd'', rfl, h5, h6⟩⟩⟩

/-- The common start of `resize` and `free`. -/
theorem fprologue {α : Type} {sl : Slice} {Q : α → FAssn} {c : Bool → MemM α}
    (hok : FOk ctx B e tail) (hb : B.ptr.block = some b) (hc : ctx.block = some cb)
    (hin : FInBuf B sl.ptr bs.size) (hsb : sl.ptr.block = some b) (hlen : sl.len.toNat = bs.size)
    (ht : FTotalTriple (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ fgr B b sl.ptr k bs q'))
      (c (decide (sl.ptr.off + bs.size = B.ptr.off + e))) Q) :
    FTotalTriple (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ fgr B b sl.ptr k bs q'))
      (ptrAddr ctx >>= fun x => if (BitVec.ofInt 64 x &&& 7) = 0 then
        checkAlign 8 ctx >>= fun _ =>
        heap_FixedBufferAllocator_ownsSlice ctx sl >>= fun y =>
        (StateT.lift (debug_assert y) : MemM Unit) >>= fun _ =>
        heap_FixedBufferAllocator_isLastAllocation ctx sl >>= c
      else throw .panic) Q := by
  obtain ⟨he, hts, hA, h0, hal8, hc0⟩ := hok
  obtain ⟨hib, hlo, hhi⟩ := hin
  refine FTotalTriple.bind (fptrAddr_ctx hc hal8 hc0) fun x => FTotalTriple.lift fun hx => ?_
  rw [if_pos hx]
  refine FTotalTriple.bind (fcheckAlign_ctx hc hal8 hc0) fun _ => ?_
  refine FTotalTriple.bind (fownsSlice_spec hb hc hc0 hib h0 hlo (by rw [hlen]; exact hhi) hA)
    fun y => FTotalTriple.lift fun hy => ?_
  subst hy
  rw [debug_assert_true, Norm.lift_pure, pure_bind]
  have hS : Reaches b (sl.ptr.off.toNat + sl.len.toNat)
      (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ fgr B b sl.ptr k bs q')) := by
    rw [hlen]; unfold fgr; exact Reaches.share.sepR.sepR.sepR
  refine FTotalTriple.bind (fisLast_spec hb hc hc0 hib hS he (by omega) h0 hlo)
    fun z => FTotalTriple.lift fun hz => ?_
  subst hz
  rw [hlen]
  exact ht

/-- Nothing changed: the invariant and the grant. -/
theorem fpost_same (hok : FOk ctx B e tail) (hb : B.ptr.block = some b) (hc : ctx.block = some cb)
    (hin : FInBuf B s bs.size) (hsb : s.block = some b) {r : Res}
    (h : (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ fgr B b s k bs q')) r) :
    ((finv ctx B).own ⋆ (finv ctx B).granted s k bs) r :=
  Full.sep_mono (fun _ x => fown_intro hok hb hc (by unfold fbody; exact x))
    (fun _ x => fgrant_intro hsb hb hin.2.1 hin.2.2 x) (Full.sep_assoc' h)

/-- The grant shrinks in place to `n` bytes; the rest is junk, the share is weakened. -/
theorem fpost_shrink {n : Nat} (hok : FOk ctx B e tail) (hb : B.ptr.block = some b)
    (hc : ctx.block = some cb) (hin : FInBuf B s bs.size) (hsb : s.block = some b) (hn : n ≤ bs.size) :
    EUpd (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ fgr B b s k bs q'))
      ((finv ctx B).own ⋆ FAssn.ex fun bs' => ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆
        (finv ctx B).granted s k bs') := by
  have hs0 : 0 ≤ s.off := by have := hok.2.2.2.1; have := hin.2.1; omega
  have hsz : (bs.extract 0 n).size = n := by simp only [Array.size_extract]; omega
  refine EUpd.trans (EUpd.of_imp (P' := (fst ctx B e q b cb ⋆ ftail B e tail) ⋆
      (up (regionIn s B.A B.S B.K (2 ^ k) (bs.extract 0 n)) ⋆ bshare b q' (s.off.toNat + bs.size)))
      fun r h => ?_)
    (EUpd.trans (EUpd.frameL (EUpd.frameL (EUpd.weaken (k' := s.off.toNat + (bs.extract 0 n).size)
      (by omega)))) (EUpd.of_imp fun r h => ?_))
  · unfold fgr at h
    have h1 : (fst ctx B e q b cb ⋆ (ftail B e tail ⋆
        ((up (regionIn s B.A B.S B.K (2 ^ k) (bs.extract 0 n)) ⋆
          up (regionIn (s.add n) B.A B.S B.K 1 (bs.extract n bs.size))) ⋆
            bshare b q' (s.off.toNat + bs.size)))) r :=
      Full.sep_mono_right (fun _ x => Full.sep_mono_right (fun _ y => Full.sep_mono_left
        (fun r z => Full.up_sep ⟨Region.regionIn_split z.1 (k := n) (a' := 1) hn (Nat.mod_one _), z.2⟩) y) x) h
    have h2 : ((up (regionIn (s.add n) B.A B.S B.K 1 (bs.extract n bs.size)) ⋆ fst ctx B e q b cb) ⋆
        (ftail B e tail ⋆ (up (regionIn s B.A B.S B.K (2 ^ k) (bs.extract 0 n)) ⋆
          bshare b q' (s.off.toNat + bs.size)))) r := Full.of_eq (by ac_rfl) h1
    exact Full.sep_assoc' (Full.sep_mono_left (fun _ x => fst_absorb x) h2)
  · refine Full.sep_mono (fun _ x => fown_intro hok hb hc (by unfold fbody; exact x))
      (fun _ x => ⟨bs.extract 0 n, Full.sep_lift.mpr ⟨⟨hsz, keepsPrefix_extract hn⟩,
        fgrant_intro hsb hb hin.2.1 (by rw [hsz]; have := hin.2.2; omega) x⟩⟩) h

/-- `end_index` moved back by `len - n`: the end of the last grant rejoins the tail. -/
theorem fpost_last_shrink {n : Nat} (hok : FOk ctx B e tail) (hb : B.ptr.block = some b)
    (hc : ctx.block = some cb) (hin : FInBuf B s bs.size) (hsb : s.block = some b)
    (hlast : s.off + bs.size = B.ptr.off + e) (hn : n ≤ bs.size) :
    EUpd (fst ctx B (e - (bs.size - n)) q b cb ⋆ (ftail B e tail ⋆ fgr B b s k bs q'))
      ((finv ctx B).own ⋆ FAssn.ex fun bs' => ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆
        (finv ctx B).granted s k bs') := by
  obtain ⟨he, hts, hA, h0, hal8, hc0⟩ := hok
  obtain ⟨hib, hlo, hhi⟩ := hin
  have hs0 : 0 ≤ s.off := by omega
  have hsz : (bs.extract 0 n).size = n := by simp only [Array.size_extract]; omega
  have hq : B.ptr.add (e : Int) = (s.add n).add ((bs.extract n bs.size).size : Nat) :=
    ptr_ext (by simp [Ptr.add, hib]) (by simp [Ptr.add]; omega)
  have hnew : s.add n = B.ptr.add ((e - (bs.size - n) : Nat) : Int) :=
    ptr_ext (by simp [Ptr.add, hib]) (by simp [Ptr.add]; omega)
  refine EUpd.trans (EUpd.of_imp (P' := (fst ctx B (e - (bs.size - n)) q b cb ⋆
        ftail B (e - (bs.size - n)) (bs.extract n bs.size ++ tail)) ⋆
      (up (regionIn s B.A B.S B.K (2 ^ k) (bs.extract 0 n)) ⋆ bshare b q' (s.off.toNat + bs.size)))
      fun r h => ?_)
    (EUpd.trans (EUpd.frameL (EUpd.frameL (EUpd.weaken (k' := s.off.toNat + (bs.extract 0 n).size)
      (by omega)))) (EUpd.of_imp fun r h => ?_))
  · unfold fgr at h
    have h1 : (fst ctx B (e - (bs.size - n)) q b cb ⋆ (ftail B e tail ⋆
        ((up (regionIn s B.A B.S B.K (2 ^ k) (bs.extract 0 n)) ⋆
          up (regionIn (s.add n) B.A B.S B.K 1 (bs.extract n bs.size))) ⋆
            bshare b q' (s.off.toNat + bs.size)))) r :=
      Full.sep_mono_right (fun _ x => Full.sep_mono_right (fun _ y => Full.sep_mono_left
        (fun r z => Full.up_sep ⟨Region.regionIn_split z.1 (k := n) (a' := 1) hn (Nat.mod_one _), z.2⟩) y) x) h
    unfold ftail at h1
    have h2 : (fst ctx B (e - (bs.size - n)) q b cb ⋆
        (up (regionIn (s.add n) B.A B.S B.K 1 (bs.extract n bs.size)) ⋆
          up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail)) ⋆
        (up (regionIn s B.A B.S B.K (2 ^ k) (bs.extract 0 n)) ⋆ bshare b q' (s.off.toNat + bs.size))) r :=
      Full.of_eq (by ac_rfl) h1
    refine Full.sep_mono_left (fun r x => Full.sep_mono_right (fun r y => ?_) x) (Full.sep_assoc' h2)
    have y' := Full.sep_up y
    rw [hq] at y'
    unfold ftail
    rw [← hnew]
    exact ⟨Region.regionIn_join y'.1, y'.2⟩
  · refine Full.sep_mono (fun _ x => fown_intro (e := e - (bs.size - n))
        (tail := bs.extract n bs.size ++ tail)
        ⟨by omega, (by simp only [Array.size_append, Array.size_extract]; omega), hA, h0, hal8, hc0⟩
        hb hc (by unfold fbody; exact x))
      (fun _ x => ⟨bs.extract 0 n, Full.sep_lift.mpr ⟨⟨hsz, keepsPrefix_extract hn⟩,
        fgrant_intro hsb hb hlo (by rw [hsz]; omega) x⟩⟩) h

/-- `end_index` moved forward by `n - len`: the last grant takes the start of the tail; its share
goes back to the invariant, and it gets half of the invariant's, weakened to its new end. -/
theorem fpost_last_grow {n : Nat} (hok : FOk ctx B e tail) (hb : B.ptr.block = some b)
    (hc : ctx.block = some cb) (hin : FInBuf B s bs.size) (hsb : s.block = some b)
    (hlast : s.off + bs.size = B.ptr.off + e) (hn : bs.size ≤ n) (hroom : e + (n - bs.size) ≤ B.cap) :
    EUpd (fst ctx B (e + (n - bs.size)) q b cb ⋆ (ftail B e tail ⋆ fgr B b s k bs q'))
      ((finv ctx B).own ⋆ FAssn.ex fun bs' => ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆
        (finv ctx B).granted s k bs') := by
  obtain ⟨he, hts, hA, h0, hal8, hc0⟩ := hok
  obtain ⟨hib, hlo, hhi⟩ := hin
  have hs0 : 0 ≤ s.off := by omega
  have hq : B.ptr.add (e : Int) = s.add (bs.size : Nat) :=
    ptr_ext (by simp [Ptr.add, hib]) (by simp [Ptr.add]; omega)
  have hq2 : (B.ptr.add (e : Int)).add ((n - bs.size : Nat) : Int) =
      B.ptr.add ((e + (n - bs.size) : Nat) : Int) := Region.Ptr.add_add_nat _ _ _
  let E := e + (n - bs.size)
  let gbs := bs ++ tail.extract 0 (n - bs.size)
  let nt := tail.extract (n - bs.size) tail.size
  have hgs : gbs.size = n := by simp only [gbs, Array.size_append, Array.size_extract]; omega
  refine EUpd.trans (EUpd.of_imp (P' := ((fst ctx B E q b cb ⋆ bshare b q' (s.off.toNat + bs.size)) ⋆
      ftail B E nt) ⋆ up (regionIn s B.A B.S B.K (2 ^ k) gbs)) fun r h => ?_)
    (EUpd.trans (EUpd.frame (EUpd.frame (fst_join (by simp only [bnd]; omega))))
    (EUpd.trans (EUpd.of_imp (P' := (fst ctx B E (q.add q').half b cb ⋆ ftail B E nt) ⋆
      (up (regionIn s B.A B.S B.K (2 ^ k) gbs) ⋆ bshare b (q.add q').half (bnd B))) fun r h => ?_)
    (EUpd.trans (EUpd.frameL (EUpd.frameL (EUpd.weaken (k' := s.off.toNat + gbs.size)
      (by simp only [bnd]; omega)))) (EUpd.of_imp fun r h => ?_))))
  · unfold fgr ftail at h
    have h1 : (fst ctx B E q b cb ⋆ ((up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1
        (tail.extract 0 (n - bs.size))) ⋆ up (regionIn (B.ptr.add (E : Int)) B.A B.S B.K 1 nt)) ⋆
        (up (regionIn s B.A B.S B.K (2 ^ k) bs) ⋆ bshare b q' (s.off.toNat + bs.size)))) r := by
      refine Full.sep_mono_right (fun _ x => Full.sep_mono_left (fun r y => ?_) x) h
      have := Region.regionIn_split y.1 (k := n - bs.size) (a' := 1) (by omega) (Nat.mod_one _)
      rw [hq2] at this
      exact Full.up_sep ⟨this, y.2⟩
    have h2 : (((fst ctx B E q b cb ⋆ bshare b q' (s.off.toNat + bs.size)) ⋆
        up (regionIn (B.ptr.add (E : Int)) B.A B.S B.K 1 nt)) ⋆
        (up (regionIn s B.A B.S B.K (2 ^ k) bs) ⋆ up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1
          (tail.extract 0 (n - bs.size))))) r := Full.of_eq (by ac_rfl) h1
    refine Full.sep_mono_right (fun r y => ?_) h2
    have y' := Full.sep_up y
    rw [hq] at y'
    exact ⟨Region.regionIn_join y'.1, y'.2⟩
  · have h1 : (((fst ctx B E (q.add q').half b cb ⋆ bshare b (q.add q').half (bnd B)) ⋆
        ftail B E nt) ⋆ up (regionIn s B.A B.S B.K (2 ^ k) gbs)) r :=
      Full.sep_mono_left (fun _ x => Full.sep_mono_left (fun _ y => fst_split y) x) h
    exact Full.of_eq (by ac_rfl) h1
  · have hnt : nt.size = B.cap - E := by
      show (tail.extract (n - bs.size) tail.size).size = B.cap - (e + (n - bs.size))
      simp only [Array.size_extract]; omega
    refine Full.sep_mono (fun _ x => fown_intro (e := E) (tail := nt)
        ⟨by omega, hnt, hA, h0, hal8, hc0⟩ hb hc (by unfold fbody; exact x))
      (fun _ x => ⟨gbs, Full.sep_lift.mpr ⟨⟨hgs, ?_⟩, fgrant_intro hsb hb hlo (by rw [hgs]; omega) x⟩⟩) h
    show keepsPrefix bs (bs ++ tail.extract 0 (n - bs.size))
    unfold keepsPrefix
    rw [Region.extract_append_left, Array.extract_eq_self_of_le (by simp <;> omega)]

/-- `free` of the last grant: it rejoins the tail, its share the invariant's. -/
theorem fpost_free_last (hok : FOk ctx B e tail) (hb : B.ptr.block = some b)
    (hc : ctx.block = some cb) (hin : FInBuf B s bs.size) (hlast : s.off + bs.size = B.ptr.off + e) :
    EUpd (fst ctx B (e - bs.size) q b cb ⋆ (ftail B e tail ⋆ fgr B b s k bs q')) (finv ctx B).own := by
  obtain ⟨he, hts, hA, h0, hal8, hc0⟩ := hok
  obtain ⟨hib, hlo, hhi⟩ := hin
  have hs0 : 0 ≤ s.off := by omega
  have hq : B.ptr.add (e : Int) = s.add (bs.size : Nat) :=
    ptr_ext (by simp [Ptr.add, hib]) (by simp [Ptr.add]; omega)
  have hnew : s = B.ptr.add ((e - bs.size : Nat) : Int) :=
    ptr_ext (by simp [Ptr.add, hib]) (by simp [Ptr.add]; omega)
  refine EUpd.trans (EUpd.of_imp (P' := (fst ctx B (e - bs.size) q b cb ⋆
      bshare b q' (s.off.toNat + bs.size)) ⋆ ftail B (e - bs.size) (bs ++ tail)) fun r h => ?_)
    (EUpd.trans (EUpd.frame (fst_join (by simp only [bnd]; omega))) (EUpd.of_imp fun r h => ?_))
  · unfold fgr ftail at h
    have h1 : ((fst ctx B (e - bs.size) q b cb ⋆ bshare b q' (s.off.toNat + bs.size)) ⋆
        (up (regionIn s B.A B.S B.K (2 ^ k) bs) ⋆
          up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail))) r := Full.of_eq (by ac_rfl) h
    refine Full.sep_mono_right (fun r y => ?_) h1
    have y' := Full.sep_up y
    rw [hq] at y'
    unfold ftail
    rw [← hnew]
    exact ⟨Region.regionIn_weaken (Region.regionIn_join y'.1) (Nat.one_dvd _), y'.2⟩
  · exact fown_intro (e := e - bs.size) (tail := bs ++ tail)
      ⟨by omega, (by simp only [Array.size_append]; omega), hA, h0, hal8, hc0⟩ hb hc
      (by unfold fbody; exact h)

/-- `free` of a grant that is not the last: its bytes are junk, its share joins the invariant's. -/
theorem fpost_free_leak (hok : FOk ctx B e tail) (hb : B.ptr.block = some b)
    (hc : ctx.block = some cb) (hin : FInBuf B s bs.size) :
    EUpd (fst ctx B e q b cb ⋆ (ftail B e tail ⋆ fgr B b s k bs q')) (finv ctx B).own := by
  have hs0 : 0 ≤ s.off := by have := hok.2.2.2.1; have := hin.2.1; omega
  refine EUpd.trans (EUpd.of_imp (P' := (fst ctx B e q b cb ⋆ bshare b q' (s.off.toNat + bs.size)) ⋆
      ftail B e tail) fun r h => ?_)
    (EUpd.trans (EUpd.frame (fst_join (by have := hin.2.2; simp only [bnd]; omega)))
      (EUpd.of_imp fun r h => fown_intro hok hb hc (by unfold fbody; exact h)))
  unfold fgr at h
  have h1 : ((up (regionIn s B.A B.S B.K (2 ^ k) bs) ⋆ fst ctx B e q b cb) ⋆
      (bshare b q' (s.off.toNat + bs.size) ⋆ ftail B e tail)) r := Full.of_eq (by ac_rfl) h
  exact Full.sep_assoc' (Full.sep_mono_left (fun _ x => fst_absorb x) h1)

end Grant

theorem fresize_spec (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hn : 0 < n.toNat) (hfit : ffits B n.toNat k) (hlen : s.len.toNat = bs.size) :
    FTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s.ptr k bs) (impl.resize ctx s k n ra)
      ((finv ctx B).resizePost s.ptr k bs n.toNat) := by
  refine fopen_grant fun e tail q b cb q' hok hb hc hin hsb => ?_
  have hok' := hok
  obtain ⟨he, hts, hA, h0, hal8, hc0⟩ := hok
  have hin' := hin
  obtain ⟨hib, hlo, hhi⟩ := hin'
  have hcap : B.cap < 2 ^ 64 := by omega
  have heN : (BitVec.ofNat 64 e).toNat = e := toNat_ofNat_lt (by omega)
  have hnc : n.toNat + B.cap < 2 ^ 64 := by unfold ffits at hfit; have := Nat.two_pow_pos k; omega
  unfold impl
  simp only [heap_FixedBufferAllocator_resize]
  gen_norm
  refine fprologue hok' hb hc hin hsb hlen ?_
  by_cases hl : s.ptr.off + bs.size = B.ptr.off + e
  · -- the last allocation
    simp only [hl, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, le_eq, hlen]
    by_cases hle : n.toNat ≤ bs.size
    · rw [if_pos (by simpa using hle), sub_ok (by rw [hlen]; exact hle), Norm.lift_pure, pure_bind]
      refine FTotalTriple.bind fload_end fun x => FTotalTriple.lift fun hx => ?_
      subst hx
      have hsub : (s.len - n).toNat = bs.size - n.toNat := by rw [toNat_sub_le (by omega), hlen]
      rw [sub_ok (by rw [heN, hsub]; omega), Norm.lift_pure, pure_bind]
      have hv : BitVec.ofNat 64 e - (s.len - n) = BitVec.ofNat 64 (e - (bs.size - n.toNat)) :=
        ofNat_eq_of_toNat (by rw [toNat_sub_le (by rw [heN, hsub]; omega), heN, hsub])
      rw [hv]
      refine FTotalTriple.bind (fstore_end _) fun _ => ?_
      exact FTotalTriple.eupd (fpost_last_shrink hok' hb hc hin hsb hl hle)
        (FTotalTriple.ret (Q := (finv ctx B).resizePost s.ptr k bs n.toNat) true)
    · rw [if_neg (by simpa using hle), sub_ok (by rw [hlen]; omega), Norm.lift_pure, pure_bind]
      refine FTotalTriple.bind fload_end fun x => FTotalTriple.lift fun hx => ?_
      subst hx
      have hsub : (n - s.len).toNat = n.toNat - bs.size := by rw [toNat_sub_le (by omega), hlen]
      have hadd : (n - s.len).toNat + (BitVec.ofNat 64 e).toNat < 2 ^ 64 := by
        rw [hsub, heN]; omega
      rw [add_ok hadd, Norm.lift_pure, pure_bind]
      refine FTotalTriple.bind (fproject_ctx8 hc hc0) fun x => FTotalTriple.lift fun hx => ?_
      subst hx
      refine FTotalTriple.bind (fproject_ctx16 hc hc0) fun x => FTotalTriple.lift fun hx => ?_
      subst hx
      refine FTotalTriple.bind fload_len fun x => FTotalTriple.lift fun hx => ?_
      subst hx
      rw [gt_eq, toNat_add_ok hadd, hsub, heN, toNat_ofNat_lt hcap]
      by_cases hroom : B.cap < n.toNat - bs.size + e
      · rw [if_pos (by simpa using hroom)]
        exact FTotalTriple.conseq (FTotalTriple.ret (Q := (finv ctx B).resizePost s.ptr k bs n.toNat) false)
          (fun _ h => fpost_same hok' hb hc hin hsb h) (fun _ _ h => h)
      rw [if_neg (by simpa using hroom)]
      refine FTotalTriple.bind fload_end fun x => FTotalTriple.lift fun hx => ?_
      subst hx
      have hadd2 : (BitVec.ofNat 64 e).toNat + (n - s.len).toNat < 2 ^ 64 := by rw [hsub, heN]; omega
      rw [add_ok hadd2, Norm.lift_pure, pure_bind]
      have hv : BitVec.ofNat 64 e + (n - s.len) = BitVec.ofNat 64 (e + (n.toNat - bs.size)) :=
        ofNat_eq_of_toNat (by rw [toNat_add_ok hadd2, heN, hsub])
      rw [hv]
      refine FTotalTriple.bind (fstore_end _) fun _ => ?_
      exact FTotalTriple.eupd (fpost_last_grow hok' hb hc hin hsb hl (by omega) (by omega))
        (FTotalTriple.ret (Q := (finv ctx B).resizePost s.ptr k bs n.toNat) true)
  · -- not the last allocation
    simp only [hl, decide_false, Bool.not_false, ↓reduceIte, gt_eq, hlen]
    by_cases hgt : bs.size < n.toNat
    · rw [if_pos (by simpa using hgt)]
      exact FTotalTriple.conseq (FTotalTriple.ret (Q := (finv ctx B).resizePost s.ptr k bs n.toNat) false)
        (fun _ h => fpost_same hok' hb hc hin hsb h) (fun _ _ h => h)
    · rw [if_neg (by simpa using hgt)]
      exact FTotalTriple.eupd (fpost_shrink hok' hb hc hin hsb (by omega))
        (FTotalTriple.ret (Q := (finv ctx B).resizePost s.ptr k bs n.toNat) true)

theorem fremap_spec (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hn : 0 < n.toNat) (hfit : ffits B n.toNat k) (hlen : s.len.toNat = bs.size) :
    FTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s.ptr k bs) (impl.remap ctx s k n ra)
      ((finv ctx B).remapPost s.ptr k bs n.toNat) := by
  have hr := fresize_spec ctx B s k n ra bs hn hfit hlen
  unfold impl at hr ⊢
  simp only [heap_FixedBufferAllocator_remap]
  gen_norm
  refine FTotalTriple.bind hr fun r => ?_
  cases r with
  | true =>
    simp only [↓reduceIte]
    exact FTotalTriple.conseq (FTotalTriple.ret (Q := (finv ctx B).remapPost s.ptr k bs n.toNat)
      (some s.ptr)) (fun _ hp => hp) (fun _ _ h => h)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact FTotalTriple.conseq (FTotalTriple.ret (Q := (finv ctx B).remapPost s.ptr k bs n.toNat)
      none) (fun _ hp => hp) (fun _ _ h => h)

theorem ffree_spec (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) :
    FTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s.ptr k bs) (impl.free ctx s k ra)
      (fun _ => (finv ctx B).own) := by
  refine fopen_grant fun e tail q b cb q' hok hb hc hin hsb => ?_
  have hok' := hok
  obtain ⟨he, hts, hA, h0, hal8, hc0⟩ := hok
  have hin' := hin
  obtain ⟨hib, hlo, hhi⟩ := hin'
  have heN : (BitVec.ofNat 64 e).toNat = e := toNat_ofNat_lt (by omega)
  unfold impl
  simp only [heap_FixedBufferAllocator_free]
  gen_norm
  refine fprologue hok' hb hc hin hsb hlen ?_
  by_cases hl : s.ptr.off + bs.size = B.ptr.off + e
  · simp only [hl, decide_true, ↓reduceIte]
    refine FTotalTriple.bind fload_end fun x => FTotalTriple.lift fun hx => ?_
    subst hx
    rw [sub_ok (by rw [heN, hlen]; omega), Norm.lift_pure, pure_bind]
    have hv : BitVec.ofNat 64 e - s.len = BitVec.ofNat 64 (e - bs.size) :=
      ofNat_eq_of_toNat (by rw [toNat_sub_le (by rw [heN, hlen]; omega), heN, hlen])
    rw [hv]
    exact (fstore_end _).eupd_post fun _ => fpost_free_last hok' hb hc hin hl
  · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact FTotalTriple.eupd (fpost_free_leak hok' hb hc hin)
      (FTotalTriple.ret (Q := fun _ => (finv ctx B).own) ())

/-- **The translated `FixedBufferAllocator` satisfies the full-state allocator specification**,
in the total logic, for every allocator struct `ctx` and every buffer `B`. -/
theorem fallocSpec (ctx : Ptr) (B : FBuf) : FAllocSpec FLogic.total impl ctx (finv ctx B) where
  alloc len k ra hl hk hfit := falloc_spec ctx B len k ra hl hk hfit
  resize s k n ra bs _ hn hfit hlen _ := fresize_spec ctx B s k n ra bs hn hfit hlen
  remap s k n ra bs _ hn hfit hlen _ := fremap_spec ctx B s k n ra bs hn hfit hlen
  free s k ra bs _ hlen _ := ffree_spec ctx B s k ra bs hlen

end FBA

end AllocFba
