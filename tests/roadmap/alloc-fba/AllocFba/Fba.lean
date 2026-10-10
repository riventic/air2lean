import AllocFba.Bridge
import ZigLean.Sep.AllocSpec.Dispatch

/-!
# The translated `std.heap.FixedBufferAllocator` satisfies `AllocSpec`

`FBA.allocSpec`: the vtable entries `alloc`/`resize`/`remap`/`free` of the translated
`FixedBufferAllocator` (`Gen.lean`, Zig 0.16.0, `--allocator-model translated`) satisfy
`AllocSpec Logic.total impl ctx (FBA.inv ctx B)` for every allocator struct `ctx` and every
buffer `B`, proved from the generated code alone (no model of the allocator).

The invariant `FBA.own ctx B`: the struct at `ctx` holds `end_index = e` and the buffer slice;
the bytes `[e, cap)` of the buffer are free (`tail`); the bytes before `e` that no client holds
(alignment padding, leaked non-last frees) are `junk`; and one byte `pin` of the buffer's block
outside the buffer. The pin is there because the model's `@intFromPtr` (`ptrAddr`) needs the
block to exist, and `alloc` computes `@intFromPtr(buffer.ptr + end_index)` also when every byte
of the buffer is lent out (then the invariant owns nothing else of the block). The token of a
grant says that it lies in the buffer's block, with the buffer block's address, size and kind.

`FBA.fits n k := cap + 2^k + n ≤ 2^64`: `alloc` computes `end_index + adjust_off + n` and
`resize` computes `new_len - len + end_index` with overflow checks, so larger requests panic.

The behaviours: alignment padding (`alignPointerOffset`, also with the address computed from
the placement-given block address, wrapped to 64 bits), out-of-memory `null` (address overflow,
no room), the last allocation shrinking, growing (`resize`/`remap` in place) and being given
back by `free`, a non-last allocation shrinking in place and leaking on `free`.
-/

namespace AllocFba

open Zig Gen Assn

namespace FBA

open Zig.Wrap (toNat_ofNat_lt)
open Zig.Ops (two_pow_lt toNat_two_pow add_ok gt_eq)

/-! ## The invariant -/

/-- The buffer: its pointer and length, the address, size and kind of its block, and one byte
`pin` of that block outside the buffer; and the address, size and kind of the block of the
allocator struct (so that a stack-allocated struct can be freed). -/
structure Buf where
  ptr : Ptr
  cap : Nat
  A : Nat
  S : Nat
  K : BlockKind
  pin : Ptr
  cA : Nat
  cS : Nat
  cK : BlockKind

/-- Bytes that the allocator has given up: padding, and the bytes of non-last frees. -/
def junk : Assn := fun _ => True

/-- The `FixedBufferAllocator` struct at `ctx`: `end_index = e` and the buffer slice. -/
def state (ctx : Ptr) (B : Buf) (e : Nat) : Assn :=
  ptsM ctx B.cA B.cS B.cK 8 (BitVec.ofNat 64 e) ∗
    ptsM (ctx.add 8) B.cA B.cS B.cK 8 (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice)

def Ok (B : Buf) (e : Nat) (tail pb : Array Byte) : Prop :=
  e ≤ B.cap ∧ tail.size = B.cap - e ∧ 0 < pb.size ∧ B.A + B.ptr.off.toNat + B.cap < 2 ^ 64 ∧
    0 ≤ B.ptr.off ∧ B.pin.block = B.ptr.block ∧
    (B.pin.off + pb.size ≤ B.ptr.off ∨ B.ptr.off + B.cap ≤ B.pin.off) ∧
    B.ptr.off.toNat + B.cap ≤ B.S

/-- The state, the free bytes from `e` on, the pin, and junk. -/
def body (ctx : Ptr) (B : Buf) (e : Nat) (tail pb : Array Byte) : Assn :=
  state ctx B e ∗ (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail ∗
    (regionIn B.pin B.A B.S B.K 1 pb ∗ junk))

def own (ctx : Ptr) (B : Buf) : Assn :=
  Assn.ex fun e => Assn.ex fun tail => Assn.ex fun pb =>
    ⌜Ok B e tail pb⌝ ∗ body ctx B e tail pb

/-- The allocator issued the region: it lies in the buffer, in the buffer's block. -/
def tok (B : Buf) (p : Ptr) (n _k A S : Nat) (K : BlockKind) : Assn :=
  ⌜p.block = B.ptr.block ∧ A = B.A ∧ S = B.S ∧ K = B.K ∧ B.ptr.off ≤ p.off ∧
    p.off + n ≤ B.ptr.off + B.cap⌝

def fits (B : Buf) (n k : Nat) : Prop := B.cap + 2 ^ k + n ≤ 2 ^ 64

def inv (ctx : Ptr) (B : Buf) : AllocInv where
  own := own ctx B
  tok := tok B
  fits := fits B

theorem own_intro {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {h : Heap}
    (hok : Ok B e tail pb) (hb : body ctx B e tail pb h) : own ctx B h :=
  ⟨e, tail, pb, sep_lift.mpr ⟨hok, hb⟩⟩

/-- Anything framed onto the body is junk. -/
theorem body_absorb {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {G : Assn} {h : Heap}
    (hb : (body ctx B e tail pb ∗ G) h) : body ctx B e tail pb h := by
  unfold body at hb ⊢
  have h2 : (state ctx B e ∗ (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail ∗
      (regionIn B.pin B.A B.S B.K 1 pb ∗ (G ∗ junk)))) h := by sep_from hb
  exact sep_mono (fun _ y => y) (fun _ y => sep_mono (fun _ z => z)
    (fun _ z => sep_mono (fun _ w => w) (fun _ _ => trivial) z) y) h2

/-! ## Arithmetic of the helpers -/

theorem toNat_mask {k : Nat} (hk : k < 64) : (BitVec.ofNat 64 (2 ^ k - 1)).toNat = 2 ^ k - 1 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := two_pow_lt hk; omega)]

theorem debug_assert_true : debug_assert true = pure () := rfl

/-- Normalize a generated pure helper (`Zig.M` over `Result`). -/
macro "pure_norm" : tactic => `(tactic| simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure,
  StateT.run_monadLift, StateT.run_lift, Zig.call, liftM, monadLift, MonadLift.monadLift,
  pure_bind, bind_assoc, map_pure, map_bind, bind_map_left, debug_assert_true])

theorem toByteUnits_eq {k : Nat} (hk : k < 64) :
    mem_Alignment_toByteUnits ⟨BitVec.ofNat 6 k⟩ = pure (BitVec.ofNat 64 (2 ^ k)) := by
  have hk6 : (BitVec.ofNat 6 k).toNat = k := by simp [BitVec.toNat_ofNat]; omega
  have e : Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) = BitVec.ofNat 64 (2 ^ k) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_two_pow hk]
    simp only [Zig.shl, BitVec.toNat_shiftLeft, hk6]
    simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (two_pow_lt hk)]
  unfold mem_Alignment_toByteUnits
  pure_norm
  simp only [mem_Alignment.toBits, e]

theorem isPowerOfTwo_eq {k : Nat} (hk : k < 64) :
    math_isPowerOfTwo__anon_1 (BitVec.ofNat 64 (2 ^ k)) = pure true := by
  have hpos := Nat.two_pow_pos k
  have h1 : Zig.gt false (BitVec.ofNat 64 (2 ^ k)) 0 = true := by
    simp only [Zig.gt, Zig.lt, Bool.false_eq_true, ↓reduceIte, BitVec.ult, toNat_two_pow hk]
    simp [hpos]
  have h2 : Zig.sub false (BitVec.ofNat 64 (2 ^ k)) 1 = pure (BitVec.ofNat 64 (2 ^ k - 1)) := by
    simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte, toNat_two_pow hk]
    rw [if_neg (by simp; try omega)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_mask hk, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_two_pow hk]; simp; omega),
      toNat_two_pow hk]
    rfl
  have h3 : (BitVec.ofNat 64 (2 ^ k) &&& BitVec.ofNat 64 (2 ^ k - 1)) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_mask hk, toNat_two_pow hk, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_self]
    rfl
  unfold math_isPowerOfTwo__anon_1
  pure_norm
  simp only [h1, h2, h3, debug_assert_true, pure_bind]
  rfl

theorem isValidAlign_eq {k : Nat} (hk : k < 64) :
    mem_isValidAlign (BitVec.ofNat 64 (2 ^ k)) = pure true := by
  have h1 : Zig.gt false (BitVec.ofNat 64 (2 ^ k)) 0 = true := by
    simp only [Zig.gt, Zig.lt, Bool.false_eq_true, ↓reduceIte, BitVec.ult, toNat_two_pow hk]
    simp; exact Nat.two_pow_pos k
  unfold mem_isValidAlign mem_isValidAlignGeneric__anon_1
  pure_norm
  simp only [h1, isPowerOfTwo_eq hk, pure_bind, ↓reduceIte]
  rfl

/-- `x &&& ~~~m` and `x &&& m` split `x`. -/
theorem and_not_add_and (z m : BitVec 64) : (z &&& ~~~m).toNat + (z &&& m).toNat = z.toNat := by
  have h0 : (z &&& ~~~m) &&& (z &&& m) = 0#64 := by
    ext i; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases z[i] <;> cases m[i] <;> rfl
  rw [← BitVec.toNat_add_of_and_eq_zero h0, BitVec.add_eq_or_of_and_eq_zero _ _ h0]
  congr 1
  ext i; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
  cases z[i] <;> cases m[i] <;> rfl

/-- `alignForward`: clearing the low `k` bits. -/
theorem toNat_and_not_mask {k : Nat} (hk : k < 64) (z : BitVec 64) :
    (z &&& ~~~BitVec.ofNat 64 (2 ^ k - 1)).toNat = z.toNat - z.toNat % 2 ^ k := by
  have h := and_not_add_and z (BitVec.ofNat 64 (2 ^ k - 1))
  rw [BitVec.toNat_and z (BitVec.ofNat 64 (2 ^ k - 1)), toNat_mask hk,
    Nat.and_two_pow_sub_one_eq_mod] at h
  omega

/-- The offset that `alignPointerOffset` computes on the (64-bit wrapped) address `x`, with no
address overflow: below `2 ^ k`, and `x` plus it is a multiple of `2 ^ k`. -/
theorem alignOffset_facts {k : Nat} (hk : k < 64) (x : BitVec 64)
    (hno : x.toNat + (2 ^ k - 1) < 2 ^ 64) :
    let z := x + BitVec.ofNat 64 (2 ^ k - 1)
    let al := z &&& ~~~BitVec.ofNat 64 (2 ^ k - 1)
    x.toNat ≤ al.toNat ∧ al.toNat - x.toNat < 2 ^ k ∧ al.toNat % 2 ^ k = 0 := by
  intro z al
  have hz : z.toNat = x.toNat + (2 ^ k - 1) := by
    simp only [z, BitVec.toNat_add, toNat_mask hk]; exact Nat.mod_eq_of_lt hno
  have ha : al.toNat = z.toNat - z.toNat % 2 ^ k := toNat_and_not_mask hk z
  have hm := Nat.mod_lt z.toNat (Nat.two_pow_pos k)
  have hp := Nat.two_pow_pos k
  refine ⟨by omega, by omega, ?_⟩
  have hd := Nat.div_add_mod z.toNat (2 ^ k)
  have : al.toNat = 2 ^ k * (z.toNat / 2 ^ k) := by omega
  rw [this, Nat.mul_mod_right]

/-! ## The struct -/

section State

variable {ctx : Ptr} {B : Buf} {e : Nat} {R : Assn}

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

theorem pts_slice_parts {q : Ptr} {s : Slice} {h : Heap} (hp : pts q 8 s h) :
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

/-- A load of a field of a slice that `pts` describes. -/
theorem pts_slice_field_load {T : Type} [Enc T] {q : Ptr} {s : Slice} {o : Nat} {v : T}
    {A₀ S₀ : Nat} {K₀ : BlockKind} (hsz : Enc.size T = 8) (ho : o = 0 ∨ o = 8)
    (hv : ∀ bs : Array Byte, Enc.decode (bs.extract 0 8) = (pure s.ptr : Result Ptr) →
      Enc.decode (bs.extract 8 16) = (pure s.len : Result (BitVec 64)) →
      Enc.decode (bs.extract o (o + 8)) = (pure v : Result T)) :
    TotalTriple (ptsM q A₀ S₀ K₀ 8 s) (load T 8 (q.add o)) (fun r => ⌜r = v⌝ ∗ ptsM q A₀ S₀ K₀ 8 s) := by
  intro m hP hF hd hm hp hst
  obtain ⟨A, S, K, bs, ha, hs, h1, h2, hb⟩ := pts_slice_parts (ptsM_pts hp)
  have hao : (A + q.off.toNat + o) % 8 = 0 := by rcases ho with rfl | rfl <;> omega
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (q := q.add o) (k := o) (n := Enc.size T) (a := 8) hb hm rfl
      (by omega) (by rcases ho with rfl | rfl <;> omega) hao
  have hv' : Enc.decode (blk.bytes.extract (q.off.toNat + o) (q.off.toNat + o + Enc.size T)) =
      pure v := by rw [hx, hsz]; exact hv bs h1 h2
  refine ⟨v, _, hP, load_run hacc hv' (noRace_of_singleThread hst.single _ _ _ _), hd, ?_,
    sep_lift.mpr ⟨rfl, hp⟩, hst.recordAt _ _ _ _⟩
  funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

theorem load_end : TotalTriple (state ctx B e ∗ R) (load (BitVec 64) 8 ctx)
    (fun r => ⌜r = BitVec.ofNat 64 e⌝ ∗ (state ctx B e ∗ R)) := by
  unfold state
  exact TotalTriple.conseq (TotalTriple.frame (R := ptsM (ctx.add 8) B.cA B.cS B.cK 8
      (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice) ∗ R) (ptsM_load (by decide)))
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

theorem load_ptr : TotalTriple (state ctx B e ∗ R) (load Ptr 8 (ctx.add 8))
    (fun r => ⌜r = B.ptr⌝ ∗ (state ctx B e ∗ R)) := by
  unfold state
  have t := pts_slice_field_load (T := Ptr) (q := ctx.add 8) (A₀ := B.cA) (S₀ := B.cS) (K₀ := B.cK) (s := ⟨B.ptr, BitVec.ofNat 64 B.cap⟩)
    (o := 0) (v := B.ptr) rfl (Or.inl rfl) (fun bs h1 _ => by simpa using h1)
  push_cast at t
  simp only [Norm.add_zero_ptr] at t
  exact TotalTriple.conseq (TotalTriple.frame (R := ptsM ctx B.cA B.cS B.cK 8 (BitVec.ofNat 64 e) ∗ R) t)
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

theorem load_len : TotalTriple (state ctx B e ∗ R) (load (BitVec 64) 8 ((ctx.add 8).add 8))
    (fun r => ⌜r = BitVec.ofNat 64 B.cap⌝ ∗ (state ctx B e ∗ R)) := by
  unfold state
  have t := pts_slice_field_load (T := BitVec 64) (q := ctx.add 8) (A₀ := B.cA) (S₀ := B.cS) (K₀ := B.cK)
    (s := ⟨B.ptr, BitVec.ofNat 64 B.cap⟩) (o := 8) (v := BitVec.ofNat 64 B.cap) rfl (Or.inr rfl)
    (fun bs _ h2 => h2)
  push_cast at t
  exact TotalTriple.conseq (TotalTriple.frame (R := ptsM ctx B.cA B.cS B.cK 8 (BitVec.ofNat 64 e) ∗ R) t)
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

theorem load_slice : TotalTriple (state ctx B e ∗ R) (load Slice 8 (ctx.add 8))
    (fun r => ⌜r = ⟨B.ptr, BitVec.ofNat 64 B.cap⟩⌝ ∗ (state ctx B e ∗ R)) := by
  unfold state
  exact TotalTriple.conseq (TotalTriple.frame (R := ptsM ctx B.cA B.cS B.cK 8 (BitVec.ofNat 64 e) ∗ R)
      (ptsM_load (by decide)))
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

theorem store_end (e' : Nat) : TotalTriple (state ctx B e ∗ R)
    (store 8 ctx (BitVec.ofNat 64 e')) (fun _ => state ctx B e' ∗ R) := by
  unfold state
  exact TotalTriple.conseq (TotalTriple.frame (R := ptsM (ctx.add 8) B.cA B.cS B.cK 8
      (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice) ∗ R) (ptsM_store (by decide) _))
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

/-- The `@alignCast` of the context pointer (`*FixedBufferAllocator`, alignment 8) passes. -/
theorem ptrAddr_ctx : TotalTriple (state ctx B e ∗ R) (ptrAddr ctx)
    (fun r => ⌜(BitVec.ofInt 64 r &&& 7) = 0⌝ ∗ (state ctx B e ∗ R)) := by
  intro m hP hF hd hm hp hst
  obtain ⟨h₁, h₂, hd₁₂, rfl, ⟨g₁, g₂, -, rfl, ⟨ha, -, bs, hs, -, hb⟩, -⟩, -⟩ := id hp
  obtain ⟨b, hpb, ho⟩ := bytesAt_ownsIn hb (by rw [hs]; decide)
  have hown : OwnsIn b B.cA ((g₁ ∪ g₂) ∪ h₂) := ho.union_left.union_left
  obtain ⟨blk, hblk, hA⟩ := hown.block hm
  refine ⟨(blk.addr : Int) + ctx.off, m, _, ?_, hd, hm, sep_lift.mpr ⟨?_, hp⟩, hst⟩
  · simp [ptrAddr, hpb, hblk, zig_unfold, get, getThe, MonadStateOf.get, StateT.get]
  · rw [hA]
    have hx : ((B.cA : Int) + ctx.off) % 2 ^ 3 = 0 := by
      have : ((B.cA + ctx.off.toNat : Nat) : Int) % ((2 ^ 3 : Nat) : Int) = 0 := by exact_mod_cast ha
      rw [Int.natCast_add, Int.toNat_of_nonneg (Region.bytesAt_pos_off hb)] at this
      exact_mod_cast this
    have h0 := Region.bytesAt_pos_off hb
    exact Ops.and_mask_eq_zero (k := 3) (by decide) (by omega) hx

end State

/-! ## Overflow-checked arithmetic -/

theorem toNat_add_ok {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

theorem sub_ok {a b : BitVec 64} (h : b.toNat ≤ a.toNat) : Zig.sub false a b = pure (a - b) := by
  simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; omega)]

theorem le_eq (a b : BitVec 64) : Zig.le false a b = decide (a.toNat ≤ b.toNat) := by
  simp [Zig.le, BitVec.ule]

theorem ofInt_toNat {x : Int} (h0 : 0 ≤ x) : (BitVec.ofInt 64 x).toNat = x.toNat % 2 ^ 64 := by
  obtain ⟨N, rfl⟩ : ∃ N : Nat, x = N := ⟨x.toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]; simp

/-- The generated pure steps of `alignPointerOffset` for a `2 ^ k` alignment, `0 < k`. -/
theorem sub_one_eq {k : Nat} (hk : k < 64) :
    Zig.sub false (BitVec.ofNat 64 (2 ^ k)) 1 = pure (BitVec.ofNat 64 (2 ^ k - 1)) := by
  have hpos := Nat.two_pow_pos k
  rw [sub_ok (by rw [toNat_two_pow hk]; simp; omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_mask hk, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_two_pow hk]; simp; omega),
    toNat_two_pow hk]
  rfl

theorem rem_one (d : BitVec 64) : Zig.rem false d 1 = pure 0 := by
  simp [Zig.rem]

theorem divTrunc_one (d : BitVec 64) : Zig.divTrunc false d 1 = pure d := by
  simp [Zig.divTrunc]

/-- The result of `alignPointerOffset(x, 2 ^ k)`: `null` on address overflow, else an offset
below `2 ^ k` that aligns the address `x`. -/
def AlignRes (k : Nat) (x : Int) : Option (BitVec 64) → Prop
  | none => True
  | some d => d.toNat < 2 ^ k ∧ (x.toNat + d.toNat) % 2 ^ k = 0

theorem alignPointerOffset_spec {P : Assn} {q : Ptr} {b : BlockId} {A k : Nat} (hk : k < 64)
    (hqb : q.block = some b) (hown : ∀ h, P h → OwnsIn b A h) (h0 : 0 ≤ q.off) :
    TotalTriple P (mem_alignPointerOffset__anon_1 q (BitVec.ofNat 64 (2 ^ k)))
      (fun r => ⌜AlignRes k ((A : Int) + q.off) r⌝ ∗ P) := by
  simp only [mem_alignPointerOffset__anon_1]
  gen_norm
  simp only [isValidAlign_eq hk, debug_assert_true, Norm.lift_pure, pure_bind, le_eq,
    toNat_two_pow hk]
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos (by simp only [decide_eq_true_eq]; exact Nat.le_refl 1)]
    exact TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜AlignRes 0 ((A : Int) + q.off) r⌝ ∗ P)
      (some 0)) (fun h hp => sep_lift.mpr ⟨by simp [AlignRes, Nat.mod_one], hp⟩) (fun _ _ h => h)
  have hk1 : ¬ 2 ^ k ≤ 1 := by
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    simp at this; omega
  rw [if_neg (by simp only [decide_eq_true_eq]; exact hk1)]
  simp only [sub_one_eq hk, Norm.lift_pure, pure_bind]
  refine TotalTriple.bind (ptrAddr_owned hqb hown) fun x => TotalTriple.lift fun hx => ?_
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
    refine TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜AlignRes k ((A : Int) + q.off) r⌝ ∗ P)
      _) (fun h hp => sep_lift.mpr ⟨?_, hp⟩) (fun _ _ h => h)
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
    exact TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜AlignRes k ((A : Int) + q.off) r⌝ ∗ P)
      none) (fun h hp => sep_lift.mpr ⟨trivial, hp⟩) (fun _ _ h => h)

/-! ## `alloc` -/

theorem off_add_nat {p : Ptr} {x : Nat} (h0 : 0 ≤ p.off) : (p.add (x : Int)).off.toNat = p.off.toNat + x :=
  Region.add_off_toNat p x h0

theorem grant_intro {ctx : Ptr} {B : Buf} {p : Ptr} {k : Nat} {bs : Array Byte} {h : Heap}
    (hr : regionIn p B.A B.S B.K (2 ^ k) bs h)
    (hf : p.block = B.ptr.block ∧ B.A = B.A ∧ B.S = B.S ∧ B.K = B.K ∧ B.ptr.off ≤ p.off ∧
      p.off + bs.size ≤ B.ptr.off + B.cap) :
    granted (inv ctx B) p k bs h :=
  ⟨B.A, B.S, B.K, h, Heap.empty, Heap.disjoint_empty h, by simp, hr, ⟨hf, rfl⟩⟩

/-- After `alloc` has moved `end_index` from `e` to `e + d + n`: the padding `d` is junk, the
next `n` bytes are a grant, the rest is the new tail. -/
theorem carve_grant {ctx : Ptr} {B : Buf} {e d n k : Nat} {tail pb : Array Byte}
    (hok : Ok B e tail pb) (hfit : e + d + n ≤ B.cap)
    (hal : (B.A + B.ptr.off.toNat + e + d) % 2 ^ k = 0) {h : Heap}
    (hh : (state ctx B (e + d + n) ∗ (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail ∗
      (regionIn B.pin B.A B.S B.K 1 pb ∗ junk))) h) :
    ((inv ctx B).own ∗ Assn.ex fun bs => ⌜bs.size = n⌝ ∗
      granted (inv ctx B) (B.ptr.add ((e + d : Nat) : Int)) k bs) h := by
  obtain ⟨he, hts, hpb, hA, h0, hpin, hpo, hS⟩ := hok
  have hq0 : (B.ptr.add (e : Int)).off.toNat = B.ptr.off.toNat + e := off_add_nat h0
  have hcarve : ∀ h', regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail h' →
      (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 (tail.extract 0 d) ∗
        (regionIn (B.ptr.add ((e + d : Nat) : Int)) B.A B.S B.K (2 ^ k)
            ((tail.extract d tail.size).extract 0 n) ∗
          regionIn (B.ptr.add ((e + d + n : Nat) : Int)) B.A B.S B.K 1
            ((tail.extract d tail.size).extract n (tail.extract d tail.size).size))) h' := by
    intro h' x
    have hc := Region.regionIn_carve x (pad := d) (len := n) (by omega)
      (by rw [hq0, ← Nat.add_assoc]; exact hal)
    rw [Region.Ptr.add_add_nat, Region.Ptr.add_add_nat,
      show e + (d + n) = e + d + n by omega] at hc
    exact hc
  have hh2 := sep_mono (fun _ y => y) (fun _ y => sep_mono hcarve (fun _ z => z) y) hh
  have hh3 : ((state ctx B (e + d + n) ∗
      (regionIn (B.ptr.add ((e + d + n : Nat) : Int)) B.A B.S B.K 1
          ((tail.extract d tail.size).extract n (tail.extract d tail.size).size) ∗
        (regionIn B.pin B.A B.S B.K 1 pb ∗
          (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 (tail.extract 0 d) ∗ junk)))) ∗
      regionIn (B.ptr.add ((e + d : Nat) : Int)) B.A B.S B.K (2 ^ k)
        ((tail.extract d tail.size).extract 0 n)) h := by
    sep_from hh2
  refine sep_mono (fun _ x => own_intro (e := e + d + n)
      (tail := (tail.extract d tail.size).extract n (tail.extract d tail.size).size) (pb := pb)
      ⟨(by omega), (by simp only [Array.size_extract]; omega), hpb, hA, h0, hpin, hpo, hS⟩ ?_)
    (fun _ x => ⟨(tail.extract d tail.size).extract 0 n, sep_lift.mpr
      ⟨(by simp only [Array.size_extract]; omega), grant_intro x ⟨rfl, rfl, rfl, rfl,
        (by simp [Ptr.add]; omega), (by simp [Ptr.add, Array.size_extract]; omega)⟩⟩⟩) hh3
  unfold body
  exact sep_mono (fun _ y => y) (fun _ y => sep_mono (fun _ z => z)
    (fun _ z => sep_mono (fun _ w => w) (fun _ _ => trivial) z) y) x

/-- Use the existentials and the facts of the invariant. -/
theorem own_open {α : Type} {ctx : Ptr} {B : Buf} {c : MemM α} {Q : α → Assn} {R : Assn}
    (ht : ∀ e tail pb, Ok B e tail pb → TotalTriple (body ctx B e tail pb ∗ R) c Q) :
    TotalTriple (own ctx B ∗ R) c Q := by
  intro m hP hF hd hm hp hst
  obtain ⟨h₁, h₂, hd₁₂, rfl, ⟨e, tail, pb, hb⟩, hr⟩ := hp
  obtain ⟨hok, hb⟩ := sep_lift.mp hb
  exact ht e tail pb hok m _ hF hd hm ⟨h₁, h₂, hd₁₂, rfl, hb, hr⟩ hst

/-- The pin owns a cell of the buffer's block, with the block's address. -/
theorem pin_ownsIn {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {R : Assn} {b : BlockId}
    (hb : B.ptr.block = some b) (hok : Ok B e tail pb) :
    ∀ h, (body ctx B e tail pb ∗ R) h → OwnsIn b B.A h := by
  rintro h ⟨h₁, h₂, hd, rfl, ⟨g₁, g₂, hdg, rfl, -, ⟨g₃, g₄, hd34, rfl, -, ⟨g₅, g₆, hd56, rfl, hpin, -⟩⟩⟩, -⟩
  obtain ⟨b', hb', ho⟩ := regionIn_ownsIn hpin hok.2.2.1
  rw [hok.2.2.2.2.2.1, hb] at hb'; cases hb'
  exact ((ho.union_left).union_right hd34 |>.union_right hdg).union_left

theorem pin_block {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {R : Assn} {h : Heap}
    (hok : Ok B e tail pb) (hh : (body ctx B e tail pb ∗ R) h) : ∃ b, B.ptr.block = some b := by
  obtain ⟨h₁, h₂, hd, rfl, ⟨g₁, g₂, hdg, rfl, -, ⟨g₃, g₄, hd34, rfl, -, ⟨g₅, g₆, hd56, rfl, hpin, -⟩⟩⟩, -⟩ := hh
  have := (regionIn_facts hpin).2.2.2
  rw [hok.2.2.2.2.2.1] at this
  exact Option.isSome_iff_exists.mp this

theorem alloc_spec (ctx : Ptr) (B : Buf) (n : BitVec 64) (k : Nat) (ra : BitVec 64)
    (hn : 0 < n.toNat) (hk : k < 64) (hfit : fits B n.toNat k) :
    TotalTriple (own ctx B) (impl.alloc ctx n k ra) (allocPost (inv ctx B) n.toNat k) := by
  refine TotalTriple.conseq (P := own ctx B ∗ emp) ?_ (fun h hp => sep_emp.mpr hp) (fun _ _ h => h)
  refine own_open fun e tail pb hok => ?_
  have hok' := hok
  obtain ⟨he, hts, hpb, hA, h0, hpin, hpo, hS⟩ := hok
  refine TotalTriple.conseq (P := body ctx B e tail pb) ?_ (fun h hp => sep_emp.mp hp)
    (fun _ _ h => h)
  refine TotalTriple.of_pure (fun h hp => pin_block (R := emp) hok' (sep_emp.mpr hp))
    fun ⟨b, hb⟩ => ?_
  have hown := pin_ownsIn (ctx := ctx) (R := emp) hb hok'
  unfold impl
  simp only [heap_FixedBufferAllocator_alloc]
  gen_norm
  have hpk := Nat.two_pow_pos k
  have hcap : B.cap < 2 ^ 64 := by unfold fits at hfit; omega
  have heN : (BitVec.ofNat 64 e).toNat = e := toNat_ofNat_lt (by omega)
  unfold body
  refine TotalTriple.bind (ptrAddr_ctx (ctx := ctx) (B := B) (e := e)) fun x =>
    TotalTriple.lift fun hx => ?_
  rw [if_pos hx, toByteUnits_eq hk, Norm.lift_pure, pure_bind]
  refine TotalTriple.bind load_ptr fun p => TotalTriple.lift fun hp => ?_
  subst hp
  refine TotalTriple.bind load_end fun e₁ => TotalTriple.lift fun he₁ => ?_
  subst he₁
  refine TotalTriple.bind (alignPointerOffset_spec (A := B.A) hk (by simp [Ptr.elem, Ptr.add, hb])
    (fun h hp => hown h (sep_emp.mpr (by unfold body; exact hp))) (by simp [Ptr.elem, Ptr.add]; omega))
    fun r => TotalTriple.lift fun hr => ?_
  cases r with
  | none =>
    exact TotalTriple.conseq (TotalTriple.ret (Q := allocPost (inv ctx B) n.toNat k) none)
      (fun h hp => own_intro hok' (body_absorb (G := emp) (by unfold body; sep_from hp)))
      (fun _ _ h => h)
  | some d =>
    obtain ⟨hd, hal⟩ := hr
    simp only [Option.elim]
    refine TotalTriple.bind load_end fun e₂ => TotalTriple.lift fun he₂ => ?_
    subst he₂
    have hed : (BitVec.ofNat 64 e).toNat + d.toNat < 2 ^ 64 := by
      rw [heN]; unfold fits at hfit; omega
    rw [add_ok hed, Norm.lift_pure, pure_bind]
    have hedn : (BitVec.ofNat 64 e + d).toNat + n.toNat < 2 ^ 64 := by
      rw [toNat_add_ok hed, heN]; unfold fits at hfit; omega
    rw [add_ok hedn, Norm.lift_pure, pure_bind]
    refine TotalTriple.bind load_len fun l => TotalTriple.lift fun hl => ?_
    subst hl
    have hv : (BitVec.ofNat 64 e + d + n).toNat = e + d.toNat + n.toNat := by
      rw [toNat_add_ok hedn, toNat_add_ok hed, heN]
    rw [gt_eq, hv, toNat_ofNat_lt hcap]
    by_cases hroom : B.cap < e + d.toNat + n.toNat
    · rw [if_pos (by simpa using hroom)]
      exact TotalTriple.conseq (TotalTriple.ret (Q := allocPost (inv ctx B) n.toNat k) none)
        (fun h hp => own_intro hok' (body_absorb (G := emp) (by unfold body; sep_from hp)))
        (fun _ _ h => h)
    rw [if_neg (by simpa using hroom)]
    have hst : BitVec.ofNat 64 e + d + n = BitVec.ofNat 64 (e + d.toNat + n.toNat) := by
      apply BitVec.eq_of_toNat_eq; rw [hv, toNat_ofNat_lt (by omega)]
    rw [hst]
    refine TotalTriple.bind (store_end (e + d.toNat + n.toNat)) fun _ => ?_
    refine TotalTriple.bind load_ptr fun p => TotalTriple.lift fun hp => ?_
    subst hp
    have hptr : B.ptr.elem 1 (BitVec.ofNat 64 e + d) = B.ptr.add ((e + d.toNat : Nat) : Int) := by
      rw [Ptr.elem_eq, toNat_add_ok hed, heN, Nat.one_mul]
    rw [hptr]
    refine TotalTriple.conseq (TotalTriple.ret (Q := allocPost (inv ctx B) n.toNat k) _)
      (fun h hp => ?_) (fun _ _ h => h)
    have hal' : (B.A + B.ptr.off.toNat + e + d.toNat) % 2 ^ k = 0 := by
      have : ((B.A : Int) + (B.ptr.elem 1 (BitVec.ofNat 64 e)).off).toNat = B.A + B.ptr.off.toNat + e := by
        simp [Ptr.elem, Ptr.add, heN]; omega
      rw [this] at hal; omega
    exact carve_grant hok' (by omega) hal' hp

/-! ## `ownsSlice` and `isLastAllocation` -/

theorem ptr_ext {p q : Ptr} (h1 : p.block = q.block) (h2 : p.off = q.off) : p = q := by
  cases p; cases q; simp_all

theorem ofInt_toNat_lt {x : Int} (h0 : 0 ≤ x) (h : x.toNat < 2 ^ 64) :
    (BitVec.ofInt 64 x).toNat = x.toNat := by
  rw [ofInt_toNat h0, Nat.mod_eq_of_lt h]

/-- `ownsSlice(s)` of a slice inside the buffer is `true` (the `assert` passes). -/
theorem ownsSlice_spec {ctx : Ptr} {B : Buf} {e : Nat} {R : Assn} {s : Slice} {b : BlockId}
    (hb : B.ptr.block = some b) (hown : ∀ h, (state ctx B e ∗ R) h → OwnsIn b B.A h)
    (hsb : s.ptr.block = B.ptr.block) (h0 : 0 ≤ B.ptr.off) (hlo : B.ptr.off ≤ s.ptr.off)
    (hhi : s.ptr.off + s.len.toNat ≤ B.ptr.off + B.cap) (hA : B.A + B.ptr.off.toNat + B.cap < 2 ^ 64) :
    TotalTriple (state ctx B e ∗ R) (heap_FixedBufferAllocator_ownsSlice ctx s)
      (fun r => ⌜r = true⌝ ∗ (state ctx B e ∗ R)) := by
  simp only [heap_FixedBufferAllocator_ownsSlice, heap_FixedBufferAllocator_sliceContainsSlice]
  gen_norm
  have hcap : B.cap < 2 ^ 64 := by omega
  refine TotalTriple.bind load_slice fun x => TotalTriple.lift fun hx => ?_
  subst hx
  have hsb' : s.ptr.block = some b := by rw [hsb, hb]
  refine TotalTriple.bind (ptrAddr_owned hsb' hown) fun x₁ => TotalTriple.lift fun hx₁ => ?_
  subst hx₁
  refine TotalTriple.bind (ptrAddr_owned hb hown) fun x₂ => TotalTriple.lift fun hx₂ => ?_
  subst hx₂
  have e1 : (BitVec.ofInt 64 ((B.A : Int) + s.ptr.off)).toNat = B.A + s.ptr.off.toNat := by
    rw [ofInt_toNat_lt (by omega) (by omega)]; omega
  have e2 : (BitVec.ofInt 64 ((B.A : Int) + B.ptr.off)).toNat = B.A + B.ptr.off.toNat := by
    rw [ofInt_toNat_lt (by omega) (by omega)]; omega
  have hge : Zig.ge false (BitVec.ofInt 64 ((B.A : Int) + s.ptr.off))
      (BitVec.ofInt 64 ((B.A : Int) + B.ptr.off)) = true := by
    simp only [Zig.ge, le_eq, e1, e2, decide_eq_true_eq]; omega
  rw [if_pos hge]
  refine TotalTriple.bind (ptrAddr_owned hsb' hown) fun x₃ => TotalTriple.lift fun hx₃ => ?_
  subst hx₃
  rw [add_ok (by rw [e1]; omega), Norm.lift_pure, pure_bind]
  refine TotalTriple.bind (ptrAddr_owned hb hown) fun x₅ => TotalTriple.lift fun hx₅ => ?_
  subst hx₅
  rw [add_ok (by rw [e2, toNat_ofNat_lt hcap]; omega), Norm.lift_pure, pure_bind]
  refine TotalTriple.conseq (TotalTriple.ret (Q := fun r => ⌜r = true⌝ ∗ (state ctx B e ∗ R)) _)
    (fun h hp => sep_lift.mpr ⟨?_, hp⟩) (fun _ _ h => h)
  rw [le_eq, toNat_add_ok (by rw [e1]; omega), toNat_add_ok (by rw [e2, toNat_ofNat_lt hcap]; omega),
    e1, e2, toNat_ofNat_lt hcap]
  simp only [decide_eq_true_eq]; omega

/-- `isLastAllocation(s)`: does `s` end at `end_index`? -/
theorem isLast_spec {ctx : Ptr} {B : Buf} {e : Nat} {R : Assn} {s : Slice}
    (hsb : s.ptr.block = B.ptr.block) (he : e < 2 ^ 64) :
    TotalTriple (state ctx B e ∗ R) (heap_FixedBufferAllocator_isLastAllocation ctx s)
      (fun r => ⌜r = decide (s.ptr.off + s.len.toNat = B.ptr.off + e)⌝ ∗ (state ctx B e ∗ R)) := by
  simp only [heap_FixedBufferAllocator_isLastAllocation]
  gen_norm
  refine TotalTriple.bind load_ptr fun x => TotalTriple.lift fun hx => ?_
  subst hx
  refine TotalTriple.bind load_end fun x => TotalTriple.lift fun hx => ?_
  subst hx
  refine TotalTriple.conseq (TotalTriple.ret (Q := fun r =>
      ⌜r = decide (s.ptr.off + s.len.toNat = B.ptr.off + e)⌝ ∗ (state ctx B e ∗ R)) _)
    (fun h hp => sep_lift.mpr ⟨?_, hp⟩) (fun _ _ h => h)
  simp only [Ptr.elem_eq, toNat_ofNat_lt he, Nat.one_mul]
  by_cases hc : s.ptr.off + s.len.toNat = B.ptr.off + e
  · simp only [hc, decide_true]
    exact beq_iff_eq.mpr (ptr_ext (by simp [Ptr.add, hsb]) (by simp [Ptr.add]; omega))
  · simp only [hc, decide_false]
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg Ptr.off heq
    simp [Ptr.add] at this; omega

/-! ## `resize`, `remap`, `free` -/

/-- The heap of `resize`/`free` while it runs: the struct (with `end_index = e₀`), the tail at
`e`, the pin and junk, and the region `bs` of the slice. -/
def during (ctx : Ptr) (B : Buf) (e₀ e : Nat) (tail pb : Array Byte) (s : Ptr) (k : Nat)
    (bs : Array Byte) : Assn :=
  state ctx B e₀ ∗ ((regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail ∗
    (regionIn B.pin B.A B.S B.K 1 pb ∗ junk)) ∗ regionIn s B.A B.S B.K (2 ^ k) bs)

/-- The facts that the token of a grant gives. -/
def InBuf (B : Buf) (s : Ptr) (n : Nat) : Prop :=
  s.block = B.ptr.block ∧ B.ptr.off ≤ s.off ∧ s.off + n ≤ B.ptr.off + B.cap

/-- Open the invariant and the grant. -/
theorem open_grant {α : Type} {ctx : Ptr} {B : Buf} {s : Ptr} {k : Nat} {bs : Array Byte}
    {c : MemM α} {Q : α → Assn}
    (ht : ∀ e tail pb, Ok B e tail pb → InBuf B s bs.size →
      TotalTriple (during ctx B e e tail pb s k bs) c Q) :
    TotalTriple ((inv ctx B).own ∗ granted (inv ctx B) s k bs) c Q := by
  intro m hP hF hd hm hp hst
  obtain ⟨h₁, h₂, hd₁₂, rfl, ⟨e, tail, pb, hb⟩, A, S, K, hg⟩ := hp
  obtain ⟨hok, hb⟩ := sep_lift.mp hb
  obtain ⟨g₁, g₂, hdg, rfl, hr, ⟨⟨hblk, rfl, rfl, rfl, hlo, hhi⟩, rfl⟩⟩ := hg
  refine ht e tail pb hok ⟨hblk, hlo, hhi⟩ m _ hF hd hm ?_ hst
  have : (body ctx B e tail pb ∗ regionIn s B.A B.S B.K (2 ^ k) bs) (h₁ ∪ (g₁ ∪ Heap.empty)) := by
    simp only [Heap.union_empty] at hd₁₂ ⊢
    exact ⟨h₁, g₁, by simpa using hd₁₂, rfl, hb, hr⟩
  unfold during; unfold body at this; sep_from this

theorem during_body {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {s : Ptr} {k : Nat}
    {bs : Array Byte} {h : Heap} (hh : during ctx B e e tail pb s k bs h) :
    (body ctx B e tail pb ∗ regionIn s B.A B.S B.K (2 ^ k) bs) h := by
  unfold during at hh; unfold body; sep_from hh

theorem during_ownsIn {ctx : Ptr} {B : Buf} {e₀ e : Nat} {tail pb : Array Byte} {s : Ptr}
    {k : Nat} {bs : Array Byte} {b : BlockId} (hb : B.ptr.block = some b) (hok : Ok B e tail pb) :
    ∀ h, during ctx B e₀ e tail pb s k bs h → OwnsIn b B.A h := by
  rintro h ⟨h₁, h₂, hd, rfl, -, ⟨g₁, g₂, hdg, rfl, ⟨g₃, g₄, hd34, rfl, -, ⟨g₅, g₆, hd56, rfl, hpin, -⟩⟩, -⟩⟩
  obtain ⟨b', hb', ho⟩ := regionIn_ownsIn hpin hok.2.2.1
  rw [hok.2.2.2.2.2.1, hb] at hb'; cases hb'
  exact (((ho.union_left).union_right hd34).union_left).union_right hd

/-- Nothing changed: the invariant and the grant. -/
theorem post_same {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {s : Ptr} {k : Nat}
    {bs : Array Byte} {h : Heap} (hok : Ok B e tail pb) (hin : InBuf B s bs.size)
    (hh : during ctx B e e tail pb s k bs h) :
    ((inv ctx B).own ∗ granted (inv ctx B) s k bs) h :=
  sep_mono (fun _ x => own_intro hok x) (fun _ x => grant_intro x
    ⟨hin.1, rfl, rfl, rfl, hin.2.1, hin.2.2⟩) (during_body hh)

theorem keepsPrefix_extract {bs : Array Byte} {n : Nat} (hn : n ≤ bs.size) :
    keepsPrefix bs (bs.extract 0 n) := by
  unfold keepsPrefix
  rw [Array.extract_extract, Array.size_extract]
  simp [Nat.min_eq_left hn, Nat.min_eq_right hn]

/-- The grant shrinks in place to `n` bytes; the rest is junk. -/
theorem post_shrink {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {s : Ptr} {k : Nat}
    {bs : Array Byte} {n : Nat} {h : Heap} (hok : Ok B e tail pb) (hin : InBuf B s bs.size)
    (hn : n ≤ bs.size) (hh : during ctx B e e tail pb s k bs h) :
    ((inv ctx B).own ∗ Assn.ex fun bs' => ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗
      granted (inv ctx B) s k bs') h := by
  have hin' := hin
  obtain ⟨hib, hlo, hhi⟩ := hin'
  have h2 := sep_mono (fun _ x => x)
    (fun _ y => Region.regionIn_split y (k := n) (a' := 1) hn (Nat.mod_one _)) (during_body hh)
  have h3 : ((body ctx B e tail pb ∗ regionIn (s.add n) B.A B.S B.K 1 (bs.extract n bs.size)) ∗
      regionIn s B.A B.S B.K (2 ^ k) (bs.extract 0 n)) h := by sep_from h2
  refine sep_mono (fun _ x => own_intro hok (body_absorb x)) (fun _ x => ⟨bs.extract 0 n,
    sep_lift.mpr ⟨⟨(by simp <;> omega), (keepsPrefix_extract hn)⟩, grant_intro x
      ⟨hin.1, rfl, rfl, rfl, hin.2.1, (by simp <;> omega)⟩⟩⟩) h3

/-- `end_index` moved back by `len - n`: the end of the last grant rejoins the tail. -/
theorem post_last_shrink {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {s : Ptr} {k : Nat}
    {bs : Array Byte} {n : Nat} {h : Heap} (hok : Ok B e tail pb) (hin : InBuf B s bs.size)
    (hlast : s.off + bs.size = B.ptr.off + e) (hn : n ≤ bs.size)
    (hh : during ctx B (e - (bs.size - n)) e tail pb s k bs h) :
    ((inv ctx B).own ∗ Assn.ex fun bs' => ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗
      granted (inv ctx B) s k bs') h := by
  have hin' := hin
  obtain ⟨hib, hlo, hhi⟩ := hin'
  obtain ⟨he, hts, hpb, hA, h0, hpin, hpo, hS⟩ := hok
  unfold during at hh
  have h2 := sep_mono (fun _ x => x) (fun _ x => sep_mono (fun _ y => y)
      (fun _ y => Region.regionIn_split y (k := n) (a' := 1) hn (Nat.mod_one _)) x) hh
  have h3 : ((state ctx B (e - (bs.size - n)) ∗
      ((regionIn (s.add n) B.A B.S B.K 1 (bs.extract n bs.size) ∗
        regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail) ∗
        (regionIn B.pin B.A B.S B.K 1 pb ∗ junk))) ∗
      regionIn s B.A B.S B.K (2 ^ k) (bs.extract 0 n)) h := by sep_from h2
  have hs0 : 0 ≤ s.off := by omega
  have hq : B.ptr.add (e : Int) = (s.add n).add ((bs.extract n bs.size).size : Nat) :=
    ptr_ext (by simp [Ptr.add, hin.1]) (by simp [Ptr.add]; omega)
  have hnew : s.add n = B.ptr.add ((e - (bs.size - n) : Nat) : Int) :=
    ptr_ext (by simp [Ptr.add, hin.1]) (by simp [Ptr.add]; omega)
  refine sep_mono (fun _ x => own_intro (e := e - (bs.size - n))
      (tail := bs.extract n bs.size ++ tail) (pb := pb)
      ⟨(by omega), (by simp <;> omega), hpb, hA, h0, hpin, hpo, hS⟩ ?_)
    (fun _ x => ⟨bs.extract 0 n, sep_lift.mpr ⟨⟨(by simp <;> omega), (keepsPrefix_extract hn)⟩,
      grant_intro x ⟨hin.1, rfl, rfl, rfl, hin.2.1, (by simp <;> omega)⟩⟩⟩) h3
  unfold body
  rw [← hnew]
  refine sep_mono (fun _ y => y) (fun _ y => sep_mono (fun _ z => ?_) (fun _ z => z) y) x
  rw [hq] at z
  exact Region.regionIn_join z

/-- `end_index` moved forward by `n - len`: the last grant takes the start of the tail. -/
theorem post_last_grow {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {s : Ptr} {k : Nat}
    {bs : Array Byte} {n : Nat} {h : Heap} (hok : Ok B e tail pb) (hin : InBuf B s bs.size)
    (hlast : s.off + bs.size = B.ptr.off + e) (hn : bs.size ≤ n) (hroom : e + (n - bs.size) ≤ B.cap)
    (hh : during ctx B (e + (n - bs.size)) e tail pb s k bs h) :
    ((inv ctx B).own ∗ Assn.ex fun bs' => ⌜bs'.size = n ∧ keepsPrefix bs bs'⌝ ∗
      granted (inv ctx B) s k bs') h := by
  have hin' := hin
  obtain ⟨hib, hlo, hhi⟩ := hin'
  obtain ⟨he, hts, hpb, hA, h0, hpin, hpo, hS⟩ := hok
  unfold during at hh
  have h2 := sep_mono (fun _ x => x) (fun _ x => sep_mono (fun _ y => sep_mono
      (fun _ z => Region.regionIn_split z (k := n - bs.size) (a' := 1) (by omega) (Nat.mod_one _))
      (fun _ z => z) y) (fun _ y => y) x) hh
  have hs0 : 0 ≤ s.off := by omega
  have hq : (B.ptr.add (e : Int)) = s.add (bs.size : Nat) :=
    ptr_ext (by simp [Ptr.add, hin.1]) (by simp [Ptr.add]; omega)
  have hq2 : (B.ptr.add (e : Int)).add ((n - bs.size : Nat) : Int) =
      B.ptr.add ((e + (n - bs.size) : Nat) : Int) := Region.Ptr.add_add_nat _ _ _
  rw [hq2] at h2
  have h3 : ((state ctx B (e + (n - bs.size)) ∗
      (regionIn (B.ptr.add ((e + (n - bs.size) : Nat) : Int)) B.A B.S B.K 1
          (tail.extract (n - bs.size) tail.size) ∗
        (regionIn B.pin B.A B.S B.K 1 pb ∗ junk))) ∗
      (regionIn s B.A B.S B.K (2 ^ k) bs ∗
        regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 (tail.extract 0 (n - bs.size)))) h := by
    sep_from h2
  rw [hq] at h3
  refine sep_mono (fun _ x => own_intro (e := e + (n - bs.size))
      (tail := tail.extract (n - bs.size) tail.size) (pb := pb)
      ⟨(by omega), (by simp <;> omega), hpb, hA, h0, hpin, hpo, hS⟩ x)
    (fun _ x => ⟨bs ++ tail.extract 0 (n - bs.size), sep_lift.mpr ⟨⟨(by simp <;> omega), ?_⟩,
      grant_intro (Region.regionIn_join x) ⟨hin.1, rfl, rfl, rfl, hin.2.1, (by simp <;> omega)⟩⟩⟩) h3
  unfold keepsPrefix
  rw [Region.extract_append_left, Array.extract_eq_self_of_le (by simp <;> omega)]

/-- `free` of the last grant: it rejoins the tail. -/
theorem post_free_last {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {s : Ptr} {k : Nat}
    {bs : Array Byte} {h : Heap} (hok : Ok B e tail pb) (hin : InBuf B s bs.size)
    (hlast : s.off + bs.size = B.ptr.off + e) (hh : during ctx B (e - bs.size) e tail pb s k bs h) :
    (inv ctx B).own h := by
  have hin' := hin
  obtain ⟨hib, hlo, hhi⟩ := hin'
  obtain ⟨he, hts, hpb, hA, h0, hpin, hpo, hS⟩ := hok
  unfold during at hh
  have hs0 : 0 ≤ s.off := by omega
  have hq : (B.ptr.add (e : Int)) = s.add (bs.size : Nat) :=
    ptr_ext (by simp [Ptr.add, hin.1]) (by simp [Ptr.add]; omega)
  have hnew : s = B.ptr.add ((e - bs.size : Nat) : Int) :=
    ptr_ext (by simp [Ptr.add, hin.1]) (by simp [Ptr.add]; omega)
  have h3 : (state ctx B (e - bs.size) ∗ ((regionIn s B.A B.S B.K (2 ^ k) bs ∗
      regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail) ∗
      (regionIn B.pin B.A B.S B.K 1 pb ∗ junk))) h := by sep_from hh
  rw [hq] at h3
  refine own_intro (e := e - bs.size) (tail := bs ++ tail) (pb := pb)
    ⟨(by omega), (by simp <;> omega), hpb, hA, h0, hpin, hpo, hS⟩ ?_
  unfold body
  rw [← hnew]
  exact sep_mono (fun _ y => y) (fun _ y => sep_mono (fun _ z => Region.regionIn_weaken
    (Region.regionIn_join z) (Nat.one_dvd _)) (fun _ z => z) y) h3

/-- `free` of a grant that is not the last: its bytes are junk. -/
theorem post_free_leak {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {s : Ptr} {k : Nat}
    {bs : Array Byte} {h : Heap} (hok : Ok B e tail pb) (hh : during ctx B e e tail pb s k bs h) :
    (inv ctx B).own h :=
  own_intro hok (body_absorb (during_body hh))

theorem toNat_sub_le {a b : BitVec 64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h)

theorem ofNat_eq_of_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; rw [h, toNat_ofNat_lt (by rw [← h]; exact x.isLt)]

/-- The common start of `resize` and `free`: the `@alignCast` of the context, `ownsSlice` and its
`assert`, `isLastAllocation`. -/
theorem prologue {α : Type} {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {s : Slice}
    {k : Nat} {bs : Array Byte} {Q : α → Assn} {c : Bool → MemM α}
    (hok : Ok B e tail pb) (hin : InBuf B s.ptr bs.size) (hlen : s.len.toNat = bs.size)
    (ht : TotalTriple (during ctx B e e tail pb s.ptr k bs)
      (c (decide (s.ptr.off + bs.size = B.ptr.off + e))) Q) :
    TotalTriple (during ctx B e e tail pb s.ptr k bs)
      (ptrAddr ctx >>= fun x => if (BitVec.ofInt 64 x &&& 7) = 0 then
        heap_FixedBufferAllocator_ownsSlice ctx s >>= fun y =>
        (StateT.lift (debug_assert y) : MemM Unit) >>= fun _ =>
        heap_FixedBufferAllocator_isLastAllocation ctx s >>= c
      else throw .panic) Q := by
  have hok' := hok
  obtain ⟨he, hts, hpb, hA, h0, hpin, hpo, hS⟩ := hok
  obtain ⟨hib, hlo, hhi⟩ := hin
  refine TotalTriple.of_pure (fun h hp => pin_block (R := regionIn s.ptr B.A B.S B.K (2 ^ k) bs)
    hok' (during_body hp)) fun ⟨b, hb⟩ => ?_
  unfold during
  refine TotalTriple.bind ptrAddr_ctx fun x => TotalTriple.lift fun hx => ?_
  rw [if_pos hx]
  refine TotalTriple.bind (ownsSlice_spec hb (fun h hp => during_ownsIn hb hok' h hp) hib h0 hlo
    (by rw [hlen]; exact hhi) hA) fun y => TotalTriple.lift fun hy => ?_
  subst hy
  rw [debug_assert_true, Norm.lift_pure, pure_bind]
  refine TotalTriple.bind (isLast_spec hib (by omega)) fun z => TotalTriple.lift fun hz => ?_
  subst hz
  rw [hlen]
  exact ht

theorem resize_spec (ctx : Ptr) (B : Buf) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hn : 0 < n.toNat) (hfit : fits B n.toNat k) (hlen : s.len.toNat = bs.size) :
    TotalTriple ((inv ctx B).own ∗ granted (inv ctx B) s.ptr k bs) (impl.resize ctx s k n ra)
      (resizePost (inv ctx B) s.ptr k bs n.toNat) := by
  refine open_grant fun e tail pb hok hin => ?_
  have hok' := hok
  obtain ⟨he, hts, hpb, hA, h0, hpin, hpo, hS⟩ := hok
  have hin' := hin
  obtain ⟨hib, hlo, hhi⟩ := hin'
  have hcap : B.cap < 2 ^ 64 := by omega
  have heN : (BitVec.ofNat 64 e).toNat = e := toNat_ofNat_lt (by omega)
  have hnc : n.toNat + B.cap < 2 ^ 64 := by unfold fits at hfit; have := Nat.two_pow_pos k; omega
  unfold impl
  simp only [heap_FixedBufferAllocator_resize]
  gen_norm
  refine prologue hok' hin hlen ?_
  by_cases hl : s.ptr.off + bs.size = B.ptr.off + e
  · -- the last allocation
    simp only [hl, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, le_eq, hlen]
    by_cases hle : n.toNat ≤ bs.size
    · rw [if_pos (by simpa using hle), sub_ok (by rw [hlen]; exact hle), Norm.lift_pure, pure_bind]
      unfold during
      refine TotalTriple.bind load_end fun x => TotalTriple.lift fun hx => ?_
      subst hx
      have hsub : (s.len - n).toNat = bs.size - n.toNat := by rw [toNat_sub_le (by omega), hlen]
      rw [sub_ok (by rw [heN, hsub]; omega), Norm.lift_pure, pure_bind]
      have hv : BitVec.ofNat 64 e - (s.len - n) = BitVec.ofNat 64 (e - (bs.size - n.toNat)) :=
        ofNat_eq_of_toNat (by rw [toNat_sub_le (by rw [heN, hsub]; omega), heN, hsub])
      rw [hv]
      refine TotalTriple.bind (store_end _) fun _ => ?_
      exact TotalTriple.conseq (TotalTriple.ret (Q := resizePost (inv ctx B) s.ptr k bs n.toNat) true)
        (fun h hp => post_last_shrink hok' hin hl hle hp) (fun _ _ h => h)
    · rw [if_neg (by simpa using hle), sub_ok (by rw [hlen]; omega), Norm.lift_pure, pure_bind]
      unfold during
      refine TotalTriple.bind load_end fun x => TotalTriple.lift fun hx => ?_
      subst hx
      have hsub : (n - s.len).toNat = n.toNat - bs.size := by rw [toNat_sub_le (by omega), hlen]
      have hadd : (n - s.len).toNat + (BitVec.ofNat 64 e).toNat < 2 ^ 64 := by
        rw [hsub, heN]; omega
      rw [add_ok hadd, Norm.lift_pure, pure_bind]
      refine TotalTriple.bind load_len fun x => TotalTriple.lift fun hx => ?_
      subst hx
      rw [gt_eq, toNat_add_ok hadd, hsub, heN, toNat_ofNat_lt hcap]
      by_cases hroom : B.cap < n.toNat - bs.size + e
      · rw [if_pos (by simpa using hroom)]
        exact TotalTriple.conseq (TotalTriple.ret (Q := resizePost (inv ctx B) s.ptr k bs n.toNat) false)
          (fun h hp => post_same hok' hin hp) (fun _ _ h => h)
      rw [if_neg (by simpa using hroom)]
      refine TotalTriple.bind load_end fun x => TotalTriple.lift fun hx => ?_
      subst hx
      have hadd2 : (BitVec.ofNat 64 e).toNat + (n - s.len).toNat < 2 ^ 64 := by rw [hsub, heN]; omega
      rw [add_ok hadd2, Norm.lift_pure, pure_bind]
      have hv : BitVec.ofNat 64 e + (n - s.len) = BitVec.ofNat 64 (e + (n.toNat - bs.size)) :=
        ofNat_eq_of_toNat (by rw [toNat_add_ok hadd2, heN, hsub])
      rw [hv]
      refine TotalTriple.bind (store_end _) fun _ => ?_
      exact TotalTriple.conseq (TotalTriple.ret (Q := resizePost (inv ctx B) s.ptr k bs n.toNat) true)
        (fun h hp => post_last_grow hok' hin hl (by omega) (by omega) hp) (fun _ _ h => h)
  · -- not the last allocation
    simp only [hl, decide_false, Bool.not_false, ↓reduceIte, gt_eq, hlen]
    by_cases hgt : bs.size < n.toNat
    · rw [if_pos (by simpa using hgt)]
      exact TotalTriple.conseq (TotalTriple.ret (Q := resizePost (inv ctx B) s.ptr k bs n.toNat) false)
        (fun h hp => post_same hok' hin hp) (fun _ _ h => h)
    · rw [if_neg (by simpa using hgt)]
      exact TotalTriple.conseq (TotalTriple.ret (Q := resizePost (inv ctx B) s.ptr k bs n.toNat) true)
        (fun h hp => post_shrink hok' hin (by omega) hp) (fun _ _ h => h)

theorem remap_spec (ctx : Ptr) (B : Buf) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hn : 0 < n.toNat) (hfit : fits B n.toNat k) (hlen : s.len.toNat = bs.size) :
    TotalTriple ((inv ctx B).own ∗ granted (inv ctx B) s.ptr k bs) (impl.remap ctx s k n ra)
      (remapPost (inv ctx B) s.ptr k bs n.toNat) := by
  have hr := resize_spec ctx B s k n ra bs hn hfit hlen
  unfold impl at hr ⊢
  simp only [heap_FixedBufferAllocator_remap]
  gen_norm
  refine TotalTriple.bind hr fun r => ?_
  cases r with
  | true =>
    simp only [↓reduceIte]
    exact TotalTriple.conseq (TotalTriple.ret (Q := remapPost (inv ctx B) s.ptr k bs n.toNat)
      (some s.ptr)) (fun h hp => hp) (fun _ _ h => h)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact TotalTriple.conseq (TotalTriple.ret (Q := remapPost (inv ctx B) s.ptr k bs n.toNat)
      none) (fun h hp => hp) (fun _ _ h => h)

theorem free_spec (ctx : Ptr) (B : Buf) (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) :
    TotalTriple ((inv ctx B).own ∗ granted (inv ctx B) s.ptr k bs) (impl.free ctx s k ra)
      (fun _ => (inv ctx B).own) := by
  refine open_grant fun e tail pb hok hin => ?_
  have hok' := hok
  obtain ⟨he, hts, hpb, hA, h0, hpin, hpo, hS⟩ := hok
  have hin' := hin
  obtain ⟨hib, hlo, hhi⟩ := hin'
  have heN : (BitVec.ofNat 64 e).toNat = e := toNat_ofNat_lt (by omega)
  unfold impl
  simp only [heap_FixedBufferAllocator_free]
  gen_norm
  refine prologue hok' hin hlen ?_
  by_cases hl : s.ptr.off + bs.size = B.ptr.off + e
  · simp only [hl, decide_true, ↓reduceIte]
    unfold during
    refine TotalTriple.bind load_end fun x => TotalTriple.lift fun hx => ?_
    subst hx
    rw [sub_ok (by rw [heN, hlen]; omega), Norm.lift_pure, pure_bind]
    have hv : BitVec.ofNat 64 e - s.len = BitVec.ofNat 64 (e - bs.size) :=
      ofNat_eq_of_toNat (by rw [toNat_sub_le (by rw [heN, hlen]; omega), heN, hlen])
    rw [hv]
    exact TotalTriple.conseq (store_end _) (fun h hp => hp)
      (fun _ h hp => post_free_last hok' hin hl hp)
  · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact TotalTriple.conseq (TotalTriple.ret (Q := fun _ => (inv ctx B).own) ())
      (fun h hp => post_free_leak hok' hp) (fun _ _ h => h)

/-- **The translated `FixedBufferAllocator` satisfies the generic allocator specification**, in
the total logic, for every allocator struct `ctx` and every buffer `B`. -/
theorem allocSpec (ctx : Ptr) (B : Buf) : AllocSpec Logic.total impl ctx (inv ctx B) where
  alloc len k ra hl hk hfit := alloc_spec ctx B len k ra hl hk hfit
  resize s k n ra bs _ hn hfit hlen _ := resize_spec ctx B s k n ra bs hn hfit hlen
  remap s k n ra bs _ hn hfit hlen _ := remap_spec ctx B s k n ra bs hn hfit hlen
  free s k ra bs _ hlen _ := free_spec ctx B s k ra bs hlen

/-! ## The allocator around the vtable: grant separation, `init`, release, `reset` -/

/-- Two grants of one fixed buffer have disjoint address ranges: the premise of the copying path
of `realloc` (`Wrap.realloc_spec`). -/
theorem grantSep (ctx : Ptr) (B : Buf) (k : Nat) : GrantSep (inv ctx B) k := by
  intro h p q bs bs' A S A' S' K K' hp hq hh
  obtain ⟨h₁, h₂, hd, rfl, ⟨g₁, g₂, hd₁, rfl, ⟨-, -, b, hpb, hp0, hl₁⟩, ⟨⟨hpblk, hA, -⟩, -⟩⟩,
    ⟨g₃, g₄, hd₂, rfl, ⟨-, -, b', hqb, hq0, hl₂⟩, ⟨⟨hqblk, hA', -⟩, -⟩⟩⟩ := hh
  subst hA hA'
  have hbb : b' = b := by
    rw [hpblk, hqblk.symm] at hpb; rw [hpb] at hqb; exact (Option.some.inj hqb).symm
  subst hbb
  unfold RangeSep
  apply Classical.byContradiction
  intro hc
  simp only [not_or, Int.not_le] at hc
  obtain ⟨o, ho1, ho2, ho3⟩ : ∃ o : Nat, p.off.toNat ≤ o ∧ q.off.toNat ≤ o ∧
      (o = p.off.toNat ∨ o = q.off.toNat) := by
    rcases Nat.le_total p.off.toNat q.off.toNat with hle | hle
    · exact ⟨q.off.toNat, hle, Nat.le_refl _, Or.inr rfl⟩
    · exact ⟨p.off.toNat, Nat.le_refl _, hle, Or.inl rfl⟩
  have c₁ : g₁ (b', o) ≠ none := by
    rw [hl₁, if_pos ⟨rfl, ho1, by omega⟩]; simp
  have c₂ : g₃ (b', o) ≠ none := by
    rw [hl₂, if_pos ⟨rfl, ho2, by omega⟩]; simp
  rcases hd (b', o) with e | e
  · simp only [Heap.union_apply, Option.or_eq_none_iff] at e; exact c₁ e.1
  · simp only [Heap.union_apply, Option.or_eq_none_iff] at e; exact c₂ e.1

theorem sep_junk {P : Assn} {h : Heap} (hp : P h) : (P ∗ junk) h :=
  ⟨h, Heap.empty, Heap.disjoint_empty h, by simp, hp, trivial⟩

/-- `init` and a fresh struct: the whole buffer is free. -/
theorem own_init {ctx : Ptr} {B : Buf} {bufbs pb : Array Byte} {h : Heap}
    (hcap : bufbs.size = B.cap) (hpb : 0 < pb.size) (hA : B.A + B.ptr.off.toNat + B.cap < 2 ^ 64)
    (h0 : 0 ≤ B.ptr.off) (hpin : B.pin.block = B.ptr.block)
    (hpo : B.pin.off + pb.size ≤ B.ptr.off ∨ B.ptr.off + B.cap ≤ B.pin.off)
    (hS : B.ptr.off.toNat + B.cap ≤ B.S)
    (hh : (state ctx B 0 ∗ (regionIn B.ptr B.A B.S B.K 1 bufbs ∗ regionIn B.pin B.A B.S B.K 1 pb)) h) :
    own ctx B h := by
  refine own_intro (e := 0) (tail := bufbs) (pb := pb)
    ⟨Nat.zero_le _, by omega, hpb, hA, h0, hpin, hpo, hS⟩ ?_
  unfold body
  have e0 : B.ptr.add ((0 : Nat) : Int) = B.ptr := by simp [Ptr.add]
  rw [e0]
  exact sep_mono (fun _ x => x) (fun _ x => sep_mono (fun _ y => y) (fun _ y => sep_junk y) x) hh

/-- The invariant holds the struct. -/
theorem own_state {ctx : Ptr} {B : Buf} {h : Heap} (ho : own ctx B h) :
    ((Assn.ex fun e => state ctx B e) ∗ junk) h := by
  obtain ⟨e, tail, pb, hb⟩ := ho
  obtain ⟨-, hb⟩ := sep_lift.mp hb
  unfold body at hb
  exact sep_mono (fun _ x => ⟨e, x⟩) (fun _ _ => trivial) hb

/-- The struct is 24 bytes of its block. -/
theorem state_bytes {ctx : Ptr} {B : Buf} {e : Nat} {h : Heap} (hs : state ctx B e h) :
    ∃ bs, bs.size = 24 ∧ bytesAt ctx B.cA B.cS B.cK bs h := by
  obtain ⟨h₁, h₂, hd, rfl, ⟨-, -, bs₁, hs₁, -, hb₁⟩, ⟨-, -, bs₂, hs₂, -, hb₂⟩⟩ := hs
  have e8 : ctx.add 8 = ctx.add ((bs₁.size : Nat) : Int) := by rw [hs₁]; rfl
  rw [e8] at hb₂
  refine ⟨bs₁ ++ bs₂, by simp [hs₁, hs₂]; rfl, Region.bytesAt_append.mp ⟨h₁, h₂, hd, rfl, hb₁, hb₂⟩⟩

theorem getElem!_ofFn {n : Nat} (f : Fin n → Byte) {j : Nat} (hj : j < n) :
    (Array.ofFn f)[j]! = f ⟨j, hj⟩ := by
  simp [getElem!_def, hj]

/-- `reset` of an allocator whose every buffer byte is held: the struct, the free tail, the junk
(padding and bytes that frees leaked) together have the whole buffer, which becomes free again.
`Covers` is the precondition that no one else holds a byte of the buffer: a client that still
holds a grant would see its bytes reused, so it has to give them back first. -/
theorem reset_spec (ctx : Ptr) (B : Buf) {b : BlockId} (hb : B.ptr.block = some b)
    (hctx : ctx.block ≠ B.ptr.block) :
    TotalTriple (fun h => own ctx B h ∧ Covers b B.ptr.off.toNat (B.ptr.off.toNat + B.cap) h)
      (heap_FixedBufferAllocator_reset ctx) (fun _ => own ctx B) := by
  simp only [heap_FixedBufferAllocator_reset]
  gen_norm
  intro m hP hF hd hm ⟨ho, hcov⟩ hst
  obtain ⟨e, tail, pb, hbd⟩ := ho
  obtain ⟨hok, hbd⟩ := sep_lift.mp hbd
  have hok' := hok
  obtain ⟨he, hts, hpb, hA, h0, hpin, hpo, hS⟩ := hok
  unfold body at hbd
  obtain ⟨hs, hr, hdsr, rfl, hst₀, hrest⟩ := hbd
  obtain ⟨ht, hpj, hdt, rfl, htl, ⟨hpp, hj, hdpj, rfl, hpr, -⟩⟩ := hrest
  -- the struct's cells are in the struct's block, not the buffer's
  have hsnb : ∀ o, hs (b, o) = none := by
    intro o
    obtain ⟨bs, -, hbs⟩ := state_bytes hst₀
    obtain ⟨c, hcb, -, hl⟩ := hbs
    rw [hl]
    have : b ≠ c := by intro hcb'; subst hcb'; exact hctx (by rw [hcb, hb])
    simp [this]
  -- store `0` into `end_index`, keeping the rest of the heap exactly
  have hrun := (store_end (ctx := ctx) (B := B) (e := e) (R := fun h => h = ht ∪ (hpp ∪ hj)) 0) m
    (hs ∪ (ht ∪ (hpp ∪ hj))) hF hd hm ⟨hs, _, hdsr, rfl, hst₀, rfl⟩ hst
  obtain ⟨u, m', hQ, hr, hd', hm', ⟨hs', hr', hdsr', rfl, hst', rfl⟩, hst₁⟩ := hrun
  refine ⟨u, m', _, by simpa using hr, hd', hm', ?_, hst₁⟩
  -- the pin fixes the buffer block's address, size and kind in the memory
  have hpinpos := hpb
  have hpr0 := hpr
  obtain ⟨-, hKp, bp, hbp, -, hlp⟩ := hpr0
  rw [hpin, hb] at hbp; cases hbp
  have hpp1 : hpp (b, B.pin.off.toNat) = some ⟨pb[0]!, B.A, B.S, B.K⟩ := by
    rw [hlp]; simp [hpinpos]
  have hpj1 : (hpp ∪ hj) (b, B.pin.off.toNat) = some ⟨pb[0]!, B.A, B.S, B.K⟩ := by simp [hpp1]
  have ht1 : ht (b, B.pin.off.toNat) = none :=
    (hdt (b, B.pin.off.toNat)).resolve_right (by rw [hpj1]; simp)
  have hpincell : m.heap (b, B.pin.off.toNat) = some ⟨pb[0]!, B.A, B.S, B.K⟩ := by
    rw [hm]; simp [hsnb, ht1, hpj1]
  obtain ⟨blk, hblk, hlive, hpo', hpc⟩ := Mem.heap_some hpincell
  simp only [Cell.mk.injEq] at hpc
  obtain ⟨-, hbA, hbS, hbK⟩ := hpc
  let lo := B.ptr.off.toNat
  let inBuf : Loc → Prop := fun l => l.1 = b ∧ lo ≤ l.2 ∧ l.2 < lo + B.cap
  -- every buffer cell of the old heap is a cell of the block, with the block's metadata
  have hcell : ∀ i, i < B.cap → ∃ c, (ht ∪ (hpp ∪ hj)) (b, lo + i) = some c ∧
      c = ⟨c.byte, B.A, B.S, B.K⟩ := by
    intro i hi
    have hne := hcov (lo + i) (by omega) (by omega)
    have hsn := hsnb (lo + i)
    simp only [Heap.union_apply, hsn, Option.none_or] at hne
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hne
    refine ⟨c, hc, ?_⟩
    have : m.heap (b, lo + i) = some c := by rw [hm]; simp [hsn, hc]
    obtain ⟨blk', hblk', -, ho', hc'⟩ := Mem.heap_some this
    rw [hblk] at hblk'; cases hblk'
    rw [hc']; simp [hbA, hbS, hbK]
  -- the tail's cells are buffer cells; the pin's are not
  have hlo : (B.ptr.off.toNat : Int) = B.ptr.off := Int.toNat_of_nonneg h0
  have htin : ∀ l, ht l ≠ none → inBuf l := by
    intro l hl
    obtain ⟨-, -, bt, hbt, -, hlt⟩ := htl
    rw [hlt] at hl
    split at hl
    · rename_i hc
      simp only [Ptr.add] at hbt
      rw [hb] at hbt; cases hbt
      rw [off_add_nat h0] at hc
      exact ⟨hc.1, by omega, by omega⟩
    · exact absurd rfl hl
  have hpin0 : 0 ≤ B.pin.off := Region.bytesAt_pos_off hpr.2.2
  have hpout : ∀ l, inBuf l → hpp l = none := by
    rintro l ⟨-, hl2, hl3⟩
    obtain ⟨-, -, bq, -, -, hlq⟩ := hpr
    rw [hlq, if_neg]
    rintro ⟨-, h2, h3⟩
    have := Int.toNat_of_nonneg hpin0
    rcases hpo with hpo | hpo <;> omega
  let old := ht ∪ (hpp ∪ hj)
  let bs' : Array Byte := Array.ofFn (n := B.cap) fun i =>
    match old (b, lo + i.val) with
    | some c => c.byte
    | none => .undef
  let hT : Heap := fun l => if inBuf l then old l else none
  let hj' : Heap := fun l => if inBuf l then none else hj l
  have hsplit : old = hT ∪ (hpp ∪ hj') := by
    funext l
    show old l = (hT l).or ((hpp l).or (hj' l))
    by_cases hl : inBuf l
    · simp only [hT, hj', if_pos hl, hpout l hl, Option.none_or, Option.or_none]
    · have : ht l = none := Classical.byContradiction fun hne => hl (htin l hne)
      simp only [hT, hj', if_neg hl, Option.none_or, old, Heap.union_apply, this]
  have hdj : Heap.Disjoint hT (hpp ∪ hj') := by
    intro l
    by_cases hl : inBuf l
    · right; simp [hj', hl, hpout l hl]
    · left; simp [hT, hl]
  have hdpj' : Heap.Disjoint hpp hj' := by
    intro l; rcases hdpj l with e | e
    · left; exact e
    · right; simp only [hj']; split <;> simp [e]
  have hreg : regionIn (B.ptr.add ((0 : Nat) : Int)) B.A B.S B.K 1 bs' hT := by
    refine ⟨Nat.mod_one _, hKp, b, by simp [Ptr.add, hb], by simp [Ptr.add]; omega, fun l => ?_⟩
    obtain ⟨x, y⟩ := l
    have hoff : (B.ptr.add ((0 : Nat) : Int)).off.toNat = lo := by simp [Ptr.add, lo]
    rw [hoff]
    simp only [bs', Array.size_ofFn, hT, inBuf]
    by_cases hl : x = b ∧ lo ≤ y ∧ y < lo + B.cap
    · simp only [if_pos hl]
      obtain ⟨hx, hy1, hy2⟩ := hl
      subst hx
      obtain ⟨c, hc, hce⟩ := hcell (y - lo) (by omega)
      rw [show lo + (y - lo) = y by omega] at hc
      rw [getElem!_ofFn _ (by omega)]
      simp only [show lo + (y - lo) = y by omega, hc]
      have ho : old (x, y) = some c := hc
      rw [ho]
      exact congrArg some hce
    · simp only [if_neg hl]
  refine own_intro (e := 0) (tail := bs') (pb := pb)
    ⟨Nat.zero_le _, by simp [bs'], hpb, hA, h0, hpin, hpo, hS⟩ ?_
  unfold body
  show (state ctx B 0 ∗ (regionIn (B.ptr.add ((0 : Nat) : Int)) B.A B.S B.K 1 bs' ∗
    (regionIn B.pin B.A B.S B.K 1 pb ∗ junk))) (hs' ∪ old)
  rw [hsplit]
  exact ⟨hs', hT ∪ (hpp ∪ hj'), by rw [← hsplit]; exact hdsr', rfl, hst',
    hT, hpp ∪ hj', hdj, rfl, hreg, hpp, hj', hdpj', rfl, hpr, trivial⟩

end FBA

end AllocFba
