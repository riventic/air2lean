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

/-! ## The invariant -/

/-- The buffer: its pointer and length, the address, size and kind of its block, and one byte
`pin` of that block outside the buffer. -/
structure Buf where
  ptr : Ptr
  cap : Nat
  A : Nat
  S : Nat
  K : BlockKind
  pin : Ptr

/-- Bytes that the allocator has given up: padding, and the bytes of non-last frees. -/
def junk : Assn := fun _ => True

/-- The `FixedBufferAllocator` struct at `ctx`: `end_index = e` and the buffer slice. -/
def state (ctx : Ptr) (B : Buf) (e : Nat) : Assn :=
  pts ctx 8 (BitVec.ofNat 64 e) ∗ pts (ctx.add 8) 8 (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice)

def Ok (B : Buf) (e : Nat) (tail pb : Array Byte) : Prop :=
  e ≤ B.cap ∧ tail.size = B.cap - e ∧ 0 < pb.size ∧ B.A + B.ptr.off.toNat + B.cap < 2 ^ 64 ∧
    0 ≤ B.ptr.off ∧ B.pin.block = B.ptr.block

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

theorem two_pow_lt {k : Nat} (hk : k < 64) : 2 ^ k < 2 ^ 64 :=
  Nat.pow_lt_pow_right (by decide) hk

theorem toNat_two_pow {k : Nat} (hk : k < 64) : (BitVec.ofNat 64 (2 ^ k)).toNat = 2 ^ k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (two_pow_lt hk)]

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

theorem load_end : TotalTriple (state ctx B e ∗ R) (load (BitVec 64) 8 ctx)
    (fun r => ⌜r = BitVec.ofNat 64 e⌝ ∗ (state ctx B e ∗ R)) := by
  unfold state
  exact TotalTriple.conseq (TotalTriple.frame (R := pts (ctx.add 8) 8
      (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice) ∗ R) (TotalTriple.load (by decide)))
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

theorem load_ptr : TotalTriple (state ctx B e ∗ R) (load Ptr 8 (ctx.add 8))
    (fun r => ⌜r = B.ptr⌝ ∗ (state ctx B e ∗ R)) := by
  unfold state
  have t := pts_slice_field_load (T := Ptr) (q := ctx.add 8) (s := ⟨B.ptr, BitVec.ofNat 64 B.cap⟩)
    (o := 0) (v := B.ptr) rfl (Or.inl rfl) (fun bs h1 _ => by simpa using h1)
  push_cast at t
  simp only [Norm.add_zero_ptr] at t
  exact TotalTriple.conseq (TotalTriple.frame (R := pts ctx 8 (BitVec.ofNat 64 e) ∗ R) t)
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

theorem load_len : TotalTriple (state ctx B e ∗ R) (load (BitVec 64) 8 ((ctx.add 8).add 8))
    (fun r => ⌜r = BitVec.ofNat 64 B.cap⌝ ∗ (state ctx B e ∗ R)) := by
  unfold state
  have t := pts_slice_field_load (T := BitVec 64) (q := ctx.add 8)
    (s := ⟨B.ptr, BitVec.ofNat 64 B.cap⟩) (o := 8) (v := BitVec.ofNat 64 B.cap) rfl (Or.inr rfl)
    (fun bs _ h2 => h2)
  push_cast at t
  exact TotalTriple.conseq (TotalTriple.frame (R := pts ctx 8 (BitVec.ofNat 64 e) ∗ R) t)
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

theorem load_slice : TotalTriple (state ctx B e ∗ R) (load Slice 8 (ctx.add 8))
    (fun r => ⌜r = ⟨B.ptr, BitVec.ofNat 64 B.cap⟩⌝ ∗ (state ctx B e ∗ R)) := by
  unfold state
  exact TotalTriple.conseq (TotalTriple.frame (R := pts ctx 8 (BitVec.ofNat 64 e) ∗ R)
      (TotalTriple.load (by decide)))
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

theorem store_end (e' : Nat) : TotalTriple (state ctx B e ∗ R)
    (store 8 ctx (BitVec.ofNat 64 e')) (fun _ => state ctx B e' ∗ R) := by
  unfold state
  exact TotalTriple.conseq (TotalTriple.frame (R := pts (ctx.add 8) 8
      (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice) ∗ R) (TotalTriple.store (by decide) _))
    (fun h hp => by sep_from hp) (fun _ h hp => by sep_from hp)

/-- The `@alignCast` of the context pointer (`*FixedBufferAllocator`, alignment 8) passes. -/
theorem ptrAddr_ctx : TotalTriple (state ctx B e ∗ R) (ptrAddr ctx)
    (fun r => ⌜(BitVec.ofInt 64 r &&& 7) = 0⌝ ∗ (state ctx B e ∗ R)) := by
  intro m hP hF hd hm hp hst
  obtain ⟨h₁, h₂, hd₁₂, rfl, ⟨g₁, g₂, -, rfl, ⟨A, S, K, bs, ha, hs, -, hb, -⟩, -⟩, -⟩ := id hp
  obtain ⟨b, hpb, ho⟩ := bytesAt_ownsIn hb (by rw [hs]; decide)
  have hown : OwnsIn b A ((g₁ ∪ g₂) ∪ h₂) := ho.union_left.union_left
  obtain ⟨blk, hblk, hA⟩ := hown.block hm
  refine ⟨(blk.addr : Int) + ctx.off, m, _, ?_, hd, hm, sep_lift.mpr ⟨?_, hp⟩, hst⟩
  · simp [ptrAddr, hpb, hblk, zig_unfold, get, getThe, MonadStateOf.get, StateT.get]
  · rw [hA]
    have hx : ((A : Int) + ctx.off) % 2 ^ 3 = 0 := by
      have : ((A + ctx.off.toNat : Nat) : Int) % ((2 ^ 3 : Nat) : Int) = 0 := by exact_mod_cast ha
      rw [Int.natCast_add, Int.toNat_of_nonneg (Region.bytesAt_pos_off hb)] at this
      exact_mod_cast this
    have h0 := Region.bytesAt_pos_off hb
    exact Ops.and_mask_eq_zero (k := 3) (by decide) (by omega) hx

end State

/-! ## Overflow-checked arithmetic -/

theorem add_ok {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    Zig.add false a b = pure (a + b) := by
  simp only [Zig.add, BitVec.uaddOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; omega)]

theorem toNat_add_ok {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

theorem sub_ok {a b : BitVec 64} (h : b.toNat ≤ a.toNat) : Zig.sub false a b = pure (a - b) := by
  simp only [Zig.sub, BitVec.usubOverflow, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp; omega)]

theorem gt_eq (a b : BitVec 64) : Zig.gt false a b = decide (b.toNat < a.toNat) := by
  simp [Zig.gt, Zig.lt, BitVec.ult]

theorem le_eq (a b : BitVec 64) : Zig.le false a b = decide (a.toNat ≤ b.toNat) := by
  simp [Zig.le, BitVec.ule]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

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

/-- Normalize a generated function that uses memory to its `MemM` program. -/
macro "fba_norm" : tactic => `(tactic| (
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, Norm.run_callM, Norm.run_callR,
    Norm.run_liftM, Norm.run_liftR, Norm.run_ite, Norm.ite_bind, Norm.run_throw,
    Norm.throw_bind, Norm.lift_pure, Norm.lift_throw, Norm.sub_zero, Norm.elem_zero,
    Norm.run_get, Norm.run_modify, Norm.add_zero_ptr,
    bind_assoc, pure_bind, map_pure, bind_map_left, map_bind, Norm.beq_true_iff, bind_pure_unit,
    Zig.isNonErr, Zig.isErr, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
  try simp only [Norm.isSome_ite, Norm.elim_bind, bind_assoc, pure_bind, Norm.ite_bind,
    bind_pure_unit]))

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
  fba_norm
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

end FBA

end AllocFba
