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
  obtain ⟨he, hts, hpb, hA, h0, hpin⟩ := hok
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
      ⟨(by omega), (by simp only [Array.size_extract]; omega), hpb, hA, h0, hpin⟩ ?_)
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
  rw [hok.2.2.2.2.2, hb] at hb'; cases hb'
  exact ((ho.union_left).union_right hd34 |>.union_right hdg).union_left

theorem pin_block {ctx : Ptr} {B : Buf} {e : Nat} {tail pb : Array Byte} {R : Assn} {h : Heap}
    (hok : Ok B e tail pb) (hh : (body ctx B e tail pb ∗ R) h) : ∃ b, B.ptr.block = some b := by
  obtain ⟨h₁, h₂, hd, rfl, ⟨g₁, g₂, hdg, rfl, -, ⟨g₃, g₄, hd34, rfl, -, ⟨g₅, g₆, hd56, rfl, hpin, -⟩⟩⟩, -⟩ := hh
  have := (regionIn_facts hpin).2.2.2
  rw [hok.2.2.2.2.2] at this
  exact Option.isSome_iff_exists.mp this

theorem alloc_spec (ctx : Ptr) (B : Buf) (n : BitVec 64) (k : Nat) (ra : BitVec 64)
    (hn : 0 < n.toNat) (hk : k < 64) (hfit : fits B n.toNat k) :
    TotalTriple (own ctx B) (impl.alloc ctx n k ra) (allocPost (inv ctx B) n.toNat k) := by
  refine TotalTriple.conseq (P := own ctx B ∗ emp) ?_ (fun h hp => sep_emp.mpr hp) (fun _ _ h => h)
  refine own_open fun e tail pb hok => ?_
  have hok' := hok
  obtain ⟨he, hts, hpb, hA, h0, hpin⟩ := hok
  refine TotalTriple.conseq (P := body ctx B e tail pb) ?_ (fun h hp => sep_emp.mp hp)
    (fun _ _ h => h)
  refine TotalTriple.of_pure (fun h hp => pin_block (R := emp) hok' (sep_emp.mpr hp))
    fun ⟨b, hb⟩ => ?_
  have hown := pin_ownsIn (ctx := ctx) (R := emp) hb hok'
  unfold impl
  simp only [heap_FixedBufferAllocator_alloc]
  fba_norm
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

end FBA

end AllocFba
