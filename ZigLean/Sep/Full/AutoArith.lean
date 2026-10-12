import ZigLean.Sep.Full.AutoAttr
import ZigLean.Mem.Lemmas
import ZigLean.Range

/-!
# The arithmetic normal forms of `fsym` (`fsym_arith`, `docs/proof-automation.md`)

The simp set `fsym_arith` and the lemmas of the arithmetic solver (`arithCore` in
`ZigLean/Sep/Full/Auto.lean`). Side goals are about words, pointer offsets and sizes; the solver
states them over **one normal form**: the value `x.toNat : Nat` of every word, so that `omega`
reads them. Every other reading of a word is rewritten to it:

* **signed values**: `x.toInt` is `x.toNat - 2 ^ w * (2 * x.toNat / 2 ^ w)` (`toInt_eq_div`;
  linear for a literal width: `omega` reads a division by a literal, no case split), `Zig.val`
  and the signed comparisons and overflow bits of generated code through it;
* **width changes**: `setWidth` (widening and `@truncate`) is a remainder by `2 ^ m`, removed
  where the value fits (`Nat.mod_eq_of_lt`, side condition by `omega`); `BitVec.ofInt`/`ofNat`
  likewise (`toNat_ofInt_nowrap`, `toNat_ofNat_nowrap`);
* **word operations**: `+ - *` as values modulo `2 ^ w`, without the remainder where the result
  fits (`Zig.toNat_add_of_lt` and friends, conditional rewrites of the solver), overflow bits and
  shifts as values, low and high masks as remainders by `2 ^ x`;
* comparisons of words as comparisons of values; pointer offsets as integers.

Truncated subtractions, `Int.toNat`, `min` and `max` whose case the facts decide become opaque
atoms with a linear defining fact (`subAtom`, `toNatAtom`, `minAtom`, `maxAtom`, used by
`omegaFacts`), so `omega` explores no case split for them.

Regressions: `tests/roadmap/sep-auto/Arith.lean`.
-/

namespace Zig.Full.Auto

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

/-! **Signed values** in the normal form: `x.toInt` from `x.toNat`. The sign is
`2 * x.toNat / 2 ^ w` (`0` or `1`), a division by a literal for a literal width, which `omega`
reads without a case split (`Int.bmod` and the `if` of `BitVec.toInt_eq_toNat_cond` it does not
read, or splits on). -/

/-- The signed value of a word from its unsigned value. -/
theorem toInt_eq_div (x : BitVec w) :
    x.toInt = (x.toNat : Int) - 2 ^ w * ((2 * x.toNat / 2 ^ w : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split
  · rw [Nat.div_eq_of_lt (by omega)]; simp
  · rw [show 2 * x.toNat / 2 ^ w = 1 from Nat.div_eq_of_lt_le (by omega) (by omega)]; push_cast; omega

/-- The value of an integer operand of generated code (`Zig.val`; signed or unsigned). -/
theorem val_true (a : BitVec w) : Zig.val true a = a.toInt := rfl
theorem val_false (a : BitVec w) : Zig.val false a = (a.toNat : Int) := rfl

/-- `@truncate`: the low `m` bits. -/
theorem toNat_trunc {m : Nat} (a : BitVec w) : (Zig.trunc m a).toNat = a.toNat % 2 ^ m :=
  BitVec.toNat_setWidth m a

end Values

/-! ## Comparisons and pointer offsets -/

/-- `Zig` comparisons of unsigned words, as comparisons of their values. -/
@[fsym_arith] theorem lt_false {n : Nat} (a b : BitVec n) : Zig.lt false a b = decide (a.toNat < b.toNat) := by
  simp [Zig.lt, BitVec.ult]
@[fsym_arith] theorem le_false {n : Nat} (a b : BitVec n) : Zig.le false a b = decide (a.toNat ≤ b.toNat) := by
  simp [Zig.le, BitVec.ule]
@[fsym_arith] theorem gt_false {n : Nat} (a b : BitVec n) : Zig.gt false a b = decide (b.toNat < a.toNat) := by
  simp [Zig.gt, Zig.lt, BitVec.ult]
@[fsym_arith] theorem ge_false {n : Nat} (a b : BitVec n) : Zig.ge false a b = decide (b.toNat ≤ a.toNat) := by
  simp [Zig.ge, Zig.le, BitVec.ule]

/-- … and of signed words, as comparisons of their signed values. -/
@[fsym_arith] theorem lt_true {n : Nat} (a b : BitVec n) : Zig.lt true a b = decide (a.toInt < b.toInt) := by
  simp [Zig.lt, BitVec.slt]
@[fsym_arith] theorem le_true {n : Nat} (a b : BitVec n) : Zig.le true a b = decide (a.toInt ≤ b.toInt) := by
  simp [Zig.le, BitVec.sle]
@[fsym_arith] theorem gt_true {n : Nat} (a b : BitVec n) : Zig.gt true a b = decide (b.toInt < a.toInt) := by
  simp [Zig.gt, Zig.lt, BitVec.slt]
@[fsym_arith] theorem ge_true {n : Nat} (a b : BitVec n) : Zig.ge true a b = decide (b.toInt ≤ a.toInt) := by
  simp [Zig.ge, Zig.le, BitVec.sle]

@[fsym_arith] theorem off_add (p : Ptr) (k : Int) : (p.add k).off = p.off + k := rfl
@[fsym_arith] theorem block_add (p : Ptr) (k : Int) : (p.add k).block = p.block := rfl
@[fsym_arith] theorem off_elem (p : Ptr) (s : Nat) (i : BitVec 64) :
    (p.elem s i).off = p.off + ((s * i.toNat : Nat) : Int) := rfl
@[fsym_arith] theorem block_elem (p : Ptr) (s : Nat) (i : BitVec 64) : (p.elem s i).block = p.block := rfl

/-! ## The simp set -/

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

-- Signed values, width changes and signed overflow in the normal form.
attribute [fsym_arith] toInt_eq_div val_true val_false BitVec.toNat_setWidth toNat_trunc
  BitVec.saddOverflow BitVec.ssubOverflow BitVec.smulOverflow Bool.or_eq_false_iff

open Lean Meta Simp in
/-- The size `Enc.size T` of a closed type's encoding, as a literal (with `LawfulEnc.size_encode`:
the size of an encoded value, `(Enc.encode v).size`). -/
dsimproc [fsym_arith] reduceEncSize (Enc.size _) := fun e => do
  unless e.isAppOfArity ``Enc.size 2 && !e.hasFVar && !e.hasMVar do return .continue
  let v ← whnfD e
  let some n := v.nat? <|> v.rawNatLit? | return .continue
  return .done (mkNatLit n)

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

/-! ## Powers of two -/

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
