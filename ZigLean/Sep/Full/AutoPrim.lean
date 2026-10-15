import ZigLean.Sep.Full.AutoRules

/-!
# Step rules for primitive commands of generated code (`@[fsym]`)

Rules of the symbolic executor (`docs/proof-automation.md`) for commands that the rule library
of `AutoRules.lean` did not cover:

* `intCast_widen_step`: an unsigned widening `@intCast` (it cannot fail; the result has the
  value of its operand);
* `ptrEqAddr_raw`: pointer `==` of two pointers without a block (`@ptrFromInt`, null): the
  addresses are the offsets (MM-4);
* `storeBytes_region`, `storeEnc_region`: a store of raw bytes (`Zig.storeBytes`, which the
  translator writes for a NaN constant's exact bytes) or of a value of any encoding (`Zig.store`
  without `LawfulEnc`: a float vector, whose NaN lanes have undefined bits) at the start of an
  owned region. The region's bytes are the written ones followed by the rest (`writeBytes`).
  They follow from the native store of owned bytes (`FTotalTriple.storeBytes_bytesAt`,
  `Ops.lean`).
-/

namespace Zig.Full.Auto

open FAssn Assn

section Values

variable {P : FAssn}

/-- An unsigned widening `@intCast`: the value is kept. -/
@[fsym] theorem intCast_widen_step {n m : Nat} {a : BitVec n} {safe : Bool} (h : n ≤ m) :
    FTotalTriple P (StateT.lift (Zig.intCast false false m a safe) : MemM (BitVec m))
      (fun r => ⟪r.toNat = a.toNat⟫ ⋆ P) := by
  rw [Zig.intCast_unsigned_widen a m h]
  have ha := a.isLt
  have hp : 2 ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) h
  exact read_val (by rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega))

/-- **An item of a vector value** (`Zig.vindex`) at an index below its length. -/
@[fsym] theorem vindex_step {α : Type} {n : Nat} (a : Vector α n) (i : BitVec 64) (h : i.toNat < n) :
    FTotalTriple P (StateT.lift (Zig.vindex a i) : MemM α) (fun r => ⟪r = a[i.toNat]⟫ ⋆ P) := by
  unfold Zig.vindex; rw [dif_pos h]
  exact (FTotalTriple.ret (Q := fun r => ⟪r = a[i.toNat]⟫ ⋆ P) a[i.toNat]).pre
    fun _ hp => sep_lift.mpr ⟨rfl, hp⟩

/-- **Pointer `==`** of two pointers without a block: their offsets are their addresses. -/
@[fsym] theorem ptrEqAddr_raw {p q : Ptr} (hp : p.block = none) (hq : q.block = none) :
    FTotalTriple P (ptrEqAddr p q) (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ P) :=
  FTotalTriple.of_read fun _ _ _ _ _ _ => by simp [ptrEqAddr, ptrAddr, hp, hq, zig_unfold]

-- The size of a literal byte array (a `Zig.storeBytes` of constant bytes), for the arithmetic
-- solver (widened and truncated words, sizes of values' bytes: `AutoArith.lean`).
attribute [fsym_arith] List.size_toArray List.length_cons List.length_nil

end Values

section Bytes

variable {p : Ptr} {a al : Nat} {bs bs' : Array Byte}

/-- **A store of raw bytes** `bs'` at the start of an owned region (`Zig.storeBytes`), aligned to
`al`, which divides the region's alignment. -/
@[fsym] theorem storeBytes_region (hn : 0 < bs'.size) (hk : bs'.size ≤ bs.size) (hal : a % al = 0) :
    FTotalTriple (up (Zig.region p a bs)) (Zig.storeBytes p al bs')
      (fun _ => up (Zig.region p a (writeBytes bs 0 bs'))) :=
  FTotalTriple.up_view' fun _ ⟨A, S, K, hA, hK, hbs⟩ => by
    have ha : (A + p.off.toNat + 0) % al = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hal) (Nat.dvd_of_mod_eq_zero hA))
    have t := FTotalTriple.storeBytes_bytesAt (q := p) (k := 0) (S := S) (bs := bs) hn
      (by omega) ha hK
    simp only [Int.natCast_zero, Ptr.add_zero] at t
    exact ⟨_, _, t, hbs, fun _ _ hb' => ⟨A, S, K, hA, hK, hb'⟩⟩

/-- **A store of a value of any encoding** at the start of an owned region: its bytes
(`Enc.encode`), whatever they are (a NaN lane's are undefined). No `LawfulEnc` is needed: the
bytes, not the value, are what the region holds afterwards. -/
@[fsym] theorem storeEnc_region {T : Type} [Enc T] (w : T) (hn : 0 < (Enc.encode w).size)
    (hk : (Enc.encode w).size ≤ bs.size) (hal : a % al = 0) :
    FTotalTriple (up (Zig.region p a bs)) (Zig.store al p w)
      (fun _ => up (Zig.region p a (writeBytes bs 0 (Enc.encode w)))) :=
  storeBytes_region hn hk hal

end Bytes

end Zig.Full.Auto
