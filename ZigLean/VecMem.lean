import ZigLean.Vec
import ZigLean.Mem.Lemmas

/-!
# Bit-packed vectors in memory

Round trips and lane-write frames for the bit-packed vector encoding (`Vec.packedEnc`,
`ZigLean/Vec.lean`; `docs/vector-proofs.md` §Memory layout):

* `intOfBytes_intBytes`: the bytes of an integer of any width `m` read back as it
  (the `n * w`-bit integer that holds a vector's lanes is one);
* `laneOf_packLanes`: lane `i` of the packed integer is the `i`-th lane;
* `Vec.packedEnc_lawful`, and the `LawfulEnc` instances for `Vec (BitVec w) n` and
  `Vec (Float fmt) n`: a vector stored and loaded back is the same vector;
* `packLanes_set_mod`/`packLanes_set_shiftRight`: a lane write leaves every bit below and above
  the written lane's bits of the memory image unchanged; `Vec.set_lane_ne` and
  `Vec.storeLane_run`/`Vec.load_storeLane_ne` state that frame on lanes and through memory.
-/

namespace Zig

/-! ## Integers of any width -/

private theorem zipIdx_map_range' {β : Type} (g : Nat → β) (s d : Nat) :
    ((List.range' s d).map g).zipIdx s = (List.range' s d).map fun i => (g i, i) := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih => simp [List.range'_succ, List.zipIdx_cons, ih]

/-- Byte `i` of `intBytes v` (`ZigLean/Mem/Enc.lean`). -/
private def intByte (m : Nat) (v : BitVec m) (i : Nat) : Byte :=
  let x := (v.toNat >>> (8 * i)) % 256 |> BitVec.ofNat 8
  if m - 8 * i < 8 then .part (m - 8 * i) x else .int x

private theorem intBytes_toList {m : Nat} (v : BitVec m) :
    (intBytes v).toList = (List.range ((m + 7) / 8)).map (intByte m v) := by
  simp [intBytes, intByte, Array.toList_map]

private theorem byteBits_intByte {m : Nat} (v : BitVec m) (i : Nat) (hi : 8 * i < m) :
    byteBits m i false (intByte m v i) = some (BitVec.ofNat 8 ((v.toNat >>> (8 * i)) % 256)) := by
  have hv := v.isLt
  have hlt : v.toNat >>> (8 * i) < 2 ^ (m - 8 * i) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rwa [show m - 8 * i + 8 * i = m by omega]
  unfold intByte byteBits
  by_cases h8 : m - 8 * i < 8
  · simp only [h8]
    simp
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hlt
  · simp [h8]

private theorem foldr_intBytes {m : Nat} (v : BitVec m) (s d : Nat) (hk : s + d = (m + 7) / 8) :
    ((List.range' s d).map fun i => (intByte m v i, i)).foldr
        (fun (b, i) (acc : Result (BitVec m)) => do
          let hi ← acc
          match byteBits m i false b with
          | some x => pure (BitVec.ofNat m (x.toNat + 256 * hi.toNat))
          | none => throw .unspecified)
        (pure 0) =
      pure (BitVec.ofNat m (v.toNat >>> (8 * s))) := by
  have hv := v.isLt
  induction d generalizing s with
  | zero =>
    simp only [List.range'_zero, List.map_nil, List.foldr_nil]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have : v.toNat >>> (8 * s) = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
      exact Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))
    simp [this]
  | succ d ih =>
    simp only [List.range'_succ, List.map_cons, List.foldr_cons]
    rw [ih (s + 1) (by omega), byteBits_intByte v s (by omega)]
    simp only [bind, ExceptT.bind, pure, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      Option.bind_some]
    have hs : v.toNat >>> (8 * (s + 1)) < 2 ^ m :=
      Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hv
    have hsplit : v.toNat >>> (8 * s) % 256 + 256 * (v.toNat >>> (8 * (s + 1))) =
        v.toNat >>> (8 * s) := by
      rw [show 8 * (s + 1) = 8 * s + 8 by omega, Nat.shiftRight_add,
        Nat.shiftRight_eq_div_pow (v.toNat >>> (8 * s)) 8]
      exact Nat.mod_add_div _ _
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs, Nat.reducePow, Nat.mod_mod, hsplit]

/-- An integer of any width reads back from bytes that start with its `intBytes`. -/
theorem intOfBytes_of_extract {m : Nat} (v : BitVec m) {bs : Array Byte}
    (h : bs.extract 0 ((m + 7) / 8) = intBytes v) : intOfBytes m bs = pure v := by
  unfold intOfBytes
  rw [h, ← Array.foldr_toList, Array.toList_zipIdx, intBytes_toList, List.range_eq_range',
    zipIdx_map_range']
  exact (foldr_intBytes v 0 _ (by omega)).trans (by simp)

theorem intOfBytes_intBytes {m : Nat} (v : BitVec m) : intOfBytes m (intBytes v) = pure v :=
  intOfBytes_of_extract v (by simp [intBytes])

/-! ## Packed lanes -/

theorem packLanes_lt {w : Nat} (l : List (BitVec w)) : packLanes l < 2 ^ (w * l.length) := by
  induction l with
  | nil => simp [packLanes]
  | cons x xs ih =>
    have hx := x.isLt
    have h1 : packLanes xs + 1 ≤ 2 ^ (w * xs.length) := ih
    have h2 : 2 ^ w * (packLanes xs + 1) ≤ 2 ^ w * 2 ^ (w * xs.length) := Nat.mul_le_mul_left _ h1
    rw [List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * xs.length))]
    simp only [packLanes]
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega

theorem laneOf_packLanes {w : Nat} (l : List (BitVec w)) (i : Nat) (h : i < l.length) :
    laneOf w (packLanes l) i = l[i] := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    have hx := x.isLt
    cases i with
    | zero =>
      apply BitVec.eq_of_toNat_eq
      simp [laneOf, packLanes, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ i =>
      have hdiv : (x.toNat + 2 ^ w * packLanes xs) >>> w = packLanes xs := by
        rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt hx, Nat.zero_add]
      simp only [List.length_cons] at h
      simp only [laneOf, packLanes, List.getElem_cons_succ]
      rw [Nat.succ_mul, Nat.add_comm (i * w) w, Nat.shiftRight_add, hdiv]
      exact ih i (by omega)

theorem le_ceilPow2 (n : Nat) : n ≤ ceilPow2 n := by
  unfold ceilPow2
  split
  · omega
  · have := Nat.lt_log2_self (n := n - 1); omega

theorem Vec.packBits_toNat {α : Type} {n : Nat} (w : Nat) (toBits : α → BitVec w) (v : Vec α n) :
    (v.packBits w toBits).toNat = packLanes (v.lanes.toList.map toBits) := by
  have := packLanes_lt (v.lanes.toList.map toBits)
  simp only [List.length_map, Vector.length_toList] at this
  simp only [Vec.packBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by rwa [Nat.mul_comm])

private theorem extract_padTo (s : Nat) (a : Array Byte) : (padTo s a).extract 0 a.size = a := by
  simp [padTo]

/-- The bit-packed encoding round-trips whenever a lane's bits do (`ofBits ∘ toBits = id`). -/
theorem Vec.packedEnc_lawful {α : Type} (n w : Nat) (toBits : α → BitVec w)
    (ofBits : BitVec w → α) (h : ∀ x, ofBits (toBits x) = x) :
    @LawfulEnc (Vec α n) (Vec.packedEnc n w toBits ofBits) := by
  letI := Vec.packedEnc n w toBits ofBits
  refine ⟨fun v => ?_, fun v => ?_⟩
  · have := le_ceilPow2 ((n * w + 7) / 8)
    simp [Enc.encode, Enc.size, padTo, intBytes, packedVecLayout]
    omega
  · have hb : (intBytes (v.packBits w toBits)).size = (n * w + 7) / 8 := by simp [intBytes]
    have hx := intOfBytes_of_extract (v.packBits w toBits)
      (bs := padTo (packedVecLayout n w) (intBytes (v.packBits w toBits)))
      (by rw [← hb]; exact extract_padTo _ _)
    simp only [Enc.decode, Enc.encode, hx, bind, ExceptT.bind, pure, ExceptT.pure, ExceptT.mk,
      ExceptT.bindCont, Option.bind_some]
    congr
    rcases v with ⟨lanes⟩
    congr 1
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Vec.packBits_toNat]
    rw [laneOf_packLanes _ _ (by simpa using hi)]
    simp [h]

instance {w n : Nat} : LawfulEnc (Vec (BitVec w) n) :=
  Vec.packedEnc_lawful n w id id fun _ => rfl

instance {fmt : FloatFmt} {n : Nat} : LawfulEnc (Vec (Float fmt) n) :=
  Vec.packedEnc_lawful n fmt.width Float.bits Float.mk fun _ => rfl

/-! ## Lane writes -/

@[simp] theorem Vec.set_lane_self {α : Type} {n : Nat} (v : Vec α n) (i : Fin n) (x : α) :
    (v.set i x).lanes[i] = x := by
  simp [Vec.set]

/-- A lane write leaves every other lane unchanged. -/
theorem Vec.set_lane_ne {α : Type} {n : Nat} (v : Vec α n) (i : Fin n) (x : α) (j : Nat)
    (hj : j < n) (hne : (i : Nat) ≠ j) : (v.set i x).lanes[j] = v.lanes[j] := by
  simp [Vec.set, hne]

/-- A lane write leaves the bits below the written lane of the packed integer unchanged. -/
theorem packLanes_set_mod {w : Nat} (l : List (BitVec w)) (i : Nat) (x : BitVec w) :
    packLanes (l.set i x) % 2 ^ (i * w) = packLanes l % 2 ^ (i * w) := by
  induction l generalizing i with
  | nil => simp
  | cons y ys ih =>
    cases i with
    | zero => simp [Nat.mod_one]
    | succ i =>
      have hy := y.isLt
      have key : ∀ P : Nat, (y.toNat + 2 ^ w * P) % 2 ^ ((i + 1) * w) =
          y.toNat + 2 ^ w * (P % 2 ^ (i * w)) := by
        intro P
        rw [Nat.succ_mul, Nat.add_comm (i * w) w, Nat.pow_add, Nat.mod_mul,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hy, Nat.zero_add]
      simp only [List.set_cons_succ, packLanes, key, ih]

/-- A lane write leaves the bits above the written lane of the packed integer unchanged. -/
theorem packLanes_set_shiftRight {w : Nat} (l : List (BitVec w)) (i : Nat) (x : BitVec w) :
    packLanes (l.set i x) >>> ((i + 1) * w) = packLanes l >>> ((i + 1) * w) := by
  have hdiv : ∀ (y : BitVec w) (P : Nat), (y.toNat + 2 ^ w * P) >>> w = P := by
    intro y P
    rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt y.isLt, Nat.zero_add]
  induction l generalizing i with
  | nil => simp
  | cons y ys ih =>
    cases i with
    | zero => simp [packLanes, hdiv]
    | succ i =>
      simp only [List.set_cons_succ, packLanes]
      rw [Nat.succ_mul, Nat.add_comm _ w, Nat.shiftRight_add, Nat.shiftRight_add, hdiv, hdiv]
      exact ih i

/-- The memory image of a vector after a lane write: lane `j ≠ i` of the packed integer is
unchanged. -/
theorem laneOf_packBits_set_ne {α : Type} {n : Nat} (w : Nat) (toBits : α → BitVec w)
    (v : Vec α n) (i : Fin n) (x : α) (j : Nat) (hj : j < n) (hne : (i : Nat) ≠ j) :
    laneOf w ((v.set i x).packBits w toBits).toNat j = laneOf w (v.packBits w toBits).toNat j := by
  rw [Vec.packBits_toNat, Vec.packBits_toNat, laneOf_packLanes _ _ (by simpa using hj),
    laneOf_packLanes _ _ (by simpa using hj)]
  simp [Vec.set, hne]

/-- A write of one lane through memory (Zig's store through `&v[i]`; LLVM loads the vector,
`insertelement`s and stores it): read the vector, replace lane `i`, write it back. A model for
the frame theorems; the translator rejects a pointer to a lane of a vector that is not
byte-strided (`Check.lean`'s `CheckCtx.itemAccess`). -/
def Vec.storeLane {α : Type} {n : Nat} [Enc (Vec α n)] (align : Nat) (p : Ptr) (i : Fin n)
    (x : α) : MemM Unit := do
  let v ← load (Vec α n) align p
  store align p (v.set i x)

theorem Vec.storeLane_run {α : Type} {n : Nat} [Enc (Vec α n)] [LawfulEnc (Vec α n)] {m : Mem}
    {p : Ptr} {a : Nat} {b : BlockId} {blk : Block} {o : Nat} {v : Vec α n} (i : Fin n) (x : α)
    (h : m.access p (Enc.size (Vec α n)) a = pure (b, blk, o))
    (hv : Enc.decode (blk.bytes.extract o (o + Enc.size (Vec α n))) = pure v)
    (hK : blk.kind ≠ .constGlobal)
    (hr : NoRace m b o (Enc.size (Vec α n)) .read)
    (hw : NoRace (m.recordAt b o (Enc.size (Vec α n)) .read) b o (Enc.size (Vec α n)) .write) :
    (Vec.storeLane a p i x).run m =
      pure ((), ((m.recordAt b o (Enc.size (Vec α n)) .read).recordAt b o (Enc.size (Vec α n))
        .write).write b blk o (Enc.encode (v.set i x))) := by
  simp only [Vec.storeLane, StateT.run_bind, load_run h hv hr]
  exact store_run _ (access_recordAt.trans h) hK hw

/-- A lane write through memory, read back: the vector with lane `i` replaced, so every other
lane is the one that was in memory (`Vec.set_lane_ne`). -/
theorem Vec.load_storeLane {α : Type} {n : Nat} [Enc (Vec α n)] [LawfulEnc (Vec α n)] {m : Mem}
    {p : Ptr} {a : Nat} {b : BlockId} {blk : Block} {o : Nat} (v : Vec α n) (i : Fin n) (x : α)
    (h : m.access p (Enc.size (Vec α n)) a = pure (b, blk, o))
    (hr : NoRace (((m.recordAt b o (Enc.size (Vec α n)) .read).recordAt b o
      (Enc.size (Vec α n)) .write).write b blk o (Enc.encode (v.set i x))) b o
      (Enc.size (Vec α n)) .read) :
    (load (Vec α n) a p).run (((m.recordAt b o (Enc.size (Vec α n)) .read).recordAt b o
        (Enc.size (Vec α n)) .write).write b blk o (Enc.encode (v.set i x))) =
      pure (v.set i x, (((m.recordAt b o (Enc.size (Vec α n)) .read).recordAt b o
        (Enc.size (Vec α n)) .write).write b blk o (Enc.encode (v.set i x))).recordAt b o
        (Enc.size (Vec α n)) .read) :=
  load_store_same (v.set i x) (access_recordAt.trans (access_recordAt.trans h))
    (access_recordAt.trans (access_recordAt.trans h)) hr

end Zig
