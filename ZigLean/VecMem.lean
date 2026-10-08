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

/-- The packed encoding of a float vector round-trips its lanes' IEEE bit patterns. -/
@[instance] theorem Vec.lawfulEnc_float {fmt : FloatFmt} {n : Nat} : LawfulEnc (Vec (Float fmt) n) :=
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


/-! ## Lane pointers

A lane pointer into a bit-packed vector (`&v[i]`, `Zig.loadLane`/`Zig.storeLane` in
`ZigLean/Packed.lean`) is a bit-pointer into the vector's `n * w`-bit integer: host
`laneHost n w = ⌈n * w / 8⌉` bytes, bit offset `i * w`. On the bytes of a vector:

* `Vec.loadLane_vec`: a load through it reads lane `i`;
* `intBytes_setLane`, `Vec.storeLane_vec`: a store writes the host bytes of the vector with lane
  `i` replaced (`Vec.set`), and no other byte; every other lane keeps its bits
  (`laneOf_packBits_set_ne`);
* `Vec.load_storeLane_vec`: the whole vector loaded afterwards is `v.set i x`.
-/

/-- `N` with its `w` bits at bit `o` replaced by `x`. -/
def setBits (N o w x : Nat) : Nat :=
  N % 2 ^ o ||| (x % 2 ^ w) <<< o ||| (N >>> (o + w)) <<< (o + w)

theorem testBit_setBits (N o w x j : Nat) :
    (setBits N o w x).testBit j =
      if o ≤ j ∧ j < o + w then x.testBit (j - o) else N.testBit j := by
  simp only [setBits, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h1 : j < o
  · simp [h1, show ¬ o ≤ j by omega]
    intro h; omega
  · by_cases h2 : j < o + w
    · simp [h1, h2, show o ≤ j by omega, show j - o < w by omega]
      intro h; omega
    · have h3 : ¬ j - o < w := by omega
      simp [h1, h2, h3, show o + w + (j - (o + w)) = j by omega]
      intro _; omega

private theorem testBit_ge_of_lt {x n j : Nat} (h : x < 2 ^ n) (hj : n ≤ j) :
    x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hj))

theorem setBits_lt {N o w x M : Nat} (hN : N < 2 ^ M) (how : o + w ≤ M) :
    setBits N o w x < 2 ^ M := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_setBits]
  split
  · omega
  · exact testBit_ge_of_lt hN hj

/-- The value bits of a lane write into byte `k` (`Byte.setLane`'s `v`), whose `m` low bits are
defined. -/
private theorem setLane_val {N o w x k m lo hi : Nat} (hN : m = 8 ∨ N < 2 ^ (8 * k + m))
    (hm : m ≤ 8) (hlo : lo = Nat.min 8 (o - 8 * k)) (hhi : hi = Nat.min 8 (o + w - 8 * k))
    (hov : lo < hi) (hlom : lo ≤ m) (him : hi ≤ m) :
    ((N >>> (8 * k)) % 256 % 2 ^ m % 2 ^ lo |||
        ((x >>> (8 * k + lo - o)) % 2 ^ (hi - lo)) <<< lo |||
        (((N >>> (8 * k)) % 256 % 2 ^ m) >>> hi) <<< hi) =
      (setBits N o w x >>> (8 * k)) % 256 := by
  have hlo' : lo ≤ 8 ∧ lo ≤ o - 8 * k ∧ (lo = 8 ∨ lo = o - 8 * k) := by
    subst hlo; simp only [Nat.min_def]; split <;> omega
  have hhi' : hi ≤ 8 ∧ hi ≤ o + w - 8 * k ∧ (hi = 8 ∨ hi = o + w - 8 * k) := by
    subst hhi; simp only [Nat.min_def]; split <;> omega
  clear hlo hhi
  apply Nat.eq_of_testBit_eq
  intro t
  have h256 : (256 : Nat) = 2 ^ 8 := rfl
  simp only [h256, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, testBit_setBits]
  by_cases h1 : t < lo
  · have c : ¬ (o ≤ 8 * k + t ∧ 8 * k + t < o + w) := by omega
    simp [h1, c, show ¬ lo ≤ t by omega, show ¬ hi ≤ t by omega, show t < m by omega,
      show t < 8 by omega]
  · by_cases h2 : t < hi
    · have c : o ≤ 8 * k + t ∧ 8 * k + t < o + w := by omega
      simp [h1, c, show t < 8 by omega, show t - lo < hi - lo by omega,
        show 8 * k + lo - o + (t - lo) = 8 * k + t - o by omega, show lo ≤ t by omega,
        show ¬ hi ≤ t by omega]
    · have e : hi + (t - hi) = t := by omega
      have h5 : ¬ t - lo < hi - lo := by omega
      simp only [h1, h5, decide_false, decide_true, Bool.false_and, Bool.false_or,
        Bool.true_and, show t ≥ hi by omega]
      simp only [e, Bool.and_false, Bool.false_or]
      by_cases h4 : t < 8
      · have c : ¬ (o ≤ 8 * k + t ∧ 8 * k + t < o + w) := by omega
        by_cases h3 : t < m
        · simp [c, h3, h4]
        · simp [c, h3, h4,
            testBit_ge_of_lt (hN.resolve_left (by omega)) (show 8 * k + m ≤ 8 * k + t by omega)]
      · simp [h4, show ¬ t < m by omega]

/-- Outside a lane's bits, `setBits` keeps the bytes. -/
private theorem setBits_byte_disjoint {N o w x k : Nat}
    (h : o + w ≤ 8 * k ∨ 8 * k + 8 ≤ o ∨ w = 0) :
    (setBits N o w x >>> (8 * k)) % 256 = (N >>> (8 * k)) % 256 := by
  apply Nat.eq_of_testBit_eq
  intro t
  have h256 : (256 : Nat) = 2 ^ 8 := rfl
  simp only [h256, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, testBit_setBits]
  by_cases ht : t < 8
  · have : ¬ (o ≤ 8 * k + t ∧ 8 * k + t < o + w) := by omega
    simp [this]
  · simp [ht]

/-- A lane write into byte `k` of an integer's bytes. -/
private theorem setLane_intByte {M N k o w x : Nat} (hN : N < 2 ^ M) (hk : 8 * k < M)
    (how : o + w ≤ M) :
    (intByte M (BitVec.ofNat M N) k).setLane k o w x =
      intByte M (BitVec.ofNat M (setBits N o w x)) k := by
  have hN' := setBits_lt (x := x) hN how
  simp only [intByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hN']
  unfold Byte.setLane laneSpan
  generalize hlo : Nat.min 8 (o - 8 * k) = lo
  generalize hhi : Nat.min 8 (o + w - 8 * k) = hi
  have hlo' : lo = Min.min 8 (o - 8 * k) := hlo.symm
  have hhi' : hi = Min.min 8 (o + w - 8 * k) := hhi.symm
  have hb : (BitVec.ofNat 8 ((N >>> (8 * k)) % 256)).toNat = (N >>> (8 * k)) % 256 :=
    by simp [BitVec.toNat_ofNat]
  by_cases hd : hi ≤ lo
  · rw [setBits_byte_disjoint (by omega)]
    by_cases hr : M - 8 * k < 8 <;> simp [hr, hd]
  · by_cases hr : M - 8 * k < 8
    · have hm : Nat.min (M - 8 * k) 8 = M - 8 * k := by simp [Nat.min_def]; omega
      have hv := setLane_val (N := N) (x := x) (m := M - 8 * k)
        (Or.inr (by rwa [show 8 * k + (M - 8 * k) = M by omega])) (by omega) hlo.symm hhi.symm
        (by omega) (by omega) (by omega)
      simp only [hr, ite_true, Byte.lowBits, hm, hb, hd, decide_false, Bool.false_or]
      simp only [show ¬ M - 8 * k < lo by omega, decide_false, Bool.false_eq_true, ite_false]
      rw [hv, show Nat.max (M - 8 * k) hi = M - 8 * k by simp [Nat.max_def]; omega]
      simp [show M - 8 * k ≠ 8 by omega]
    · have hv := setLane_val (N := N) (x := x) (m := 8) (Or.inl rfl) (by omega) hlo.symm hhi.symm
        (by omega) (by omega) (by omega)
      simp only [hr, ite_false, Byte.lowBits, hb, hd, decide_false, Bool.false_or]
      simp only [show ¬ 8 < lo by omega, decide_false, Bool.false_eq_true, ite_false]
      rw [show (N >>> (8 * k)) % 256 = (N >>> (8 * k)) % 256 % 2 ^ 8 by omega, hv,
        show Nat.max 8 hi = 8 by simp [Nat.max_def]; omega]
      simp

/-- A lane write into the bytes of an integer: the bytes of the integer with the lane's bits
replaced. -/
theorem intBytes_setLane {M : Nat} (v : BitVec M) {o w : Nat} (x : Nat) (how : o + w ≤ M) :
    (intBytes v).mapIdx (fun k b => b.setLane k o w x) =
      intBytes (BitVec.ofNat M (setBits v.toNat o w x)) := by
  apply Array.ext
  · simp [intBytes]
  · intro k h1 h2
    simp only [Array.size_mapIdx, intBytes, Array.size_map, Array.size_range] at h1 h2
    have := setLane_intByte (N := v.toNat) (k := k) (o := o) (x := x) v.isLt (by omega) how
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    simpa [Array.getElem_mapIdx, intBytes, intByte] using this

private theorem lowBits_intByte {m : Nat} (v : BitVec m) (i : Nat) :
    (intByte m v i).lowBits.2 = (v.toNat >>> (8 * i)) % 256 := by
  have hv := v.isLt
  have hle : 2 ^ m ≤ 2 ^ (m - 8 * i) * 2 ^ (8 * i) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : v.toNat >>> (8 * i) < 2 ^ (m - 8 * i) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    exact Nat.lt_of_lt_of_le hv hle
  unfold intByte Byte.lowBits
  by_cases h8 : m - 8 * i < 8
  · have hm : Nat.min (m - 8 * i) 8 = m - 8 * i := by simp [Nat.min_def]; omega
    have hp : 2 ^ (m - 8 * i) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    have h256 : v.toNat >>> (8 * i) < 256 := Nat.lt_of_lt_of_le hlt hp
    simp [h8, hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h256, Nat.mod_eq_of_lt hlt]
  · simp [h8]

private theorem hostVal_foldr {m : Nat} (v : BitVec m) (s d : Nat) (hk : s + d = (m + 7) / 8) :
    ((List.range' s d).map (intByte m v)).foldr (fun b acc => b.lowBits.2 + 256 * acc) 0 =
      v.toNat >>> (8 * s) := by
  have hv := v.isLt
  induction d generalizing s with
  | zero =>
    simp only [List.range'_zero, List.map_nil, List.foldr_nil]
    symm
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
    exact Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))
  | succ d ih =>
    simp only [List.range'_succ, List.map_cons, List.foldr_cons]
    rw [ih (s + 1) (by omega), lowBits_intByte, show 8 * (s + 1) = 8 * s + 8 by omega,
      Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (v.toNat >>> (8 * s)) 8]
    exact Nat.mod_add_div _ _

/-- The host bytes of an integer read back as the integer. -/
theorem hostVal_intBytes {m : Nat} (v : BitVec m) : hostVal (intBytes v) = v.toNat := by
  unfold hostVal
  rw [intBytes_toList, List.range_eq_range', hostVal_foldr v 0 _ (by omega)]
  simp

/-- Every bit of an integer's bytes is defined. -/
theorem laneDefined_intBytes {m : Nat} (v : BitVec m) {o w : Nat} (h : o + w ≤ m) :
    laneDefined (intBytes v) o w = true := by
  unfold laneDefined
  rw [List.all_eq_true]
  intro k hk
  simp only [List.mem_range] at hk
  rw [getElem!_pos (intBytes v) k hk]
  simp only [intBytes, Array.getElem_map, Array.getElem_range, laneSpan, Byte.lowBits]
  by_cases h8 : m - 8 * k < 8
  · simp only [h8, ite_true, Nat.min_def]
    split <;> split <;> split <;> simp <;> omega
  · simp only [h8, ite_false, Nat.min_def]
    split <;> split <;> simp <;> omega

/-- A lane write in the packed integer of a list of lanes is `setBits` of the lane's bits. -/
theorem packLanes_set {w : Nat} (l : List (BitVec w)) (i : Nat) (hi : i < l.length)
    (x : BitVec w) : packLanes (l.set i x) = setBits (packLanes l) (i * w) w x.toNat := by
  have e : (i + 1) * w = i * w + w := Nat.succ_mul i w
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_setBits]
  split
  · rename_i hj
    have hl := laneOf_packLanes (l.set i x) i (by simpa using hi)
    simp only [List.getElem_set_self] at hl
    have := congrArg (fun b : BitVec w => b.toNat.testBit (j - i * w)) hl
    simp only [laneOf, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      show i * w + (j - i * w) = j by omega, show j - i * w < w by omega, decide_true,
      Bool.true_and] at this
    exact this
  · rename_i hj
    by_cases hlt : j < i * w
    · have := congrArg (fun n => n.testBit j) (packLanes_set_mod l i x)
      simpa [Nat.testBit_mod_two_pow, hlt] using this
    · have := congrArg (fun n => n.testBit (j - (i + 1) * w)) (packLanes_set_shiftRight l i x)
      simp only [Nat.testBit_shiftRight, e, show i * w + w + (j - (i * w + w)) = j by omega] at this
      exact this

/-- The packed integer of a vector after a lane write. -/
theorem Vec.packBits_set {α : Type} {n w : Nat} (toBits : α → BitVec w) (v : Vec α n)
    (i : Fin n) (x : α) : ((v.set i x).packBits w toBits).toNat =
      setBits (v.packBits w toBits).toNat (i * w) w (toBits x).toNat := by
  rw [Vec.packBits_toNat, Vec.packBits_toNat, ← packLanes_set _ _ (by simp)]
  simp [Vec.set, Vector.toList_set, List.map_set]

/-- The host of a lane pointer into `@Vector(n, T)`, `@bitSizeOf(T) = w`: the bytes of the
vector's integer (`Air2Lean/Air/Normalize.lean`'s `lanePtrLayout`). -/
abbrev laneHost (n w : Nat) : Nat := (n * w + 7) / 8

private theorem lane_end {n w : Nat} (i : Fin n) : i * w + w ≤ n * w := by
  have := Nat.mul_le_mul_right w (show i.val + 1 ≤ n from i.isLt)
  rwa [Nat.succ_mul] at this

private theorem size_intBytes {m : Nat} (v : BitVec m) : (intBytes v).size = (m + 7) / 8 := by
  simp [intBytes]

/-- The host bytes of a vector in memory: the first `laneHost n w` bytes of its image. -/
theorem Vec.host_of_encode {α : Type} {n w : Nat} (toBits : α → BitVec w)
    (ofBits : BitVec w → α) (v : Vec α n) {bs : Array Byte} {o : Nat}
    (h : bs.extract o (o + packedVecLayout n w) = (Vec.packedEnc n w toBits ofBits).encode v) :
    bs.extract o (o + laneHost n w) = intBytes (v.packBits w toBits) := by
  have hh := congrArg (fun a : Array Byte => a.extract 0 (laneHost n w)) h
  have hle : laneHost n w ≤ packedVecLayout n w := le_ceilPow2 _
  simp only [Array.extract_extract, Nat.add_zero,
    show Min.min (o + laneHost n w) (o + packedVecLayout n w) = o + laneHost n w by omega] at hh
  rw [hh]
  show (padTo _ _).extract 0 _ = _
  rw [show laneHost n w = (intBytes (v.packBits w toBits)).size from (size_intBytes _).symm,
    extract_padTo]

/-- A load through the lane pointer `&v[i]` reads lane `i` of the vector whose bytes are at its
host (`Zig.loadLane`). Only the host bytes are read. -/
theorem Vec.loadLane_vec {α : Type} {n w : Nat} [Packed α w] (v : Vec α n) (i : Fin n)
    (hvalid : Packed.valid (α := α) (Packed.toBits v.lanes[i]) = true)
    {m : Mem} {p : Ptr} {a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p (laneHost n w) a = pure (b, blk, o))
    (hv : blk.bytes.extract o (o + laneHost n w) = intBytes (v.packBits w Packed.toBits))
    (hr : NoRace m b o (laneHost n w) .read) :
    (loadLane α (laneHost n w) a (i * w) p).run m =
      pure (Packed.ofBits (Packed.toBits v.lanes[i]), m.recordAt b o (laneHost n w) .read) := by
  have hlane : BitVec.ofNat w ((v.packBits w Packed.toBits).toNat >>> (i * w)) =
      Packed.toBits v.lanes[i] := by
    rw [Vec.packBits_toNat]
    show laneOf w _ i = _
    rw [laneOf_packLanes _ _ (by simp)]
    simp
  have hvalid' : Packed.valid (α := α) (Packed.toBits v.lanes[(i : Nat)]) = true := hvalid
  simp only [loadLane, StateT.run_bind, loadBytes_run h hr]
  simp [hv, hvalid', laneDefined_intBytes _ (lane_end i), hostVal_intBytes, hlane, Packed.ofBits?,
    pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, StateT.run,
    liftM, monadLift, MonadLift.monadLift, StateT.lift]

/-- A store through the lane pointer `&v[i]` (`Zig.storeLane`) writes the host bytes of the vector
with lane `i` replaced, and no other byte. -/
theorem Vec.storeLane_vec {α : Type} {n w : Nat} [Packed α w] (v : Vec α n) (i : Fin n) (x : α)
    {m : Mem} {p : Ptr} {a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p (laneHost n w) a = pure (b, blk, o))
    (hv : blk.bytes.extract o (o + laneHost n w) = intBytes (v.packBits w Packed.toBits))
    (hK : blk.kind ≠ .constGlobal)
    (hr : NoRace m b o (laneHost n w) .read)
    (hw : NoRace (m.recordAt b o (laneHost n w) .read) b o (laneHost n w) .write) :
    (Zig.storeLane (laneHost n w) a (i * w) p x).run m =
      pure ((), ((m.recordAt b o (laneHost n w) .read).recordAt b o (laneHost n w) .write).write
        b blk o (intBytes ((v.set i x).packBits w Packed.toBits))) := by
  have hbs : (blk.bytes.extract o (o + laneHost n w)).mapIdx
      (fun k c => c.setLane k (i * w) w (Packed.toBits x).toNat) =
        intBytes ((v.set i x).packBits w Packed.toBits) := by
    rw [hv, intBytes_setLane _ _ (lane_end i)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [Vec.packBits_set, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (setBits_lt (BitVec.isLt _) (lane_end i))
  have hsize : (intBytes ((v.set i x).packBits w Packed.toBits)).size = laneHost n w :=
    size_intBytes _
  have hst := storeBytes_run (m := m.recordAt b o (laneHost n w) .read) (p := p) (a := a)
    (bs := intBytes ((v.set i x).packBits w Packed.toBits)) (kind := .write)
    (by rw [hsize]; exact access_recordAt.trans h) hK (by rwa [hsize])
  rw [hsize] at hst
  rw [Zig.storeLane, StateT.run_bind, loadBytes_run h hr, pure_bind]
  dsimp only
  rw [hbs]
  exact hst

/-- `intOfBytes` reads only its first `⌈n / 8⌉` bytes. -/
theorem intOfBytes_congr {n : Nat} {bs bs' : Array Byte}
    (h : bs.extract 0 ((n + 7) / 8) = bs'.extract 0 ((n + 7) / 8)) :
    intOfBytes n bs = intOfBytes n bs' := by
  unfold intOfBytes; rw [h]

/-- The bit-packed decode of bytes that start with the host bytes of `v` is `v`: the padding is
not read. -/
theorem Vec.packedEnc_decode {α : Type} {n w : Nat} (toBits : α → BitVec w)
    (ofBits : BitVec w → α) (hround : ∀ y, ofBits (toBits y) = y) (v : Vec α n)
    {bs : Array Byte}
    (h : bs.extract 0 (laneHost n w) = intBytes (v.packBits w toBits)) :
    (Vec.packedEnc n w toBits ofBits).decode bs = pure v := by
  simp only [Enc.decode, intOfBytes_of_extract (v.packBits w toBits) h, bind, ExceptT.bind,
    pure, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, Option.bind_some]
  congr
  rcases v with ⟨lanes⟩
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Vec.packBits_toNat]
  rw [laneOf_packLanes _ _ (by simpa using hi)]
  simp [hround]

/-- After a lane store, a load of the whole vector (`Zig.load`, as `v` after `v[i] = x`) reads
`v.set i x`: lane `i` is `x` and every other lane is `v`'s (`Vec.set_lane_ne`). Only the host
bytes are decoded; the vector's padding bytes are not read. -/
theorem Vec.load_storeLane_vec {α : Type} {n w : Nat} [Packed α w]
    (hround : ∀ y : α, Packed.ofBits (Packed.toBits y) = y) (v : Vec α n) (i : Fin n) (x : α)
    {m : Mem} {p : Ptr} {a a' : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p (laneHost n w) a = pure (b, blk, o))
    (h' : m.access p (packedVecLayout n w) a' = pure (b, blk, o))
    (hr : NoRace (((m.recordAt b o (laneHost n w) .read).recordAt b o (laneHost n w) .write).write
      b blk o (intBytes ((v.set i x).packBits w Packed.toBits))) b o (packedVecLayout n w) .read) :
    (@load (Vec α n) (Vec.packedEnc n w Packed.toBits Packed.ofBits) a' p).run
        (((m.recordAt b o (laneHost n w) .read).recordAt b o (laneHost n w) .write).write
          b blk o (intBytes ((v.set i x).packBits w Packed.toBits))) =
      pure (v.set i x, ((((m.recordAt b o (laneHost n w) .read).recordAt b o (laneHost n w)
        .write).write b blk o (intBytes ((v.set i x).packBits w Packed.toBits))).recordAt b o
        (packedVecLayout n w) .read)) := by
  have hsize : (intBytes ((v.set i x).packBits w Packed.toBits)).size = laneHost n w :=
    size_intBytes _
  have hhost : laneHost n w ≤ packedVecLayout n w := le_ceilPow2 _
  obtain ⟨-, -, -, h0, hn, -, ho⟩ := access_eq h'
  have hw : m.access p (intBytes ((v.set i x).packBits w Packed.toBits)).size a =
      pure (b, blk, o) := by rw [hsize]; exact h
  have ha := access_write_same
    (m := (m.recordAt b o (laneHost n w) .read).recordAt b o (laneHost n w) .write)
    (bs := intBytes ((v.set i x).packBits w Packed.toBits))
    (access_recordAt.trans (access_recordAt.trans hw))
    (access_recordAt.trans (access_recordAt.trans h'))
  have hx := extract_writeBytes blk.bytes o (intBytes ((v.set i x).packBits w Packed.toBits))
    (by rw [hsize]; omega)
  rw [hsize] at hx
  have hpre : ((writeBytes blk.bytes o (intBytes ((v.set i x).packBits w Packed.toBits))).extract o
      (o + packedVecLayout n w)).extract 0 (laneHost n w) =
        intBytes ((v.set i x).packBits w Packed.toBits) := by
    rw [Array.extract_extract, Nat.add_zero,
      show Min.min (o + laneHost n w) (o + packedVecLayout n w) = o + laneHost n w by omega, hx]
  exact @load_run (Vec α n) (Vec.packedEnc n w Packed.toBits Packed.ofBits) _ _ _ _ _ _ _ ha
    (Vec.packedEnc_decode _ _ hround _ hpre) hr

end Zig
