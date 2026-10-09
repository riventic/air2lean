import Proofs.Pointers.Gen
import ZigLean.Mem.Lemmas
import ZigLean.Simp

/-!
# Proofs about `examples/pointers/pointers.zig`

`swap` exchanges two `u32` values that do not overlap, and `swap(p, p)` keeps the value.
`dueOf` returns a pointer into its argument, and `same` compares block and offset.
-/

open Pointers Zig

/-- Reading back a `u32` write at its own range. `Enc.size (BitVec 32)` folds to the literal `4`
only via `LawfulEnc.size_encode` (`Enc.encode`'s array size is not `rfl`-reducible on its own) —
this packages both rewrites once, for every `u32` field read-back below. -/
theorem decode_writeBytes32 (a : Array Byte) (o : Nat) (v : BitVec 32) (h : o + 4 ≤ a.size) :
    Enc.decode ((writeBytes a o (Enc.encode v)).extract o (o + 4)) = pure v := by
  have hsz : Enc.size (BitVec 32) = 4 := rfl
  have hx := extract_writeBytes a o (Enc.encode v) (by rw [LawfulEnc.size_encode v]; omega)
  rw [LawfulEnc.size_encode v, hsz] at hx
  simp only [hx, LawfulEnc.decode_encode]

/-- A `u32` write at `o` does not change a read of a disjoint `u32` range at `o'` in the same
array (`hd`: the two ranges do not overlap). -/
theorem extract_writeBytes32_disjoint (a : Array Byte) (o : Nat) (v : BitVec 32) (o' : Nat)
    (h : o + 4 ≤ a.size) (h' : o' + 4 ≤ a.size) (hd : o + 4 ≤ o' ∨ o' + 4 ≤ o) :
    (writeBytes a o (Enc.encode v)).extract o' (o' + 4) = a.extract o' (o' + 4) := by
  have hsz : Enc.size (BitVec 32) = 4 := rfl
  have hsize : (Enc.encode v).size = 4 := (LawfulEnc.size_encode v).trans hsz
  have h2 : o + (Enc.encode v).size ≤ a.size := by rw [hsize]; exact h
  have hd2 : o + (Enc.encode v).size ≤ o' ∨ o' + 4 ≤ o := by rw [hsize]; exact hd
  exact extract_writeBytes_disjoint a o (Enc.encode v) o' 4 h2 h' hd2

/-- `swap` as its four memory operations, each on the memory the previous one left (a read also
records a footprint entry with M22, so it is no longer a no-op on `Mem`). -/
theorem swap_run {m m₁ m₂ m₃ m₄ : Mem} {p q : Ptr} {x y : BitVec 32}
    (hx : (load (BitVec 32) 4 p).run m = pure (x, m₁))
    (hy : (load (BitVec 32) 4 q).run m₁ = pure (y, m₂))
    (h₁ : (store 4 p y).run m₂ = pure ((), m₃))
    (h₂ : (store 4 q x).run m₃ = pure ((), m₄)) :
    (swap p q).run m = pure ((), m₄) := by
  simp only [StateT.run] at hx hy h₁ h₂
  simp only [swap, StateT.run', zig_unfold, hx, hy, h₁, h₂]

set_option maxHeartbeats 800000 in
/-- `swap` exchanges two `u32` values whose bytes do not overlap. If `p = q`, the value stays
(forced by `hxv`/`hyv`: the same block/offset decodes to one value). `NoRace` for the two reads
(`hnr1`/`hnr2`) and the two writes (`hnr3`/`hnr4`) — the four ops `swap` performs — is an explicit
hypothesis, as everywhere in this file (`ZigLean/Mem/Lemmas.lean`'s `NoRace`); so is that neither
block is a `const` global (`hK`/`hK'`, a write to one throws `.illegal`). Four branches, each
composing several `Enc.size (BitVec 32)`-vs-`4` defeq checks, need more than the default budget. -/
theorem swap_spec (m : Mem) (p q : Ptr) (x y : BitVec 32) {b c : BlockId} {blk blk' : Block}
    {o o' : Nat}
    (hp : m.access p 4 4 = pure (b, blk, o)) (hq : m.access q 4 4 = pure (c, blk', o'))
    (hK : blk.kind ≠ .constGlobal) (hK' : blk'.kind ≠ .constGlobal)
    (hxv : Enc.decode (blk.bytes.extract o (o + 4)) = pure x)
    (hyv : Enc.decode (blk'.bytes.extract o' (o' + 4)) = pure y)
    (hd : p = q ∨ p.block ≠ q.block ∨ p.off + 4 ≤ q.off ∨ q.off + 4 ≤ p.off)
    (hnr1 : NoRace m b o 4 .read)
    (hnr2 : NoRace (m.recordAt b o 4 .read) c o' 4 .read)
    (hnr3 : NoRace ((m.recordAt b o 4 .read).recordAt c o' 4 .read) b o 4 .write)
    (hnr4 : NoRace (((m.recordAt b o 4 .read).recordAt c o' 4 .read).recordAt b o 4 .write)
      c o' 4 .write) :
    ∃ m' blkP blkQ, (swap p q).run m = pure ((), m') ∧
      m'.access p 4 4 = pure (b, blkP, o) ∧ Enc.decode (blkP.bytes.extract o (o + 4)) = pure y ∧
      m'.access q 4 4 = pure (c, blkQ, o') ∧ Enc.decode (blkQ.bytes.extract o' (o' + 4)) = pure x := by
  -- `omega` cannot see through `Enc.size (BitVec 32)` on its own; pin the numeral once so every
  -- bound proof below (`rw [LawfulEnc.size_encode _]; omega`) can pick it up from context.
  have hsz32 : Enc.size (BitVec 32) = 4 := rfl
  have hpb := (access_eq hp).1
  have hp0 := (access_eq hp).2.2.2.1
  have hpn := (access_eq hp).2.2.2.2.1
  have hpo2 := (access_eq hp).2.2.2.2.2.2
  have hqb := (access_eq hq).1
  have hq0 := (access_eq hq).2.2.2.1
  have hqn := (access_eq hq).2.2.2.2.1
  have hqo2 := (access_eq hq).2.2.2.2.2.2
  have hx := load_run hp hxv hnr1
  have hq₁ : (m.recordAt b o 4 .read).access q 4 4 = pure (c, blk', o') := access_recordAt.trans hq
  have hy := load_run hq₁ hyv hnr2
  have hp₂ : ((m.recordAt b o 4 .read).recordAt c o' 4 .read).access p 4 4 = pure (b, blk, o) :=
    access_recordAt.trans (access_recordAt.trans hp)
  have hq₂ : ((m.recordAt b o 4 .read).recordAt c o' 4 .read).access q 4 4 = pure (c, blk', o') :=
    access_recordAt.trans hq₁
  have h₁ := store_run y hp₂ hK hnr3
  have hyw : Enc.decode
      (({ blk with bytes := writeBytes blk.bytes o (Enc.encode y) } : Block).bytes.extract
        o (o + 4)) = pure y := decode_writeBytes32 blk.bytes o y (by omega)
  rcases hd with rfl | hd
  · -- One pointer: `hp`/`hq` are the same access, forcing `blk = blk'`/`o = o'`, and `hxv`/`hyv`
    -- the same decode, forcing `x = y`. Storing `x` (= `y`) at `q` (= `p`) restates `h₁`.
    obtain ⟨rfl, rfl, rfl⟩ : (b, blk, o) = (c, blk', o') := by
      have h := hp.symm.trans hq; injection h with h; injection h
    have hxy : x = y := by
      have h := hxv.symm.trans hyv; injection h with h; injection h
    subst hxy
    have hp₃ := access_store_same x hp₂ hp₂
    have h₂ := store_run x hp₃ hK hnr4
    have hbx : (writeBytes blk.bytes o (Enc.encode x)).size = blk.bytes.size :=
      writeBytes_size blk.bytes o (Enc.encode x) (by rw [LawfulEnc.size_encode x]; omega)
    exact ⟨_, _, _, swap_run hx hy h₁ h₂, access_store_same x hp₃ hp₃,
      decode_writeBytes32 (writeBytes blk.bytes o (Enc.encode x)) o x (by omega),
      access_store_same x hp₃ hp₃,
      decode_writeBytes32 (writeBytes blk.bytes o (Enc.encode x)) o x (by omega)⟩
  · -- Two distinct pointers, disjoint bytes: derive `b ≠ c ∨` offset-disjoint (`access_eq`).
    have hbc' : b ≠ c ∨ o + 4 ≤ o' ∨ o' + 4 ≤ o := by
      rcases hd with h | h | h
      · exact Or.inl (fun hbc => h (by rw [hpb, hqb, hbc]))
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    by_cases hbc : b = c
    · -- Same block, disjoint offsets: both writes land in block `b`, so every step uses
      -- `access_store_same`; the two writes never touch each other's range (`hd'`).
      subst hbc
      have hd' : o + 4 ≤ o' ∨ o' + 4 ≤ o := hbc'.resolve_left (· rfl)
      have hblk : blk = blk' := by
        have := (access_eq hp).2.1; have := (access_eq hq).2.1; simp_all
      subst hblk
      have hp₃ := access_store_same y hp₂ hp₂
      have hq₃ := access_store_same y hp₂ hq₂
      have h₂ := store_run x hq₃ hK hnr4
      refine ⟨_, _, _, swap_run hx hy h₁ h₂, access_store_same x hq₃ hp₃, ?_,
        access_store_same x hq₃ hq₃, ?_⟩
      · have hby : (writeBytes blk.bytes o (Enc.encode y)).size = blk.bytes.size :=
          writeBytes_size blk.bytes o (Enc.encode y) (by rw [LawfulEnc.size_encode y]; omega)
        rw [extract_writeBytes32_disjoint (writeBytes blk.bytes o (Enc.encode y)) o' x o
          (by omega) (by omega) hd'.symm]
        exact hyw
      · exact decode_writeBytes32 (writeBytes blk.bytes o (Enc.encode y)) o' x
          (by have hby : (writeBytes blk.bytes o (Enc.encode y)).size = blk.bytes.size :=
                writeBytes_size blk.bytes o (Enc.encode y) (by rw [LawfulEnc.size_encode y]; omega)
              omega)
    · -- Different blocks: each write is invisible to an access in the other block
      -- (`access_store_other`), so the two reads-back are independent.
      have hq₃ := access_store_other y hp₂ hq₂ hbc
      have hp₃ := access_store_same y hp₂ hp₂
      have h₂ := store_run x hq₃ hK' hnr4
      refine ⟨_, _, _, swap_run hx hy h₁ h₂, access_store_other x hq₃ hp₃ (Ne.symm hbc), hyw,
        access_store_same x hq₃ hq₃, decode_writeBytes32 blk'.bytes o' x (by omega)⟩

/-- `&j.due`: the offset of `due` in `Job` is 4 (the compiler's layout). -/
theorem dueOf_spec (j : Ptr) (m : Mem) : (dueOf j).run m = pure (j.add 4, m) := by
  simp [dueOf, zig_unfold]

/-- Pointer equality is equality of block and offset. -/
theorem same_spec (p q : Ptr) (m : Mem) : (same p q).run m = pure (decide (p = q), m) := by
  simp [same, zig_unfold]
  rfl

theorem maxPtr_none_left (b : Option Ptr) (m : Mem) : (maxPtr none b).run m = pure (b, m) := by
  simp [maxPtr, zig_unfold]

theorem maxPtr_none_right (p : Ptr) (m : Mem) : (maxPtr (some p) none).run m = pure (some p, m) := by
  simp [maxPtr, zig_unfold, Zig.optPayload]

/-- Two pointers: the one to the larger value; `p` if the values are equal. The second load
runs on `m₁`, the memory the first left, and records its own footprint entry in `m₂`. -/
theorem maxPtr_spec {m₁ m₂ : Mem} (p q : Ptr) (m : Mem) (x y : BitVec 32)
    (hx : (load (BitVec 32) 4 p).run m = pure (x, m₁))
    (hy : (load (BitVec 32) 4 q).run m₁ = pure (y, m₂)) :
    (maxPtr (some p) (some q)).run m = pure (some (if y.toNat ≤ x.toNat then p else q), m₂) := by
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hx hy
  by_cases h : y.toNat ≤ x.toNat <;>
    simp [maxPtr, zig_unfold, Zig.optPayload, hx, hy, h, Zig.ge, Zig.le, BitVec.ule]

/-- `delay` adds `d` to the job's `duration` (at offset 0). `NoRace` for the read (`hnr1`) and the
write (`hnr2`) is an explicit hypothesis, as in `swap_spec`. -/
theorem delay_spec (j : Ptr) (m : Mem) (x d : BitVec 32) {b : BlockId} {blk : Block} {o : Nat}
    (hj : m.access (j.add 0) 4 4 = pure (b, blk, o)) (hK : blk.kind ≠ .constGlobal)
    (hxv : Enc.decode (blk.bytes.extract o (o + 4)) = pure x) (h : x.toNat + d.toNat < 2 ^ 32)
    (hnr1 : NoRace m b o 4 .read) (hnr2 : NoRace (m.recordAt b o 4 .read) b o 4 .write) :
    ∃ m' blk', (delay j d).run m = pure ((), m') ∧
      m'.access (j.add 0) 4 4 = pure (b, blk', o) ∧
      Enc.decode (blk'.bytes.extract o (o + 4)) = pure (x + d) := by
  have hj0 := (access_eq hj).2.2.2.1
  have hjn := (access_eq hj).2.2.2.2.1
  have hjo2 := (access_eq hj).2.2.2.2.2.2
  have hx := load_run hj hxv hnr1
  have hsz : Enc.size (BitVec 32) = 4 := rfl
  rw [hsz] at hx
  have hj₁ : (m.recordAt b o 4 .read).access (j.add 0) 4 4 = pure (b, blk, o) :=
    access_recordAt.trans hj
  have hs := store_run (x + d) hj₁ hK hnr2
  refine ⟨_, _, ?_, access_store_same (x + d) hj₁ hj₁, decode_writeBytes32 blk.bytes o (x + d) ?_⟩
  · simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hx hs
    have hno : ¬ 2 ^ 32 ≤ x.toNat + d.toNat := by omega
    simp [delay, zig_unfold, hx, hs, Zig.add, BitVec.uaddOverflow, hno]
  · omega

/-- A sum that does not fit in `u32` is the safety panic `integerOverflow`. -/
theorem delay_overflow {m₁ : Mem} (j : Ptr) (m : Mem) (x d : BitVec 32)
    (hx : (load (BitVec 32) 4 (j.add 0)).run m = pure (x, m₁)) (h : 2 ^ 32 ≤ x.toNat + d.toNat) :
    (delay j d).run m = throw .overflow := by
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hx
  simp [delay, zig_unfold, hx, Zig.add, BitVec.uaddOverflow, h]

-- Concrete instantiations keep the load premises satisfiable as memory bookkeeping evolves.
example :
    let m := Mem.ofGlobals [(Enc.encode (1 : BitVec 32), 4, .global),
      (Enc.encode (2 : BitVec 32), 4, .global)]
    (maxPtr (some ⟨some 0, 0⟩) (some ⟨some 1, 0⟩)).run m =
      pure (some ⟨some 1, 0⟩, (m.recordAt 0 0 4 .read).recordAt 1 0 4 .read) := by
  dsimp only
  have hfull (v : BitVec 32) : (Enc.encode v).extract 0 4 = Enc.encode v := by
    rw [← show (Enc.encode v).size = 4 from LawfulEnc.size_encode v]
    exact Array.extract_size
  apply maxPtr_spec (m₁ := (Mem.ofGlobals [(Enc.encode (1 : BitVec 32), 4, .global),
    (Enc.encode (2 : BitVec 32), 4, .global)]).recordAt 0 0 4 .read) _ _ _ 1 2
  all_goals simp [load, loadBytes, recordAccess, Mem.ofGlobals, Mem.addGlobal, Mem.access,
    Mem.recordAt, alignUp, Enc.size, intSize, intAlign, LawfulEnc.size_encode,
    hfull, LawfulEnc.decode_encode, raceCheck, Mem.solo, raceAt, set, MonadStateOf.set, StateT.set, zig_unfold]

example :
    let m := Mem.ofGlobals [(Enc.encode (4294967295 : BitVec 32), 4, .global)]
    (delay ⟨some 0, 0⟩ 1).run m = throw .overflow := by
  dsimp only
  have hfull (v : BitVec 32) : (Enc.encode v).extract 0 4 = Enc.encode v := by
    rw [← show (Enc.encode v).size = 4 from LawfulEnc.size_encode v]
    exact Array.extract_size
  apply delay_overflow
    (m₁ := (Mem.ofGlobals [(Enc.encode (4294967295 : BitVec 32), 4, .global)]).recordAt 0 0 4 .read)
    _ _ 4294967295 1
  · simp [load, loadBytes, recordAccess, Mem.ofGlobals, Mem.addGlobal, Mem.access,
      Mem.recordAt, alignUp, Enc.size, intSize, intAlign, Ptr.add, LawfulEnc.size_encode,
      hfull, LawfulEnc.decode_encode, raceCheck, Mem.solo, raceAt, set, MonadStateOf.set, StateT.set, zig_unfold]
  · decide
