import ZigLean.Mem.Enc
import ZigLean.Simp

/-!
# Lemmas about memory

The run of `loadBytes`/`storeBytes` when the access succeeds, what a store does to other
accesses, and the `u32` round trip. `M17` builds separation logic on these.
-/

namespace Zig

attribute [zig_unfold] callM callR

/-- An access that succeeds: its block is live, the bytes are in the block, and the address is
aligned. -/
theorem access_eq {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p n a = pure (b, blk, o)) :
    p.block = some b ∧ m.blocks[b]? = some blk ∧ blk.live ∧ 0 ≤ p.off ∧
      p.off + n ≤ blk.bytes.size ∧ (blk.addr + p.off.toNat) % a = 0 ∧ o = p.off.toNat := by
  unfold Mem.access at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at h; cases h
  · rename_i b' hb
    split at h
    · simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at h; cases h
    · rename_i blk' hblk
      split at h
      · rename_i hc
        simp [pure, ExceptT.pure, ExceptT.mk] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hb, hblk, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, rfl⟩
      · simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at h
        cases h

theorem access_of {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block}
    (hb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hl : blk.live) (h0 : 0 ≤ p.off)
    (hn : p.off + n ≤ blk.bytes.size) (ha : (blk.addr + p.off.toNat) % a = 0) :
    m.access p n a = pure (b, blk, p.off.toNat) := by
  simp [Mem.access, hb, hblk, hl, h0, hn, ha]

theorem writeBytes_size (a : Array Byte) (o : Nat) (bs : Array Byte) (h : o + bs.size ≤ a.size) :
    (writeBytes a o bs).size = a.size := by
  simp [writeBytes]; omega

/-- A read of the written range gives the written bytes. -/
theorem extract_writeBytes (a : Array Byte) (o : Nat) (bs : Array Byte) (h : o + bs.size ≤ a.size) :
    (writeBytes a o bs).extract o (o + bs.size) = bs := by
  apply Array.ext
  · simp [writeBytes]; omega
  · intro i _ _
    have ho : Min.min o a.size = o := Nat.min_eq_left (by omega)
    simp [writeBytes, ho]

/-- A read of a range that does not overlap the written one is unchanged. -/
theorem extract_writeBytes_disjoint (a : Array Byte) (o : Nat) (bs : Array Byte) (o' n : Nat)
    (h : o + bs.size ≤ a.size) (h' : o' + n ≤ a.size) (hd : o + bs.size ≤ o' ∨ o' + n ≤ o) :
    (writeBytes a o bs).extract o' (o' + n) = a.extract o' (o' + n) := by
  apply Array.ext
  · simp [writeBytes]; omega
  · intro i h1 _
    have ho : Min.min o a.size = o := Nat.min_eq_left (by omega)
    simp only [Array.size_extract, writeBytes_size a o bs h] at h1
    simp only [writeBytes, Array.getElem_extract, Array.getElem_append, Array.size_append,
      Array.size_extract, ho]
    split
    · split
      · simp
      · omega
    · congr 1; omega

theorem loadBytes_run {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p n a = pure (b, blk, o)) :
    (loadBytes p n a).run m = pure (blk.bytes.extract o (o + n), m) := by
  simp [loadBytes, h, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure,
    StateT.pure, StateT.run, liftM, monadLift, MonadLift.monadLift, StateT.lift, ExceptT.pure,
    ExceptT.mk, ExceptT.bind, ExceptT.bindCont]

/-- The memory after writing `bs` at offset `o` of block `b` (`storeBytes`). -/
def Mem.write (m : Mem) (b : BlockId) (blk : Block) (o : Nat) (bs : Array Byte) : Mem :=
  { m with blocks := m.blocks.set! b { blk with bytes := writeBytes blk.bytes o bs } }

theorem storeBytes_run {m : Mem} {p : Ptr} {a : Nat} {bs : Array Byte} {b : BlockId}
    {blk : Block} {o : Nat} (h : m.access p bs.size a = pure (b, blk, o)) :
    (storeBytes p a bs).run m = pure ((), m.write b blk o bs) := by
  simp [storeBytes, Mem.write, h, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    MonadStateOf.set, bind, StateT.bind, pure, StateT.run, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont]

/-- After a write to block `b`, an access to `b` sees the new bytes, at the same offset. -/
theorem access_write_same {m : Mem} {p q : Ptr} {a n' a' : Nat} {bs : Array Byte} {b : BlockId}
    {blk : Block} {o o' : Nat} (hw : m.access p bs.size a = pure (b, blk, o))
    (hq : m.access q n' a' = pure (b, blk, o')) :
    (m.write b blk o bs).access q n' a' =
      pure (b, { blk with bytes := writeBytes blk.bytes o bs }, o') := by
  obtain ⟨hpb, hblk, hl, h0, hn, _, rfl⟩ := access_eq hw
  obtain ⟨hqb, -, -, h0', hn', ha', rfl⟩ := access_eq hq
  have hlt : b < m.blocks.size := by
    rcases Array.getElem?_eq_some_iff.mp hblk with ⟨h, _⟩; exact h
  apply access_of hqb
  · simp [Mem.write, hlt]
  · exact hl
  · exact h0'
  · rw [writeBytes_size _ _ _ (by omega)]; exact hn'
  · exact ha'

/-- A write to block `b` does not change an access to another block. -/
theorem access_write_other {m : Mem} {q : Ptr} {n' a' : Nat} {bs : Array Byte}
    {b c : BlockId} {blk blk' : Block} {o o' : Nat}
    (hq : m.access q n' a' = pure (c, blk', o')) (hbc : b ≠ c) :
    (m.write b blk o bs).access q n' a' = pure (c, blk', o') := by
  obtain ⟨hqb, hblk', hl, h0, hn, ha, rfl⟩ := access_eq hq
  exact access_of hqb (by simp [Mem.write, Array.getElem?_setIfInBounds_ne hbc, hblk']) hl h0 hn ha

/-! ## Typed access -/

/-- An encoding that reads back what it writes. -/
class LawfulEnc (α : Type) [Enc α] : Prop where
  size_encode : ∀ v : α, (Enc.encode v).size = Enc.size α
  decode_encode : ∀ v : α, Enc.decode (Enc.encode v) = pure v

theorem load_run {α : Type} [Enc α] {m : Mem} {p : Ptr} {a : Nat} {b : BlockId} {blk : Block}
    {o : Nat} {v : α} (h : m.access p (Enc.size α) a = pure (b, blk, o))
    (hv : Enc.decode (blk.bytes.extract o (o + Enc.size α)) = pure v) :
    (load α a p).run m = pure (v, m) := by
  simp only [load, StateT.run_bind, loadBytes_run h]
  simp [hv, pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, StateT.run,
    liftM, monadLift, MonadLift.monadLift, StateT.lift]

theorem store_run {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {p : Ptr} {a : Nat} {b : BlockId}
    {blk : Block} {o : Nat} (v : α) (h : m.access p (Enc.size α) a = pure (b, blk, o)) :
    (store a p v).run m = pure ((), m.write b blk o (Enc.encode v)) := by
  rw [← LawfulEnc.size_encode v] at h
  exact storeBytes_run h

/-- After a store at `p`, a load of the same type at `p` gives the stored value. -/
theorem load_store_same {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {p : Ptr} {a a' : Nat}
    {b : BlockId} {blk : Block} {o : Nat} (v : α)
    (h : m.access p (Enc.size α) a = pure (b, blk, o))
    (h' : m.access p (Enc.size α) a' = pure (b, blk, o)) :
    (load α a' p).run (m.write b blk o (Enc.encode v)) =
      pure (v, m.write b blk o (Enc.encode v)) := by
  have hw := h
  rw [← LawfulEnc.size_encode v] at hw
  have h0 := (access_eq h).2.2.2.1
  have hn := (access_eq h).2.2.2.2.1
  have ho := (access_eq h).2.2.2.2.2.2
  apply load_run (access_write_same hw h')
  have hx := extract_writeBytes blk.bytes o (Enc.encode v) (by rw [LawfulEnc.size_encode v]; omega)
  rw [LawfulEnc.size_encode v] at hx
  simp only [hx, LawfulEnc.decode_encode]

/-- A store at `p` does not change a load at `q` in another block, or at a range of the same
block that does not overlap. -/
theorem load_store_other {α β : Type} [Enc α] [LawfulEnc α] [Enc β] {m : Mem} {p q : Ptr}
    {a a' : Nat} {b c : BlockId} {blk blk' : Block} {o o' : Nat} (v : α) {w : β}
    (hp : m.access p (Enc.size α) a = pure (b, blk, o))
    (hq : m.access q (Enc.size β) a' = pure (c, blk', o'))
    (hd : b ≠ c ∨ o + Enc.size α ≤ o' ∨ o' + Enc.size β ≤ o)
    (hw : Enc.decode (blk'.bytes.extract o' (o' + Enc.size β)) = pure w) :
    (load β a' q).run (m.write b blk o (Enc.encode v)) =
      pure (w, m.write b blk o (Enc.encode v)) := by
  by_cases hbc : b = c
  · subst hbc
    have hd' : o + Enc.size α ≤ o' ∨ o' + Enc.size β ≤ o := hd.resolve_left (· rfl)
    have hblk : blk' = blk := by
      have := (access_eq hp).2.1; have := (access_eq hq).2.1; simp_all
    subst hblk
    have hpw := hp
    rw [← LawfulEnc.size_encode v] at hpw
    apply load_run (access_write_same hpw hq)
    have h0 := (access_eq hp).2.2.2.1
    have h0' := (access_eq hq).2.2.2.1
    have hn := (access_eq hp).2.2.2.2.1
    have hn' := (access_eq hq).2.2.2.2.1
    have ho := (access_eq hp).2.2.2.2.2.2
    have ho' := (access_eq hq).2.2.2.2.2.2
    rw [extract_writeBytes_disjoint _ _ _ _ _ (by rw [LawfulEnc.size_encode v]; omega) (by omega)
      (by rw [LawfulEnc.size_encode v]; omega)]
    exact hw
  · exact load_run (access_write_other hq hbc) hw

/-! ## Pointer-level form -/

/-- The memory after `storeBytes p _ bs` (when the access succeeds). -/
def Mem.writeAt (m : Mem) (p : Ptr) (bs : Array Byte) : Mem :=
  match p.block with
  | some b => match m.blocks[b]? with
    | some blk => m.write b blk p.off.toNat bs
    | none => m
  | none => m

theorem writeAt_eq {m : Mem} {p : Ptr} {n a : Nat} {bs : Array Byte} {b : BlockId} {blk : Block}
    {o : Nat} (h : m.access p n a = pure (b, blk, o)) : m.writeAt p bs = m.write b blk o bs := by
  obtain ⟨hb, hblk, -, -, -, -, rfl⟩ := access_eq h
  simp [Mem.writeAt, hb, hblk]

/-- A load that succeeds does not change the memory, and its access succeeds. -/
theorem load_inv {α : Type} [Enc α] {m m' : Mem} {p : Ptr} {a : Nat} {v : α}
    (h : (load α a p).run m = pure (v, m')) :
    m' = m ∧ ∃ b blk o, m.access p (Enc.size α) a = pure (b, blk, o) ∧
      Enc.decode (blk.bytes.extract o (o + Enc.size α)) = pure v := by
  simp only [load, loadBytes, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, ExceptT.bind, ExceptT.mk,
    pure, StateT.pure, ExceptT.pure, Option.bind_some, ExceptT.bindCont] at h
  generalize hacc : m.access p (Enc.size α) a = r at h
  match r, hacc, h with
  | none, _, h => simp at h
  | some (.error _), _, h =>
    simp only [ExceptT.bindCont, Option.bind_some] at h; cases h
  | some (.ok (b, blk, o)), hacc, h =>
    simp only [ExceptT.bindCont, Option.bind_some] at h
    generalize hd : (Enc.decode (blk.bytes.extract o (o + Enc.size α)) : Result α) = d at h
    match d, hd, h with
    | none, _, h => simp at h
    | some (.error _), _, h =>
      simp only [ExceptT.bindCont, Option.bind_some] at h; cases h
    | some (.ok w), hd, h =>
      simp only [ExceptT.bindCont, Option.bind_some] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, b, blk, o, rfl, hd⟩

theorem store_run' {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {p : Ptr} {a : Nat} {u : α}
    (hp : (load α a p).run m = pure (u, m)) (v : α) :
    (store a p v).run m = pure ((), m.writeAt p (Enc.encode v)) := by
  obtain ⟨-, b, blk, o, h, -⟩ := load_inv hp
  rw [store_run v h, writeAt_eq h]

/-- After a store at `p`, a load at `p` gives the stored value. -/
theorem load_writeAt_same {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {p : Ptr} {a : Nat} {u : α}
    (hp : (load α a p).run m = pure (u, m)) (v : α) :
    (load α a p).run (m.writeAt p (Enc.encode v)) = pure (v, m.writeAt p (Enc.encode v)) := by
  obtain ⟨-, b, blk, o, h, -⟩ := load_inv hp
  rw [writeAt_eq h]
  exact load_store_same v h h

/-- A store at `p` does not change a load at `q` whose bytes do not overlap. -/
theorem load_writeAt_other {α β : Type} [Enc α] [LawfulEnc α] [Enc β] {m : Mem} {p q : Ptr}
    {a a' : Nat} {u : α} {w : β} (hp : (load α a p).run m = pure (u, m))
    (hq : (load β a' q).run m = pure (w, m))
    (hd : p.block ≠ q.block ∨ p.off + Enc.size α ≤ q.off ∨ q.off + Enc.size β ≤ p.off) (v : α) :
    (load β a' q).run (m.writeAt p (Enc.encode v)) = pure (w, m.writeAt p (Enc.encode v)) := by
  obtain ⟨-, b, blk, o, h, -⟩ := load_inv hp
  obtain ⟨-, c, blk', o', h', hw⟩ := load_inv hq
  rw [writeAt_eq h]
  obtain ⟨hb, -, -, h0, -, -, rfl⟩ := access_eq h
  obtain ⟨hc, -, -, h0', -, -, rfl⟩ := access_eq h'
  apply load_store_other v h h' _ hw
  rcases hd with hd | hd | hd
  · left; intro hbc; subst hbc; exact hd (hb.trans hc.symm)
  · right; left; omega
  · right; right; omega

instance : LawfulEnc (BitVec 32) where
  size_encode v := by simp [Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign, alignUp]
  decode_encode v := by
    have hr : Array.range 4 = #[0, 1, 2, 3] := by decide
    simp [Enc.encode, Enc.decode, intSize, intAlign, alignUp, padTo, intBytes, intOfBytes, hr,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    congr 2
    apply BitVec.eq_of_toNat_eq
    have := v.isLt
    simp only [Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    omega

instance : LawfulEnc (BitVec 8) where
  size_encode v := by simp [Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign, alignUp]
  decode_encode v := by
    have hr : Array.range 1 = #[0] := by decide
    simp [Enc.encode, Enc.decode, intSize, intAlign, alignUp, padTo, intBytes, intOfBytes, hr,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    congr 2
    apply BitVec.eq_of_toNat_eq
    have := v.isLt
    simp only [BitVec.toNat_ofNat]
    omega

end Zig
