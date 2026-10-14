import ZigLean.Mem.Lemmas
import ZigLean.Asm

/-!
# Frame rule of the asm effect contract (A01)

`ZigLean/Asm.lean` puts every memory effect of an accepted asm block in its generated wrapper:
loads of the read-write locations, then stores of the lvalue outputs. This module states what
such a wrapper may change (`Frame`): the bytes of its declared locations, nothing else. A block
keeps its liveness, kind, address, alignment and size; every byte outside the declared
`(block, offset, length)` locations keeps its value. The access log and the clocks (`recordAt`)
may grow.

The rules are compositional: `Frame.load` (a read changes no byte), `Frame.store` (a store
changes only its own bytes), `Frame.trans`. `Frame.of_load_run`/`Frame.of_store_run` invert any
successful `load`/`store` run, so a client can derive the frame of a whole wrapper from its run
alone, without computing it (`tests/roadmap/asm-effects/AsmEffects/Proofs.lean`).
-/

namespace Zig.Asm

/-- A written location: block, byte offset, byte length. -/
abbrev Loc := BlockId × Nat × Nat

/-- Byte `i` of block `b` is in the location. -/
def Loc.Covers (l : Loc) (b : BlockId) (i : Nat) : Prop := l.1 = b ∧ l.2.1 ≤ i ∧ i < l.2.1 + l.2.2

/-- What a block keeps under a frame: everything except its bytes' values. -/
def Block.shape (x : Block) : Bool × BlockKind × Nat × Nat × Nat :=
  (x.live, x.kind, x.addr, x.align, x.bytes.size)

/-- The byte `i` of block `b`, if both exist. -/
def byteAt (m : Mem) (b : BlockId) (i : Nat) : Option Byte := (m.blocks[b]?).bind (·.bytes[i]?)

/-- `after` differs from `before` only in bytes of `locs`: no block is added, removed, freed or
reshaped, and every other byte is unchanged. -/
def Frame (locs : List Loc) (before after : Mem) : Prop :=
  (∀ b : BlockId, (after.blocks[b]?).map Block.shape = (before.blocks[b]?).map Block.shape) ∧
    ∀ (b : BlockId) (i : Nat), (∀ l ∈ locs, ¬ l.Covers b i) → byteAt after b i = byteAt before b i

theorem Frame.refl (locs : List Loc) (m : Mem) : Frame locs m m :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

theorem Frame.trans {l₁ l₂ : List Loc} {m₁ m₂ m₃ : Mem} (h₁ : Frame l₁ m₁ m₂)
    (h₂ : Frame l₂ m₂ m₃) : Frame (l₁ ++ l₂) m₁ m₃ := by
  refine ⟨fun b => (h₂.1 b).trans (h₁.1 b), fun b i hi => ?_⟩
  rw [h₂.2 b i (fun l hl => hi l (List.mem_append_right _ hl)),
    h₁.2 b i (fun l hl => hi l (List.mem_append_left _ hl))]

/-- A frame over fewer locations is a frame over more. -/
theorem Frame.mono {l₁ l₂ : List Loc} {m m' : Mem} (h : Frame l₁ m m') (sub : ∀ l ∈ l₁, l ∈ l₂) :
    Frame l₂ m m' :=
  ⟨h.1, fun b i hi => h.2 b i (fun l hl => hi l (sub l hl))⟩

/-- Recording an access changes no block. -/
theorem Frame.recordAt (locs : List Loc) (m : Mem) (block off len : Nat) (kind : AccessKind) :
    Frame locs m (m.recordAt block off len kind) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

theorem Frame.readAt (locs : List Loc) (m : Mem) (blk : Block) (block off len : Nat)
    (kind : AccessKind) : Frame locs m (m.readAt blk block off len kind) :=
  Mem.readAt_cases (P := Frame locs m) (Frame.refl locs m) (Frame.recordAt locs m block off len kind)

theorem writeBytes_getElem?_outside (a : Array Byte) (o : Nat) (bs : Array Byte) (i : Nat)
    (h : o + bs.size ≤ a.size) (hi : i < o ∨ o + bs.size ≤ i) :
    (writeBytes a o bs)[i]? = a[i]? := by
  by_cases ha : i < a.size
  · have hs : i + 1 ≤ a.size := ha
    have hx := extract_writeBytes_disjoint a o bs i 1 h hs (by omega)
    have h1 : ((writeBytes a o bs).extract i (i + 1))[0]? = (writeBytes a o bs)[i]? := by
      rw [Array.getElem?_extract]; simp [writeBytes_size a o bs h, ha, Nat.min_eq_left hs]
    have h2 : (a.extract i (i + 1))[0]? = a[i]? := by
      rw [Array.getElem?_extract]; simp [ha, Nat.min_eq_left hs]
    rw [← h1, ← h2, hx]
  · have hw : (writeBytes a o bs).size = a.size := writeBytes_size a o bs h
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

/-- A write of `bs` at offset `o` of block `b` changes only those bytes. -/
theorem Frame.write {m : Mem} {b : BlockId} {blk : Block} {o : Nat} {bs : Array Byte}
    (hblk : m.blocks[b]? = some blk) (h : o + bs.size ≤ blk.bytes.size) :
    Frame [(b, o, bs.size)] m (m.write b blk o bs) := by
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have hget : m.blocks[b] = blk := (Array.getElem?_eq_some_iff.mp hblk).2
  refine ⟨fun c => ?_, fun c i hi => ?_⟩
  · by_cases hc : c = b
    · subst hc
      simp [Mem.write, hget, hlt, Block.shape, writeBytes_size _ _ _ h]
    · simp [Mem.write, Array.getElem?_setIfInBounds_ne (Ne.symm hc)]
  · by_cases hc : c = b
    · subst hc
      have hout : i < o ∨ o + bs.size ≤ i := by
        have := hi (c, o, bs.size) (by simp)
        simp only [Loc.Covers, true_and, not_and, Nat.not_lt] at this
        omega
      simp [byteAt, Mem.write, hget, hlt, writeBytes_getElem?_outside _ _ _ _ h hout]
    · simp [byteAt, Mem.write, Array.getElem?_setIfInBounds_ne (Ne.symm hc)]

/-- Any successful `load` changes no byte. -/
theorem Frame.of_load_run {α : Type} [Enc α] {m m' : Mem} {p : Ptr} {a : Nat} {v : α}
    (locs : List Loc) (h : (load α a p).run m = pure (v, m')) : Frame locs m m' := by
  obtain ⟨b, _, o, _, _, rfl⟩ := load_inv h
  exact Frame.readAt locs m _ b o _ .read

/-- Inverts a successful `storeBytes`: the access succeeds in a writable block, and the result
is the input with the write recorded, then the bytes written. -/
theorem storeBytes_inv {m m' : Mem} {p : Ptr} {a : Nat} {bs : Array Byte} {kind : AccessKind}
    (h : (storeBytes p a bs kind).run m = pure ((), m')) :
    ∃ b blk o, m.accessW p bs.size a = pure (b, blk, o) ∧
      m' = (m.recordAt b o bs.size kind).write b blk o bs := by
  unfold storeBytes recordAccess at h
  cases hacc : m.accessW p bs.size a with
  | none => simp [hacc, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      liftM, monadLift, MonadLift.monadLift, StateT.lift, ExceptT.bind, ExceptT.mk,
      ExceptT.bindCont, pure, ExceptT.pure] at h
  | some r =>
    cases r with
    | error e =>
      simp [hacc, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, liftM,
        monadLift, MonadLift.monadLift, StateT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        pure, ExceptT.pure] at h
      cases h
    | ok r =>
      obtain ⟨b, blk, o⟩ := r
      refine ⟨b, blk, o, rfl, ?_⟩
      cases hr : raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) b o bs.size
          kind with
      | some e =>
        simp [hacc, hr, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
          liftM, monadLift, MonadLift.monadLift, StateT.lift, ExceptT.bind, ExceptT.mk,
          ExceptT.bindCont, pure, ExceptT.pure, throw, throwThe, MonadExceptOf.throw] at h
        cases h
      | none =>
        simp [hacc, hr, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
          liftM, monadLift, MonadLift.monadLift, StateT.lift, ExceptT.bind, ExceptT.mk,
          ExceptT.bindCont, pure, ExceptT.pure, set, StateT.set, MonadStateOf.set] at h
        cases h
        rfl

/-- A write access that succeeds is an access that succeeds. -/
theorem access_of_accessW {m : Mem} {p : Ptr} {n a : Nat} {r : BlockId × Block × Nat}
    (h : m.accessW p n a = pure r) : m.access p n a = pure r := by
  unfold Mem.accessW at h
  cases hr : m.access p n a with
  | none => simp [hr, bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h
  | some x =>
    cases x with
    | error e =>
      simp [hr, bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h
      cases h
    | ok r' =>
      simp only [hr, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind_some] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at h
        cases h
      · exact h

/-- A write access that succeeds is not to a `const` global. -/
theorem kind_of_accessW {m : Mem} {p : Ptr} {n a : Nat} {r : BlockId × Block × Nat}
    (h : m.accessW p n a = pure r) : r.2.1.kind ≠ .constGlobal := by
  unfold Mem.accessW at h
  cases hr : m.access p n a with
  | none => simp [hr, bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h
  | some x =>
    cases x with
    | error e =>
      simp [hr, bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h
      cases h
    | ok r' =>
      simp only [hr, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind_some] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at h
        cases h
      · rename_i hk
        have h : some (Except.ok r') = some (Except.ok r) := h
        simp only [Option.some.injEq, Except.ok.injEq] at h
        exact h ▸ hk

/-- Any successful `store` at `p` changes only the `Enc.size α` bytes at `p`. -/
theorem Frame.of_store_run {α : Type} [Enc α] [LawfulEnc α] {m m' : Mem} {p : Ptr} {a : Nat}
    {v : α} (h : (store a p v).run m = pure ((), m')) :
    ∃ b, p.block = some b ∧ Frame [(b, p.off.toNat, Enc.size α)] m m' := by
  obtain ⟨b, blk, o, hacc, rfl⟩ := storeBytes_inv h
  have hacc' := access_of_accessW hacc
  obtain ⟨hb, hblk, -, h0, hn, -, rfl⟩ := access_eq hacc'
  refine ⟨b, hb, ?_⟩
  have hw := Frame.write (m := m.recordAt b p.off.toNat (Enc.encode v).size .write) (bs := Enc.encode v)
    (o := p.off.toNat) hblk (by omega)
  rw [LawfulEnc.size_encode v] at hw
  exact (Frame.recordAt [] m _ _ _ _).trans hw

/-- Inverts a successful bind in `MemM`. -/
theorem run_bind_ok {α β : Type} {x : MemM α} {f : α → MemM β} {m m' : Mem} {r : β}
    (h : (x >>= f).run m = pure (r, m')) :
    ∃ v m₁, x.run m = pure (v, m₁) ∧ (f v).run m₁ = pure (r, m') := by
  simp only [StateT.run_bind] at h
  generalize hx : x.run m = rx at h
  match rx, hx, h with
  | .mk none, _, h => simp [bind, ExceptT.bind, ExceptT.mk] at h; cases h
  | .mk (some (.error _)), _, h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] at h; cases h
  | .mk (some (.ok (v, m₁))), hx, h =>
    refine ⟨v, m₁, rfl, ?_⟩
    simpa [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] using h

/-! ### Memory regions and environment reads (A01, ASM-05, ASM-06) -/

/-- A region read changes no byte. -/
theorem Frame.of_readRegion_run {m m' : Mem} {p : Ptr} {n : Nat} {bs : Array Byte}
    (locs : List Loc) (h : (readRegion p n).run m = pure (bs, m')) : Frame locs m m' := by
  unfold readRegion at h
  split at h
  · have h : some (Except.ok (#[], m)) = some (Except.ok (bs, m')) := h
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact Frame.refl _ _
  · obtain ⟨b, _, o, -, -, -, rfl⟩ := loadBytes_inv h
    exact Frame.readAt locs m _ b o n .read

/-- A region write of `n > 0` bytes at `p` changes only those bytes. -/
theorem Frame.of_writeRegion_run {m m' : Mem} {p : Ptr} {n : Nat} {bs : Array Byte}
    (h : (writeRegion p n bs).run m = pure ((), m')) :
    ∃ b, (n = 0 → m' = m) ∧ (0 < n → p.block = some b) ∧ Frame [(b, p.off.toNat, n)] m m' := by
  unfold writeRegion at h
  split at h
  · have h : some (Except.ok ((), m)) = some (Except.ok ((), m')) := h
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨0, fun _ => rfl, fun hn => by omega, Frame.refl _ _⟩
  · obtain ⟨b, blk, o, hacc, rfl⟩ := storeBytes_inv h
    obtain ⟨hb, hblk, -, h0, hsz, -, rfl⟩ := access_eq (access_of_accessW hacc)
    have hw := Frame.write (m := m.recordAt b p.off.toNat (fitBytes n bs).size .write)
      (bs := fitBytes n bs) (o := p.off.toNat) hblk (by rw [fitBytes_size] at hsz ⊢; omega)
    rw [fitBytes_size] at hw
    exact ⟨b, fun hn => absurd hn (by assumption), fun _ => hb,
      (Frame.recordAt [] m _ _ _ _).trans hw⟩

/-- An environment read changes no byte. -/
theorem Frame.of_envWord_run {m m' : Mem} {w : Nat} {v : BitVec w} (locs : List Loc)
    (h : (envWord w).run m = pure (v, m')) : Frame locs m m' := by
  rw [envWord_run] at h
  have h : some (Except.ok (_, _)) = some (Except.ok (v, m')) := h
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩

end Zig.Asm
