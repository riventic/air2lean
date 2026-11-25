import AsmEffects.Gen
import Proofs.Asm.Effects

/-!
# The asm effect contract of the generated wrappers (A01)

`AsmEffects/Gen.lean` is the translator's output for the hand-written AIR in `air/0.16.0`. Every
theorem here is about that unchanged generated text. Every block is a defined function over the
instruction model (`airIsaFx_<hash>`, A02 decision 1, premise ASM-07), so what an instruction
computes is proved (`incm_block`, `swapm_block`, ...), never assumed. The frame and alias
theorems follow from the wrapper alone (ASM-03 is the premise that the real instructions touch
memory only as that wrapper does).

* `incm_frame`, `setm_frame`, `swapm_frame`: any successful run changes only the bytes of the
  declared memory operands (`Zig.Asm.Frame`).
* `incm_spec`: the `+m` operand gets its old contents plus one.
* `swapm_alias`: the same pointer for both `+m` operands is `.unspecified`; `swapm_disjoint`: a
  successful run had disjoint operands.
* `addr_spec`, `incLocal_spec`: `+r`/`+m` on a local pass the old value and store the new one.
* `barrier_spec`: the registry-approved `"memory"` clobber block has no effect.
-/

open Zig Zig.Asm AsmEffects

/-! ## The blocks, from the instruction model (no hypothesis) -/

/-- `incl %[x]` on a `+m` operand. -/
theorem incm_block (x : BitVec 32) : airIsaFx_2840265087 x = x + 1 := by simp [zig_unfold]

/-- `incl %[y]` on a `+m` local. -/
theorem incLocal_block (x : BitVec 32) : airIsaFx_2360474586 x = x + 1 := by simp [zig_unfold]

/-- `movq %[v], %[x]` to an `=m` operand. -/
theorem setm_block (v : BitVec 64) : airIsaFx_2229968081 v = v := by simp [zig_unfold]

/-- `movl`/`xchgl`/`movl` through `eax`: the two `+m` operands are swapped. -/
theorem swapm_block (x y : BitVec 32) : airIsaFx_3102165980 x y = (y, x) := by simp [zig_unfold]

/-- `addq %[v], %[x]` on a `+r` operand. -/
theorem addr_block (v x : BitVec 64) : airIsaFx_2072205809 v x = x + v := by simp [zig_unfold]

theorem incm_eq (p : Ptr) :
    incm p = (load (BitVec 32) 4 p >>= fun x => store 4 p (x + 1)) := by
  simp [incm, incm_block, StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

theorem setm_eq (p : Ptr) (v : BitVec 64) : setm p v = store 8 p v := by
  simp [setm, setm_block, StateT.run'_eq, StateT.run_monadLift]

theorem swapm_eq (p q : Ptr) :
    swapm p q = (do
      guard [(p, 4), (q, 4)]
      let x ← load (BitVec 32) 4 p
      let y ← load (BitVec 32) 4 q
      store 4 p y
      store 4 q x) := by
  simp [swapm, swapm_block, StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

/-- `+m` (`incl`) writes exactly its operand: the 4 bytes at `p`. -/
theorem incm_frame {p : Ptr} {m m' : Mem} (h : (incm p).run m = pure ((), m')) :
    ∃ b, p.block = some b ∧ Frame [(b, p.off.toNat, 4)] m m' := by
  rw [incm_eq] at h
  obtain ⟨x, m₁, hl, hs⟩ := run_bind_ok h
  obtain ⟨b, hb, hf⟩ := Frame.of_store_run hs
  exact ⟨b, hb, (Frame.of_load_run [] hl).trans hf⟩

/-- `=m` (`movq`) writes exactly its operand: the 8 bytes at `p`. -/
theorem setm_frame {p : Ptr} {v : BitVec 64} {m m' : Mem} (h : (setm p v).run m = pure ((), m')) :
    ∃ b, p.block = some b ∧ Frame [(b, p.off.toNat, 8)] m m' := by
  rw [setm_eq] at h
  exact Frame.of_store_run h

/-- Two `+m` operands: a successful run changes the 4 bytes at `p` and the 4 bytes at `q`,
nothing else. -/
theorem swapm_frame {p q : Ptr} {m m' : Mem} (h : (swapm p q).run m = pure ((), m')) :
    ∃ b c, p.block = some b ∧ q.block = some c ∧
      Frame [(b, p.off.toNat, 4), (c, q.off.toNat, 4)] m m' := by
  rw [swapm_eq] at h
  obtain ⟨_, m₁, hg, h⟩ := run_bind_ok h
  obtain ⟨x, m₂, hx, h⟩ := run_bind_ok h
  obtain ⟨y, m₃, hy, h⟩ := run_bind_ok h
  obtain ⟨_, m₄, hp, hq⟩ := run_bind_ok h
  have hg' : m₁ = m := by
    cases hd : disjoint [(p, 4), (q, 4)]
    · rw [guard_of_overlap hd] at hg
      simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at hg
      cases hg
    · rw [guard_of_disjoint hd] at hg
      simp [pure, ExceptT.pure, ExceptT.mk] at hg
      cases hg
      rfl
  subst hg'
  obtain ⟨b, hb, fp⟩ := Frame.of_store_run hp
  obtain ⟨c, hc, fq⟩ := Frame.of_store_run hq
  exact ⟨b, c, hb, hc, ((Frame.of_load_run [] hx).trans ((Frame.of_load_run [] hy).trans
    (fp.trans fq)))⟩

/-- A successful `swapm` had disjoint operands: the alias guard ran first. -/
theorem swapm_disjoint {p q : Ptr} {m m' : Mem} (h : (swapm p q).run m = pure ((), m')) :
    disjoint [(p, 4), (q, 4)] = true := by
  rw [swapm_eq] at h
  obtain ⟨_, _, hg, _⟩ := run_bind_ok h
  cases hd : disjoint [(p, 4), (q, 4)]
  · rw [guard_of_overlap hd] at hg
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at hg
    cases hg
  · rfl

/-- The same pointer for both `+m` operands: the result depends on the store order, which the
contract does not fix, so the wrapper throws `.unspecified` before any access. -/
theorem swapm_alias {p : Ptr} {b : BlockId} (hb : p.block = some b) (m : Mem) :
    (swapm p p).run m = throw .unspecified := by
  rw [swapm_eq, StateT.run_bind, guard_of_overlap (disjoint_self hb (by decide) (by decide))]
  rfl

/-- The `+m` operand ends up holding its old contents plus one (`load_run`,
`store_run`, `load_store_same`). -/
theorem incm_spec (p : Ptr) (m : Mem) (x : BitVec 32) {b : BlockId} {blk : Block} {o : Nat}
    (hp : m.access p 4 4 = pure (b, blk, o)) (hK : blk.kind ≠ .constGlobal)
    (hx : Enc.decode (blk.bytes.extract o (o + 4)) = pure x)
    (hnr1 : NoRace m b o 4 .read) (hnr2 : NoRace (m.recordAt b o 4 .read) b o 4 .write) :
    ∃ m', (incm p).run m = pure ((), m') ∧
      ∃ blk', m'.access p 4 4 = pure (b, blk', o) ∧
        Enc.decode (blk'.bytes.extract o (o + 4)) = pure (x + 1) := by
  have hl := load_run (α := BitVec 32) hp hx hK hnr1
  have hp₁ : (m.recordAt b o 4 .read).access p 4 4 = pure (b, blk, o) := access_recordAt.trans hp
  have hs := store_run (x + 1) hp₁ hK hnr2
  refine ⟨_, ?_, _, access_store_same (x + 1) hp₁ hp₁, ?_⟩
  · rw [incm_eq, StateT.run_bind, hl]
    exact hs
  · have h0 := (access_eq hp).2.2.2.1
    have hn := (access_eq hp).2.2.2.2.1
    have ho := (access_eq hp).2.2.2.2.2.2
    have hw := extract_writeBytes blk.bytes o (Enc.encode (x + 1))
      (by rw [LawfulEnc.size_encode]; show o + 4 ≤ _; omega)
    rw [LawfulEnc.size_encode] at hw
    show Enc.decode ((writeBytes blk.bytes o _).extract o (o + Enc.size (BitVec 32))) = _
    rw [hw, LawfulEnc.decode_encode]

/-- `+r` on a local: the old value and the input reach the block, the new value is returned.
`addq` adds: from the instruction model, no hypothesis. -/
theorem addr_spec (x v : BitVec 64) : addr x v = pure (x + v) := by
  simp [addr, zig_unfold]

/-- `+m` on a local (`incl`), from the instruction model. -/
theorem incLocal_spec (x : BitVec 32) : incLocal x = pure (x + 1) := by
  simp [incLocal, zig_unfold]

/-- The registry's compiler barrier (`"memory"` clobber, empty template) has no effect. -/
theorem barrier_spec : barrier = pure () := by
  simp [barrier, zig_unfold]
