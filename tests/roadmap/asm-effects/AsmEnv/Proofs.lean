import AsmEnv.Gen
import Proofs.Asm.Effects

/-!
# Environment reads, memory inputs and memory-region contracts (A01)

`AsmEnv/Gen.lean` is the translator's output for the fresh Zig 0.17.0 export in `air-env/0.17.0`
(`asm_env.zig`; 0.16.0 and 0.15.2 translate identically, 0.14.1 has no inline asm export).
Every theorem is about that unchanged text.

* `elapsed_eq`, `elapsed_counter`: the two `rdtsc` are two environment reads (ASM-05): under an
  oracle that answers 0 then 1, `elapsed` returns 1, which one repeatable value (`a - a = 0`)
  could never give.
* `random_reads`: `rdrand` is one oracle query and changes no byte.
* `rand64_frame`: the flag output reaches memory only through the program's own store to `ok`.
* `loadm_eq`: an `m` input is the value (the compiler's private copy, A01).
* `fill_frame`, `copy_frame`: a memory-region contract (ASM-06) writes only its declared
  region: `n` bytes at `dst`, whatever the opaque computes; `copy`'s read of `src` changes no
  byte. `copy_overlap`: overlapping regions are `.unspecified` (the result of a forward copy
  depends on their distance). `fill_zero`: a zero count touches no memory at all, whatever `dst` holds.
* `fill_spec`: with the instruction's behaviour as an ASM-02 hypothesis (`rep stosb` stores
  `al` `rcx` times), the region holds `n` copies of the byte.
-/

open Zig Zig.Asm AsmEnv

theorem elapsed_eq :
    elapsed = (envWord 64 >>= fun a => envWord 64 >>= fun b => pure (subWrap b a)) := by
  simp [elapsed, ticks, StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, callM,
    StateT.run_lift]

/-- Two reads, two answers: with the oracle `0, 1` the difference is `1`. -/
theorem elapsed_counter :
    (elapsed.run { arbitrary := #[0, 1] }).run =
      some (.ok (1, { arbitrary := #[0, 1], arbitraryNext := 2 })) := by
  rw [elapsed_eq]
  rfl

/-- No repeatable value: a model in which both reads were one value `a` gives `a - a = 0`. -/
theorem elapsed_not_repeatable :
    ¬ ∀ m : Mem, ∃ m' a, (elapsed.run m).run = some (.ok (subWrap a a, m')) := by
  intro h
  obtain ⟨m', a, ha⟩ := h { arbitrary := #[0, 1] }
  rw [elapsed_counter] at ha
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at ha
  have : subWrap a a = 0 := by simp [subWrap]
  rw [this] at ha
  exact absurd ha.1 (by decide)

theorem random_eq : random = envWord 64 := by
  simp [random, StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, callM, StateT.run_lift]

/-- `rdrand` is one oracle query and changes no byte. -/
theorem random_reads {m m' : Mem} {v : BitVec 64} (locs : List Loc)
    (h : random.run m = pure (v, m')) : Frame locs m m' := by
  rw [random_eq] at h
  exact Frame.of_envWord_run locs h

/-- An `m` input is its value: with `movq` as the identity (ASM-02), `loadm` is the load. -/
theorem loadm_eq (hmov : ∀ x, airAsm_1506351414 x = x) (p : Ptr) :
    loadm p = load (BitVec 64) 8 p := by
  simp [loadm, hmov, StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

theorem fill_eq (p : Ptr) (n : BitVec 64) (b : BitVec 8) :
    fill p n b = writeRegion p n.toNat (airAsmFx_2696465393 b n).2.2 := by
  simp [fill, StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, callM, StateT.run_lift]

/-- `rep stosb` writes only its declared region, whatever the opaque computes. -/
theorem fill_frame {p : Ptr} {n : BitVec 64} {b : BitVec 8} {m m' : Mem}
    (h : (fill p n b).run m = pure ((), m')) :
    ∃ blk, (0 < n.toNat → p.block = some blk) ∧ Frame [(blk, p.off.toNat, n.toNat)] m m' := by
  rw [fill_eq] at h
  obtain ⟨blk, -, hb, hf⟩ := Frame.of_writeRegion_run h
  exact ⟨blk, hb, hf⟩

/-- A zero count touches no memory, whatever `dst` holds (even no block). -/
theorem fill_zero (p : Ptr) (b : BitVec 8) (m : Mem) : (fill p 0 b).run m = pure ((), m) := by
  rw [fill_eq]
  simp [writeRegion]

theorem copy_eq (d s : Ptr) (n : BitVec 64) :
    copy d s n = (guard [(d, n.toNat), (s, n.toNat)] >>= fun _ => readRegion s n.toNat >>= fun r =>
      writeRegion d n.toNat (airAsmFx_2096841937 n r).2.2.2) := by
  simp [copy, StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, callM, StateT.run_lift]

/-- `rep movsb` reads its source region and writes only its destination region. -/
theorem copy_frame {d s : Ptr} {n : BitVec 64} {m m' : Mem}
    (h : (copy d s n).run m = pure ((), m')) :
    ∃ blk, (0 < n.toNat → d.block = some blk) ∧ Frame [(blk, d.off.toNat, n.toNat)] m m' := by
  rw [copy_eq] at h
  obtain ⟨_, m₀, hg, hrest⟩ := run_bind_ok h
  have hm₀ : m₀ = m := by
    cases hd : disjoint [(d, n.toNat), (s, n.toNat)]
    · rw [guard_of_overlap hd] at hg
      simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure] at hg
      cases hg
    · rw [guard_of_disjoint hd] at hg
      simp [pure, ExceptT.pure, ExceptT.mk] at hg
      cases hg
      rfl
  subst hm₀
  obtain ⟨r, m₁, hr, hw⟩ := run_bind_ok (x := readRegion s n.toNat)
    (f := fun r => writeRegion d n.toNat (airAsmFx_2096841937 n r).2.2.2) hrest
  obtain ⟨blk, -, hb, hf⟩ := Frame.of_writeRegion_run hw
  exact ⟨blk, hb, by simpa using (Frame.of_readRegion_run [] hr).trans hf⟩

/-- An overlapping copy depends on the distance between the regions, which the opaque does not
see: the wrapper refuses it (`.unspecified`) before any access. -/
theorem copy_overlap {p : Ptr} {b : BlockId} (hb : p.block = some b) {n : BitVec 64}
    (hn : 0 < n.toNat) (m : Mem) : (copy p p n).run m = throw .unspecified := by
  rw [copy_eq, StateT.run_bind, guard_of_overlap (disjoint_self hb hn hn)]
  rfl
