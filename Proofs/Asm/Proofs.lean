import Proofs.Asm.Gen

/-!
# Proofs about `examples/asm/asm.zig`

`bswap32`/`lzcnt64`/`popcnt64`/`divmod` each lower to one *defined* block function
(`airIsa_<hash>`: the decoded instructions over the x86_64 instruction model
`ZigLean/Isa/X86.lean`, A02 decision 1; `docs/generated-code.md` § Inline asm). No theorem here
has a hypothesis about an instruction: what the instruction computes follows from the model
(premise ASM-07), and `simp [zig_unfold]` runs the block.

Each wrapper is first shown equal to the Zig builtin with the same meaning (`@byteSwap`,
`@popCount`, `@clz`, `/` and `%`); the properties follow from the builtins' library lemmas.
-/

open Asm

/-- `bswap %[ret]` on a 32-bit register is `@byteSwap`. -/
theorem bswap32_eq (x : BitVec 32) : bswap32 x = pure (Zig.byteSwap x) := by
  simp [bswap32, zig_unfold]

/-- `popcnt` is `@popCount`. -/
theorem popcnt64_eq (x : BitVec 64) : popcnt64 x = pure x.cpop := by
  simp [popcnt64, zig_unfold]

/-- `lzcnt` is `@clz`. -/
theorem lzcnt64_eq (x : BitVec 64) : lzcnt64 x = pure x.clz := by
  simp [lzcnt64, zig_unfold]

/-- `bswap` is its own inverse: applying `bswap32` twice returns the input. Proved from the
instruction model; the earlier version assumed it (`hinv`). -/
theorem bswap32_involutive (x : BitVec 32) :
    (do let y ← bswap32 x; bswap32 y) = pure x := by
  simp [bswap32_eq, Zig.byteSwap_involution]

/-- `popcnt` never sets more bits than the register width. -/
theorem popcnt64_le_width (x : BitVec 64) : ∀ r, popcnt64 x = pure r → r.toNat ≤ 64 := by
  intro r hr
  rw [popcnt64_eq] at hr
  cases hr
  exact BitVec.toNat_cpop_le x

/-- `lzcnt` of an all-ones register is 0 (no leading zero bit to count). -/
theorem lzcnt64_allOnes : lzcnt64 (-1#64) = pure (0#64) := by
  rw [lzcnt64_eq, show (-1#64).clz = 0#64 by decide]

/-- `lzcnt(1) = 63` and `lzcnt(0) = 64` (the native results of
`tests/roadmap/asm-semantics/expected_x86_64.txt`), computed by the kernel. -/
theorem lzcnt64_one : lzcnt64 (1#64) = pure (63#64) := by
  rw [lzcnt64_eq, show (1#64).clz = 63#64 by decide]

theorem lzcnt64_zero : lzcnt64 (0#64) = pure (64#64) := by
  rw [lzcnt64_eq, show (0#64).clz = 64#64 by decide]

/-- `popcnt` of an all-ones register is 64. -/
theorem popcnt64_allOnes : popcnt64 (-1#64) = pure (64#64) := by
  rw [popcnt64_eq, show (-1#64).cpop = 64#64 by decide]

/-- The block of `divmod` faults exactly for a zero divisor: `xorl %edx, %edx` makes the
dividend `edx:eax = eax`, so the quotient always fits and #DE is the divisor being zero. This
was the allowlist entry's reviewed claim (`AsmFault.zeroInput 1`, premise ASM-04); it is now a
theorem about the instructions. -/
theorem divmod_fault (a b : BitVec 32) :
    airIsa_3653072158_fault a b = if b = 0 then some .trap else none := by
  simp [zig_unfold]

/-- `divl` with `edx = 0` gives the quotient and the remainder. -/
theorem divmod_block (a b : BitVec 32) : airIsa_3653072158 a b = (a / b, a % b) := by
  simp [zig_unfold]

/-- For a nonzero divisor, `divmod` puts the remainder in the high 32 bits and the quotient in
the low 32 bits (two outputs, the second one a store to the local `rem`). -/
theorem divmod_spec (a b : BitVec 32) (hb : b ≠ 0) :
    divmod a b = pure ((a % b).setWidth 64 <<< 32 ||| (a / b).setWidth 64) := by
  unfold divmod
  rw [divmod_fault, divmod_block]
  simp only [hb, ↓reduceIte]
  simp [zig_unfold, Zig.shl]

/-- `divl` with a zero divisor is #DE (SIGFPE natively): the model traps. -/
theorem divmod_zero_traps (a : BitVec 32) : divmod a 0 = throw .trap := by
  unfold divmod
  rw [divmod_fault]
  simp [zig_unfold]
