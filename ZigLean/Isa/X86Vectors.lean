import ZigLean.Isa.X86

/-!
# x86_64 instruction model against recorded native results (A02, evidence for ASM-07)

Each `example` is one native observation, checked by the kernel against the model
(`ZigLean/Isa/X86.lean`), with no hypothesis:

* `tests/roadmap/asm-semantics/expected_x86_64.txt` (the probe of `check.sh`, Zig 0.17, x86_64
  Linux; run under Rosetta on the development host and on x86_64 CPUs in CI): `lzcnt`, `popcnt`,
  `bsr` and `divl`;
* `examples/asm/asm.zig`'s own tests (`bswap`, `popcnt`, `lzcnt`).

The differential test (`tests/diff`, `scripts/diff.sh asm`) compares the generated functions of
`examples/asm` with the native instructions on many more inputs; these vectors are the ones a
reader can check by hand.
-/

namespace Zig.Isa.X86.Vectors

/-- One two-operand count instruction `op %[x], %[ret]` at 64 bits. -/
def cnt (op : CntOp) : Block where
  instrs := [.cnt op .w64 (.vreg 1) (.vreg 0)]
  inputs := [(.vreg 1, .w64)]
  outputs := [(.vreg 0, .w64)]

/-- `xorl %edx, %edx; divl %[b]` with the dividend in `eax`: quotient in `eax`, remainder in
`edx`. -/
def divl : Block where
  instrs := [.bin .xor .w32 (.loc rdx) rdx, .div .w32 (.vreg 3)]
  inputs := [(rax, .w32), (.vreg 3, .w32)]
  outputs := [(rax, .w32), (rdx, .w32)]
  early := [rdx]

/-- `bswap %[ret]` at 32 bits. -/
def bswap32 : Block where
  instrs := [.un .bswap .w32 (.vreg 0)]
  inputs := [(.vreg 0, .w32)]
  outputs := [(.vreg 0, .w32)]

example : (cnt .lzcnt).check = none := by decide
example : divl.check = none := by decide
example : bswap32.check = none := by decide

-- expected_x86_64.txt: `x=… lzcnt=… popcnt=…`
example : (cnt .lzcnt).out [0x0000000000000000] 0 = 64 := by decide
example : (cnt .lzcnt).out [0x0000000000000001] 0 = 63 := by decide
example : (cnt .lzcnt).out [0x8000000000000000] 0 = 0 := by decide
example : (cnt .lzcnt).out [0xffffffffffffffff] 0 = 0 := by decide
example : (cnt .lzcnt).out [0x00f0000000000000] 0 = 8 := by decide
example : (cnt .popcnt).out [0x0000000000000000] 0 = 0 := by decide
example : (cnt .popcnt).out [0x0000000000000001] 0 = 1 := by decide
example : (cnt .popcnt).out [0x8000000000000000] 0 = 1 := by decide
example : (cnt .popcnt).out [0xffffffffffffffff] 0 = 64 := by decide
example : (cnt .popcnt).out [0x00f0000000000000] 0 = 4 := by decide

-- expected_x86_64.txt: `bsr(1)=0 bsr(2^63)=63`. `bsr` is not `lzcnt`: on a CPU without LZCNT
-- the `lzcnt` encoding runs as `bsr` (the reason for the CPU-feature check, ASM-09).
example : (cnt .bsr).out [1] 0 = 0 := by decide
example : (cnt .bsr).out [0x8000000000000000] 0 = 63 := by decide
example : (cnt .bsr).fault [1] = none := by decide
-- `bsr` of zero: the destination is undefined (Intel) or unchanged (AMD); the model chooses
-- neither.
example : (cnt .bsr).fault [0] = some .unspecified := by decide

-- expected_x86_64.txt: `divl 100/7={ 14, 2 } divl 0xffffffff/1={ 4294967295, 0 }`
example : (divl.out [100, 7] 0, divl.out [100, 7] 1) = (14, 2) := by decide
example : (divl.out [0xffffffff, 1] 0, divl.out [0xffffffff, 1] 1) = (4294967295, 0) := by decide
example : divl.fault [100, 7] = none := by decide
-- #DE (SIGFPE) for a zero divisor.
example : divl.fault [100, 0] = some .trap := by decide

-- examples/asm/asm.zig: `test "bswap32"`, `test "popcnt64"`, `test "lzcnt64"`.
example : bswap32.out [0x12345678] 0 = 0x78563412 := by decide
example : (cnt .popcnt).out [0b1011] 0 = 3 := by decide
example : (cnt .lzcnt).out [0x80000000] 0 = 32 := by decide

end Zig.Isa.X86.Vectors
