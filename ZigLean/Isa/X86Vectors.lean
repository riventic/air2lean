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

/-! ### The footprint check rejects a wrong declaration

Each block below differs from an accepted one in one declared fact; `Block.check` names the
instruction and the location. -/

-- `divl` without the `xorl`: it reads `edx`, which no input and no instruction defines.
example : ({ divl with instrs := [.div .w32 (.vreg 3)] } : Block).check
    = some (.undefinedRead 0 rdx) := by decide
-- `edx` is neither an output nor a clobber.
example : ({ divl with outputs := [(rax, .w32)], early := [] } : Block).check
    = some (.undeclaredWrite 0 rdx) := by decide
-- The `edx` output is not early-clobber: the compiler may put the divisor in `edx`, and the
-- `xorl` would overwrite it before `divl` reads it.
example : ({ divl with early := [] } : Block).check = some (.staleRead 1 (.vreg 3)) := by decide
-- `bswap` of a 16-bit register has an undefined result.
example : ({ instrs := [.un .bswap .w16 (.vreg 0)], inputs := [(.vreg 0, .w16)],
             outputs := [(.vreg 0, .w16)] } : Block).check = some (.noEncoding 0) := by decide
-- `incl` on a memory operand of a 64-bit type.
example : ({ instrs := [.un .inc .w32 (.mem 0)], inputs := [(.mem 0, .w64)],
             outputs := [(.mem 0, .w64)] } : Block).check = some (.memWidth 0 (.mem 0)) := by decide
-- `addq` on 32-bit operands reads the undefined upper halves of their registers.
example : ({ instrs := [.bin .add .w64 (.loc (.vreg 1)) (.vreg 0)],
             inputs := [(.vreg 1, .w32), (.vreg 0, .w32)],
             outputs := [(.vreg 0, .w32)] } : Block).check
    = some (.undefinedRead 0 (.vreg 1)) := by decide
-- An output that no instruction writes; a 16-bit write does not define a 64-bit output, a
-- 32-bit write does (it zero-extends).
example : ({ instrs := [], inputs := [(.vreg 1, .w64)], outputs := [(.vreg 0, .w64)] } : Block).check
    = some (.outputUndefined 0) := by decide
example : ({ instrs := [.bin .mov .w16 (.loc (.vreg 1)) (.vreg 0)], inputs := [(.vreg 1, .w16)],
             outputs := [(.vreg 0, .w64)] } : Block).check = some (.outputUndefined 0) := by decide
example : ({ instrs := [.bin .mov .w32 (.loc (.vreg 1)) (.vreg 0)], inputs := [(.vreg 1, .w32)],
             outputs := [(.vreg 0, .w64)] } : Block).check = none := by decide
-- `movl %[a], %[r]; movl %[r], %[m]` (`=r`, `=m`, `r`): the compiler may put `r` in the register
-- that holds `m`'s address, so the store after the write to `r` may go elsewhere. With `=&r`
-- the block is accepted.
example : ({ instrs := [.bin .mov .w32 (.loc (.vreg 2)) (.vreg 0),
                        .bin .mov .w32 (.loc (.vreg 0)) (.mem 1)],
             inputs := [(.vreg 2, .w32)], outputs := [(.vreg 0, .w32), (.mem 1, .w32)] } : Block).check
    = some (.staleAddress 1 (.mem 1)) := by decide
example : ({ instrs := [.bin .mov .w32 (.loc (.vreg 2)) (.vreg 0),
                        .bin .mov .w32 (.loc (.vreg 0)) (.mem 1)],
             inputs := [(.vreg 2, .w32)], outputs := [(.vreg 0, .w32), (.mem 1, .w32)],
             early := [.vreg 0] } : Block).check = none := by decide
-- A clobbered register carries an operand.
example : ({ instrs := [], inputs := [(rax, .w32)], outputs := [], clobbers := [0] } : Block).check
    = some .declaration := by decide

end Zig.Isa.X86.Vectors
