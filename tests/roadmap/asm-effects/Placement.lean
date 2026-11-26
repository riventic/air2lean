import ZigLean.Isa.X86Placement

/-!
# The footprint check's rules are needed (A02, ASM-07 item 4)

`Zig.Isa.X86.Block.check_placement` proves that a block which passes `Block.check` computes the
same under every admissible placement. Each mutant below is the check without one of its rules.
For each, the kernel checks a block that

* the check rejects with exactly that rule's violation (so the mutated check would accept it,
  and the theorem's proof would fail), and
* computes another value on the machine than in the model, under an admissible placement and an
  entry state that holds the inputs (so the mutated check would be unsound).

The mutants (`assurance/mutation-map.json`, A02):

- `"stale-read-unchecked"`: an input is read after a write to an output without `&`. The
  compiler may give both one register.
- `"stale-address-unchecked"`: a memory operand is accessed after a write to a register output
  without `&`. The compiler may hold the operand's address in that register.
- `"undefined-read-unchecked"`: a 64-bit read of a 32-bit input. The upper half of the register
  is whatever the caller left.
- `"undeclared-write-unchecked"`: a write to a register that is neither an output nor a clobber.
  The compiler may hold an input there.

The last example is the positive case: a block that passes the check under a placement that
shares one register between its input and its output.
-/

namespace AsmPlacement

open Zig.Isa.X86

/-- The machine state with `v` in the register `r` and 0 elsewhere. -/
def only (r : Fin 16) (v : BitVec 64) : State := fun l => if l = .reg r then v else 0

/-- The outputs of the placed block on the machine, from `p0`. -/
def machine (P : Placement) (b : Block) (p0 : State) (k : Nat) : Option (BitVec 64) :=
  (P.run p0 (b.instrs.map (Instr.place P.loc)) p0).map (P.out b · k)

/-! ## `"stale-read-unchecked"` -/

/-- `movq $0, %[ret]; addq %[x], %[ret]` with `[ret] "=r"` and `[x] "r"`. -/
def staleRead : Block where
  instrs := [.bin .mov .w64 (.imm 0) (.vreg 0), .bin .add .w64 (.loc (.vreg 1)) (.vreg 0)]
  inputs := [(.vreg 1, .w64)]
  outputs := [(.vreg 0, .w64)]

/-- Both operands in `rax`. -/
def shared : Placement := ⟨fun _ => 0, fun _ => []⟩

theorem staleRead_rejected : staleRead.check = some (.staleRead 1 (.vreg 1)) := by decide

theorem staleRead_admissible : shared.Admissible staleRead := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [staleRead, shared, Block.operandLocs, Block.inputLocs, Block.outputLocs, Placement.loc]

theorem staleRead_entry : shared.Entry staleRead [5] (only 0 5) := by
  simp [Placement.Entry, staleRead, shared, Placement.loc, only, initState, State.get]

/-- The model adds the input to 0; the machine adds the zeroed register to itself. -/
theorem staleRead_differs :
    staleRead.out [5] 0 = 5 ∧ machine shared staleRead (only 0 5) 0 = some 0 := by
  constructor <;> rfl

/-! ## `"stale-address-unchecked"` -/

/-- `movq %[x], %[ret]; movq %[ret], %[m]` with `[ret] "=r"`, `[m] "=m"` and `[x] "r"`. -/
def staleAddress : Block where
  instrs := [.bin .mov .w64 (.loc (.vreg 2)) (.vreg 0), .bin .mov .w64 (.loc (.vreg 0)) (.mem 1)]
  inputs := [(.vreg 2, .w64)]
  outputs := [(.vreg 0, .w64), (.mem 1, .w64)]

/-- `ret` in `rax`, `x` in `rcx`, the address of `m` in `rax`. -/
def addressInOutput : Placement := ⟨fun k => if k = 0 then 0 else 1, fun _ => [0]⟩

theorem staleAddress_rejected : staleAddress.check = some (.staleAddress 1 (.mem 1)) := by decide

theorem staleAddress_admissible : addressInOutput.Admissible staleAddress := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [staleAddress, addressInOutput, Block.operandLocs, Block.inputLocs, Block.outputLocs,
      Placement.loc]

theorem staleAddress_entry : addressInOutput.Entry staleAddress [7] (only 1 7) := by
  simp [Placement.Entry, staleAddress, addressInOutput, Placement.loc, only, initState, State.get]

/-- The second instruction stores through `rax`, which no longer holds the address. -/
theorem staleAddress_differs :
    addressInOutput.run (only 1 7) (staleAddress.instrs.map (Instr.place addressInOutput.loc))
      (only 1 7) = none := by
  rfl

/-! ## `"undefined-read-unchecked"` -/

/-- `movq %[x], %[ret]` with a 32-bit `x`: the instruction reads all 64 bits of its register. -/
def undefinedRead : Block where
  instrs := [.bin .mov .w64 (.loc (.vreg 1)) (.vreg 0)]
  inputs := [(.vreg 1, .w32)]
  outputs := [(.vreg 0, .w64)]

/-- `ret` in `rax`, `x` in `rcx`: no register is shared. -/
def apart : Placement := ⟨fun k => if k = 0 then 0 else 1, fun _ => []⟩

theorem undefinedRead_rejected : undefinedRead.check = some (.undefinedRead 0 (.vreg 1)) := by
  decide

theorem undefinedRead_admissible : apart.Admissible undefinedRead := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [undefinedRead, apart, Block.operandLocs, Block.inputLocs, Block.outputLocs,
      Placement.loc]

/-- `rcx` holds the input 5 in its low half and the caller's bits above it. -/
theorem undefinedRead_entry : apart.Entry undefinedRead [5] (only 1 0xdead00000005#64) := by
  simp [Placement.Entry, undefinedRead, apart, Placement.loc, only, initState, State.get]
  decide

theorem undefinedRead_differs :
    undefinedRead.out [5] 0 = 5 ∧
      machine apart undefinedRead (only 1 0xdead00000005#64) 0 = some 0xdead00000005#64 := by
  constructor <;> rfl

/-! ## `"undeclared-write-unchecked"` -/

/-- `xorl %%ecx, %%ecx; movq %[x], %[ret]` without an `rcx` clobber. -/
def undeclaredWrite : Block where
  instrs := [.bin .xor .w32 (.loc (.reg 1)) (.reg 1), .bin .mov .w64 (.loc (.vreg 1)) (.vreg 0)]
  inputs := [(.vreg 1, .w64)]
  outputs := [(.vreg 0, .w64)]

theorem undeclaredWrite_rejected :
    undeclaredWrite.check = some (.undeclaredWrite 0 (.reg 1)) := by decide

/-- Without the clobber the compiler may hold `x` in `rcx`. -/
theorem undeclaredWrite_admissible : apart.Admissible undeclaredWrite := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [undeclaredWrite, apart, Block.operandLocs, Block.inputLocs, Block.outputLocs,
      Placement.loc]

theorem undeclaredWrite_entry : apart.Entry undeclaredWrite [5] (only 1 5) := by
  simp [Placement.Entry, undeclaredWrite, apart, Placement.loc, only, initState, State.get]

theorem undeclaredWrite_differs :
    undeclaredWrite.out [5] 0 = 5 ∧ machine apart undeclaredWrite (only 1 5) 0 = some 0 := by
  constructor <;> rfl

/-! ## A checked block under a sharing placement -/

/-- `lzcntq %[x], %[ret]` with `[ret] "=r"` and `[x] "r"`. -/
def lzcnt : Block where
  instrs := [.cnt .lzcnt .w64 (.vreg 1) (.vreg 0)]
  inputs := [(.vreg 1, .w64)]
  outputs := [(.vreg 0, .w64)]

theorem lzcnt_checked : lzcnt.check = none := by decide

theorem lzcnt_admissible : shared.Admissible lzcnt := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [lzcnt, shared, Block.operandLocs, Block.inputLocs, Block.outputLocs, Placement.loc]

/-- The theorem's hypotheses are satisfiable with both operands in one register, and its
conclusion is what the machine computes: `lzcnt(1) = 63`. -/
theorem lzcnt_shared (x : BitVec 64) (p0 : State) (h : p0 (.reg 0) = x) :
    ∃ p, shared.run p0 (lzcnt.instrs.map (Instr.place shared.loc)) p0 = some p ∧
      shared.out lzcnt p 0 = lzcnt.out [x] 0 := by
  have hentry : shared.Entry lzcnt [x] p0 := by
    simp [Placement.Entry, lzcnt, shared, Placement.loc, initState, State.get, h]
  obtain ⟨p, hrun, hout, _⟩ := Block.check_placement lzcnt_checked lzcnt_admissible hentry
  exact ⟨p, hrun, hout 0⟩

theorem lzcnt_shared_one : machine shared lzcnt (only 0 1) 0 = some 63 := by rfl

end AsmPlacement
