import DeviceAsm.Gen
import ZigLean.Sep.Full.AutoAll

/-!
# Device asm proofs on the generated `rdtsc` client (L13)

`DeviceAsm/Gen.lean` is the unchanged translation of the real 0.16.0 export of
`device_asm.zig`'s `elapsed` with `--device-contract tsc.json`. Without the contract the same AIR
is rejected (`ASM_VOLATILE_EFFECT`): as an M21 `opaque`, the two `rdtsc` would be one repeatable
value and `elapsed` would provably return 0. Here each `rdtsc` is one `asm` event of the device
trace (`Zig.vasm`), and its value is the asm oracle's answer after every earlier event (premise
DEV-01).

The statements are total triples of the full-state logic over the device state `devOwn D`
(`docs/sep-full-state.md` §Device state), for every device state `D` (its oracles and its trace
so far); `fsym` walks the generated code with the library's device rules
(`ZigLean/Sep/Full/Device.lean`), of which the `cpu` contract is an instance.
-/

namespace DeviceAsmProofs
open Zig Zig.Full Zig.Full.FAssn DeviceAsm

/-- The declared template (`tsc.json`). -/
abbrev tsc : String := "rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax"

/-- One `rdtsc` event with the value `v`. -/
abbrev stamp (v : BitVec 64) : DevEvent := .asm tsc [] 64 v.toNat

/-- **Two `rdtsc` are two events, in order**: the second answer is the oracle's answer after the
first event, and `elapsed` returns their wrapping difference. Nothing else changes (the triple
frames every other resource). -/
theorem elapsed_trace (D : DevState) (a b : BitVec 64)
    (ha : D.asmOracle D.trace tsc [] 64 = some a)
    (hb : D.asmOracle (D.trace ++ [stamp a]) tsc [] 64 = some b) :
    FTotalTriple (devOwn D) elapsed
      (fun r => ⟪r = b - a⟫ ⋆ devOwn { D with trace := D.trace ++ [stamp a, stamp b] }) := by
  fsym

/-- **The run from program start**, with the environment's device state `D` in the start memory
(adequacy, `FTotalTriple.run_init_dev`): `elapsed` returns the difference, and the final device
state is `D` with the two events appended. -/
theorem elapsed_run (σ : Placement) (D : DevState) (a b : BitVec 64)
    (ha : D.asmOracle D.trace tsc [] 64 = some a)
    (hb : D.asmOracle (D.trace ++ [stamp a]) tsc [] 64 = some b) :
    ∃ m', elapsed.run { mem0 σ with dev := D } = pure (b - a, m') ∧
      m'.dev = { D with trace := D.trace ++ [stamp a, stamp b] } := by
  obtain ⟨v, m', r', hr, hh, hq, -⟩ := FTotalTriple.run_init_dev σ [] (by decide) (by simp) D
    ((elapsed_trace D a b ha hb).frame (R := globals []))
  obtain ⟨rfl, hd⟩ := sep_lift.mp (sep_assoc hq)
  exact ⟨m', hr, hh.dev hd⟩

/-- A counter that advances once per event. -/
def counter : AsmOracle := fun h _ _ n => some (BitVec.ofNat n h.length)

/-- **Never merged**: under a counter that advances on every event, `elapsed` returns 1. A
translation that made `rdtsc` one repeatable value would return `a - a = 0` for every device. -/
theorem elapsed_not_merged :
    FTotalTriple (devOwn { asmOracle := counter }) elapsed
      (fun r => ⟪r = 1⟫ ⋆ devOwn { asmOracle := counter, trace := [stamp 0, stamp 1] }) :=
  elapsed_trace { asmOracle := counter } 0 1 rfl rfl

theorem merged_is_zero (a : BitVec 64) : a - a = 0 := by simp

end DeviceAsmProofs
