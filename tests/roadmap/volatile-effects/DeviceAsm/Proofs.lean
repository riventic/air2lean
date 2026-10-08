import DeviceAsm.Gen

/-!
# Device asm proofs on the generated `rdtsc` client (L13)

`DeviceAsm/Gen.lean` is the unchanged translation of the real 0.16.0 export of
`device_asm.zig`'s `elapsed` with `--device-contract tsc.json`. Without the contract the same AIR
is rejected (`ASM_VOLATILE_EFFECT`): as an M21 `opaque`, the two `rdtsc` would be one repeatable
value and `elapsed` would provably return 0. Here each `rdtsc` is one `asm` event of the device
trace (`Zig.vasm`), and its value is the asm oracle's answer after every earlier event (premise
DEV-01).
-/

namespace DeviceAsmProofs
open Zig DeviceAsm

/-- The declared template (`tsc.json`). -/
def tsc : String := "rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax"

def tick (v : BitVec 64) : DevEvent := .asm tsc [] 64 v.toNat

/-- The memory `m` after the device events `es`, nothing else changed. -/
def after (m : Mem) (es : List DevEvent) : Mem :=
  { m with dev := { m.dev with trace := m.dev.trace ++ es } }

theorem after_append (m : Mem) (es fs : List DevEvent) :
    after (after m es) fs = after m (es ++ fs) := by simp [after]

theorem declared : air2lean_device.asms.contains tsc = true := by decide

theorem tsc_run {m : Mem} {v : BitVec 64} (ho : m.dev.asmOracle m.dev.trace tsc [] 64 = some v) :
    (vasm air2lean_device tsc [] 64).run m = pure (v, after m [tick v]) :=
  vasm_run declared ho

/-- **Two `rdtsc` are two events, in order**: the second answer is the oracle's answer after the
first event, and `elapsed` returns their wrapping difference. -/
theorem elapsed_trace (m : Mem) (a b : BitVec 64)
    (ha : m.dev.asmOracle m.dev.trace tsc [] 64 = some a)
    (hb : m.dev.asmOracle (m.dev.trace ++ [tick a]) tsc [] 64 = some b) :
    elapsed.run m = pure (b - a, after m [tick a, tick b]) := by
  have h1 := tsc_run ha
  have h2 := tsc_run (m := after m [tick a]) (v := b) (by simpa [after] using hb)
  simp only [StateT.run, tsc] at h1 h2
  simp [elapsed, zig_unfold, h1, h2, Zig.subWrap, after_append]

/-- A counter that advances once per event. -/
def counter : AsmOracle := fun h _ _ n => some (BitVec.ofNat n h.length)

/-- **Never merged**: under a counter that advances on every event, `elapsed` returns 1. A
translation that made `rdtsc` one repeatable value would return `a - a = 0` for every device. -/
theorem elapsed_not_merged :
    elapsed.run { dev := { asmOracle := counter } } =
      pure (1, after { dev := { asmOracle := counter } } [tick 0, tick 1]) :=
  elapsed_trace _ 0 1 rfl rfl

theorem merged_is_zero (a : BitVec 64) : a - a = 0 := by simp

end DeviceAsmProofs
