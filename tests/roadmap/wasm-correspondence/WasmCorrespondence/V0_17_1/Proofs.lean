import WasmCorrespondence.Contracts
import WasmCorrespondence.V0_17_1.X64.Gen
import WasmCorrespondence.V0_17_1.A64.Gen
import WasmCorrespondence.V0_17_1.Wasm32.Gen
import WasmCorrespondence.V0_17_1.Wasi.Gen

/-!
# T05: every translation of the DES kernels meets the one contract

`kernels.zig` translated from its x86_64-linux, aarch64-macos, wasm32-freestanding and
wasm32-wasi exports by one Zig version (`check.sh`). `meets` proves the contract of
`Contracts.lean` for all four at once: each field has one proof, run on every target. The
theorems after it are its instances, each about one target's generated module, which is what a
claim of `relation.json` cites (a theorem is never relabeled to another target). The file of the
0.17.1 translations is written; the file of the 0.16.0 ones is it with that version's names
(`scripts/fixtures.py instance`).
-/

namespace WasmCorrespondence.V0_17_1.Proofs

open Zig WasmCorrespondence WasmCorrespondence.V0_17_1

/-- The translated targets. -/
inductive Target where
  | x64
  | a64
  | wasm32
  | wasi

/-- The pointer width of a target's profile. -/
def Target.width : Target → PtrWidth
  | .x64 | .a64 => .w64
  | .wasm32 | .wasi => .w32

/-- A target's translation. -/
def kernels : Target → Kernels
  | .x64 => ⟨X64.des_time_add32, X64.des_time_add64, X64.des_event_before, X64.usize_bits⟩
  | .a64 => ⟨A64.des_time_add32, A64.des_time_add64, A64.des_event_before, A64.usize_bits⟩
  | .wasm32 =>
    ⟨Wasm32.des_time_add32, Wasm32.des_time_add64, Wasm32.des_event_before, Wasm32.usize_bits⟩
  | .wasi => ⟨Wasi.des_time_add32, Wasi.des_time_add64, Wasi.des_event_before, Wasi.usize_bits⟩

/-- Every translation meets the contract at its profile's pointer width. -/
theorem meets (t : Target) : (kernels t).Meets t.width where
  time_add32 a b := by
    cases t <;>
      rcases addWithOverflow_max_cases (a.setWidth 32) (b.setWidth 32) 4294967295#32 (by decide)
        with h | h | h <;>
      simp [kernels, zig_run, zig_unfold, timeAdd, trunc, isNonErr, isErr, unwrapPayload,
        unwrapErr, h] <;> rfl
  time_add64 a b := by
    cases t <;>
      rcases addWithOverflow_max_cases a b 18446744073709551615#64 (by decide) with h | h | h <;>
      simp [kernels, zig_run, zig_unfold, timeAdd, isNonErr, isErr, unwrapPayload, unwrapErr,
        h] <;> rfl
  event_before t1 s1 t2 s2 := by
    cases t <;> by_cases h1 : t1.toNat < t2.toNat <;> by_cases h2 : t1 = t2 <;>
      by_cases h3 : s1.toNat % 2 ^ 32 < s2.toNat % 2 ^ 32 <;>
      simp [kernels, zig_run, zig_unfold, eventBefore, trunc, h1, h2, h3]
  usize_bits := by cases t <;> simp [kernels, Target.width, zig_run, zig_unfold] <;> rfl

/-! ## Instances: one target's generated module each -/

theorem des_time_add32_x64 (a b : BitVec 64) : X64.des_time_add32 a b = pure (timeAdd 32 a b) :=
  (meets .x64).time_add32 a b
theorem des_time_add32_a64 (a b : BitVec 64) : A64.des_time_add32 a b = pure (timeAdd 32 a b) :=
  (meets .a64).time_add32 a b
theorem des_time_add32_wasm32 (a b : BitVec 64) :
    Wasm32.des_time_add32 a b = pure (timeAdd 32 a b) := (meets .wasm32).time_add32 a b
theorem des_time_add32_wasi (a b : BitVec 64) : Wasi.des_time_add32 a b = pure (timeAdd 32 a b) :=
  (meets .wasi).time_add32 a b

theorem des_time_add64_x64 (a b : BitVec 64) : X64.des_time_add64 a b = pure (timeAdd 64 a b) :=
  (meets .x64).time_add64 a b
theorem des_time_add64_a64 (a b : BitVec 64) : A64.des_time_add64 a b = pure (timeAdd 64 a b) :=
  (meets .a64).time_add64 a b
theorem des_time_add64_wasm32 (a b : BitVec 64) :
    Wasm32.des_time_add64 a b = pure (timeAdd 64 a b) := (meets .wasm32).time_add64 a b
theorem des_time_add64_wasi (a b : BitVec 64) : Wasi.des_time_add64 a b = pure (timeAdd 64 a b) :=
  (meets .wasi).time_add64 a b

theorem des_event_before_x64 (t1 s1 t2 s2 : BitVec 64) :
    X64.des_event_before t1 s1 t2 s2 = pure (eventBefore t1 s1 t2 s2) :=
  (meets .x64).event_before t1 s1 t2 s2
theorem des_event_before_a64 (t1 s1 t2 s2 : BitVec 64) :
    A64.des_event_before t1 s1 t2 s2 = pure (eventBefore t1 s1 t2 s2) :=
  (meets .a64).event_before t1 s1 t2 s2
theorem des_event_before_wasm32 (t1 s1 t2 s2 : BitVec 64) :
    Wasm32.des_event_before t1 s1 t2 s2 = pure (eventBefore t1 s1 t2 s2) :=
  (meets .wasm32).event_before t1 s1 t2 s2
theorem des_event_before_wasi (t1 s1 t2 s2 : BitVec 64) :
    Wasi.des_event_before t1 s1 t2 s2 = pure (eventBefore t1 s1 t2 s2) :=
  (meets .wasi).event_before t1 s1 t2 s2

theorem usize_bits_x64 : X64.usize_bits = pure 64 := (meets .x64).usize_bits
theorem usize_bits_a64 : A64.usize_bits = pure 64 := (meets .a64).usize_bits
theorem usize_bits_wasm32 : Wasm32.usize_bits = pure 32 := (meets .wasm32).usize_bits
theorem usize_bits_wasi : Wasi.usize_bits = pure 32 := (meets .wasi).usize_bits

end WasmCorrespondence.V0_17_1.Proofs
