import NanBits.Gen
import ZigLean.EndianLemmas

/-! `nan_bits.zig` from the translation of one Zig version's export (`check.sh` puts it at
`NanBits.Gen`, for each of 0.14.1, 0.15.2, 0.16.0 and 0.17.0): kernel-checked results, then `main`
prints the lines of `native.zig`'s cases (`unspecified` matches any native value).

The NaN cases are the counterexample of `docs/architecture-audit/nan-bits.md`: before the fix the
model derived the canonical NaN's bits (`0x7fc00000`) where x86_64 gives `0xffc00000` and a
propagated payload gives `0x7fc00123` on both targets. -/

open Zig NanBits

namespace NanBitsModel

def f32 (b : Nat) : Zig.F32 := Zig.Float.ofBits (BitVec.ofNat 32 b)
def f64 (b : Nat) : Zig.F64 := Zig.Float.ofBits (BitVec.ofNat 64 b)

/-- The result of running `f` from the translation's initial memory. -/
def result {α : Type} (f : MemM α) : Option (Except Error α) :=
  ((f.run (mem0 .fresh)).run).map (·.map Prod.fst)

def z : Zig.F32 := f32 0
/-- A quiet NaN with a payload (`native.zig`'s `payload32`). -/
def payload : Zig.F32 := f32 0x7fc00123

/-! ## A NaN that an operation makes: its bits are `.unspecified` wherever they become an integer -/

theorem storeLoad_nan : result (storeLoad z z) = some (.error .unspecified) := by decide +kernel
theorem storeLoad64_nan : result (storeLoad64 (f64 0) (f64 0)) = some (.error .unspecified) := by
  decide +kernel
theorem sumBits_nan : result (sumBits payload (f32 0x3f800000)) = some (.error .unspecified) := by
  decide +kernel
theorem unionView_nan : (unionView z z).run = some (.error .unspecified) := by decide +kernel
theorem arrayCast_nan : (arrayCast z z).run = some (.error .unspecified) := by decide +kernel
theorem vectorCast_nan : (vectorCast z z).run = some (.error .unspecified) := by decide +kernel
theorem structView_nan : result (structView z z) = some (.error .unspecified) := by decide +kernel
theorem copyBytes_nan : result (copyBytes z z) = some (.error .unspecified) := by decide +kernel

/-- The counterexample's old claims are not derivable: no integer (the canonical NaN's
`0x7fc00000`, x86_64's `0xffc00000`, the propagated payload `0x7fc00123`) is a result. -/
theorem storeLoad_no_value (b : BitVec 32) : result (storeLoad z z) ≠ some (.ok b) := by
  rw [storeLoad_nan]; intro h; cases h
theorem sumBits_no_value (b : BitVec 32) :
    result (sumBits payload (f32 0x3f800000)) ≠ some (.ok b) := by
  rw [sumBits_nan]; intro h; cases h

/-- A stored NaN read back as a float: `.unspecified` (an over-approximation: the model does
not know which NaN the bytes hold; native code reads a NaN). -/
theorem reloadIsNaN_unspecified : result (reloadIsNaN z z) = some (.error .unspecified) := by
  decide +kernel

/-! ## Determined bits stay exact -/

theorem finiteBits_ok : result (finiteBits (f32 0x3f800000) (f32 0x40400000)) =
    some (.ok 0x3eaaaaab) := by decide +kernel
/-- A NaN constant (a signaling one) stored at run time keeps its bits. -/
theorem constStore_ok : result constStore = some (.ok 0x7fa00002) := by decide +kernel
/-- A NaN constant in a global initializer keeps its bits. -/
theorem constGlobal_ok : result constGlobal = some (.ok 0x7fa00001) := by decide +kernel

/-! ## The general statement behind the cases (`ZigLean/EndianLemmas.lean`) -/

/-- Every `f32` NaN's stored bytes read as a `u32` are `.unspecified`. -/
theorem f32_nan_u32 : ∀ v : Zig.F32, v.isNaN = true →
    intOfBytesOf .little 32 ((floatEncOf .little .f32).encode v) false = throw .unspecified :=
  fun _ h => floatEncOf_nan_int .little .f32 h false (by decide) (by decide)

end NanBitsModel

open NanBitsModel

def hexN (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

class Hex (α : Type) where
  toNat : α → Nat

instance {n : Nat} : Hex (BitVec n) := ⟨BitVec.toNat⟩
instance : Hex Bool := ⟨fun b => if b then 1 else 0⟩

def fmt {α : Type} [Hex α] : Option (Except Zig.Error α) → String
  | some (.ok v) => hexN (Hex.toNat v)
  | some (.error .unspecified) => "unspecified"
  | some (.error e) => s!"error {repr e}"
  | none => "none"

def line {α : Type} [Hex α] (name : String) (r : Option (Except Zig.Error α)) : IO Unit :=
  IO.println s!"{name}: {fmt r}"

def main : IO Unit := do
  line "storeLoad" (result (storeLoad z z))
  line "storeLoad64" (result (storeLoad64 (f64 0) (f64 0)))
  line "sumBits" (result (sumBits payload (f32 0x3f800000)))
  line "unionView" (unionView z z).run
  line "arrayCast" (arrayCast z z).run
  line "vectorCast" (vectorCast z z).run
  line "structView" (result (structView z z))
  line "copyBytes" (result (copyBytes z z))
  line "finiteBits" (result (finiteBits (f32 0x3f800000) (f32 0x40400000)))
  line "constStore" (result constStore)
  line "constGlobal" (result constGlobal)
  line "reloadIsNaN" (result (reloadIsNaN z z))
