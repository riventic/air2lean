import EncExactness.Gen
import EncExactness.Opaque

/-! `enc_exactness.zig` and `opaque_bytes.zig` from the translations of one Zig version's exports
(`check.sh` puts them at `EncExactness.Gen` and `EncExactness.Opaque`, for each of 0.14.1, 0.15.2,
0.16.0 and 0.17.0): kernel-checked results that hold at every version, then `main` prints the
lines of `native.zig`'s cases (`unspecified` matches any native value).

The padded-integer reads are the counterexample of `docs/architecture-audit/enc-exactness.md`:
before the fix the 0.17.0 model read the `u16` `0x0200` as the `i10` `-512`, where native 0.17.0
ReleaseSafe code reads `512` on aarch64 (no `i10` at all: `trunc nsw` poison) and `-512` on
x86_64. The per-version statements are `ZigLean/EndianLemmas.lean`'s `intEncExt_*` and
`Rows.lean`. -/

open Zig EncExactness

namespace EncExactnessModel

/-- The result of running `f` from the translation's initial memory. -/
def result {α : Type} (f : MemM α) : Option (Except Error α) :=
  ((f.run (mem0 .fresh)).run).map (·.map Prod.fst)

/-- A stored `i24` reads back as stored at every version: the store and the load use one
encoding (`intEncOf` up to 0.16.0, `intEncExt` from 0.17.0). -/
theorem i24RoundTrip_exact : result (i24RoundTrip (-2)) = some (.ok (-2)) := by decide +kernel

/-- A stored `bool` reads back as the byte 1 at every version. -/
theorem boolByte_true : result (boolByte true) = some (.ok 1) := by decide +kernel

/-- An allocator's `vtable` word read as a `u64` is no value at every version: the model has no
address there (`Byte.handle`, `docs/architecture-audit/model-handle-bytes.md`). Before the fix it
read 0, where native code reads the address. -/
theorem allocatorWord_unspecified :
    ((Opaque.allocatorWord {}).run (Opaque.mem0 .fresh)).run.map (·.map Prod.fst) =
      some (.error .unspecified) := by
  decide +kernel

end EncExactnessModel

open EncExactnessModel

def hexN (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def fmt {n : Nat} : Option (Except Zig.Error (BitVec n)) → String
  | some (.ok v) => hexN v.toNat
  | some (.error .unspecified) => "unspecified"
  | some (.error e) => s!"error {repr e}"
  | none => "none"

def line {n : Nat} (name : String) (r : Option (Except Zig.Error (BitVec n))) : IO Unit :=
  IO.println s!"{name}: {fmt r}"

def main : IO Unit := do
  line "i10ZeroPad" (result (i10ZeroPad 0x0200))
  line "u24SetPad" (result (u24SetPad 0x01000005))
  line "i24ZeroPad" (result (i24ZeroPad 0x00800000))
  line "e24SetPad" (result (e24SetPad 0x01000005))
  line "i10StoreBytes" (result (i10StoreBytes (-1)))
  line "u24StoreBytes" (result (u24StoreBytes 5))
  line "i24RoundTrip" (result (i24RoundTrip (-2)))
  line "boolByte" (result (boolByte true))
  -- Native prints whether the word is 0 (an address otherwise varies with the build); the model
  -- once printed 0x1 here.
  let w := ((Opaque.allocatorWord {}).run (Opaque.mem0 .fresh)).run.map (·.map Prod.fst)
  line "allocatorWordIsZero" (w.map (·.map fun v => (if v = 0 then 1 else 0 : BitVec 8)))
