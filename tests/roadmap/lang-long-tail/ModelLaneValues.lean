import LangLongTail.LaneValues

/-! L09: the translated `lane_values.zig` against `probe_lane_values.zig`'s native output.

    lake env lean --run tests/roadmap/lang-long-tail/ModelLaneValues.lean <native output>

(with the compiled `LangLongTail.LaneValues` of a version on `LEAN_PATH`, as `check.sh` does)
prints the probe's lines from the translation: lane pointers of whole-byte lanes (`u8`, `i16`,
`u32`, `u64`, `u128`, `f32`, `f64`) as a parameter, a result, a struct field, a `const` lane and
a constant, and `@intFromPtr` of `&v[1]` relative to the vector (the vector's address in Zig
0.17.1, the lane's up to 0.16.0). Every call starts from the program's initial memory, as the
probe's one call of each `global*` function does. It fails unless the native file has exactly
these lines. -/

open LaneValues Zig

def hexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def run {n : Nat} (r : MemM (BitVec n)) (fmt : Nat → String) : String :=
  match (r.run (mem0 .fresh)).run with
  | some (.ok (v, _)) => fmt v.toNat
  | _ => "model-error"

def hex {n : Nat} (r : MemM (BitVec n)) : String := run r hexNat

def dec {n : Nat} (r : MemM (BitVec n)) : String := run r toString

def modelLines : List String :=
  [s!"globalU8 {hex (globalU8 0x5a)}", s!"globalU32 {hex (globalU32 0x5a)}",
   s!"globalU128 {hex (globalU128 0x5a)}", s!"globalF64 {hex (globalF64 0x5a)}"] ++
  [0, 0x89abcdef, 0xffffffff].flatMap fun (a : Nat) =>
    let a' := BitVec.ofNat 32 a
    ([0, 0x1234567].flatMap fun (x : Nat) =>
      let x' := BitVec.ofNat 32 x
      [("valuesU8", valuesU8), ("valuesI16", valuesI16), ("valuesU32", valuesU32),
       ("valuesU64", valuesU64), ("valuesU128", valuesU128), ("valuesF32", valuesF32),
       ("valuesF64", valuesF64)].map fun (name, f) =>
        s!"{name} {hexNat a} {hexNat x} {hex (f a' x')}") ++
    [s!"offset {hexNat a} {dec (offsetU8 a')} {dec (offsetU32 a')} {dec (offsetF64 a')}"]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: ModelLaneValues.lean <native output>"; return 2
  let native := (← IO.FS.lines path).toList.filter (· ≠ "")
  if native == modelLines then
    IO.println s!"lane_values: {modelLines.length} native lines match the model"
    return 0
  IO.eprintln "lane_values: the native output differs from the model"
  for m in modelLines do IO.eprintln s!"  model:  {m}"
  for n in native do IO.eprintln s!"  native: {n}"
  return 1
