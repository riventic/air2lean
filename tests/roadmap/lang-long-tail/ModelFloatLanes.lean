import LangLongTail.FloatLanes

/-! L09: the translated `float_lanes.zig` against `probe_float_lanes.zig`'s native output.

    lake env lean --run tests/roadmap/lang-long-tail/ModelFloatLanes.lean <native output>

(with the compiled `LangLongTail.FloatLanes` of a version on `LEAN_PATH`, as `check.sh` does)
prints the probe's lines from the translation: lane pointers into `@Vector(n, f80)` are
bit-pointers into the vector's bit-packed integer (`Zig.loadLane`/`Zig.storeLane` on the
lane's 80 bits). It fails unless the native file has exactly these lines. -/

open FloatLanes Zig

def hexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def f (bits : Nat) : F80 := ⟨BitVec.ofNat 80 bits⟩

def swapLine : String :=
  let r : MemM (Vec F80 2) := do
    let p ← alloc .stack 32 32
    store 32 p (⟨#v[f 0x3fffc000000000000000, f 0xc0009000000000000000]⟩ : Vec F80 2)
    swap p
    load (Vec F80 2) 32 p
  match (r.run (mem0 .fresh)).run with
  | some (.ok (v, _)) => "swap" ++ String.join (v.lanes.toList.map (" " ++ hexNat ·.bits.toNat))
  | _ => "swap model-error"

def middleLine (x : Nat) : String :=
  match ((middle (f x)).run (mem0 .fresh)).run with
  | some (.ok (v, _)) => s!"middle {hexNat x} {hexNat v.bits.toNat}"
  | _ => s!"middle {hexNat x} model-error"

def modelLines : List String :=
  [swapLine, middleLine 0, middleLine 0x4002a000000000000000, middleLine 0xc001f000000000000000]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: ModelFloatLanes.lean <native output>"; return 2
  let native := (← IO.FS.lines path).toList.filter (· ≠ "")
  if native == modelLines then
    IO.println s!"float_lanes: {modelLines.length} native lines match the model"
    return 0
  IO.eprintln "float_lanes: the native output differs from the model"
  for m in modelLines do IO.eprintln s!"  model:  {m}"
  for n in native do IO.eprintln s!"  native: {n}"
  return 1
