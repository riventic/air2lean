import LangLongTail.LaneShapes

/-! L09: the translated `lane_shapes.zig` against `probe_lane_shapes.zig`'s native output.

    lake env lean --run tests/roadmap/lang-long-tail/ModelLaneShapes.lean <native output>

(with the compiled `LangLongTail.LaneShapes` of a version on `LEAN_PATH`, as `check.sh` does)
prints the probe's lines from the translation: a lane pointer into `@Vector(4, u9)` as a
constant, a function result, a struct field, into a vector field and `const`, each a bit-pointer
into the vector's integer (`Zig.loadLane`/`Zig.storeLane`), and a whole-byte lane as the control.
Every call starts from the program's initial memory, as the probe's one `globalLane` call does.
It fails unless the native file has exactly these lines. -/

open LaneShapes Zig

def hexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def result {n : Nat} (r : MemM (BitVec n)) : String :=
  match (r.run (mem0 .fresh)).run with
  | some (.ok (v, _)) => hexNat v.toNat
  | _ => "model-error"

def modelLines : List String :=
  [s!"globalLane 1aa {result (globalLane 0x1aa)}"] ++
  [0, 0x89abcdef, 0xffffffff].flatMap fun (a : Nat) =>
    ([0, 0x155, 0xfe01].flatMap fun (x : Nat) =>
      [s!"viaResult {hexNat a} {hexNat x} {result (viaResult (.ofNat 32 a) (.ofNat 16 x))}",
       s!"viaField {hexNat a} {hexNat x} {result (viaField (.ofNat 32 a) (.ofNat 16 x))}",
       s!"fieldLane {hexNat a} {hexNat x} {result (fieldLane (.ofNat 32 a) (.ofNat 16 x))}",
       s!"byteLocal {hexNat a} {hexNat x} {result (byteLocal (.ofNat 32 a) (.ofNat 32 x))}"]) ++
    [s!"constLane {hexNat a} {result (constLane (.ofNat 32 a))}"]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: ModelLaneShapes.lean <native output>"; return 2
  let native := (← IO.FS.lines path).toList.filter (· ≠ "")
  if native == modelLines then
    IO.println s!"lane_shapes: {modelLines.length} native lines match the model"
    return 0
  IO.eprintln "lane_shapes: the native output differs from the model"
  for m in modelLines do IO.eprintln s!"  model:  {m}"
  for n in native do IO.eprintln s!"  native: {n}"
  return 1
