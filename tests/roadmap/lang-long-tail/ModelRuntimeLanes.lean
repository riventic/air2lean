import LangLongTail.RuntimeLanes

/-! L09: the translated `runtime_lanes.zig` (Zig 0.14.1/0.15.2) against
`probe_runtime_lanes.zig`'s native output.

    lake env lean --run tests/roadmap/lang-long-tail/ModelRuntimeLanes.lean <native output>

(with the compiled `LangLongTail.RuntimeLanes` of a version on `LEAN_PATH`, as `check.sh` does)
stores the probe's vector in memory (`Enc (Vec α n)`, the bit-packed image), runs the translated
store at each runtime index (`Zig.storeLaneAt`), reads the vector back and prints its lanes. It
fails unless the native file has exactly these lines, or unless an index past the lanes is the
`outOfBounds` safety panic. -/

open RuntimeLanes Zig

def hexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The lanes of `init` after `f` ran on a pointer to it. -/
def after {α : Type} {n : Nat} [Enc (Vec α n)] (init : Vec α n) (f : Ptr → MemM Unit) :
    Except Error (Vec α n) :=
  let r : MemM (Vec α n) := do
    let p ← alloc .stack (Enc.size (Vec α n)) (Enc.align (Vec α n))
    store (Enc.align (Vec α n)) p init
    f p
    load (Vec α n) (Enc.align (Vec α n)) p
  match (r.run (mem0 .fresh)).run with
  | some (.ok (v, _)) => .ok v
  | some (.error e) => .error e
  | none => .error .unspecified

def line {α : Type} {n : Nat} [Enc (Vec α n)] (name : String) (i : Nat) (fmt : α → String)
    (init : Vec α n) (f : Ptr → MemM Unit) : String :=
  match after init f with
  | .ok v => s!"{name} {i}" ++ String.join (v.lanes.toList.map (" " ++ fmt ·))
  | .error e => s!"{name} {i} model-error {repr e}"

def u (x : BitVec w) : String := s!"{x.toNat}"

def modelLines : List String :=
  (List.range 4).map (fun i => line "setU9" i u (⟨#v[1, 2, 3, 4]⟩ : Vec (BitVec 9) 4)
    (setU9 · (BitVec.ofNat 64 i) 500)) ++
  (List.range 3).map (fun i => line "setU24" i u (⟨#v[0x10, 0x20, 0x30]⟩ : Vec (BitVec 24) 3)
    (setU24 · (BitVec.ofNat 64 i) 0xabcdef)) ++
  (List.range 5).map (fun i => line "setBool" i (fun b => if b then "1" else "0")
    (⟨#v[true, false, true, false, true]⟩ : Vec Bool 5) (setBool · (BitVec.ofNat 64 i) (i % 2 == 1))) ++
  (List.range 2).map (fun i => line "setF80" i (fun f : F80 => hexNat f.bits.toNat)
    (⟨#v[⟨0x3fffc000000000000000⟩, ⟨0xc0009000000000000000⟩]⟩ : Vec F80 2)
    (setF80 · (BitVec.ofNat 64 i) ⟨0x4000c000000000000000⟩)) ++
  (List.range 6).map fun n =>
    match ((fillSum (BitVec.ofNat 64 n)).run (mem0 .fresh)).run with
    | some (.ok (v, _)) => s!"fillSum {n} {v.toNat}"
    | _ => s!"fillSum {n} model-error"

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: ModelRuntimeLanes.lean <native output>"; return 2
  let native := (← IO.FS.lines path).toList.filter (· ≠ "")
  let mut ok := native == modelLines
  unless ok do
    IO.eprintln "runtime_lanes: the native output differs from the model"
    for m in modelLines do IO.eprintln s!"  model:  {m}"
    for n in native do IO.eprintln s!"  native: {n}"
  -- Past the lanes: the safety check before `vector_store_elem` panics.
  unless (after (⟨#v[1, 2, 3, 4]⟩ : Vec (BitVec 9) 4) (setU9 · 4 0)) matches .error .outOfBounds do
    ok := false
    IO.eprintln "runtime_lanes: a store at index 4 of a 4-lane vector is not the outOfBounds panic"
  if ok then
    IO.println s!"runtime_lanes: {modelLines.length} native lines match the model"
    return 0
  return 1
