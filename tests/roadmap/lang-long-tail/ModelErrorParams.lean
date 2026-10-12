import LangLongTail.ErrorParams

/-! L10: the translated `error_params.zig` against `probe_error_params.zig`'s native output.

    lake env lean --run tests/roadmap/lang-long-tail/ModelErrorParams.lean <native output>

(with the compiled `LangLongTail.ErrorParams` on `LEAN_PATH`, as `check.sh` does) prints the
model's line for every probe case and fails unless the native file has exactly these lines. -/

open ErrorParams Zig

def inputs : List (BitVec 32) := [0, 1, 2, 7, 0x7fffffff]

def showR (r : Result String) : String :=
  match r.run with
  | some (.ok v) => v
  | some (.error e) => s!"model-error {repr e}"
  | none => "model-none"

def euLine (name : String) (x : BitVec 32) (r : Result (Except ErrName (BitVec 32))) : String :=
  s!"{name} {x.toNat} " ++ showR (r.map fun
    | .ok v => s!"{v.toNat}"
    | .error e => s!"error.{e}")

def valLine (name : String) (x : BitVec 32) (r : Result (BitVec 32)) : String :=
  s!"{name} {x.toNat} " ++ showR (r.map fun v => s!"{v.toNat}")

def modelLines : List String :=
  inputs.map (fun x => euLine "orBoom" x (orBoom x "Boom")) ++
  inputs.map (fun x => euLine "forward" x (forward x)) ++
  inputs.map (fun x => valLine "viaFail" x (viaFail x)) ++
  inputs.map (fun x => valLine "unwrapEmpty" x (unwrapEmpty (.ok x))) ++
  inputs.map (fun x => valLine "skipFirst" x (skipFirst "Boom" x))

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: ModelErrorParams.lean <native output>"; return 2
  let native := (← IO.FS.lines path).toList.filter (· ≠ "")
  if native == modelLines then
    IO.println s!"error_params: {modelLines.length} native lines match the model"
    return 0
  IO.eprintln "error_params: the native output differs from the model"
  for m in modelLines do
    unless native.contains m do IO.eprintln s!"  model only:  {m}"
  for n in native do
    unless modelLines.contains n do IO.eprintln s!"  native only: {n}"
  return 1
