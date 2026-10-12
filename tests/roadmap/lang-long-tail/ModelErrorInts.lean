import LangLongTail.ErrorInts

/-! L10: the translated `error_ints.zig` against `probe_error_ints.zig`'s native output. The
export is of the probe's own compilation (`error_ints.root`), so `errorTable`, the numbering the
patched compiler wrote after analysis, is the numbering of the native program.

    lake env lean --run tests/roadmap/lang-long-tail/ModelErrorInts.lean <native output>

(with the compiled `LangLongTail.ErrorInts` of a version on `LEAN_PATH`, as `check.sh` does)
prints the probe's lines from the translation and fails unless the native file has exactly these
lines. It also checks the cases a native run cannot print: code 0 and the code after the last
error are the safety panic (`back`), and so is every code of a numbering shifted by one (a
mutant that guesses the numbering from the program's own error sets). -/

open ErrorInts Zig

def run {α : Type} (r : MemM α) : Option α :=
  match (r.run (mem0 .fresh)).run with
  | some (.ok (v, _)) => some v
  | _ => none

/-- The bytes of the name slice that `r` returns, as text. -/
def runName (r : MemM Slice) : Option String :=
  run do
    let s ← r
    let bs ← loadBytes s.ptr s.len.toNat 1
    pure (String.fromUTF8! (ByteArray.mk (bs.map fun b => match b with
      | .int x => x.toNat.toUInt8
      | _ => 63)))

def nameLine (c : Nat) : String :=
  match runName (nameOf (BitVec.ofNat _ c)) with
  | some s => s!"nameOf {c} {s}"
  | none => s!"nameOf {c} model-error"

def codeLine (e : ErrName) : String :=
  match (code e).run with
  | some (.ok c) =>
    let n := (runName (nameOf c)).getD "model-error"
    let rt := match (roundTrip e).run with | some (.ok b) => toString b | _ => "model-error"
    let vm := match run (viaMemory e) with | some b => toString b | none => "model-error"
    s!"code {e} {c.toNat} {n} {rt} {vm}"
  | _ => s!"code {e} model-error"

def modelLines : List String :=
  ["Alpha", "Beta", "Gamma"].map codeLine ++ (List.range 8).map (nameLine ∘ (· + 1))

def panics (c : Nat) : Bool := (back (BitVec.ofNat _ c)).run == some (.error .panic)

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: ModelErrorInts.lean <native output>"; return 2
  let native := (← IO.FS.lines path).toList.filter (· ≠ "")
  let mut ok := native == modelLines
  unless ok do
    IO.eprintln "error_ints: the native output differs from the model"
    for m in modelLines do IO.eprintln s!"  model:  {m}"
    for n in native do IO.eprintln s!"  native: {n}"
  unless panics 0 && panics (errorTable.size + 1) && !panics errorTable.size do
    ok := false
    IO.eprintln "error_ints: `@errorFromInt` bounds: code 0 and the code after the last error must panic"
  if ok then
    IO.println s!"error_ints: {modelLines.length} native lines match the model ({errorTable.size} errors)"
    return 0
  return 1
