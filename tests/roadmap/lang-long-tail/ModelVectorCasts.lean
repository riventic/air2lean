import LangLongTail.VectorCasts

/-! L09/L07: the translated `vector_casts.zig` against `probe_vector_casts.zig`'s native output.

    lake env lean --run tests/roadmap/lang-long-tail/ModelVectorCasts.lean <native output>

(with the compiled `LangLongTail.VectorCasts` of a version on `LEAN_PATH`, as `check.sh` does)
prints the model's line for every probe case and fails unless the native file has exactly these
lines. `stdEql` runs `std.mem.eql`'s translation over two 40-byte blocks. -/

open VectorCasts Zig

def showR {α : Type} (f : α → String) (r : Result α) : String :=
  match r.run with
  | some (.ok v) => f v
  | some (.error e) => s!"model-error {repr e}"
  | none => "model-none"

def nums {n w : Nat} (xs : Vector (BitVec w) n) : String :=
  ",".intercalate (xs.toList.map fun x => s!"{x.toNat}")

def line (name : String) (s : String) : String := s!"{name} 0 {s}"

def bytesFrom (f : Nat → Nat) (n : Nat) : Array Byte :=
  (Array.range n).map fun i => .int (BitVec.ofNat 8 (f i))

/-- `stdEql` on two 40-byte blocks: `b` is `a` with `edit` applied. -/
def stdEqlOn (edit : Array Byte → Array Byte) : Result Bool := do
  let a := bytesFrom (fun i => i * 13 % 256) 40
  let run : MemM Bool := do
    let pa ← alloc .stack 40 1
    let pb ← alloc .stack 40 1
    storeBytes pa 1 a
    storeBytes pb 1 (edit a)
    stdEql pa pb
  let (v, _) ← run.run (mem0 .fresh)
  pure v

def bump (i : Nat) (bs : Array Byte) : Array Byte :=
  bs.modify i fun | .int x => .int (x + 1) | b => b

def a16 : Vector (BitVec 8) 16 := Vector.ofFn fun i => BitVec.ofNat 8 (i.val * 7 % 256)

def modelLines : List String :=
  [ s!"eqlChunk 0 {showR toString (eqlChunk a16 a16)}",
    s!"eqlChunk 1 {showR toString (eqlChunk a16 (a16.set 15 (a16[15] ^^^ 1)))}",
    s!"stdEql 0 {showR toString (stdEqlOn id)}",
    s!"stdEql 1 {showR toString (stdEqlOn (bump 33))}",
    s!"stdEql 2 {showR toString (stdEqlOn (bump 0))}",
    line "bytesToLanes" (showR (nums ·.lanes) (bytesToLanes #v[1, 2, 3, 250])),
    line "lanesToBytes" (showR nums (lanesToBytes ⟨#v[9, 8, 7, 255]⟩)),
    line "u24ItemToLane" (showR (nums ·.lanes) (u24ItemToLane #v[0xabcdef])),
    line "u24LaneToItem" (showR nums (u24LaneToItem ⟨#v[0x123456]⟩)),
    line "boolItemToLane" (showR (fun v => ",".intercalate (v.lanes.toList.map fun b => if b then "1" else "0"))
      (boolItemToLane #v[true])),
    line "boolLanesToByte" (showR (s!"{·.toNat}")
      (boolLanesToByte ⟨#v[true, false, true, true, false, false, false, true]⟩)),
    line "lanesToWord" (showR (s!"{·.toNat}") (lanesToWord ⟨#v[0x11, 0x22, 0x33, 0x44]⟩)),
    line "wordToLanes" (showR (nums ·.lanes) (wordToLanes 0xdeadbeef)),
    line "bytesToHalves" (showR (nums ·.lanes) (bytesToHalves #v[1, 2, 3, 4])),
    line "halvesToBytes" (showR nums (halvesToBytes ⟨#v[0xbeef, 0x1234]⟩)),
    line "packedLanesToInt" (showR (s!"{·.toNat}") (packedLanesToInt ⟨#v[1, 6, 5]⟩)),
    line "intToPackedLanes" (showR (nums ·.lanes) (intToPackedLanes 0b101110001)) ]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: ModelVectorCasts.lean <native output>"; return 2
  let native := (← IO.FS.lines path).toList.filter (· ≠ "")
  if native == modelLines then
    IO.println s!"vector_casts: {modelLines.length} native lines match the model"
    return 0
  IO.eprintln "vector_casts: the native output differs from the model"
  for m in modelLines do
    unless native.contains m do IO.eprintln s!"  model only:  {m}"
  for n in native do
    unless modelLines.contains n do IO.eprintln s!"  native only: {n}"
  return 1
