import ZigLean.VecMem

/-! L09: the model's side of `probe.zig`. Prints, for each probed vector, the size, alignment
and memory image of `Enc.encode` before and after a lane write (`Vec.set`), in the probe's line
format (`--` for an undefined byte; a `Byte.part` prints its defined low bits), and compares
them with a recorded probe output:

    lake env lean --run tests/roadmap/vector-layouts/Model.lean \
      tests/roadmap/vector-layouts/aarch64-macos-ReleaseSafe.txt

It also checks at run time that each image decodes back to its vector. The universal statements
are the theorems in `ZigLean/VecMem.lean`; the examples below instantiate them. -/

open Zig

/-- The instance that the translator's `Zig.load`/`Zig.store` resolve is the bit-packed one. -/
example : Enc.size (Vec (BitVec 9) 4) = 8 := rfl
example : Enc.size (Vec (BitVec 24) 3) = 16 := rfl
example : Enc.size (Vec (BitVec 40) 2) = 16 := rfl
example : Enc.size (Vec (Float .f80) 2) = 32 := rfl
example : Enc.size (Vec (BitVec 32) 3) = 16 := rfl
example (v : Vec (BitVec 9) 4) : Enc.decode (Enc.encode v) = pure v := LawfulEnc.decode_encode v
example (v : Vec (BitVec 24) 3) : Enc.decode (Enc.encode v) = pure v := LawfulEnc.decode_encode v
example (v : Vec F80 2) : Enc.decode (Enc.encode v) = pure v := LawfulEnc.decode_encode v
example (v : Vec (BitVec 9) 4) (x : BitVec 9) :
    laneOf 9 ((v.set 2 x).packBits 9 id).toNat 0 = laneOf 9 (v.packBits 9 id).toNat 0 :=
  laneOf_packBits_set_ne 9 id v 2 x 0 (by decide) (by decide)

def hex2 (x : BitVec 8) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  if s.length < 2 then "0" ++ s else s

def byteStr : Byte → String
  | .undef => "--"
  | .int x => hex2 x
  | .part _ x => hex2 x
  | _ => "??"

def image (bs : Array Byte) : String := String.join (bs.toList.map fun b => " " ++ byteStr b)

def roundTrips {α : Type} [Enc α] [BEq α] (v : α) : Bool :=
  match (Enc.decode (Enc.encode v) : Result α).run with
  | some (.ok w) => w == v
  | _ => false

/-- The two probe lines of one vector, and whether both images decode back. -/
def case {α : Type} {n : Nat} [Enc (Vec α n)] [BEq α] (name : String) (lanes : Vector α n)
    (i : Fin n) (x : α) : List String × Bool :=
  let v : Vec α n := ⟨lanes⟩
  let w := v.set i x
  ([s!"vector {name} {Enc.size (Vec α n)} {Enc.align (Vec α n)}{image (Enc.encode v)}",
    s!"lane {name} {i.val}{image (Enc.encode w)}"], roundTrips v && roundTrips w)

/-- The lane-pointer lines of a vector of `w`-bit integer or `bool` lanes: a load through
`&v[j]` (`Zig.loadLane`, `j` the lane after `i`), and the bytes after the host
(`⌈n * w / 8⌉` bytes) set to a5 before a store through `&v[i]` (`Zig.storeLane`). Also whether
that store left the host bytes of `v.set i x` (the `lane` line). -/
def laneCase {α : Type} {n w : Nat} [Enc (Vec α n)] [Packed α w] (name : String)
    (lanes : Vector α n) (i : Fin n) (x : α) : List String × Bool :=
  let v : Vec α n := ⟨lanes⟩
  let (S, host, j) := (Enc.size (Vec α n), (n * w + 7) / 8, (i.val + 1) % n)
  let run {β : Type} (f : Ptr → MemM β) : Option β := (((do
    let p ← alloc .stack S S
    storeBytes p S (Enc.encode v)
    storeBytes (p.add host) 1 (Array.replicate (S - host) (.int 0xa5))
    f p : MemM β).run {}).run.bind Except.toOption).map Prod.fst
  let loaded := run fun p => loadLane α host S (j * w) p
  let stored := run fun p => do storeLane host S (i * w) p x; loadBytes p S 1
  let hex (y : α) := String.ofList (Nat.toDigits 16 (Packed.toBits y).toNat)
  ([s!"load {name} {j} {(loaded.map hex).getD "??"}",
    s!"pad {name}{image ((stored.getD #[]).extract host S)}"],
    stored.map (·.extract 0 host) == some ((Enc.encode (v.set i x)).extract 0 host))

def f80 (bits : Nat) : F80 := ⟨BitVec.ofNat 80 bits⟩

/-- `case` and, for a lane pointer into bit-packed integer or `bool` lanes, `laneCase`. -/
def both {α : Type} {n w : Nat} [Enc (Vec α n)] [BEq α] [Packed α w] (name : String)
    (lanes : Vector α n) (i : Fin n) (x : α) : List String × Bool :=
  let (a, ok) := case name lanes i x
  let (b, ok') := laneCase name lanes i x
  (a ++ b, ok && ok')

def cases : List (List String × Bool) := [
  both "u9x4" (#v[0x1ff, 0, 0x1ff, 1] : Vector (BitVec 9) 4) 2 0x0aa,
  both "i9x2" (#v[-1, 1] : Vector (BitVec 9) 2) 1 (-2),
  both "u12x3" (#v[0xabc, 0x123, 0xfff] : Vector (BitVec 12) 3) 0 0x555,
  both "u4x4" (#v[1, 2, 3, 4] : Vector (BitVec 4) 4) 3 0xf,
  both "u1x8" (#v[1, 0, 1, 0, 0, 0, 0, 1] : Vector (BitVec 1) 8) 6 1,
  both "u24x2" (#v[0xabcdef, 0x123456] : Vector (BitVec 24) 2) 0 0x000001,
  both "u24x3" (#v[0xabcdef, 0x123456, 0x777777] : Vector (BitVec 24) 3) 1 0xfedcba,
  both "u40x2" (#v[0xaabbccddee, 0x1122334455] : Vector (BitVec 40) 2) 1 0x0102030405,
  -- 1.0, -2.0 and 0.5 as x87 extended-precision bits. A lane pointer into a float vector stays
  -- outside the subset.
  case "f80x2" (#v[f80 0x3fff8000000000000000, f80 0xc0008000000000000000] : Vector F80 2) 0
    (f80 0x3ffe8000000000000000),
  both "bool5" (#v[true, false, true, true, false] : Vector Bool 5) 1 true,
  both "bool16" (#v[true, false, true, true, false, true, false, false, false, false, false,
    false, false, false, false, true] : Vector Bool 16) 15 false,
  case "u8x3" (#v[1, 2, 3] : Vector (BitVec 8) 3) 2 0xff,
  case "u16x3" (#v[1, 0x8000, 3] : Vector (BitVec 16) 3) 0 0xbeef,
  case "u32x3" (#v[1, 2, 3] : Vector (BitVec 32) 3) 1 0xdeadbeef]

/-- The vector a probe line is about (`vector f80x2 …`, `lane f80x2 …`, `load u9x4 …`). -/
def lineVector (line : String) : String := ((line.splitOn " ").drop 1).headD ""

def main (args : List String) : IO UInt32 := do
  -- `--skip NAME`: a vector whose layout is a declared divergence of the file's Zig version
  -- (`f80x2` in 0.17.0, tests/roadmap/aarch64-abi/Model.lean); neither side's lines are compared.
  let (args, skip) := match args with
    | [path, "--skip", name] => ([path], some name)
    | _ => (args, none)
  let keep (line : String) : Bool := skip != some (lineVector line)
  let model := (cases.flatMap (·.1)).filter keep
  unless cases.all (·.2) do
    IO.eprintln "vector-layouts: a model image does not decode back to its vector, or a lane \
      store did not leave the image of `Vec.set`"
    return 1
  let [path] := args | do
    model.forM IO.println
    return 0
  let observed := (((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)).filter keep
  if observed == model then
    IO.println s!"vector-layouts: {model.length} model lines match {path}"
    return 0
  for (o, m) in observed.zip model do
    if o != m then IO.eprintln s!"probe: {o}\nmodel: {m}"
  if observed.length != model.length then
    IO.eprintln s!"probe has {observed.length} lines, model {model.length}"
  return 1
