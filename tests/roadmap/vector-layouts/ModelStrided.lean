import ZigLean.VecStride

/-! L09: the model's side of `probe_strided.zig`, the element-stride vector layout of the
self-hosted x86_64 backend at the baseline CPU. Prints the probe's lines from
`ZigLean/VecStride.lean` (`x86VecSize`/`x86VecAlign`, `Vec.stridedEnc` over the lane encodings of
that backend: `Zig.intEncExt` for an integer, the float encoding) and compares them with a
recorded probe output:

    lake env lean --run tests/roadmap/vector-layouts/ModelStrided.lean \
      tests/roadmap/vector-layouts/stage2-x86_64-linux.txt

It also checks at run time that each image decodes back to its vector and that a store of a
lane's bytes at its cell leaves the image of `Vec.set` (instances of `Vec.stridedEnc_lawful`
and `Vec.stridedEnc_set`). -/

open Zig

/-- The encoding of an integer vector is lawful at every lane width and count, and its size is
the backend's. -/
example (n w : Nat) (signed : Bool) :
    letI := intEncExt .little signed w
    @LawfulEnc (Vec (BitVec w) n) (Vec.stridedEnc n (x86VecAlign n (intSize w))) :=
  letI := intEncExt .little signed w
  haveI := intEncExt_lawful .little signed w
  Vec.stridedEnc_lawful n _
example (n w : Nat) (signed : Bool) :
    (@Vec.stridedEnc _ (intEncExt .little signed w) n (x86VecAlign n (intSize w))).size =
      x86VecSize n (intSize w) := rfl
/-- A store of lane 2's bytes at its cell leaves the image of the vector with lane 2 replaced. -/
example (v : Vec (BitVec 9) 4) (x : BitVec 9) :
    letI := intEncExt .little false 9
    (Vec.stridedEnc 4 16).encode (v.set 2 x) =
      writeBytes ((Vec.stridedEnc 4 16).encode v) (2 * 2) (Enc.encode x) :=
  letI := intEncExt .little false 9
  haveI := intEncExt_lawful .little false 9
  Vec.stridedEnc_set 16 v 2 x (fun y _ => LawfulEnc.size_encode y) (LawfulEnc.size_encode x)

def hex2 (x : BitVec 8) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  if s.length < 2 then "0" ++ s else s

def byteStr : Byte → String
  | .undef => "--"
  | .int x => hex2 x
  | .part _ x => hex2 x
  | _ => "??"

def image (bs : Array Byte) : String := String.join (bs.toList.map fun b => " " ++ byteStr b)

def hex (x : Nat) : String := String.ofList (Nat.toDigits 16 x)

def decoded {α : Type} [Enc α] (bs : Array Byte) : Option α :=
  match (Enc.decode bs : Result α).run with
  | some (.ok w) => some w
  | _ => none

/-- The probe lines of a vector of integer or float lanes with the lane encoding `enc`, and
whether the images decode back and the cell store leaves the image of `Vec.set`. -/
def case {α : Type} {n : Nat} [BEq α] (enc : Enc α) (bits : α → Nat) (name : String)
    (lanes : Vector α n) (i : Fin n) (x : α) : List String × Bool :=
  letI := enc
  let s := Enc.size α
  let align := x86VecAlign n s
  letI : Enc (Vec α n) := Vec.stridedEnc n align
  let size := Enc.size (Vec α n)
  let v : Vec α n := ⟨lanes⟩
  let w := v.set i x
  let j := (i.val + 1) % n
  let loaded := (decoded (α := α) ((Enc.encode v).extract (j * s) ((j + 1) * s))).map (hex ∘ bits)
  ([s!"vector {name} {size} {align}{image (Enc.encode v)}",
    s!"whole {name}{image (Enc.encode v)}",
    s!"lane {name} {i.val}{image (Enc.encode w)}",
    s!"load {name} {j} {loaded.getD "??"}",
    s!"cell {name} {i.val}{image (writeBytes (Array.replicate size (.int 0xa5)) (i * s) (Enc.encode x))}"],
    decoded (Enc.encode v) == some v && decoded (Enc.encode w) == some w &&
      writeBytes (Enc.encode v) (i * s) (Enc.encode x) == Enc.encode w)

def int {w n : Nat} (signed : Bool) :=
  case (α := BitVec w) (n := n) (intEncExt .little signed w) BitVec.toNat

def float {fmt : FloatFmt} {n : Nat} :=
  case (α := Float fmt) (n := n) inferInstance (·.bits.toNat)

/-- The probe lines of a `bool` vector of up to 64 lanes: the bit-packed encoding
(`x86BoolVec_eq`). -/
def boolCase {n : Nat} (name : String) (lanes : Vector Bool n) (i : Fin n) (x : Bool) :
    List String × Bool :=
  let v : Vec Bool n := ⟨lanes⟩
  let w := v.set i x
  let j := (i.val + 1) % n
  let loaded := (decoded (α := Vec Bool n) (Enc.encode v)).bind (·.lanes[j]?)
  ([s!"vector {name} {x86BoolVecSize n} {x86BoolVecAlign n}{image (Enc.encode v)}",
    s!"whole {name}{image (Enc.encode v)}",
    s!"lane {name} {i.val}{image (Enc.encode w)}",
    s!"load {name} {j} {(loaded.map fun b => hex b.toNat).getD "??"}"],
    decoded (Enc.encode v) == some v && decoded (Enc.encode w) == some w &&
      Enc.size (Vec Bool n) == x86BoolVecSize n && Enc.align (Vec Bool n) == x86BoolVecAlign n)

/-- The lane types of the probe's `layout` table with their bit sizes: an integer and a float
have the ABI size `intSize`. -/
def laneTypes : List (String × Nat) := [("u1", 1), ("u4", 4), ("u7", 7), ("u8", 8), ("u9", 9),
  ("i9", 9), ("u12", 12), ("u16", 16), ("u24", 24), ("u32", 32), ("u40", 40), ("u64", 64),
  ("u65", 65), ("u128", 128), ("f16", 16), ("f32", 32), ("f64", 64), ("f80", 80), ("f128", 128)]

def layouts : List String :=
  (laneTypes.flatMap fun (name, bits) => (List.range 41).map fun n =>
    s!"layout {name} {n} {x86VecSize n (intSize bits)} {x86VecAlign n (intSize bits)}") ++
  (List.range 41 ++ [63, 64, 65, 127, 128, 129, 255, 256, 257, 511, 512, 513]).map fun n =>
    s!"layout bool {n} {x86BoolVecSize n} {x86BoolVecAlign n}"

def f32 (bits : Nat) : Float .f32 := ⟨BitVec.ofNat 32 bits⟩
def f80 (bits : Nat) : F80 := ⟨BitVec.ofNat 80 bits⟩

def cases : List (List String × Bool) := [
  int false "u9x4" (#v[0x1ff, 0, 0x1ff, 1] : Vector (BitVec 9) 4) 2 0x0aa,
  int true "i9x2" (#v[-1, 1] : Vector (BitVec 9) 2) 1 (-2),
  int false "u12x3" (#v[0xabc, 0x123, 0xfff] : Vector (BitVec 12) 3) 0 0x555,
  int false "u4x4" (#v[1, 2, 3, 4] : Vector (BitVec 4) 4) 3 0xf,
  int false "u1x8" (#v[1, 0, 1, 0, 0, 0, 0, 1] : Vector (BitVec 1) 8) 6 1,
  int false "u24x2" (#v[0xabcdef, 0x123456] : Vector (BitVec 24) 2) 0 0x000001,
  int true "i24x3" (#v[-2, 0x123456, -0x800000] : Vector (BitVec 24) 3) 1 (-0x012346),
  int false "u40x2" (#v[0xaabbccddee, 0x1122334455] : Vector (BitVec 40) 2) 1 0x0102030405,
  int false "u8x3" (#v[1, 2, 3] : Vector (BitVec 8) 3) 2 0xff,
  int false "u16x3" (#v[1, 0x8000, 3] : Vector (BitVec 16) 3) 0 0xbeef,
  int false "u32x3" (#v[1, 2, 3] : Vector (BitVec 32) 3) 1 0xdeadbeef,
  int false "u64x3" (#v[1, 0x8000000000000000, 3] : Vector (BitVec 64) 3) 2 0x0123456789abcdef,
  -- 1.0, -2.0, 0.5 and 3.0 as IEEE single bits; 1.0, -2.0 and 0.5 as x87 extended bits.
  float "f32x3" (#v[f32 0x3f800000, f32 0xc0000000, f32 0x3f000000] : Vector (Float .f32) 3) 1
    (f32 0x40400000),
  float "f80x2" (#v[f80 0x3fff8000000000000000, f80 0xc0008000000000000000] : Vector F80 2) 0
    (f80 0x3ffe8000000000000000),
  boolCase "bool5" (#v[true, false, true, true, false] : Vector Bool 5) 1 true,
  boolCase "bool16" (#v[true, false, true, true, false, true, false, false, false, false, false,
    false, false, false, false, true] : Vector Bool 16) 15 false]

def main (args : List String) : IO UInt32 := do
  let model := layouts ++ cases.flatMap (·.1)
  unless cases.all (·.2) do
    IO.eprintln "vector-layouts: an element-stride image does not decode back to its vector, a \
      cell store did not leave the image of `Vec.set`, or a `bool` vector has another layout"
    return 1
  let [path] := args | do
    model.forM IO.println
    return 0
  let observed := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  if observed == model then
    IO.println s!"vector-layouts: {model.length} element-stride model lines match {path}"
    return 0
  for (o, m) in observed.zip model do
    if o != m then IO.eprintln s!"probe: {o}\nmodel: {m}"
  if observed.length != model.length then
    IO.eprintln s!"probe has {observed.length} lines, model {model.length}"
  return 1
