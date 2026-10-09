import Gen

/-! The generated functions of `ib.zig` (`Gen.lean`) on the input classes of `native.zig`: each
row is illegal behaviour, and the model gives `.illegal` (or, for a NaN `@divExact` quotient
under safety, the safety check's `.panic`). A legal control row per function returns a value.
`check.sh` runs this file on the retained translation and on each mutant of `mutations.py`; a
failing row raises `illegal-behavior case …`. -/

open Zig IllegalBehavior

namespace IllegalCases

def errOf {α : Type} (r : Result α) : Option Error :=
  match r.run with
  | some (.error e) => some e
  | _ => none

def memErr {α : Type} (x : MemM α) : Option Error := errOf ((x.run mem0).map Prod.fst)

def f64 (bits : Nat) : F64 := Zig.Float.ofBits (BitVec.ofNat 64 bits)
def one : F64 := f64 0x3FF0000000000000
def two : F64 := f64 0x4000000000000000
def three : F64 := f64 0x4008000000000000
def six : F64 := f64 0x4018000000000000
def tiny : F64 := f64 1
def zero : F64 := f64 0
def nan : F64 := f64 0x7FF8000000000000

def check (name : String) (got : Option Error) (want : Option Error) : IO Unit :=
  unless got == want do
    throw (IO.userError s!"illegal-behavior case {name}: got {repr got}, want {repr want}")

def vec2 (a b : F64) : Vec F64 2 := ⟨#v[a, b]⟩

/-- A heap buffer of `n` bytes `0, 1, …`, as a slice. -/
def buffer (n : Nat) : MemM Slice := do
  let p ← alloc .heap n 1
  for i in [0:n] do store 1 (p.add i) (BitVec.ofNat 8 i)
  pure ⟨p, BitVec.ofNat 64 n⟩

def cases : IO Unit := do
  check "divExactSafe 6/3" (errOf (divExactSafe six three)) none
  check "divExactSafe tiny/1" (errOf (divExactSafe tiny one)) (some .illegal)
  check "divExactSafe 3/2" (errOf (divExactSafe three two)) (some .illegal)
  check "divExactSafe 1/0" (errOf (divExactSafe one zero)) (some .illegal)
  check "divExactSafe 0/0 (safety check)" (errOf (divExactSafe zero zero)) (some .panic)
  check "divExactUnsafe 6/3" (errOf (divExactUnsafe six three)) none
  check "divExactUnsafe tiny/1" (errOf (divExactUnsafe tiny one)) (some .illegal)
  check "divExactUnsafe 3/2" (errOf (divExactUnsafe three two)) (some .illegal)
  check "divExactUnsafe 0/0" (errOf (divExactUnsafe zero zero)) (some .illegal)
  check "divExactLanes" (errOf (divExactLanes (vec2 tiny three) (vec2 one two))) (some .illegal)
  check "divExactLanes exact" (errOf (divExactLanes (vec2 six six) (vec2 three two))) none
  check "divExactIntUnsafe 7/2" (errOf (divExactIntUnsafe 7 2)) (some .illegal)
  check "divExactIntUnsafe 6/2" (errOf (divExactIntUnsafe 6 2)) none
  check "shlExactUnsafe 0x80000000<<1" (errOf (shlExactUnsafe 0x80000000 1)) (some .illegal)
  check "shlExactUnsafe 1<<31" (errOf (shlExactUnsafe 1 31)) none
  check "shl24Unsafe 1<<24" (errOf (shl24Unsafe 1 24)) (some .illegal)
  check "shl24Unsafe 1<<23" (errOf (shl24Unsafe 1 23)) none
  check "shr24Unsafe 0x800000>>31" (errOf (shr24Unsafe 0x800000 31)) (some .illegal)
  check "toIntSafe nan" (errOf (toIntSafe nan)) (some .illegal)
  check "toIntUnsafe nan" (errOf (toIntUnsafe nan)) (some .illegal)
  check "toIntUnsafe 2^31" (errOf (toIntUnsafe (f64 0x41E0000000000000))) (some .illegal)
  check "toIntUnsafe 6" (errOf (toIntUnsafe six)) none
  check "copyOverlapUnsafe 4" (memErr (do let s ← buffer 8; copyOverlapUnsafe s.ptr 4)) (some .illegal)
  check "copyLenUnsafe 4/5"
    (memErr (do let d ← buffer 4; let s ← buffer 5; copyLenUnsafe d s)) (some .illegal)
  check "copyLenUnsafe 4/4"
    (memErr (do let d ← buffer 4; let s ← buffer 4; copyLenUnsafe d s)) none
  let item (i : Nat) : MemM (BitVec 32) := do
    let items ← alloc .heap 16 4
    for k in [0:4] do store 4 (items.elem 4 (BitVec.ofNat 64 k)) (BitVec.ofNat 32 k)
    let sl ← alloc .heap 16 8
    store 8 sl (⟨items, 2⟩ : Slice)
    itemUnsafe sl (BitVec.ofNat 64 i)
  check "itemUnsafe past length, inside block" (memErr (item 3)) (some .illegal)
  check "itemUnsafe in range" (memErr (item 1)) none

end IllegalCases

def main : IO Unit := do
  IllegalCases.cases
  IO.println "illegal-behavior cases: all rows match"
