/-!
# Test-only runner: generated effect-contract asm wrappers on model memory (A01)

`harness.py` appends this after `Interp.lean` (A03's interpretation, with read-write and memory
operands) and the rebound wrappers (`AsmHarness.Wrappers`, the unchanged text of
`AsmEffects/Gen.lean`). Each memory check runs the wrapper on one 32-byte global block holding a
distinct byte pattern, then compares the whole block with the expected bytes: the declared
location holds the instruction's result and every other byte is unchanged (the frame). The
alias check passes one pointer for both `swapm` operands and expects `.unspecified`.

Every failure prints `MISMATCH wrapper <check> <input>`; the program exits 1 on any failure.
-/

namespace AsmHarness.Effects

open Zig

def pattern : Array Byte := Array.ofFn (n := 32) fun i => .int (BitVec.ofNat 8 (0xC0 + i.val))

def mem (bytes : Array Byte) : Mem := Mem.ofGlobals [(bytes, 8, .global)]

def at0 (off : Nat) : Ptr := ⟨some 0, off⟩

/-- `bytes` with the little-endian encoding of `v` at `off`. -/
def put {w : Nat} [Enc (BitVec w)] (bytes : Array Byte) (off : Nat) (v : BitVec w) : Array Byte :=
  writeBytes bytes off (Enc.encode v)

/-- The bytes of block 0 after a successful run, or a description of the outcome. -/
def after (r : Result (Unit × Mem)) : Except String (Array Byte) :=
  match r.run with
  | some (.ok (_, m)) => match m.blocks[0]? with
    | some b => .ok b.bytes
    | none => .error "no block"
  | some (.error e) => .error s!"error {repr e}"
  | none => .error "diverged"

def lcg (seed count : Nat) : List Nat :=
  (List.range count).foldl (init := ([], seed)) (fun (acc, s) _ =>
    let s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    (acc ++ [s], s)) |>.1

def values32 : List Nat :=
  [0, 1, 0x7F, 0xFF, 0x12345678, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFE, 0xFFFFFFFF] ++
    (lcg 0xA01 120).map (· % 2 ^ 32)

def values64 : List Nat :=
  [0, 1, 2 ^ 32, 2 ^ 63, 2 ^ 64 - 1] ++ lcg 0xA011 120

def pairs32 : List (Nat × Nat) := (values32.zip values32.reverse) ++ [(5, 5), (0, 0xFFFFFFFF)]

def check (fn : String) (inputs : List α) (render : α → String) (ok : α → Bool)
    (detail : α → String) : List String :=
  inputs.filterMap fun x =>
    if ok x then none else some s!"MISMATCH wrapper {fn} {render x}: {detail x}"

def describe (r : Except String (Array Byte)) : String :=
  match r with
  | .ok bs => s!"bytes {repr (bs.toList.take 32)}"
  | .error e => e

def memCheck (fn : String) (inputs : List α) [ToString α] (run : α → Result (Unit × Mem))
    (expected : α → Array Byte) : List String :=
  check fn inputs toString (fun x => after (run x) == .ok (expected x)) (fun x => describe (after (run x)))

def b32 := BitVec.ofNat 32
def b64 := BitVec.ofNat 64

def failures : List String :=
  -- `+m` (`incl`) at offset 8: that u32 is incremented, every other byte is unchanged.
  memCheck "incm" values32
    (fun x => (Wrappers.incm (at0 8)).run (mem (put pattern 8 (b32 x))))
    (fun x => put pattern 8 (b32 x + 1)) ++
  -- `=m` (`movq`) at offset 16.
  memCheck "setm" values64
    (fun v => (Wrappers.setm (at0 16) (b64 v)).run (mem pattern))
    (fun v => put pattern 16 (b64 v)) ++
  -- Two `+m` operands (`xchg` through `eax`) at offsets 4 and 20: the values swap.
  memCheck "swapm" pairs32
    (fun (x, y) => (Wrappers.swapm (at0 4) (at0 20)).run (mem (put (put pattern 4 (b32 x)) 20 (b32 y))))
    (fun (x, y) => put (put pattern 4 (b32 y)) 20 (b32 x)) ++
  -- One pointer for both operands: `.unspecified`, whatever the instruction order would give.
  check "swapm-alias" values32 toString
    (fun x => match ((Wrappers.swapm (at0 4) (at0 4)).run (mem (put pattern 4 (b32 x)))).run with
      | some (.error .unspecified) => true
      | _ => false)
    (fun x => describe (after ((Wrappers.swapm (at0 4) (at0 4)).run (mem (put pattern 4 (b32 x)))))) ++
  -- `+r` and `+m` on locals.
  check "addr" (values64.zip values64.reverse) toString
    (fun (x, v) => (Wrappers.addr (b64 x) (b64 v)).run == some (.ok (b64 x + b64 v)))
    (fun _ => "not x + v") ++
  check "incLocal" values32 toString
    (fun x => (Wrappers.incLocal (b32 x)).run == some (.ok (b32 x + 1))) (fun _ => "not x + 1") ++
  check "barrier" [()] (fun _ => "()") (fun _ => Wrappers.barrier.run == some (.ok ()))
    (fun _ => "not pure ()")

def main : IO UInt32 := do
  let bad := failures
  for line in bad.take 20 do IO.println line
  if bad.isEmpty then
    IO.println s!"PASS asm-wrappers effects {values32.length} {values64.length} {pairs32.length}"
    return 0
  IO.println s!"FAIL asm-wrappers: {bad.length} failures"
  return 1

end AsmHarness.Effects

def main : IO UInt32 := AsmHarness.Effects.main
