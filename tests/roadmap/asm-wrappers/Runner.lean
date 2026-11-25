/-!
# Test-only runner: generated asm wrappers against Zig source semantics (A03)

`harness.py` appends this after `Interp.lean`, the generated module (`AsmHarness.Wrappers`), the
interpreted counterparts (`AsmHarness.Cross`) and the sampled inputs (`AsmHarness.Inputs`).

Two checks:

* wrapper: the real generated wrapper (`AsmHarness.Wrappers.<fn>`, the unchanged text of
  `Proofs/Asm/Gen.lean`, with its `airIsa_<hash>` definitions over the instruction model) returns
  `Oracle.<fn>`, the function `examples/asm/asm.zig` defines. For `divmod` the remainder reaches
  the result only through the wrapper's store to the local `rem`, so this also checks the
  wrapper's memory plumbing.
* model: each `airIsa_<hash>` returns what the interpretation of its template text returns
  (`Cross.failures`). This is evidence for premise ASM-07 from a second implementation, not a
  premise of any theorem.

Every failure prints `MISMATCH <check> <fn> <input>`; the program exits 1 on any failure.
-/

namespace AsmHarness.Oracle

/-- `@byteSwap`, by byte extraction. -/
def bswap32 (x : BitVec 32) : BitVec 32 :=
  (x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8).setWidth 32

/-- `@popCount`, by binary digits. -/
def popcnt64 (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((Nat.toDigits 2 x.toNat).count '1')

/-- `@clz`, by scanning from the top bit. -/
def lzcnt64 (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 64).reverse.takeWhile (fun i => !x.getLsbD i)).length

/-- `(@as(u64, a % b) << 32) | (a / b)`. -/
def divmod (a b : BitVec 32) : BitVec 64 :=
  (a % b).setWidth 64 <<< 32 ||| (a / b).setWidth 64

end AsmHarness.Oracle

namespace AsmHarness.Runner

open AsmHarness

def returns (r : Zig.Result (BitVec w)) (expected : BitVec w) : Bool :=
  match r.run with
  | some (.ok v) => v == expected
  | _ => false

def describe (r : Zig.Result (BitVec w)) : String :=
  match r.run with
  | some (.ok v) => s!"ok {v.toNat}"
  | some (.error _) => "error"
  | none => "diverged"

/-- Failure lines of one check over `inputs`. -/
def check (kind fn : String) (inputs : List α) (render : α → String) (ok : α → Bool)
    (detail : α → String) : List String :=
  inputs.filterMap fun x =>
    if ok x then none else some s!"MISMATCH {kind} {fn} {render x}: {detail x}"

/-- The generated wrapper `call` returns `oracle` on every input. -/
def wrapper [ToString α] (fn : String) (inputs : List α) (call : α → Zig.Result (BitVec w))
    (oracle : α → BitVec w) : List String :=
  check "wrapper" fn inputs toString (fun x => returns (call x) (oracle x)) (describe ∘ call)

def failures : List String :=
  let b32 := BitVec.ofNat 32
  let b64 := BitVec.ofNat 64
  wrapper "bswap32" Inputs.bswap32 (Wrappers.bswap32 ∘ b32) (Oracle.bswap32 ∘ b32) ++
  wrapper "popcnt64" Inputs.popcnt64 (Wrappers.popcnt64 ∘ b64) (Oracle.popcnt64 ∘ b64) ++
  wrapper "lzcnt64" Inputs.lzcnt64 (Wrappers.lzcnt64 ∘ b64) (Oracle.lzcnt64 ∘ b64) ++
  wrapper "divmod" Inputs.divmod (fun (a, b) => Wrappers.divmod (b32 a) (b32 b))
    (fun (a, b) => Oracle.divmod (b32 a) (b32 b)) ++
  -- Each `airIsa_<hash>` against the interpretation of its template text.
  Cross.failures

def main : IO UInt32 := do
  let counts := [("bswap32", Inputs.bswap32.length), ("popcnt64", Inputs.popcnt64.length),
    ("lzcnt64", Inputs.lzcnt64.length), ("divmod", Inputs.divmod.length)]
  let bad := failures
  for line in bad.take 20 do IO.println line
  if bad.isEmpty then
    IO.println s!"PASS asm-wrappers {counts}"
    return 0
  IO.println s!"FAIL asm-wrappers: {bad.length} failures"
  return 1

end AsmHarness.Runner

def main : IO UInt32 := AsmHarness.Runner.main
