import ZigLean

/-! Runtime regression for docs/illegal-behavior.md: each op's model checks its own
illegal-behaviour precondition and throws `.illegal`, with or without a Sema check before it.
`lake env lean --run tests/roadmap/illegal-behavior/Runtime.lean` exits 1 on the first failure;
`check.sh`'s mutants must each make one of these checks fail. -/

open Zig

namespace IllegalRuntime

/-- `none` for a result, the error otherwise. -/
def errOf {α : Type} (r : Result α) : Option Error :=
  match r.run with
  | some (.error e) => some e
  | _ => none

def memErr {α : Type} (x : MemM α) : Option Error := errOf ((x.run {}).map Prod.fst)

def f64 (bits : Nat) : F64 := Zig.Float.ofBits (BitVec.ofNat 64 bits)
def one : F64 := f64 0x3FF0000000000000
def two : F64 := f64 0x4000000000000000
def three : F64 := f64 0x4008000000000000
def six : F64 := f64 0x4018000000000000
def tiny : F64 := f64 1
def zero : F64 := f64 0
def inf : F64 := f64 0x7FF0000000000000
def nan : F64 := f64 0x7FF8000000000000

def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"illegal-behavior runtime: {name}")

def floatCases : IO Unit := do
  -- `@divExact` with safety: the truncated quotient, `.illegal` when inexact, NaN left to Sema.
  check "6/3 safe" (((Zig.Float.divExactTrunc six three (Zig.Float.div six three)).run.bind
    Except.toOption).map Zig.Float.bits == some two.bits)
  check "2^-1074/1 safe" (errOf (Zig.Float.divExactTrunc tiny one (Zig.Float.div tiny one)) == some .illegal)
  check "3/2 safe" (errOf (Zig.Float.divExactTrunc three two (Zig.Float.div three two)) == some .illegal)
  check "1/0 safe" (errOf (Zig.Float.divExactTrunc one zero (Zig.Float.div one zero)) == some .illegal)
  check "0/0 safe passes NaN" (errOf (Zig.Float.divExactTrunc zero zero (Zig.Float.div zero zero)) == none)
  check "inf/2 safe" (errOf (Zig.Float.divExactTrunc inf two (Zig.Float.div inf two)) == none)
  -- `@divExact` without safety: NaN too.
  check "6/3 unsafe" (errOf (Zig.Float.divExactChk six three (Zig.Float.div six three)) == none)
  check "2^-1074/1 unsafe" (errOf (Zig.Float.divExactChk tiny one (Zig.Float.div tiny one)) == some .illegal)
  check "0/0 unsafe" (errOf (Zig.Float.divExactChk zero zero (Zig.Float.div zero zero)) == some .illegal)
  -- `@intFromFloat` of NaN: unchecked with or without safety.
  check "NaN to int safe" (errOf (Zig.Float.toInt true 32 true nan) == some .illegal)
  check "NaN to int unsafe" (errOf (Zig.Float.toInt true 32 false nan) == some .illegal)
  check "inf to int safe" (errOf (Zig.Float.toInt true 32 true inf) == some .overflow)
  check "inf to int unsafe" (errOf (Zig.Float.toInt true 32 false inf) == some .illegal)
  check "2^31 to int unsafe" (errOf (Zig.Float.toInt true 32 false (f64 0x41E0000000000000)) == some .illegal)

def intCases : IO Unit := do
  check "divExact 7/2" (errOf (divExact true (7 : BitVec 32) 2) == some .illegal)
  check "divExact /0" (errOf (divExact true (7 : BitVec 32) 0) == some .illegal)
  check "divExact minInt/-1" (errOf (divExact true (BitVec.intMin 32) (-1)) == some .illegal)
  check "divExact 6/3" (errOf (divExact true (6 : BitVec 32) 3) == none)
  check "shlExact lost bit" (errOf (shlExact false (0x80000000 : BitVec 32) (1 : BitVec 5)) == some .illegal)
  check "shlExact 1<<31" (errOf (shlExact false (1 : BitVec 32) (31 : BitVec 5)) == none)
  check "shlChk u24 by 24" (errOf (shlChk (1 : BitVec 24) (24 : BitVec 5)) == some .illegal)
  check "shlChk u24 by 23" (errOf (shlChk (1 : BitVec 24) (23 : BitVec 5)) == none)
  check "shrChk u24 by 31" (errOf (shrChk false (1 : BitVec 24) (31 : BitVec 5)) == some .illegal)
  check "shrExact u24 by 24" (errOf (shrExact false (0 : BitVec 24) (24 : BitVec 5)) == some .illegal)
  check "shrExact lost bit" (errOf (shrExact false (1 : BitVec 24) (1 : BitVec 5)) == some .overflow)

def memCases : IO Unit := do
  let overlap : MemM Unit := do
    let p ← alloc .heap 8 1
    memset (α := BitVec 8) 1 p 8 (some 0)
    memcpy 1 1 1 (p.add 1) p 4 4
  check "memcpy overlap" (memErr overlap == some .illegal)
  let disjoint : MemM Unit := do
    let p ← alloc .heap 8 1
    memset (α := BitVec 8) 1 p 8 (some 0)
    memcpy 1 1 1 (p.add 4) p 4 4
  check "memcpy disjoint" (memErr disjoint == none)
  let lenMismatch : MemM Unit := do
    let p ← alloc .heap 8 1
    let q ← alloc .heap 8 1
    memset (α := BitVec 8) 1 q 8 (some 0)
    memcpy 1 1 1 p q 4 5
  check "memcpy count mismatch" (memErr lenMismatch == some .illegal)
  let moveOverlap : MemM Unit := do
    let p ← alloc .heap 8 1
    memset (α := BitVec 8) 1 p 8 (some 0)
    memmove 1 1 1 (p.add 1) p 4
  check "memmove overlap" (memErr moveOverlap == none)
  -- A slice shorter than its block: a read past the slice but inside the block.
  let past : MemM (BitVec 8) := do
    let p ← alloc .heap 8 1
    memset (α := BitVec 8) 1 p 8 (some 7)
    checkIndex ⟨p, 2⟩ 5 >>= fun _ => load (BitVec 8) 1 (p.elem 1 5)
  check "slice item past length" (memErr past == some .illegal)
  check "ptrFromInt 0" (memErr (checkAddr 4 true 0) == some .illegal)
  check "ptrFromInt misaligned" (memErr (checkAddr 4 true 6) == some .illegal)
  check "ptrFromInt 0 allowzero" (memErr (checkAddr 4 false 0) == none)
  let misaligned : MemM Unit := do
    let p ← alloc .heap 8 4
    checkAlign 4 (p.add 1)
  check "alignCast misaligned" (memErr misaligned == some .illegal)
  let aligned : MemM Unit := do
    let p ← alloc .heap 8 4
    checkAlign 4 (p.add 4)
  check "alignCast aligned" (memErr aligned == none)

end IllegalRuntime

def main : IO Unit := do
  IllegalRuntime.floatCases
  IllegalRuntime.intCases
  IllegalRuntime.memCases
  IO.println "illegal-behavior runtime: all cases pass"
