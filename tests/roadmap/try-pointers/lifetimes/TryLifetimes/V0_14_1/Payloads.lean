import TryLifetimes.V0_14_1.PayloadsGen
import ZigLean.Sep.Full.AutoAll

/-! L04: the alias and cleanup rules of pointer try for every payload shape (`try_payloads.zig`),
on the translation of the retained export of one Zig version (`TryLifetimes.V0_14_1.PayloadsGen`;
written for Zig 0.17.1, the modules of 0.14.1, 0.15.2 and 0.16.0 are this one with the version
renamed: `check.sh`, `scripts/fixtures.py instance`).

The one-byte rules are in `../../../TryPointers/AliasProofs.lean` and
`../../../aliases/TryAliases/Proofs.lean`. Here the same statements hold for a payload of two,
four and eight bytes, for a struct payload (its `LawfulEnc` is derived by `fsym`) and for a union
whose error set is `anyerror` (the operations without a declared domain):

* `writeAlias*`: both pointer-try results address the same payload; the value written through the
  first is read through the second and left in the union. An error writes nothing.
* `cleanup*`: the result is read before the cleanup runs; success runs only the `defer`, an error
  runs the `errdefer` and the `defer` and leaves the union unchanged. With one counter for both
  cleanup pointers an error increments it twice.
* `resetOnError*`: the error name is read before the `errdefer` overwrites the whole union with
  `.ok fallback`; success returns the payload address and leaves the union unchanged.

Every theorem is a total full-state triple walked by `fsym` on each shape of the union
(`ZigLean/Sep/Full/Try.lean`, `Typed.lean`); nothing here is specific to a payload type. `main`
checks the same functions on concrete memories against the values that the native tests of
`try_payloads.zig` assert. -/

open Zig
open scoped Zig
open Zig.Full Zig.Full.FAssn
open TryLifetimes.V0_14_1.Payloads

namespace TryLifetimes.V0_14_1.PayloadRules

/-- The finite domain that the AIR declares for `Failure`. -/
abbrev domain : ErrorDomain := ⟨#["Bad", "Other"], by decide, by decide⟩

/-- A present error belongs to the declared domain. -/
def Admitted {α : Type} (u : Except ErrName α) : Prop :=
  ∀ e, u = .error e → domain.names.contains e = true

theorem Admitted.all {α : Type} {u : Except ErrName α} (h : Admitted u) :
    (errTagOf u).all domain.names.contains = true := by
  cases u with
  | ok => rfl
  | error e => exact h e rfl

/-- The union after `resetOnError p f`: overwritten with `.ok f` on the error path only. -/
def resetAfter {α : Type} (f : α) : Except ErrName α → Except ErrName α
  | .ok x => .ok x
  | .error _ => .ok f

/-! ## Two pointer-try results alias -/

theorem writeAlias16_owned (p : Ptr) (u : Except ErrName (BitVec 16)) (y : BitVec 16)
    (hdom : Admitted u) :
    FTotalTriple (up (pts p 2 u)) (writeAlias16 p y)
      (fun r => ⟪r = writeView y u⟫ ⋆ up (pts p 2 (writeView y u))) := by
  have hd := hdom.all
  unfold writeAlias16; cases u <;> fsym

theorem writeAlias32_owned (p : Ptr) (u : Except ErrName (BitVec 32)) (y : BitVec 32)
    (hdom : Admitted u) :
    FTotalTriple (up (pts p 4 u)) (writeAlias32 p y)
      (fun r => ⟪r = writeView y u⟫ ⋆ up (pts p 4 (writeView y u))) := by
  have hd := hdom.all
  unfold writeAlias32; cases u <;> fsym

theorem writeAlias64_owned (p : Ptr) (u : Except ErrName (BitVec 64)) (y : BitVec 64)
    (hdom : Admitted u) :
    FTotalTriple (up (pts p 8 u)) (writeAlias64 p y)
      (fun r => ⟪r = writeView y u⟫ ⋆ up (pts p 8 (writeView y u))) := by
  have hd := hdom.all
  unfold writeAlias64; cases u <;> fsym

theorem writeAliasPair_owned (p : Ptr) (u : Except ErrName Pair) (y : Pair) (hdom : Admitted u) :
    FTotalTriple (up (pts p 4 u)) (writeAliasPair p y)
      (fun r => ⟪r = writeView y u⟫ ⋆ up (pts p 4 (writeView y u))) := by
  have hd := hdom.all
  unfold writeAliasPair; cases u <;> fsym

/-- `anyerror`: no declared domain, so no premise on the error. -/
theorem writeAliasAny_owned (p : Ptr) (u : Except ErrName (BitVec 32)) (y : BitVec 32) :
    FTotalTriple (up (pts p 4 u)) (writeAliasAny p y)
      (fun r => ⟪r = writeView y u⟫ ⋆ up (pts p 4 (writeView y u))) := by
  unfold writeAliasAny; cases u <;> fsym

/-- The first alias is cast to `*i16`: the same typed access, so the same rule. -/
theorem writeAliasSigned_owned (p : Ptr) (u : Except ErrName (BitVec 16)) (y : BitVec 16)
    (hdom : Admitted u) :
    FTotalTriple (up (pts p 2 u)) (writeAliasSigned p y)
      (fun r => ⟪r = writeView y u⟫ ⋆ up (pts p 2 (writeView y u))) := by
  have hd := hdom.all
  unfold writeAliasSigned; cases u <;> fsym

/-! ## Cleanup paths: distinct counters -/

theorem cleanup16_owned (p o e : Ptr) (u : Except ErrName (BitVec 16)) (c k : BitVec 32)
    (hdom : Admitted u) (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts p 2 u) ⋆ (up (pts o 4 c) ⋆ up (pts e 4 k))) (cleanup16 p o e)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 2 u) ⋆ (up (pts o 4 (c + 1)) ⋆
          up (pts e 4 (match u with | .ok _ => k | .error _ => k + 1))))) := by
  have hd := hdom.all
  unfold cleanup16; cases u <;> fsym

theorem cleanup32_owned (p o e : Ptr) (u : Except ErrName (BitVec 32)) (c k : BitVec 32)
    (hdom : Admitted u) (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts p 4 u) ⋆ (up (pts o 4 c) ⋆ up (pts e 4 k))) (cleanup32 p o e)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 4 u) ⋆ (up (pts o 4 (c + 1)) ⋆
          up (pts e 4 (match u with | .ok _ => k | .error _ => k + 1))))) := by
  have hd := hdom.all
  unfold cleanup32; cases u <;> fsym

theorem cleanup64_owned (p o e : Ptr) (u : Except ErrName (BitVec 64)) (c k : BitVec 32)
    (hdom : Admitted u) (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts p 8 u) ⋆ (up (pts o 4 c) ⋆ up (pts e 4 k))) (cleanup64 p o e)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 8 u) ⋆ (up (pts o 4 (c + 1)) ⋆
          up (pts e 4 (match u with | .ok _ => k | .error _ => k + 1))))) := by
  have hd := hdom.all
  unfold cleanup64; cases u <;> fsym

theorem cleanupPair_owned (p o e : Ptr) (u : Except ErrName Pair) (c k : BitVec 32)
    (hdom : Admitted u) (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts p 4 u) ⋆ (up (pts o 4 c) ⋆ up (pts e 4 k))) (cleanupPair p o e)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 4 u) ⋆ (up (pts o 4 (c + 1)) ⋆
          up (pts e 4 (match u with | .ok _ => k | .error _ => k + 1))))) := by
  have hd := hdom.all
  unfold cleanupPair; cases u <;> fsym

theorem cleanupAny_owned (p o e : Ptr) (u : Except ErrName (BitVec 32)) (c k : BitVec 32)
    (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts p 4 u) ⋆ (up (pts o 4 c) ⋆ up (pts e 4 k))) (cleanupAny p o e)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 4 u) ⋆ (up (pts o 4 (c + 1)) ⋆
          up (pts e 4 (match u with | .ok _ => k | .error _ => k + 1))))) := by
  unfold cleanupAny; cases u <;> fsym

/-! ## Cleanup paths: one counter for both cleanup pointers -/

theorem cleanup16_shared_owned (p c : Ptr) (u : Except ErrName (BitVec 16)) (k : BitVec 32)
    (hdom : Admitted u) (hk : k.toNat + 2 < 2 ^ 32) :
    FTotalTriple (up (pts p 2 u) ⋆ up (pts c 4 k)) (cleanup16 p c c)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 2 u) ⋆ up (pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1)))) := by
  have hd := hdom.all
  unfold cleanup16; cases u <;> fsym

theorem cleanup32_shared_owned (p c : Ptr) (u : Except ErrName (BitVec 32)) (k : BitVec 32)
    (hdom : Admitted u) (hk : k.toNat + 2 < 2 ^ 32) :
    FTotalTriple (up (pts p 4 u) ⋆ up (pts c 4 k)) (cleanup32 p c c)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 4 u) ⋆ up (pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1)))) := by
  have hd := hdom.all
  unfold cleanup32; cases u <;> fsym

theorem cleanup64_shared_owned (p c : Ptr) (u : Except ErrName (BitVec 64)) (k : BitVec 32)
    (hdom : Admitted u) (hk : k.toNat + 2 < 2 ^ 32) :
    FTotalTriple (up (pts p 8 u) ⋆ up (pts c 4 k)) (cleanup64 p c c)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 8 u) ⋆ up (pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1)))) := by
  have hd := hdom.all
  unfold cleanup64; cases u <;> fsym

theorem cleanupPair_shared_owned (p c : Ptr) (u : Except ErrName Pair) (k : BitVec 32)
    (hdom : Admitted u) (hk : k.toNat + 2 < 2 ^ 32) :
    FTotalTriple (up (pts p 4 u) ⋆ up (pts c 4 k)) (cleanupPair p c c)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 4 u) ⋆ up (pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1)))) := by
  have hd := hdom.all
  unfold cleanupPair; cases u <;> fsym

theorem cleanupAny_shared_owned (p c : Ptr) (u : Except ErrName (BitVec 32)) (k : BitVec 32)
    (hk : k.toNat + 2 < 2 ^ 32) :
    FTotalTriple (up (pts p 4 u) ⋆ up (pts c 4 k)) (cleanupAny p c c)
      (fun r => ⟪r = u⟫ ⋆
        (up (pts p 4 u) ⋆ up (pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1)))) := by
  unfold cleanupAny; cases u <;> fsym

/-! ## `errdefer` rewriting the whole addressed union -/

theorem resetOnError16_owned (p : Ptr) (u : Except ErrName (BitVec 16)) (f : BitVec 16)
    (hdom : Admitted u) :
    FTotalTriple (up (pts p 2 u)) (resetOnError16 p f)
      (fun r => ⟪r = tryView (BitVec 16) p u⟫ ⋆ up (pts p 2 (resetAfter f u))) := by
  have hd := hdom.all
  unfold resetOnError16; cases u <;> fsym

theorem resetOnError32_owned (p : Ptr) (u : Except ErrName (BitVec 32)) (f : BitVec 32)
    (hdom : Admitted u) :
    FTotalTriple (up (pts p 4 u)) (resetOnError32 p f)
      (fun r => ⟪r = tryView (BitVec 32) p u⟫ ⋆ up (pts p 4 (resetAfter f u))) := by
  have hd := hdom.all
  unfold resetOnError32; cases u <;> fsym

theorem resetOnError64_owned (p : Ptr) (u : Except ErrName (BitVec 64)) (f : BitVec 64)
    (hdom : Admitted u) :
    FTotalTriple (up (pts p 8 u)) (resetOnError64 p f)
      (fun r => ⟪r = tryView (BitVec 64) p u⟫ ⋆ up (pts p 8 (resetAfter f u))) := by
  have hd := hdom.all
  unfold resetOnError64; cases u <;> fsym

theorem resetOnErrorPair_owned (p : Ptr) (u : Except ErrName Pair) (f : Pair) (hdom : Admitted u) :
    FTotalTriple (up (pts p 4 u)) (resetOnErrorPair p f)
      (fun r => ⟪r = tryView Pair p u⟫ ⋆ up (pts p 4 (resetAfter f u))) := by
  have hd := hdom.all
  unfold resetOnErrorPair; cases u <;> fsym

/-! ## The native tests' observations (the differential side) -/

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def value {α : Type} (x : MemM α) : Option (Except Error α) :=
  (x.run (mem0 .fresh)).run.map (·.map Prod.fst)

private def cell {α : Type} [Enc α] (a : Nat) (v : Except ErrName α) : MemM Ptr := do
  let p ← alloc .heap (Enc.size (Except ErrName α)) a
  store a p v
  pure p

private def counter (v : BitVec 32) : MemM Ptr := do
  let p ← alloc .heap 4 4
  store 4 p v
  pure p

/-- The result of `f` on a union holding `v`, and the union afterwards. -/
private def aliased {α : Type} [Enc α] (a : Nat) (f : Ptr → α → MemM (Except ErrName α))
    (v : Except ErrName α) (y : α) : MemM (Except ErrName α × Except ErrName α) := do
  let c ← cell a v
  let r ← f c y
  pure (r, ← load (Except ErrName α) a c)

/-- The result of `f`, the union afterwards and both counters (one counter when `shared`). -/
private def cleaned {α : Type} [Enc α] (a : Nat) (f : Ptr → Ptr → Ptr → MemM (Except ErrName α))
    (v : Except ErrName α) (shared : Bool) :
    MemM (Except ErrName α × Except ErrName α × BitVec 32 × BitVec 32) := do
  let c ← cell a v
  let o ← counter 0
  let e ← if shared then pure o else counter 0
  let r ← f c o e
  pure (r, ← load (Except ErrName α) a c, ← load (BitVec 32) 4 o, ← load (BitVec 32) 4 e)

/-- Whether `f` returned the payload address (or its error), and the union afterwards. -/
private def reset {α : Type} [Enc α] (a : Nat) (f : Ptr → α → MemM (Except ErrName Ptr))
    (v : Except ErrName α) (y : α) : MemM (Except ErrName Bool × Except ErrName α) := do
  let c ← cell a v
  let r ← f c y
  pure (r.map (· == errPayloadPtr α c), ← load (Except ErrName α) a c)

/-- One payload shape: the three functions on a success and on an error. -/
private def shape {α : Type} [Enc α] [DecidableEq α] (name : String) (a : Nat) (x y : α)
    (alias : Option (Ptr → α → MemM (Except ErrName α)))
    (cleanup : Ptr → Ptr → Ptr → MemM (Except ErrName α))
    (resetOn : Option (Ptr → α → MemM (Except ErrName Ptr))) : IO Unit := do
  if let some f := alias then
    require (value (aliased a f (.ok x) y) == some (.ok (.ok y, .ok y))) s!"{name}: alias write"
    require (value (aliased a f (.error "Other") y) == some (.ok (.error "Other", .error "Other")))
      s!"{name}: alias error"
  require (value (cleaned a cleanup (.ok x) false) == some (.ok (.ok x, .ok x, 1, 0)))
    s!"{name}: cleanup success"
  require (value (cleaned a cleanup (.error "Bad") false)
    == some (.ok (.error "Bad", .error "Bad", 1, 1))) s!"{name}: cleanup error"
  require (value (cleaned a cleanup (.ok x) true) == some (.ok (.ok x, .ok x, 1, 1)))
    s!"{name}: shared cleanup success"
  require (value (cleaned a cleanup (.error "Bad") true)
    == some (.ok (.error "Bad", .error "Bad", 2, 2))) s!"{name}: shared cleanup error"
  if let some f := resetOn then
    require (value (reset a f (.ok x) y) == some (.ok (.ok true, .ok x))) s!"{name}: reset success"
    require (value (reset a f (.error "Bad") y) == some (.ok (.error "Bad", .ok y)))
      s!"{name}: reset error"

def main : IO Unit := do
  shape "u16" 2 (0x0102 : BitVec 16) 0xa1b2 (some writeAlias16) cleanup16 (some resetOnError16)
  shape "u32" 4 (0x01020304 : BitVec 32) 0xa1b2c3d4 (some writeAlias32) cleanup32
    (some resetOnError32)
  shape "u64" 8 (0x0102030405060708 : BitVec 64) 0xa1b2c3d4e5f60718 (some writeAlias64) cleanup64
    (some resetOnError64)
  shape "Pair" 4 ({ a := 0x01020304, b := 0x0506 } : Pair) { a := 0xa1b2c3d4, b := 0xe5f6 }
    (some writeAliasPair) cleanupPair (some resetOnErrorPair)
  shape "anyerror!u32" 4 (0x01020304 : BitVec 32) 0xa1b2c3d4 (some writeAliasAny) cleanupAny none
  require (value (aliased 2 writeAliasSigned (.ok 0x0102) (-2)) == some (.ok (.ok 0xfffe, .ok 0xfffe)))
    "i16 alias write"
  require (value (aliased 2 writeAliasSigned (.error "Other") (-2))
    == some (.ok (.error "Other", .error "Other"))) "i16 alias error"
  IO.println "pointer-try payload-shape theorems and runtime cases passed"

end TryLifetimes.V0_14_1.PayloadRules
