import ZigLean.Mem.Enc

/-!
# `@Vector(n, T)`

`Zig.Vec α n`: Zig's SIMD vector. Distinct from the array `Vector α n` (`ZigLean/Mem/Enc.lean`):
same lanes, but the ABI size and alignment round up to a power of 2 (`docs/air-json.md` §Type,
`k = "vector"`), so `Check.lean`'s `modelLayout` gives it a different formula than the array's
plain `n * Enc.size α`.

`Emit.lean` lifts a scalar op lane-wise with `map`/`map2`/`map2M` (the same function the scalar
case calls, e.g. `Zig.add`); every other lane-wise op (`div`, `@min`, bitwise, shifts,
comparisons, casts, …) is the scalar expression in `mapM`/`map2M`/`map3M` (`Emit.lean`'s
`emitLaneWise`), builds `select` and `reduce` (`std.builtin.ReduceOp`, Zig's lane
order: lane 0 first) from here, and expands `@shuffle` to an explicit per-lane pick at emission
time (the mask is comptime-known, so no runtime shuffle function is needed).
-/

namespace Zig

/-- The smallest power of 2 that is `≥ n` (`n = 0`: `1`). -/
def ceilPow2 (n : Nat) : Nat := if n ≤ 1 then 1 else 2 ^ (Nat.log2 (n - 1) + 1)

/-- `@Vector(n, α)`. -/
structure Vec (α : Type) (n : Nat) where
  lanes : Vector α n
  deriving Repr, Inhabited, BEq

/-- `n * Enc.size α`, rounded up to a power of 2: the ABI size and alignment
(`Check.lean`'s `modelLayout`). -/
def vecLayout (n elemSize : Nat) : Nat := ceilPow2 (n * elemSize)

instance {α : Type} {n : Nat} [Enc α] : Enc (Vec α n) where
  size := vecLayout n (Enc.size α)
  align := vecLayout n (Enc.size α)
  encode v := padTo (vecLayout n (Enc.size α)) ((v.lanes.toArray.map Enc.encode).flatten)
  decode bs := do
    let xs ← (Array.range n).mapM fun i =>
      (Enc.decode (bs.extract (i * Enc.size α) ((i + 1) * Enc.size α)) : Result α)
    if h : xs.size = n then pure ⟨⟨xs, h⟩⟩ else throw .unspecified

/-- A vector with every lane `a` (`splat`). -/
def Vec.splat {α : Type} {n : Nat} (a : α) : Vec α n := ⟨Vector.replicate n a⟩

/-- Lane-wise unary op. -/
def Vec.map {α β : Type} {n : Nat} (f : α → β) (v : Vec α n) : Vec β n := ⟨v.lanes.map f⟩

/-- Lane-wise binary op (`add_wrap`, `bit_and`, …). -/
def Vec.map2 {α β γ : Type} {n : Nat} (f : α → β → γ) (a : Vec α n) (b : Vec β n) : Vec γ n :=
  ⟨Vector.zipWith f a.lanes b.lanes⟩

/-- Lane-wise unary op in `Result` (throws on the first lane that throws). -/
def Vec.mapM {α β : Type} {n : Nat} (f : α → Result β) (v : Vec α n) : Result (Vec β n) := do
  let lanes ← v.lanes.mapM f
  pure ⟨lanes⟩

/-- Lane-wise binary op in `Result` (checked arithmetic: throws on the first lane that
overflows). -/
def Vec.map2M {α β γ : Type} {n : Nat} (f : α → β → Result γ) (a : Vec α n) (b : Vec β n) :
    Result (Vec γ n) := do
  let lanes ← (a.lanes.zip b.lanes).mapM fun (x, y) => f x y
  pure ⟨lanes⟩

/-- Lane-wise ternary op in `Result` (`@mulAdd`). -/
def Vec.map3M {α β γ δ : Type} {n : Nat} (f : α → β → γ → Result δ) (a : Vec α n) (b : Vec β n)
    (c : Vec γ n) : Result (Vec δ n) := do
  let lanes ← ((a.lanes.zip b.lanes).zip c.lanes).mapM fun ((x, y), z) => f x y z
  pure ⟨lanes⟩

/-- A vector of pairs as a pair of vectors (`@addWithOverflow` on vectors). -/
def Vec.unzip {α β : Type} {n : Nat} (v : Vec (α × β) n) : Vec α n × Vec β n :=
  (⟨v.lanes.map (·.1)⟩, ⟨v.lanes.map (·.2)⟩)

/-- `select`: lane `i` is `a`'s lane if `pred`'s lane `i` is true, else `b`'s. -/
def Vec.select {α : Type} {n : Nat} (pred : Vec Bool n) (a b : Vec α n) : Vec α n :=
  ⟨pred.lanes.mapFinIdx fun i p _ => if p then a.lanes[i] else b.lanes[i]⟩

/-- `@reduce`: fold the vector left to right, lane 0 first (Zig's lane order). Unreachable for
`n = 0`: no Zig vector has length 0 (`[Inhabited α]` is only for the `!`-indexed lane 0, never
actually hit at `n = 0`). -/
def Vec.reduce {α : Type} {n : Nat} [Inhabited α] (f : α → α → α) (v : Vec α n) : α :=
  (v.lanes.toArray.extract 1 n).foldl f v.lanes.toArray[0]!

/-- `@reduce`, monadic (float `.Min`/`.Max`: `Zig.Float.minChk`/`maxChk` can throw). -/
def Vec.reduceM {α : Type} {n : Nat} [Inhabited α] (f : α → α → Result α) (v : Vec α n) :
    Result α :=
  (v.lanes.toArray.extract 1 n).foldlM f v.lanes.toArray[0]!

end Zig
