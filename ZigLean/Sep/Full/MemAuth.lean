import ZigLean.Sep.Full.StackDepth

/-!
# The memory's authority over the counter cell (`docs/sep-full-state.md` §Authoritative counters)

`Ghost.ac` is one authoritative counter cell (`ZigLean/Sep/Full/ACell.lean`) with the keys
`AKey`. `MemAuth m c` is what the memory `m` demands of the whole cell `c` (a resource and its
frame together); it is the last conjunct of `GOk`, so every judgment keeps it against every
frame:

* `stack`: the stack tokens (`StackAuth`, `ZigLean/Sep/Full/StackDepth.lean`).
* `tick`: **the step meter** (`TickAuth`, §Step ticks): the credits (`cred`) are a frame-authority
  key, and the memory meters the authority `●L`: the credits held plus the steps run so far
  (`Mem.ticks`) are at most `L`. The receipts (`spent`) are at most the steps run. Plain mode
  (`unmetered`) and a meter exclude each other. So no judgment that ticks without paying a
  credit can keep `TickAuth` against a frame that holds `●L` with every credit out.
* `noStack`: the plain-mode fact `noStack` (no thread has a stack budget) is true.
* `onlyCred`: no key but `cred` has a frame authority, so a step that adds a fragment of another
  key (a receipt, `noStack`, `unmetered`) stays valid.

`MemAuth.Keep m m'` is the per-primitive obligation: a step from `m` to `m'` keeps every stack
authority, leaves `Mem.ticks` and keeps `noStack`. Every primitive but `Zig.tick` and the stack
pushes and pops proves it once (`MemAuth.Keep.of_blocks`, `MemAuth.Keep.shape`, the `alloc` and
`free` instances); the rules that re-establish `GOk` take it.

The ghost parts that hold exclusive stack tokens are linear: `StackAuth` demands each of them.
Every other part of the cell can be dropped (`MemAuth.drop`).
-/

namespace Zig

/-- No thread has a stack budget (`Mem.stacks`, MM-18): every generated `mem0`, and every memory
without `Mem.withStack`. No primitive gives a thread a budget. -/
def Mem.NoStack (m : Mem) : Prop := ∀ t, (m.stackOf t).budget = none

theorem Mem.noStack_of_stacks {m : Mem} (h : m.stacks = #[]) : m.NoStack := fun t => by
  simp [Mem.stackOf, h]; rfl
namespace Full

/-- **The step meter** (module doc): the credits held plus the steps run are at most a frame
authority `●L`; the receipts are at most the steps run; plain mode excludes a meter. -/
structure TickAuth (m : Mem) (c : KCell) : Prop where
  meter : ∀ L, 0 < c.auth .cred L → c.frag .cred + m.ticks ≤ L
  spent : c.frag .spent ≤ m.ticks
  plain : 0 < c.frag .unmetered → ∀ L, c.auth .cred L = 0

/-- **The memory's authority over the counter cell** (module doc). -/
structure MemAuth (m : Mem) (c : KCell) : Prop where
  stack : StackAuth m c
  tick : TickAuth m c
  noStack : 0 < c.frag .noStack → m.NoStack
  onlyCred : ∀ k L, k ≠ .cred → c.auth k L = 0

/-- **A step keeps the memory's authority** (module doc): the per-primitive obligation. -/
structure MemAuth.Keep (m m' : Mem) : Prop where
  stack : ∀ c, StackAuth m c → StackAuth m' c
  ticks : m'.ticks = m.ticks
  noStack : m.NoStack → m'.NoStack

namespace MemAuth

variable {m m' m'' : Mem} {c : KCell}

theorem keep (h : MemAuth m c) (hk : Keep m m') : MemAuth m' c :=
  ⟨hk.stack c h.stack, ⟨fun L hL => by rw [hk.ticks]; exact h.tick.meter L hL,
    by rw [hk.ticks]; exact h.tick.spent, h.tick.plain⟩, fun hp => hk.noStack (h.noStack hp),
    h.onlyCred⟩

theorem Keep.refl (m : Mem) : Keep m m := ⟨fun _ h => h, rfl, id⟩

theorem Keep.trans (h₁ : Keep m m') (h₂ : Keep m' m'') : Keep m m'' :=
  ⟨fun c h => h₂.stack c (h₁.stack c h), h₂.ticks.trans h₁.ticks, fun h => h₂.noStack (h₁.noStack h)⟩

/-- A step that keeps the stack states, the blocks, the address space and the step count. -/
theorem Keep.of_blocks (hb : m'.blocks = m.blocks) (hst : m'.stacks = m.stacks)
    (hlim : m'.place.addrLimit = m.place.addrLimit) (ht : m'.ticks = m.ticks) : Keep m m' :=
  ⟨fun _ h => h.keep_shape hst hlim (by rw [hb]) fun b blk' hb' =>
      ⟨blk', by rw [← hb]; exact hb', rfl, rfl, rfl, rfl⟩,
    ht, fun h t => by simp only [Mem.stackOf, hst]; exact h t⟩

theorem Keep.of_aux (hb : m'.blocks = m.blocks) (h : m.Aux m') : Keep m m' :=
  Keep.of_blocks hb h.1 (by rw [h.2.1]) h.2.2

/-- A step that keeps the stack states, the address space, the step count, and every block's
liveness, address, size and kind (stores, loads, recorded accesses). -/
theorem Keep.shape (hst : m'.stacks = m.stacks) (hlim : m'.place.addrLimit = m.place.addrLimit)
    (hsz : m'.blocks.size = m.blocks.size)
    (hb : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → ∃ blk, m.blocks[b]? = some blk ∧
      blk'.live = blk.live ∧ blk'.addr = blk.addr ∧ blk'.bytes.size = blk.bytes.size ∧
        blk'.kind = blk.kind)
    (ht : m'.ticks = m.ticks) : Keep m m' :=
  ⟨fun _ h => h.keep_shape hst hlim hsz hb, ht, fun h t => by simp only [Mem.stackOf, hst]; exact h t⟩

/-- Replacing block `b` by one with the same liveness, address, size and kind (a store). -/
theorem Keep.set {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (h : m'.blocks = m.blocks.set! b nb) (hl : nb.live = blk.live) (ha : nb.addr = blk.addr)
    (hs : nb.bytes.size = blk.bytes.size) (hk : nb.kind = blk.kind) (hst : m'.stacks = m.stacks)
    (hlim : m'.place.addrLimit = m.place.addrLimit) (ht : m'.ticks = m.ticks) : Keep m m' := by
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  refine Keep.shape hst hlim (by rw [h]; simp [Array.set!_eq_setIfInBounds]) (fun b' blk' hb' => ?_) ht
  rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hb'
  by_cases e : b = b'
  · subst e
    simp only [hlt, ↓reduceIte, Option.some.injEq] at hb'
    subst hb'
    exact ⟨blk, hb, hl, ha, hs, hk⟩
  · simp only [e, ↓reduceIte] at hb'
    exact ⟨blk', hb', rfl, rfl, rfl, rfl⟩

/-- A step that keeps the stack states and the step count, and changes blocks only within
`StackAuth.keep`'s premises (a new or moved block is clear of every reserve, an old one keeps its
place or is clear). -/
theorem Keep.of_stackKeep (hst : m'.stacks = m.stacks)
    (hlim : m.place.addrLimit ≤ m'.place.addrLimit) (hsz : m.blocks.size ≤ m'.blocks.size)
    (hold : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → blk'.live = true →
      b < m.blocks.size → ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
        ((∀ t S, (m.stackOf t).budget = some S → blk'.clearOf (m.stackOf t).base S = true) ∨
          (blk.addr = blk'.addr ∧ blk'.bytes.size ≤ blk.bytes.size ∧
            blk.kind.mappedLo ≤ blk'.kind.mappedLo)))
    (hnew : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → m.blocks.size ≤ b →
      ∀ t S, (m.stackOf t).budget = some S → blk'.clearOf (m.stackOf t).base S = true)
    (ht : m'.ticks = m.ticks) : Keep m m' :=
  ⟨fun _ h => h.keep hst hlim hsz hold hnew, ht, fun h t => by simp only [Mem.stackOf, hst]; exact h t⟩

/-- Pushing a block clear of every reserve (a new mapping, a moved one). -/
theorem Keep.push {nb : Block} (h : m'.blocks = m.blocks.push nb) (hst : m'.stacks = m.stacks)
    (hlim : m'.place.addrLimit = m.place.addrLimit) (ht : m'.ticks = m.ticks)
    (hc : ∀ t S, (m.stackOf t).budget = some S → nb.clearOf (m.stackOf t).base S = true) :
    Keep m m' := by
  refine Keep.of_stackKeep hst (by omega) (by rw [h]; simp) (fun b blk' hb' hl hbs => ?_)
    (fun b blk' hb' hbs t S hS => ?_) ht
  · rw [h, Array.getElem?_push, if_neg (Nat.ne_of_lt hbs)] at hb'
    exact ⟨blk', hb', hl, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩
  · have hlt := (Array.getElem?_eq_some_iff.mp hb').1
    rw [h, Array.size_push] at hlt
    obtain rfl : b = m.blocks.size := by omega
    rw [h, Array.getElem?_push_size] at hb'
    cases hb'
    exact hc t S hS

/-- **A block at `Mem.newAddr` is clear of every reserve** (the placement's address avoids them,
`Mem.placeOk`; the fallback lies above `Mem.top`). -/
theorem _root_.Zig.Mem.newAddr_reservesClear {nb : Block} {N align : Nat} (ha : nb.addr = m.newAddr N align)
    (hN : nb.bytes.size ≤ N) :
    ∀ t S, (m.stackOf t).budget = some S → nb.clearOf (m.stackOf t).base S = true := fun t S hS => by
  have := allocAddr_apart_none (m := m) (kind := .heap) (size := N) (align := align) rfl t S hS
  rw [Mem.allocAddr_heap] at this
  exact clearOf_of_apart (by rw [ha]; omega)

/-- In a memory without stack budgets, a step that keeps the step count and gives no thread a
budget keeps the authority: there are no stack tokens to keep. -/
theorem Keep.of_noStack (hm : m.NoStack) (hm' : m'.NoStack) (ht : m'.ticks = m.ticks) : Keep m m' :=
  ⟨fun c h => by
    refine ⟨fun t => ?_, fun t _ S _ _ h' => by rw [hm' t] at h'; cases h'⟩
    have := h.thread t
    unfold ThreadOk at this ⊢
    rw [hm t] at this; rw [hm' t]; exact this, ht, fun _ => hm'⟩

/-- `alloc` of a block that no stack budget charges. -/
theorem Keep.allocOther {kind : BlockKind} {size align : Nat} (hk : m.stackBudget? kind = none) :
    Keep m (m.afterAlloc kind size align) :=
  ⟨fun _ h => h.allocOther hk, rfl, fun h t => by
    have hst : (m.afterAlloc kind size align).stacks = m.stacks := by
      simp [Mem.afterAlloc, Mem.stacksAfterAlloc, hk]
    simp only [Mem.stackOf, hst]; exact h t⟩

/-- A block ends (a dead block holds no reserve). -/
theorem Keep.kill {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (h : m'.blocks = m.blocks.set! b { blk with live := false }) (hst : m'.stacks = m.stacks)
    (hlim : m'.place.addrLimit = m.place.addrLimit) (ht : m'.ticks = m.ticks) : Keep m m' := by
  refine Keep.of_stackKeep hst (by omega) (by rw [h]; simp) (fun b' blk' hb' hl _ => ?_)
    (fun b' blk' hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by rw [h]; simp; omega)) ht
  rw [h] at hb'
  rcases getElem?_set!_dead hb hb' with ⟨-, hd⟩ | ⟨-, hb''⟩
  · rw [hd] at hl; cases hl
  · exact ⟨blk', hb'', hl, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩

/-- `free`. -/
theorem Keep.free {p : Ptr} {x : Unit} (hrun : ((Zig.free p).run m).run = some (.ok (x, m'))) :
    Keep m m' := by
  obtain ⟨b, blk, -, -, -, rfl⟩ := free_ok_live hrun
  exact ⟨fun _ h => h.free hrun, rfl, id⟩

/-- **`StackAuth` reads only the exclusive fragments.** -/
theorem _root_.Zig.Full.StackAuth.congr {c c' : KCell} (h : StackAuth m c)
    (he : ∀ k v, c'.ex k v = c.ex k v) : StackAuth m c' :=
  ⟨fun t => (h.thread t).transfer rfl (Nat.le_refl _) (Nat.le_refl _)
    (fun _ blk' hb' hl _ => ⟨blk', hb', hl, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩)
    (fun _ _ hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by omega))
    (fun k v _ => he k v), h.apart⟩

/-- **Dropping a part without exclusive fragments keeps the authority** (credits, receipts,
the plain-mode facts, a credit authority: everything but the stack tokens). -/
theorem drop {a b : KCell} (h : MemAuth m (a.add b)) (hb : ∀ k v, b.ex k v = 0) : MemAuth m a := by
  obtain ⟨hs, ⟨h1, h2, h3⟩, h4, h5⟩ := h
  refine ⟨hs.congr fun k v => by simp [hb], ⟨fun L hL => ?_, ?_, fun hp L => ?_⟩, fun hp => h4 ?_,
    fun k L hk => ?_⟩
  · have := h1 L (by simp; omega); simp at this; omega
  · have := h2; simp at this; omega
  · have := h3 (by simp; omega) L; simp at this; omega
  · simp; omega
  · have := h5 k L hk; simp at this; omega

/-- **The start**: in a memory without stack budgets the empty cell is authorized. -/
theorem unit (hm : m.NoStack) : MemAuth m ACell.unit :=
  ⟨StackAuth.of_noBudget hm fun _ _ _ => rfl, ⟨fun _ h => absurd h (by simp), by simp,
    fun h => absurd h (by simp)⟩, fun h => absurd h (by simp), fun _ _ _ => rfl⟩

end MemAuth

end Full
end Zig
