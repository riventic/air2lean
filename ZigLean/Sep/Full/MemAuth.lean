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
* `cur`: the token `cur t` (`curCell`, the one exclusive fragment of the key `cur`) names the
  running thread (`m.current = t`). At most one exists, so a thread holds it only while it runs:
  the thread rules hand it to a thread's step and take it back (`docs/sep-full-state.md` §Stack
  depth, the current thread).

`MemAuth m c d` also reads **the device cell** `d` (`Ghost.dev`, `DCell`; `docs/sep-full-state.md`
§Device state; maintainer decision 2026-11-25): an exclusive fragment `devOwn D` holds the whole
device state `Mem.dev` (oracles and trace, L13). `dev`: every fragment the cell holds names
`m.dev`, and there is at most one. So two `devOwn` never compose, and a resource with `devOwn D`
knows the memory's device state: a device step (`vload`, `vasm`, …) changes `m.dev` together
with the fragment, and no other step changes either.

`MemAuth.Keep m m'` is the per-primitive obligation: a step from `m` to `m'` keeps every stack
authority, leaves `Mem.ticks` and `Mem.dev`, keeps `noStack` and the current thread. Every
primitive but `Zig.tick`, the stack pushes and pops and the device steps proves it once
(`MemAuth.Keep.of_blocks`, `MemAuth.Keep.shape`, the `alloc` and `free` instances); the rules that
re-establish `GOk` take it. A scheduler stop changes the current thread: it keeps `MemAuth` only
where no `cur` token is held (`MemAuth.stop`).

The ghost parts that hold exclusive stack tokens are linear: `StackAuth` demands each of them.
Every other part of the cell can be dropped (`MemAuth.drop`), and so can a device fragment
(`MemAuth.dropDev`).
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

/-- **The device cell** (`docs/sep-full-state.md` §Device state): how many exclusive fragments
`devOwn D` hold each device state `D`. Composition adds the counts; the memory admits at most one
fragment, of its own device state (`MemAuth.dev`). -/
abbrev DCell := DevState → Nat

/-- The empty device cell. -/
def DCell.unit : DCell := fun _ => 0

@[simp] theorem DCell.unit_apply (D : DevState) : DCell.unit D = 0 := rfl

open Classical in
/-- The device cell of `devOwn D`: one fragment of `D`. -/
noncomputable def DCell.one (D : DevState) : DCell := fun D' => if D' = D then 1 else 0

@[simp] theorem DCell.one_self (D : DevState) : DCell.one D D = 1 := by simp [DCell.one]

theorem DCell.one_ne {D X : DevState} (h : X ≠ D) : DCell.one D X = 0 := by simp [DCell.one, h]

/-- **The memory's authority over the counter cell and the device cell** (module doc). -/
structure MemAuth (m : Mem) (c : KCell) (d : DCell) : Prop where
  stack : StackAuth m c
  tick : TickAuth m c
  noStack : 0 < c.frag .noStack → m.NoStack
  onlyCred : ∀ k L, k ≠ .cred → c.auth k L = 0
  cur : ∀ v, 0 < c.ex .cur v → v.1 = m.current
  /-- The device fragments: at most one, of the memory's device state. -/
  dev : ∀ D, 0 < d D → d D = 1 ∧ m.dev = D

/-- **A step keeps the memory's authority** (module doc): the per-primitive obligation. -/
structure MemAuth.Keep (m m' : Mem) : Prop where
  stack : ∀ c, StackAuth m c → StackAuth m' c
  ticks : m'.ticks = m.ticks
  noStack : m.NoStack → m'.NoStack
  current : m'.current = m.current
  dev : m'.dev = m.dev

namespace MemAuth

variable {m m' m'' : Mem} {c : KCell} {d : DCell}

theorem keep (h : MemAuth m c d) (hk : Keep m m') : MemAuth m' c d :=
  ⟨hk.stack c h.stack, ⟨fun L hL => by rw [hk.ticks]; exact h.tick.meter L hL,
    by rw [hk.ticks]; exact h.tick.spent, h.tick.plain⟩, fun hp => hk.noStack (h.noStack hp),
    h.onlyCred, fun v hv => by rw [hk.current]; exact h.cur v hv,
    fun D hD => by rw [hk.dev]; exact h.dev D hD⟩

/-- **Only the device cell matters for `dev`**: another counter cell with the same authority. -/
theorem withDev {d' : DCell} (h : MemAuth m c d) (hd : ∀ D, 0 < d' D → d' D = 1 ∧ m.dev = D) :
    MemAuth m c d' :=
  ⟨h.stack, h.tick, h.noStack, h.onlyCred, h.cur, hd⟩

/-- **A device fragment can be dropped**: fewer fragments are still at most one, of `m.dev`. -/
theorem dropDev {d' : DCell} (h : MemAuth m c d) (hle : ∀ D, d' D ≤ d D) : MemAuth m c d' :=
  h.withDev fun D hD => by
    obtain ⟨h1, h2⟩ := h.dev D (Nat.lt_of_lt_of_le hD (hle D))
    exact ⟨by have := hle D; omega, h2⟩

/-- The empty device cell is authorized in every memory. -/
theorem dev_unit (m : Mem) : ∀ D, 0 < DCell.unit D → DCell.unit D = 1 ∧ m.dev = D :=
  fun _ h => absurd h (Nat.lt_irrefl 0)

/-- **A device fragment is the only one**: next to the fragment of `D`, the rest `e` of an
authorized device cell holds no fragment, and `D` is the memory's device state. -/
theorem dev_only {d e : DCell} {D : DevState} (h : MemAuth m c d) (hd : ∀ X, d X = DCell.one D X + e X) :
    m.dev = D ∧ ∀ X, e X = 0 := by
  have hD := h.dev D (by rw [hd, DCell.one_self]; omega)
  refine ⟨hD.2, fun X => ?_⟩
  by_cases hX : X = D
  · subst hX; have := hD.1; rw [hd, DCell.one_self] at this; omega
  · refine Nat.eq_zero_of_not_pos fun hp => hX ?_
    exact (h.dev X (by rw [hd]; omega)).2.symm.trans hD.2

/-- **A device step's authority**: the memory with the device state `D'` in place of `D`
authorizes the device cell with the fragment of `D'` in place of the fragment of `D`. -/
theorem setDev {d d' e : DCell} {D : DevState} (D' : DevState) (h : MemAuth m c d)
    (hd : ∀ X, d X = DCell.one D X + e X) (hd' : ∀ X, d' X = DCell.one D' X + e X) :
    MemAuth { m with dev := D' } c d' := by
  have he := (h.dev_only hd).2
  refine ⟨h.stack.keep_shape rfl rfl rfl fun _ blk' hb' => ⟨blk', hb', rfl, rfl, rfl, rfl⟩,
    ⟨h.tick.meter, h.tick.spent, h.tick.plain⟩, h.noStack, h.onlyCred, h.cur, fun X hX => ?_⟩
  rw [hd', he X, Nat.add_zero] at hX ⊢
  by_cases hXD : X = D'
  · subst hXD; exact ⟨DCell.one_self X, rfl⟩
  · rw [DCell.one_ne hXD] at hX; exact absurd hX (Nat.lt_irrefl 0)

/-- **The device fragment of the memory's state can be added** next to a device cell without
fragments. -/
theorem addDev {d d' : DCell} (h : MemAuth m c d) (h0 : ∀ X, d X = 0)
    (hd' : ∀ X, d' X = DCell.one m.dev X + d X) : MemAuth m c d' :=
  h.withDev fun X hX => by
    rw [hd', h0 X, Nat.add_zero] at hX ⊢
    by_cases hXD : X = m.dev
    · subst hXD; exact ⟨DCell.one_self _, rfl⟩
    · rw [DCell.one_ne hXD] at hX; exact absurd hX (Nat.lt_irrefl 0)

theorem Keep.refl (m : Mem) : Keep m m := ⟨fun _ h => h, rfl, id, rfl, rfl⟩

theorem Keep.trans (h₁ : Keep m m') (h₂ : Keep m' m'') : Keep m m'' :=
  ⟨fun c h => h₂.stack c (h₁.stack c h), h₂.ticks.trans h₁.ticks, fun h => h₂.noStack (h₁.noStack h),
    h₂.current.trans h₁.current, h₂.dev.trans h₁.dev⟩

/-- A step that keeps the stack states, the blocks, the address space, the step count, the
current thread and the device state. -/
theorem Keep.of_blocks (hb : m'.blocks = m.blocks) (hst : m'.stacks = m.stacks)
    (hlim : m'.place.addrLimit = m.place.addrLimit) (ht : m'.ticks = m.ticks)
    (hc : m'.current = m.current := by first | rfl | assumption | simp)
    (hd : m'.dev = m.dev := by first | rfl | assumption | simp) : Keep m m' :=
  ⟨fun _ h => h.keep_shape hst hlim (by rw [hb]) fun b blk' hb' =>
      ⟨blk', by rw [← hb]; exact hb', rfl, rfl, rfl, rfl⟩,
    ht, fun h t => by simp only [Mem.stackOf, hst]; exact h t, hc, hd⟩

theorem Keep.of_aux (hb : m'.blocks = m.blocks) (h : m.Aux m')
    (hc : m'.current = m.current := by first | rfl | assumption | simp) : Keep m m' :=
  Keep.of_blocks hb h.1 (by rw [h.2.1]) h.ticks hc h.dev

/-- A step that keeps the stack states, the address space, the step count, and every block's
liveness, address, size and kind (stores, loads, recorded accesses). -/
theorem Keep.shape (hst : m'.stacks = m.stacks) (hlim : m'.place.addrLimit = m.place.addrLimit)
    (hsz : m'.blocks.size = m.blocks.size)
    (hb : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → ∃ blk, m.blocks[b]? = some blk ∧
      blk'.live = blk.live ∧ blk'.addr = blk.addr ∧ blk'.bytes.size = blk.bytes.size ∧
        blk'.kind = blk.kind)
    (ht : m'.ticks = m.ticks) (hc : m'.current = m.current := by first | rfl | assumption | simp)
    (hd : m'.dev = m.dev := by first | rfl | assumption | simp) : Keep m m' :=
  ⟨fun _ h => h.keep_shape hst hlim hsz hb, ht, fun h t => by simp only [Mem.stackOf, hst]; exact h t,
    hc, hd⟩

/-- Replacing block `b` by one with the same liveness, address, size and kind (a store). -/
theorem Keep.set {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (h : m'.blocks = m.blocks.set! b nb) (hl : nb.live = blk.live) (ha : nb.addr = blk.addr)
    (hs : nb.bytes.size = blk.bytes.size) (hk : nb.kind = blk.kind) (hst : m'.stacks = m.stacks)
    (hlim : m'.place.addrLimit = m.place.addrLimit) (ht : m'.ticks = m.ticks)
    (hc : m'.current = m.current := by first | rfl | assumption | simp)
    (hd : m'.dev = m.dev := by first | rfl | assumption | simp) : Keep m m' := by
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  refine Keep.shape hst hlim (by rw [h]; simp [Array.set!_eq_setIfInBounds]) (fun b' blk' hb' => ?_) ht hc hd
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
    (ht : m'.ticks = m.ticks) (hcur : m'.current = m.current := by first | rfl | assumption | simp)
    (hd : m'.dev = m.dev := by first | rfl | assumption | simp) : Keep m m' :=
  ⟨fun _ h => h.keep hst hlim hsz hold hnew, ht, fun h t => by simp only [Mem.stackOf, hst]; exact h t,
    hcur, hd⟩

/-- Pushing a block clear of every reserve (a new mapping, a moved one). -/
theorem Keep.push {nb : Block} (h : m'.blocks = m.blocks.push nb) (hst : m'.stacks = m.stacks)
    (hlim : m'.place.addrLimit = m.place.addrLimit) (ht : m'.ticks = m.ticks)
    (hc : ∀ t S, (m.stackOf t).budget = some S → nb.clearOf (m.stackOf t).base S = true)
    (hcur : m'.current = m.current := by first | rfl | assumption | simp)
    (hd : m'.dev = m.dev := by first | rfl | assumption | simp) : Keep m m' := by
  refine Keep.of_stackKeep hst (by omega) (by rw [h]; simp) (fun b blk' hb' hl hbs => ?_)
    (fun b blk' hb' hbs t S hS => ?_) ht hcur hd
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
theorem Keep.of_noStack (hm : m.NoStack) (hm' : m'.NoStack) (ht : m'.ticks = m.ticks)
    (hc : m'.current = m.current := by first | rfl | assumption | simp)
    (hd : m'.dev = m.dev := by first | rfl | assumption | simp) : Keep m m' :=
  ⟨fun c h => by
    refine ⟨fun t => ?_, fun t _ S _ _ h' => by rw [hm' t] at h'; cases h'⟩
    have := h.thread t
    unfold ThreadOk at this ⊢
    rw [hm t] at this; rw [hm' t]; exact this, ht, fun _ => hm', hc, hd⟩

/-- `alloc` of a block that no stack budget charges. -/
theorem Keep.allocOther {kind : BlockKind} {size align : Nat} (hk : m.stackBudget? kind = none) :
    Keep m (m.afterAlloc kind size align) :=
  ⟨fun _ h => h.allocOther hk, rfl, fun h t => by
    have hst : (m.afterAlloc kind size align).stacks = m.stacks := by
      simp [Mem.afterAlloc, Mem.stacksAfterAlloc, hk]
    simp only [Mem.stackOf, hst]; exact h t, rfl, rfl⟩

/-- A live block replaced in place by one that is clear of every reserve or occupies no more
than it did (`StackAuth.keep`'s condition on an old block). -/
theorem Keep.setLive {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (hl : blk.live = true) (h : m'.blocks = m.blocks.set! b nb)
    (hn : (∀ t S, (m.stackOf t).budget = some S → nb.clearOf (m.stackOf t).base S = true) ∨
      (blk.addr = nb.addr ∧ nb.bytes.size ≤ blk.bytes.size ∧ blk.kind.mappedLo ≤ nb.kind.mappedLo))
    (hax : m.Aux m') (hc : m'.current = m.current := by first | rfl | assumption | simp) :
    Keep m m' := by
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  refine Keep.of_stackKeep hax.1 (by rw [hax.2.1]; exact Nat.le_refl _) (by rw [h]; simp)
    (fun b' blk' hb' hl' _ => ?_)
    (fun b' blk' hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by rw [h]; simp; omega))
    hax.ticks hc hax.dev
  rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hb'
  by_cases e : b = b'
  · subst e
    simp only [hlt, ↓reduceIte, Option.some.injEq] at hb'
    subst hb'
    exact ⟨blk, hb, hl, hn⟩
  · simp only [e, ↓reduceIte] at hb'
    exact ⟨blk', hb', hl', .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩

/-- A block replaced in place by one that occupies less (same address, at most as many bytes, a
mapping start at least as high: a trim or a prefix `munmap`, an `mremap` shrink). -/
theorem Keep.shrink {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (hl : blk.live = true) (h : m'.blocks = m.blocks.set! b nb) (ha : nb.addr = blk.addr)
    (hs : nb.bytes.size ≤ blk.bytes.size) (hlo : blk.kind.mappedLo ≤ nb.kind.mappedLo)
    (hax : m.Aux m') (hc : m'.current = m.current := by first | rfl | assumption | simp) :
    Keep m m' :=
  Keep.setLive hb hl h (.inr ⟨ha.symm, hs, hlo⟩) hax hc

/-- A block whose live bytes are clear of every reserve may grow in place (an `mremap` growth:
`Mem.mappingRoom` checks the reserves). -/
theorem Keep.growClear {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (hl : blk.live = true) (h : m'.blocks = m.blocks.set! b nb)
    (hc : ∀ t S, (m.stackOf t).budget = some S → nb.clearOf (m.stackOf t).base S = true)
    (hax : m.Aux m') (hcur : m'.current = m.current := by first | rfl | assumption | simp) :
    Keep m m' :=
  Keep.setLive hb hl h (.inl hc) hax hcur

/-- A block whose live bytes lie apart from a reserve is clear of it. -/
theorem _root_.Zig.Block.clearOf_of_liveApart {blk : Block} {base S : Nat}
    (h : blk.bytes.size ≤ blk.kind.mappedLo ∨ S = 0 ∨ blk.addr + blk.bytes.size ≤ base ∨
      base + S ≤ blk.addr + blk.kind.mappedLo) :
    blk.clearOf base S = true := by
  cases hc : blk.clearOf base S
  · obtain ⟨-, h2, h3, h4, h5⟩ := Block.clearOf_false_iff.mp hc
    omega
  · rfl

/-- `Mem.reservesFree` as a statement about each reserve. -/
theorem _root_.Zig.Mem.reservesFree_apart {A n : Nat} (h : m.reservesFree A n = true) (t S : Nat)
    (hS : (m.stackOf t).budget = some S) :
    n = 0 ∨ S = 0 ∨ A + n ≤ (m.stackOf t).base ∨ (m.stackOf t).base + S ≤ A :=
  reserveClear_budget (all_getD h rfl t) hS

/-- A block ends (a dead block holds no reserve). -/
theorem Keep.kill {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (h : m'.blocks = m.blocks.set! b { blk with live := false }) (hst : m'.stacks = m.stacks)
    (hlim : m'.place.addrLimit = m.place.addrLimit) (ht : m'.ticks = m.ticks)
    (hc : m'.current = m.current := by first | rfl | assumption | simp)
    (hd : m'.dev = m.dev := by first | rfl | assumption | simp) : Keep m m' := by
  refine Keep.of_stackKeep hst (by omega) (by rw [h]; simp) (fun b' blk' hb' hl _ => ?_)
    (fun b' blk' hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by rw [h]; simp; omega)) ht hc
    hd
  rw [h] at hb'
  rcases getElem?_set!_dead hb hb' with ⟨-, hd⟩ | ⟨-, hb''⟩
  · rw [hd] at hl; cases hl
  · exact ⟨blk', hb'', hl, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩

/-- `free`. -/
theorem Keep.free {p : Ptr} {x : Unit} (hrun : ((Zig.free p).run m).run = some (.ok (x, m'))) :
    Keep m m' := by
  obtain ⟨b, blk, -, -, -, rfl⟩ := free_ok_live hrun
  exact ⟨fun _ h => h.free hrun, rfl, id, rfl, rfl⟩

/-- **`StackAuth` reads only the exclusive fragments of the threads' keys** (`sp`, `blk`, `frm`). -/
theorem _root_.Zig.Full.StackAuth.congrTid {c c' : KCell} (h : StackAuth m c)
    (he : ∀ k v t, k.tid = some t → c'.ex k v = c.ex k v) : StackAuth m c' :=
  ⟨fun t => (h.thread t).transfer rfl (Nat.le_refl _) (Nat.le_refl _)
    (fun _ blk' hb' hl _ => ⟨blk', hb', hl, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩)
    (fun _ _ hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by omega))
    (fun k v hk => he k v t hk), h.apart⟩

/-- **`StackAuth` reads only the exclusive fragments.** -/
theorem _root_.Zig.Full.StackAuth.congr {c c' : KCell} (h : StackAuth m c)
    (he : ∀ k v, c'.ex k v = c.ex k v) : StackAuth m c' :=
  h.congrTid fun k v _ _ => he k v

/-- **Dropping a part without exclusive fragments keeps the authority** (credits, receipts,
the plain-mode facts, a credit authority: everything but the stack tokens and `cur`). -/
theorem drop {a b : KCell} (h : MemAuth m (a.add b) d) (hb : ∀ k v, b.ex k v = 0) :
    MemAuth m a d := by
  obtain ⟨hs, ⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := h
  refine ⟨hs.congr fun k v => by simp [hb], ⟨fun L hL => ?_, ?_, fun hp L => ?_⟩, fun hp => h4 ?_,
    fun k L hk => ?_, fun v hv => h6 v (by simp; omega), h7⟩
  · have := h1 L (by simp; omega); simp at this; omega
  · have := h2; simp at this; omega
  · have := h3 (by simp; omega) L; simp at this; omega
  · simp; omega
  · have := h5 k L hk; simp at this; omega

/-- **The running thread's token**: next to a cell without a `cur` token, the memory authorizes
`cur m.current`. -/
theorem addCur (h : MemAuth m c d) : MemAuth m ((curCell m.current).add c) d := by
  obtain ⟨hs, ⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := h
  refine ⟨hs.congrTid fun k v t hk => ?_, ⟨fun L hL => ?_, by simpa [curCell] using h2,
    fun hp L => ?_⟩, fun hp => h4 (by simpa [curCell] using hp), fun k L hk => by simp [curCell, h5 k L hk],
    fun v hv => ?_, h7⟩
  · have : k ≠ .cur := by rintro rfl; cases hk
    simp [curCell, this]
  · have := h1 L (by simpa [curCell] using hL); simpa [curCell] using this
  · simpa [curCell] using h3 (by simpa [curCell] using hp) L
  · by_cases e : v = (m.current, 0)
    · rw [e]
    · exact h6 v (by simpa [curCell, e] using hv)

/-- **A `cur` token can be dropped**: the memory demands none. -/
theorem dropCur {t : ThreadId} (h : MemAuth m ((curCell t).add c) d) : MemAuth m c d := by
  obtain ⟨hs, ⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := h
  refine ⟨hs.congrTid fun k v t' hk => ?_, ⟨fun L hL => ?_, by simpa [curCell] using h2,
    fun hp L => ?_⟩, fun hp => h4 (by simpa [curCell] using hp), fun k L hk => by
      simpa [curCell] using h5 k L hk, fun v hv => h6 v (by simp; omega), h7⟩
  · have : k ≠ .cur := by rintro rfl; cases hk
    simp [curCell, this]
  · have := h1 L (by simpa [curCell] using hL); simpa [curCell] using this
  · simpa [curCell] using h3 (by simpa [curCell] using hp) L

/-- **Only the stack tokens change** (a stack push or pop): a cell with the same counted
fragments, authorities and `cur` token, whose stack tokens the new memory authorizes, in a
memory with the same step count and current thread. -/
theorem restack {c' : KCell} (h : MemAuth m c d) (hs : StackAuth m' c') (ht : m'.ticks = m.ticks)
    (hc : m'.current = m.current) (hns : m.NoStack → m'.NoStack) (hf : ∀ k, c'.frag k = c.frag k)
    (ha : ∀ k n, c'.auth k n = c.auth k n) (hx : ∀ v, c'.ex .cur v = c.ex .cur v)
    (hd : m'.dev = m.dev := by first | rfl | assumption | simp) : MemAuth m' c' d :=
  ⟨hs, ⟨fun L hL => by rw [ht, hf]; exact h.tick.meter L (by rw [← ha]; exact hL),
    by rw [ht, hf]; exact h.tick.spent, fun hp L => by
      rw [ha]; exact h.tick.plain (by rw [← hf]; exact hp) L⟩,
    fun hp => hns (h.noStack (by rw [← hf]; exact hp)), fun k L hk => by rw [ha]; exact h.onlyCred k L hk,
    fun v hv => by rw [hc]; exact h.cur v (by rw [← hx]; exact hv),
    fun D hD => by rw [hd]; exact h.dev D hD⟩

/-- **A scheduler stop**: a memory with another current thread authorizes a cell without a `cur`
token (a thread holds `cur` only while it runs). -/
theorem stop (h : MemAuth m c d) (hc : ∀ v, c.ex .cur v = 0) (t : ThreadId) :
    MemAuth { m with current := t } c d :=
  ⟨h.stack.keep_shape rfl rfl rfl fun _ blk' hb' => ⟨blk', hb', rfl, rfl, rfl, rfl⟩,
    ⟨h.tick.meter, h.tick.spent, h.tick.plain⟩, h.noStack, h.onlyCred,
    fun v hv => absurd (hc v) (by omega), h.dev⟩

/-- **The start**: in a memory without stack budgets the empty cells are authorized. -/
theorem unit (hm : m.NoStack) : MemAuth m ACell.unit DCell.unit :=
  ⟨StackAuth.of_noBudget hm fun _ _ _ => rfl, ⟨fun _ h => absurd h (by simp), by simp,
    fun h => absurd h (by simp)⟩, fun h => absurd h (by simp), fun _ _ _ => rfl,
    fun _ h => absurd h (by simp), dev_unit m⟩

end MemAuth

end Full
end Zig
