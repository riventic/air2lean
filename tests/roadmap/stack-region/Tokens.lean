import ZigLean.Sep.Full.StackDepth
import ZigLean.Mem.Reuse

/-! Stack depth tokens (`docs/sep-full-state.md` §Stack depth, `ZigLean/Sep/Full/StackDepth.lean`):
kernel-checked instances on a start memory with a main-thread budget of 64 bytes.

* `start_auth`: the start memory authorizes `sp 0 64 0` (the introduction, `StackAuth.withStack`).
* `no_second_sp`, `no_mint_start`: no second `sp 0` fragment, and none from nothing.
* `room_from_sp`: `sp 0 64 0` gives room for a stack block of charge 16 (`StackAuth.allocOk`).
* `alloc_with_sp`: after that `alloc`, the memory authorizes `sp 0 64 16` and the block's entry
  token (`StackAuth.alloc`).
* `push_without_sp_cx`: the same `alloc` without the token breaks the authority of a frame that
  holds `sp 0 64 0`. So under a budget every stack push goes through `sp`: a partial
  `alloc .stack` rule with precondition `emp` does not hold once `StackAuth` is part of `Holds`
  (correction (d): the rules for other kinds need `kind ≠ .stack`; stack pushes take `plain`).
* `drop_sp_cx`, `unit_budget_cx`: dropping the token `sp`, or starting from no ghost state,
  breaks the authority under a budget (corrections (a) and (b)).
* `placement_cx`: a placement with a smaller address space breaks the reserve layout
  (correction (c)). -/

open Zig Zig.Full

/-- An address space of 4096 + 256 bytes. -/
def small : Placement := { propose := fun _ => none, addrLimit := 4096 + 256 }

/-- The start memory with a main-thread stack budget of 64 bytes. -/
def m₀ : Mem := ({ place := small } : Mem).withStack 64

theorem reserve₀ : ({ place := small } : Mem).reserveAt? 0 64 = some 4096 := by decide +kernel

theorem noBudget₀ (t : Nat) : (({ place := small } : Mem).stackOf t).budget = none := by
  simp [Mem.stackOf]; rfl

theorem start_auth : StackAuth m₀ ((spCell 0 64 0).add ACell.unit) :=
  StackAuth.withStack noBudget₀ (fun _ _ _ => rfl) reserve₀

theorem no_second_sp (S D S' D' : Nat) :
    ¬ ((spCell 0 S D).add ((spCell 0 S' D').add ACell.unit)).Valid :=
  spCell_excl 0 S D S' D' _

theorem valid₀ : ((spCell 0 64 0).add ACell.unit).Valid :=
  ACell.Valid.add_ex _ ACell.valid_unit fun _ => rfl

theorem no_mint_start (D : Nat) (hv : ((spCell 0 64 D).add ((spCell 0 64 0).add ACell.unit)).Valid) :
    ¬ StackAuth m₀ ((spCell 0 64 D).add ((spCell 0 64 0).add ACell.unit)) :=
  start_auth.no_mint 0 64 D hv

theorem budget₀ : (m₀.stackOf 0).budget = some 64 := by decide +kernel

theorem current₀ : m₀.current = 0 := by decide +kernel

theorem room_from_sp : m₀.allocOk .stack 8 8 = true :=
  start_auth.allocOk (D := 0) valid₀ current₀ budget₀ (by simp [spCell]) (by decide)

theorem alloc_with_sp :
    StackAuth (m₀.afterAlloc .stack 8 8)
      ((spCell 0 64 16).add ((entCell 0 (some 0) 0 16).add ACell.unit)) := by
  have h := (StackAuth.alloc (D := 0) (size := 8) (align := 8) start_auth valid₀ current₀ budget₀
    (by decide)).2.2
  have e₁ : m₀.blocks.size = 0 := by decide +kernel
  have e₂ : stackCharge 8 8 = 16 := rfl
  rw [e₁, e₂] at h
  exact h

theorem depth₁ : (m₀.afterAlloc .stack 8 8).stackDepth 0 = 16 := by decide +kernel

theorem budget₁ : ((m₀.afterAlloc .stack 8 8).stackOf 0).budget = some 64 := by decide +kernel

/-- A push without `sp` breaks the frame's `sp 0 64 0`: the depth is 16 after it. -/
theorem push_without_sp_cx : ¬ StackAuth (m₀.afterAlloc .stack 8 8) ((spCell 0 64 0).add ACell.unit) := by
  intro h
  obtain ⟨-, -, L, hent⟩ := h.of_budget (D := 0) valid₀ budget₁ (by simp [spCell])
  have := hent.depth_le
  rw [← Mem.stackDepth_eq, depth₁] at this
  omega

/-- **The empty ghost state is not authorized in every memory** (correction (b): `GOk.unit`,
`MemAuth.unit` and `FOwned.start` need `Mem.NoStack`): under a budget, no stack token at all is
not authorized. -/
theorem unit_budget_cx : ¬ StackAuth m₀ ACell.unit := by
  intro h
  have h0 := h.thread 0
  unfold ThreadOk at h0
  rw [budget₀] at h0
  obtain ⟨D, hD, -⟩ := h0
  simp [ACell.unit] at hD

/-- **Dropping an exclusive token breaks `Holds`** (correction (a): the drop rules need
`Ghost.Affine`): the start memory authorizes `sp 0 64 0` and not the cell without it. -/
theorem drop_sp_cx : StackAuth m₀ ((spCell 0 64 0).add ACell.unit) ∧ ¬ StackAuth m₀ ACell.unit :=
  ⟨start_auth, unit_budget_cx⟩

/-- An address space of 16 bytes: below the main thread's reserve. -/
def tiny : Placement := { propose := fun _ => none, addrLimit := 16 }

theorem base₀ : (m₀.stackOf 0).base = 4096 := by decide +kernel

/-- **A smaller address space breaks the reserve** (correction (c): `withPlacement` needs
`m.NoStack ∨ m.place.addrLimit ≤ σ.addrLimit`): the reserve of `m₀` lies above the limit of
`tiny`, so no cell is authorized after the placement change. -/
theorem placement_cx (c : KCell) : ¬ StackAuth (m₀.withPlacement tiny) c := by
  intro h
  have h0 := h.thread 0
  unfold ThreadOk at h0
  have hb : ((m₀.withPlacement tiny).stackOf 0).budget = some 64 := budget₀
  rw [hb] at h0
  obtain ⟨D, -, hr, -⟩ := h0
  have hl := hr.limit
  have e : ((m₀.withPlacement tiny).stackOf 0).base = 4096 := base₀
  rw [e] at hl
  simp [Mem.withPlacement, tiny] at hl

#print axioms start_auth
#print axioms no_mint_start
#print axioms room_from_sp
#print axioms alloc_with_sp
#print axioms push_without_sp_cx
#print axioms drop_sp_cx
#print axioms unit_budget_cx
#print axioms placement_cx
