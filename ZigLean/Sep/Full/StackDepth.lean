import ZigLean.Sep.Full.ACell
import ZigLean.Mem.Lemmas
import ZigLean.Conc.Lemmas

/-!
# Stack depth tokens (`docs/sep-full-state.md` §Stack depth)

The memory-authority instance of the authoritative counter cell (`ZigLean/Sep/Full/ACell.lean`)
for the per-thread stack budget of the memory model (MM-18, `Mem.stacks`). Keys (`AKey`):

* `sp t` holds the exclusive fragment `(S, D)` (**`sp t S D`**): thread `t` has the budget `S`
  and its stack depth (`Mem.stackDepth`) is at most `D`. One per thread with a budget, none for
  a thread without one: the memory decides (`ACell.MemEx`), so no judgment creates one
  (`StackAuth.no_mint`).
* `blk t b` and `frm t ℓ` hold the exclusive fragment `(ℓ, c)` (**`ent t o ℓ c`**): the live
  stack entry of `t` for block `b` (or the frame pushed at logical depth `ℓ`), pushed at logical
  depth `ℓ` with charge `c`.
* `cred` is the credits' key (frame authority), `spent` the receipts of steps run,
  `unmetered` the plain mode of steps and `noStack` the fact that no thread has a stack budget
  (`ZigLean/Sep/Full/MemAuth.lean`).

`StackAuth m c` is the memory-authority conjunct about the whole ghost cell `c` (resource and
frame): every thread with a budget has exactly one `sp` fragment, the live entries of each
thread carry their `ent` fragments in push order, below `D` (`EntOk`), and the blocks inside each
reserve are that thread's own fallback blocks, where the LIFO fallback put them (`StackLayoutOk`).

The step lemmas are the memory side of the rules: with `sp t S D` and `D + c ≤ S` a stack block
has room (`StackAuth.allocOk`, the LIFO fallback is valid), `alloc` turns `sp t S D` into
`sp t S (D + c) ⋆ ent t b D c` (`StackAuth.alloc`), `free` of that block turns `sp t S (ℓ + c) ⋆
ent t b ℓ c` back into `sp t S ℓ` (`StackAuth.free_top`), `enterFrame`/`leaveFrame` likewise
(`StackAuth.enterFrame`, `StackAuth.leaveFrame`). A step that keeps every stack state keeps
`StackAuth` under the premises of `StackAuth.keep` (instances: `StackAuth.allocOther`,
`StackAuth.free`, `StackAuth.keep_shape`). Each other primitive proves those premises at the
wiring step; the thread primitives (`clone`, its exit, spawn) change stack states and need
their own lemmas.
-/

namespace Zig

/-! ## `Array.popWhile` -/

/-- `popWhile` keeps a prefix, pops only elements that satisfy `p`, and its last element does
not satisfy `p`. -/
theorem popWhile_spec {α : Type} (p : α → Bool) : ∀ (n : Nat) (as : Array α), as.size = n →
    (as.popWhile p).size ≤ as.size ∧
    (∀ i, i < (as.popWhile p).size → (as.popWhile p)[i]? = as[i]?) ∧
    (∀ i (h : i < as.size), (as.popWhile p).size ≤ i → p as[i] = true) ∧
    ∀ e, (as.popWhile p).back? = some e → p e = false := by
  intro n
  induction n with
  | zero =>
    intro as h
    have : as = #[] := Array.eq_empty_of_size_eq_zero h
    subst this
    simp
  | succ n ih =>
    intro as h
    rw [Array.popWhile]
    have hpos : as.size > 0 := by omega
    rw [dif_pos hpos]
    split
    · rename_i hp
      obtain ⟨h1, h2, h3, h4⟩ := ih as.pop (by simp; omega)
      refine ⟨by simp at h1; omega, fun i hi => ?_, fun i hi hk => ?_, h4⟩
      · rw [h2 i hi, Array.getElem?_pop]
        have : i < as.size - 1 := by have := Nat.lt_of_lt_of_le hi h1; simpa using this
        simp [this]
      · by_cases hl : i = as.size - 1
        · subst hl; exact hp
        · have hi' : i < as.pop.size := by simp; omega
          have := h3 i hi' hk
          simpa [Array.getElem_pop] using this
    · rename_i hp
      refine ⟨Nat.le_refl _, fun _ _ => rfl, fun i hi hk => absurd hi (by omega), fun e he => ?_⟩
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)] at he
      cases he; simpa using hp

namespace Full

/-! ## Keys and token cells -/

/-- The keys of the authoritative counter cell of the full-state logic (module doc): `t` a
`ThreadId`, `b` a `BlockId` (written `Nat`, so that `omega` sees the comparisons). -/
inductive AKey where
  | cred
  | sp (t : Nat)
  | blk (t b : Nat)
  | frm (t ℓ : Nat)
  | spent
  | unmetered
  | noStack
  | cur
  deriving DecidableEq

/-- The authoritative counter cell of the full-state logic (`Ghost.ac`): the stack tokens, the
credits, the step receipts and the plain-mode facts. -/
abbrev KCell := ACell AKey (Nat × Nat)

/-- The thread of a key (none for the credits, the step keys, `noStack` and `cur`). -/
def AKey.tid : AKey → Option ThreadId
  | .cred | .spent | .unmetered | .noStack | .cur => none
  | .sp t => some t
  | .blk t _ => some t
  | .frm t _ => some t

/-- The key of the token of stack entry `e` of thread `t` at logical depth `ℓ`: its block's,
or (a frame) its depth's. -/
def entKey (t : ThreadId) (e : StackEntry) (ℓ : Nat) : AKey :=
  match e.block with
  | some b => .blk t b
  | none => .frm t ℓ

/-- **`sp t S D`**: thread `t` has the budget `S` and its stack depth is at most `D`. -/
def spCell (t : ThreadId) (S D : Nat) : KCell := ACell.exAt (.sp t) (S, D)

/-- The key of the token of an entry for block `o` (a frame: `none`) at logical depth `D`. -/
def newKey (t : ThreadId) (o : Option Nat) (D : Nat) : AKey :=
  match o with
  | some b => .blk t b
  | none => .frm t D

@[simp] theorem newKey_some (t b D : Nat) : newKey t (some b) D = .blk t b := rfl
@[simp] theorem newKey_none (t D : Nat) : newKey t none D = .frm t D := rfl

/-- **`ent t o ℓ c`**: thread `t`'s live stack entry for block `o` (a frame: `none`), pushed at
logical depth `ℓ` with charge `c`. -/
def entCell (t : ThreadId) (o : Option BlockId) (ℓ c : Nat) : KCell :=
  ACell.exAt (newKey t o ℓ) (ℓ, c)

/-- **`cur t`**: thread `t` runs (`m.current = t`, `MemAuth.cur`). One key for every thread, so at
most one such fragment exists: a thread's resources hold it only while that thread runs
(`docs/sep-full-state.md` §Stack depth, the current thread). -/
def curCell (t : ThreadId) : KCell := ACell.exAt .cur (t, 0)

/-! ## The memory-authority conjunct -/

/-- The live entries of `t`'s stack `es` carry their tokens at logical depths `L i`, in push
order, below `D`; every frame token names a live frame, every block token a block that exists,
and a live one an entry. -/
structure EntOk (c : KCell) (blocks : Array Block) (t : ThreadId) (es : Array StackEntry)
    (D : Nat) (L : Nat → Nat) : Prop where
  live : ∀ i (hi : i < es.size), es[i].liveIn blocks = true →
    0 < es[i].charge ∧ es[i].base ≤ L i ∧ L i + es[i].charge ≤ D ∧
      c.ex (entKey t es[i] (L i)) (L i, es[i].charge) = 1
  order : ∀ i j (hi : i < es.size) (hj : j < i), es[i].liveIn blocks = true →
    es[j].liveIn blocks = true → L j + es[j].charge ≤ L i
  frm : ∀ ℓ v, 0 < c.ex (.frm t ℓ) v →
    ∃ i, ∃ hi : i < es.size, es[i].liveIn blocks = true ∧ es[i].block = none ∧ L i = ℓ
  blk : ∀ b v, 0 < c.ex (.blk t b) v → b < blocks.size ∧
    ((blocks[b]?.map (·.live)).getD false = true → ∃ i, ∃ hi : i < es.size, es[i].block = some b)

/-- The reserve `[s.base, s.base + S)` of a thread with the budget `S` holds only that thread's
fallback blocks, each in the slot of its entry counted from the reserve's end; the entries are
pushed in order and name blocks that exist; the reserve lies in the address space. -/
structure StackLayoutOk (m : Mem) (s : StackState) (S : Nat) : Prop where
  limit : s.base + S ≤ m.place.addrLimit
  order : ∀ i j (hi : i < s.entries.size) (hj : j < i),
    s.entries[j].base + s.entries[j].charge ≤ s.entries[i].base
  ids : ∀ i (hi : i < s.entries.size) (b : Nat), s.entries[i].block = some b → b < m.blocks.size
  inRes : ∀ (b : Nat) (blk : Block), m.blocks[b]? = some blk → blk.clearOf s.base S = false →
    ∃ i, ∃ hi : i < s.entries.size, s.entries[i].block = some b ∧
      s.base + S ≤ blk.addr + (s.entries[i].base + s.entries[i].charge) ∧
      blk.addr + blk.bytes.size + s.entries[i].base ≤ s.base + S

/-- Thread `t`'s part of `StackAuth`: with a budget `S`, one token `sp t S D`, the layout of its
reserve and its entries' tokens; without one, no stack token of `t`. -/
def ThreadOk (m : Mem) (c : KCell) (t : ThreadId) : Prop :=
  match (m.stackOf t).budget with
  | none => (∀ v, c.ex (.sp t) v = 0) ∧ (∀ b v, c.ex (.blk t b) v = 0) ∧ ∀ ℓ v, c.ex (.frm t ℓ) v = 0
  | some S => ∃ D, c.ex (.sp t) (S, D) = 1 ∧ StackLayoutOk m (m.stackOf t) S ∧
      ∃ L, EntOk c m.blocks t (m.stackOf t).entries D L

/-- **The memory authority of the stack tokens** (module doc): every thread's `ThreadOk`, and
the reserves of two threads with a budget are apart. -/
structure StackAuth (m : Mem) (c : KCell) : Prop where
  thread : ∀ t, ThreadOk m c t
  apart : ∀ t t' S S', t ≠ t' → (m.stackOf t).budget = some S → (m.stackOf t').budget = some S' →
    S = 0 ∨ S' = 0 ∨ (m.stackOf t).base + S ≤ (m.stackOf t').base ∨
      (m.stackOf t').base + S' ≤ (m.stackOf t).base

/-! ## Introduction: the start memory -/

/-- Without any stack budget, a cell without stack tokens is authorized. -/
theorem StackAuth.of_noBudget {m : Mem} {c : KCell} (hb : ∀ t, (m.stackOf t).budget = none)
    (hc : ∀ k v, k ≠ .cred → c.ex k v = 0) : StackAuth m c := by
  refine ⟨fun t => ?_, fun t _ S _ _ h => by rw [hb t] at h; cases h⟩
  unfold ThreadOk; rw [hb t]
  exact ⟨fun v => hc _ v (by simp), fun b v => hc _ v (by simp), fun ℓ v => hc _ v (by simp)⟩

theorem Mem.reserveAt?_placeOk {m : Mem} {t S A : Nat} (h : m.reserveAt? t S = some A) :
    m.placeOk A S 16 = true := by
  unfold Mem.reserveAt? Mem.reserveAt?.fit at h
  dsimp only at h
  split at h
  · split at h
    · cases h; assumption
    · split at h
      · cases h; assumption
      · cases h
  · split at h
    · cases h; assumption
    · cases h

/-! ## Non-mintable and exclusive -/

/-- The memory's demand on key `sp t` (`ACell.MemEx`): one fragment with the budget `S` if `t`
has one, else none. -/
theorem StackAuth.memEx {m : Mem} {c : KCell} (h : StackAuth m c) (t : ThreadId) :
    c.MemEx (.sp t) ((m.stackOf t).budget.map fun S v => v.1 = S) := by
  have := h.thread t
  unfold ThreadOk at this
  cases hb : (m.stackOf t).budget with
  | none => rw [hb] at this; exact this.1
  | some S =>
    rw [hb] at this
    obtain ⟨D, hD, -⟩ := this
    exact ⟨(S, D), hD, rfl⟩

/-- **`sp` cannot be minted**: next to a cell that the memory authorizes, one more `sp t`
fragment is invalid or unauthorized (`ACell.MemEx.no_mint`). -/
theorem StackAuth.no_mint {m : Mem} {c : KCell} (h : StackAuth m c) (t : ThreadId)
    (S D : Nat) (hv' : ((spCell t S D).add c).Valid) : ¬ StackAuth m ((spCell t S D).add c) :=
  fun h' => ACell.MemEx.no_mint (S, D) (h.memEx t) hv' (h'.memEx t)

/-- **`sp` is exclusive**: two `sp t` fragments are invalid. -/
theorem spCell_excl (t : ThreadId) (S D S' D' : Nat) (G : KCell) :
    ¬ ((spCell t S D).add ((spCell t S' D').add G)).Valid :=
  ACell.exAt_excl

/-! ## The held entries and the depth -/

section Held

variable {blocks : Array Block} {es : Array StackEntry}

/-- The predicate that `StackState.held` pops. -/
abbrev deadIn (blocks : Array Block) (e : StackEntry) : Bool := !e.liveIn blocks

theorem held_eq (s : StackState) (blocks : Array Block) :
    s.held blocks = s.entries.popWhile (deadIn blocks) := rfl

theorem popHeld_size_le : (es.popWhile (deadIn blocks)).size ≤ es.size :=
  (popWhile_spec _ _ es rfl).1

theorem popHeld_get {i : Nat} (hi : i < (es.popWhile (deadIn blocks)).size) :
    (es.popWhile (deadIn blocks))[i]? = es[i]? :=
  (popWhile_spec _ _ es rfl).2.1 i hi

/-- A live entry is held. -/
theorem lt_popHeld {i : Nat} (hi : i < es.size) (hl : es[i].liveIn blocks = true) :
    i < (es.popWhile (deadIn blocks)).size := by
  refine Nat.lt_of_not_le fun hk => ?_
  have := (popWhile_spec _ _ es rfl).2.2.1 i hi hk
  simp [hl] at this

theorem stackEnd_eq (h : Array StackEntry) :
    stackEnd h = if hk : 0 < h.size then h[h.size - 1].base + h[h.size - 1].charge else 0 := by
  unfold stackEnd
  by_cases hk : 0 < h.size
  · rw [dif_pos hk, Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  · rw [dif_neg hk, Array.back?_eq_getElem?, Array.getElem?_eq_none (by omega)]

/-- The topmost held entry is live and is the entry at the same index. -/
theorem popHeld_top (hk : 0 < (es.popWhile (deadIn blocks)).size) :
    ∃ hi : (es.popWhile (deadIn blocks)).size - 1 < es.size,
      (es.popWhile (deadIn blocks))[(es.popWhile (deadIn blocks)).size - 1] =
        es[(es.popWhile (deadIn blocks)).size - 1] ∧
      es[(es.popWhile (deadIn blocks)).size - 1].liveIn blocks = true := by
  have hle : (es.popWhile (deadIn blocks)).size ≤ es.size := popHeld_size_le
  have hi : (es.popWhile (deadIn blocks)).size - 1 < es.size := by omega
  have he := popHeld_get (es := es) (blocks := blocks)
    (i := (es.popWhile (deadIn blocks)).size - 1) (by omega)
  rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hi] at he
  have heq := Option.some.inj he
  refine ⟨hi, heq, ?_⟩
  have := (popWhile_spec _ _ es rfl).2.2.2 _ (by
    rw [Array.back?_eq_getElem?]
    exact Array.getElem?_eq_getElem
      (by omega : (es.popWhile (deadIn blocks)).size - 1 < (es.popWhile (deadIn blocks)).size))
  rw [heq] at this
  simpa using this

theorem popHeld_getElem {i : Nat} (hi : i < (es.popWhile (deadIn blocks)).size) :
    (es.popWhile (deadIn blocks))[i] = es[i]'(Nat.lt_of_lt_of_le hi popHeld_size_le) := by
  have := popHeld_get (es := es) (blocks := blocks) hi
  rw [Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi popHeld_size_le)] at this
  exact Option.some.inj this

/-- Every held entry ends at or below the depth (the entries are pushed in order). -/
theorem end_le_held
    (hord : ∀ i j (hi : i < es.size) (hj : j < i), es[j].base + es[j].charge ≤ es[i].base)
    {i : Nat} (hi : i < es.size) (hk : i < (es.popWhile (deadIn blocks)).size) :
    es[i].base + es[i].charge ≤ stackEnd (es.popWhile (deadIn blocks)) := by
  obtain ⟨hi', heq, -⟩ := popHeld_top (es := es) (blocks := blocks) (by omega)
  rw [stackEnd_eq, dif_pos (by omega), heq]
  by_cases e : i = (es.popWhile (deadIn blocks)).size - 1
  · subst e; exact Nat.le_refl _
  · have := hord _ i hi' (by omega); omega

/-- Every live entry ends at or below the depth. -/
theorem end_le_depth
    (hord : ∀ i j (hi : i < es.size) (hj : j < i), es[j].base + es[j].charge ≤ es[i].base)
    {i : Nat} (hi : i < es.size) (hl : es[i].liveIn blocks = true) :
    es[i].base + es[i].charge ≤ stackEnd (es.popWhile (deadIn blocks)) :=
  end_le_held hord hi (lt_popHeld hi hl)

/-- With the entries' tokens below `D`, the depth is at most `D`. -/
theorem EntOk.depth_le {c : KCell} {t D : Nat} {L : Nat → Nat} (h : EntOk c blocks t es D L) :
    stackEnd (es.popWhile (deadIn blocks)) ≤ D := by
  rw [stackEnd_eq]
  split
  · rename_i hk
    obtain ⟨hi, heq, hl⟩ := popHeld_top (es := es) (blocks := blocks) hk
    rw [heq]
    obtain ⟨-, h1, h2, -⟩ := h.live _ hi hl
    omega
  · exact Nat.zero_le _

end Held

theorem _root_.Zig.Mem.stackDepth_eq (m : Mem) (t : ThreadId) :
    m.stackDepth t = stackEnd ((m.stackOf t).entries.popWhile (deadIn m.blocks)) := rfl

/-- The facts of `ThreadOk` for a thread with a budget, at the `D` of a token that is present. -/
theorem StackAuth.of_budget {m : Mem} {c : KCell} {t S D : Nat} (h : StackAuth m c) (hv : c.Valid)
    (hS : (m.stackOf t).budget = some S) (hD : 0 < c.ex (.sp t) (S, D)) :
    c.ex (.sp t) (S, D) = 1 ∧ StackLayoutOk m (m.stackOf t) S ∧
      ∃ L, EntOk c m.blocks t (m.stackOf t).entries D L := by
  have := h.thread t
  unfold ThreadOk at this
  rw [hS] at this
  obtain ⟨D', h1, h2, h3⟩ := this
  have := (hv (.sp t)).2.2.2.2 (S, D) (S, D') hD (by omega)
  cases this
  exact ⟨h1, h2, h3⟩

theorem _root_.Zig.Mem.addrFree_iff {m : Mem} {A n : Nat} :
    m.addrFree A n = true ↔
      ∀ (b : Nat) (blk : Block), m.blocks[b]? = some blk → blk.clearOf A n = true := by
  unfold Mem.addrFree
  rw [Array.all_eq_true]
  constructor
  · intro h b blk hb
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
    exact h b hi
  · intro h i hi
    exact h i _ (Array.getElem?_eq_getElem hi)

/-- The LIFO fallback of a stack block lies in the reserve, below the depth: with
`d + size + a ≤ S` (`a` the alignment, at least 1) it starts after `base` and ends at or below
`base + S - d`, one alignment step below at most. -/
theorem fallback_bounds {base S d size align : Nat} (h : d + stackCharge size align ≤ S) :
    base + 1 ≤ alignDown (base + S - d - size) (Nat.max align 1) ∧
      alignDown (base + S - d - size) (Nat.max align 1) + size + d ≤ base + S ∧
      base + S < alignDown (base + S - d - size) (Nat.max align 1) + stackCharge size align + d ∧
      alignDown (base + S - d - size) (Nat.max align 1) % Nat.max align 1 = 0 := by
  have ha : 0 < Nat.max align 1 := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_right _ _)
  unfold alignDown stackCharge at *
  generalize Nat.max align 1 = a at *
  have h1 := Nat.div_add_mod (base + S - d - size) a
  have h2 := Nat.mod_lt (base + S - d - size) ha
  rw [Nat.mul_comm] at h1
  refine ⟨by omega, by omega, by omega, Nat.mul_mod_left _ _⟩

/-- A placed address of a stack block is valid at the alignment that `allocOk` checks. -/
theorem placedFor?_fitOk {m : Mem} {size align A : Nat}
    (h : m.placedFor? .stack size align = some A) : m.fitOk A size (Nat.max align 1) = true := by
  obtain ⟨h0, ha, hl, hf⟩ := Mem.placedFor?_ok h
  have : Nat.max align 1 = align := by
    cases align with
    | zero => simp at ha; omega
    | succ n => simp
  rw [this]
  simp [Mem.fitOk, h0, ha, hl, hf]

theorem _root_.Zig.Block.clearOf_false_iff {blk : Block} {A n : Nat} :
    blk.clearOf A n = false ↔ blk.live = true ∧ n ≠ 0 ∧ blk.kind.mappedLo < blk.bytes.size ∧
      blk.addr + blk.kind.mappedLo < A + n ∧ A < blk.addr + blk.bytes.size := by
  simp only [Block.clearOf, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
    beq_eq_false_iff_ne, decide_eq_false_iff_not, Nat.not_le]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- **Room from `sp`**: the running thread `t` with the token `sp t S D` and `D + c ≤ S` (`c`
the block's charge) has room for the stack block: its charge fits, and its address (the
placement's, or the LIFO fallback in the reserve) is valid. -/
theorem StackAuth.allocOk {m : Mem} {c : KCell} {t S D size align : Nat} (h : StackAuth m c)
    (hv : c.Valid) (hcur : m.current = t) (hS : (m.stackOf t).budget = some S)
    (hD : 0 < c.ex (.sp t) (S, D)) (hfit : D + stackCharge size align ≤ S) :
    m.allocOk .stack size align = true := by
  obtain ⟨-, hlay, L, hent⟩ := h.of_budget hv hS hD
  have hdep : m.stackDepth t ≤ D := hent.depth_le
  subst hcur
  simp only [Mem.allocOk, Mem.stackBudget?, hS, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, ?_⟩
  simp only [Mem.allocAddr, Mem.stackBudget?, hS]
  cases hp : m.placedFor? .stack size align with
  | some A => exact placedFor?_fitOk hp
  | none =>
    simp only [Option.getD_none, Mem.stackFallback]
    obtain ⟨b1, b2, b3, b4⟩ := fallback_bounds (base := (m.stackOf m.current).base)
      (h := Nat.le_trans (Nat.add_le_add_right hdep _) hfit)
    generalize alignDown _ _ = A at b1 b2 b3 b4
    simp only [Mem.fitOk, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨by omega, b4⟩, by have := hlay.limit; omega⟩, Mem.addrFree_iff.mpr fun b blk hb => ?_⟩
    refine Classical.byContradiction fun hc => ?_
    simp only [Bool.not_eq_true] at hc
    obtain ⟨hlive, hn, hlo, h1, h2⟩ := Block.clearOf_false_iff.mp hc
    have hres : blk.clearOf (m.stackOf m.current).base S = false := by
      unfold stackCharge at hfit
      exact Block.clearOf_false_iff.mpr ⟨hlive, by omega, hlo, by omega, by omega⟩
    obtain ⟨i, hi, hbi, e1, -⟩ := hlay.inRes b blk hb hres
    have hli : (m.stackOf m.current).entries[i].liveIn m.blocks = true := by
      simp [StackEntry.liveIn, hbi, hb, hlive]
    have := end_le_depth hlay.order hi hli
    rw [← Mem.stackDepth_eq] at this
    omega

/-! ## Threads that a step does not push to -/

theorem getD_setStackAt (ss : Array StackState) (t t' : Nat) (s : StackState) :
    (setStackAt ss t s).getD t' default = if t' = t then s else ss.getD t' default := by
  unfold setStackAt
  by_cases ht : t < ss.size
  · simp only [ht, ite_true]
    rw [Array.set!_eq_setIfInBounds]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
    by_cases e : t' = t
    · subst e; simp [ht]
    · simp [Ne.symm e, e]
  · simp only [ht, ite_false]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_append,
      Array.size_replicate]
    by_cases e : t' = t
    · subst e
      have : t' = ss.size + (t' - ss.size) := by omega
      simp [← this]
    · have : t' ≠ ss.size + (t - ss.size) := by omega
      simp only [this, ite_false, e, Array.getElem?_append, Array.getElem?_replicate]
      by_cases h1 : t' < ss.size
      · simp [h1]
      · simp only [h1, ite_false, Array.getElem?_eq_none (Nat.le_of_not_lt h1)]
        split <;> rfl

/-- **A thread that the step does not push to keeps its part** (`ThreadOk`): its stack state
and its tokens stay; no live block of the new memory was dead or is new inside its reserve,
except blocks clear of the reserve; a block that stays in the reserve keeps its address and
does not grow. -/
theorem ThreadOk.transfer {m m' : Mem} {c c' : KCell} {t : Nat} (h : ThreadOk m c t)
    (hst : m'.stackOf t = m.stackOf t) (hlim : m.place.addrLimit ≤ m'.place.addrLimit)
    (hsz : m.blocks.size ≤ m'.blocks.size)
    (hold : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → blk'.live = true →
      b < m.blocks.size → ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
        ((∀ S, (m.stackOf t).budget = some S → blk'.clearOf (m.stackOf t).base S = true) ∨
          (blk.addr = blk'.addr ∧ blk'.bytes.size ≤ blk.bytes.size ∧
            blk.kind.mappedLo ≤ blk'.kind.mappedLo)))
    (hnew : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → m.blocks.size ≤ b →
      ∀ S, (m.stackOf t).budget = some S → blk'.clearOf (m.stackOf t).base S = true)
    (hc : ∀ k v, k.tid = some t → c'.ex k v = c.ex k v) : ThreadOk m' c' t := by
  unfold ThreadOk at h ⊢
  rw [hst]
  cases hb : (m.stackOf t).budget with
  | none =>
    rw [hb] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨fun v => by rw [hc _ _ rfl]; exact h1 v, fun b v => by rw [hc _ _ rfl]; exact h2 b v,
      fun ℓ v => by rw [hc _ _ rfl]; exact h3 ℓ v⟩
  | some S =>
    rw [hb] at h
    obtain ⟨D, hD, hlay, L, hent⟩ := h
    have hlive : ∀ i (hi : i < (m.stackOf t).entries.size),
        (m.stackOf t).entries[i].liveIn m'.blocks = true →
          (m.stackOf t).entries[i].liveIn m.blocks = true := by
      intro i hi hl
      unfold StackEntry.liveIn at hl ⊢
      split at hl
      · rename_i b hbi
        have hbs := hlay.ids i hi b hbi
        cases hb' : m'.blocks[b]? with
        | none => simp [hb'] at hl
        | some blk' =>
          simp only [hb', Option.map_some, Option.getD_some] at hl
          obtain ⟨blk, hbk, hl', -⟩ := hold b blk' hb' hl hbs
          simp [hbk, hl']
      · simp at hl ⊢; exact hl
    have hframe : ∀ i (hi : i < (m.stackOf t).entries.size), (m.stackOf t).entries[i].block = none →
        (m.stackOf t).entries[i].liveIn m'.blocks = (m.stackOf t).entries[i].liveIn m.blocks := by
      intro i hi hbi; simp [StackEntry.liveIn, hbi]
    refine ⟨D, by rw [hc _ _ rfl]; exact hD, ⟨Nat.le_trans hlay.limit hlim, hlay.order,
      fun i hi b hbi => Nat.lt_of_lt_of_le (hlay.ids i hi b hbi) hsz, ?_⟩, L, ⟨?_, ?_, ?_, ?_⟩⟩
    · intro b blk' hb' hclr
      obtain ⟨hl', hn, hlo', h1', h2'⟩ := Block.clearOf_false_iff.mp hclr
      by_cases hbs : b < m.blocks.size
      · obtain ⟨blk, hbk, hl, hor⟩ := hold b blk' hb' hl' hbs
        rcases hor with hcl | ⟨ea, es, elo⟩
        · rw [hcl S hb] at hclr; cases hclr
        · have hclr0 : blk.clearOf (m.stackOf t).base S = false :=
            Block.clearOf_false_iff.mpr ⟨hl, hn, by omega, by omega, by omega⟩
          obtain ⟨i, hi, hbi, e1, e2⟩ := hlay.inRes b blk hbk hclr0
          exact ⟨i, hi, hbi, by omega, by omega⟩
      · rw [hnew b blk' hb' (by omega) S hb] at hclr; cases hclr
    · intro i hi hl
      obtain ⟨h1, h2, h3, h4⟩ := hent.live i hi (hlive i hi hl)
      exact ⟨h1, h2, h3, by rw [hc _ _ (by unfold entKey; split <;> rfl)]; exact h4⟩
    · intro i j hi hj hl hl'
      exact hent.order i j hi hj (hlive i hi hl) (hlive j (by omega) hl')
    · intro ℓ v hv
      rw [hc _ _ rfl] at hv
      obtain ⟨i, hi, hl, hbi, hL⟩ := hent.frm ℓ v hv
      exact ⟨i, hi, by rw [hframe i hi hbi]; exact hl, hbi, hL⟩
    · intro b v hv
      rw [hc _ _ rfl] at hv
      obtain ⟨hbs, hex⟩ := hent.blk b v hv
      refine ⟨Nat.lt_of_lt_of_le hbs hsz, fun hl => hex ?_⟩
      cases hb' : m'.blocks[b]? with
      | none => simp [hb'] at hl
      | some blk' =>
        simp only [hb', Option.map_some, Option.getD_some] at hl
        obtain ⟨blk, hbk, hl', -⟩ := hold b blk' hb' hl hbs
        simp [hbk, hl']

/-! ## The thread that pushes an entry -/

theorem StackEntry.liveIn_congr {blocks blocks' : Array Block} {e : StackEntry}
    (h : ∀ b, e.block = some b → blocks'[b]? = blocks[b]?) :
    e.liveIn blocks' = e.liveIn blocks := by
  unfold StackEntry.liveIn
  split
  · rename_i b hb; rw [h b hb]
  · rfl

/-- **The thread that pushes keeps its part**, with the token `sp t S (D + c)` and the new
entry's token at logical depth `D`: the step pushes one entry for block `o` (a frame: `none`)
with charge `c` on the held entries (`Mem.pushEntry`), keeps every old block, and its new block,
if any, is clear of the reserve or is the entry's block in its fallback slot. -/
theorem ThreadOk.push {m m' : Mem} {c c' : KCell} {t S D ch : Nat} {o : Option Nat}
    {L : Nat → Nat} (hS : (m.stackOf t).budget = some S) (hlay : StackLayoutOk m (m.stackOf t) S)
    (hent : EntOk c m.blocks t (m.stackOf t).entries D L)
    (hst : m'.stackOf t = { (m.stackOf t) with entries :=
      (((m.stackOf t).entries.popWhile (deadIn m.blocks)).push
        { block := o, base := m.stackDepth t, charge := ch }) })
    (hlim : m.place.addrLimit ≤ m'.place.addrLimit) (hsz : m.blocks.size ≤ m'.blocks.size)
    (hold : ∀ b, b < m.blocks.size → m'.blocks[b]? = m.blocks[b]?)
    (hnew : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → m.blocks.size ≤ b →
      blk'.clearOf (m.stackOf t).base S = true ∨ (o = some b ∧
        (m.stackOf t).base + S ≤ blk'.addr + (m.stackDepth t + ch) ∧
        blk'.addr + blk'.bytes.size + m.stackDepth t ≤ (m.stackOf t).base + S))
    (hoid : ∀ b, o = some b →
      m.blocks.size ≤ b ∧ ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = true)
    (hch : 0 < ch) (hsp : c'.ex (.sp t) (S, D + ch) = 1) (hnk : c'.ex (newKey t o D) (D, ch) = 1)
    (hc : ∀ k v, k ≠ .sp t → k ≠ newKey t o D → c'.ex k v = c.ex k v) :
    ThreadOk m' c' t := by
  unfold ThreadOk
  rw [hst]
  rw [Mem.stackDepth_eq] at hnew ⊢
  generalize m.stackOf t = s at *
  obtain ⟨budget, base, es, native⟩ := s
  simp only at *
  subst hS
  have hdep := hent.depth_le
  have hHle := popHeld_size_le (es := es) (blocks := m.blocks)
  have hHget : ∀ i (hi : i < (es.popWhile (deadIn m.blocks)).size) (hi' : i < es.size),
      (es.popWhile (deadIn m.blocks))[i] = es[i] :=
    fun i hi _ => popHeld_getElem hi
  have hHlive : ∀ i (hi : i < es.size), es[i].liveIn m.blocks = true →
      i < (es.popWhile (deadIn m.blocks)).size := fun i hi hl => lt_popHeld hi hl
  have hHend : ∀ i (hi : i < es.size), i < (es.popWhile (deadIn m.blocks)).size →
      es[i].base + es[i].charge ≤ stackEnd (es.popWhile (deadIn m.blocks)) :=
    fun i hi hk => end_le_held hlay.order hi hk
  have hlv : ∀ i (hi : i < es.size), es[i].liveIn m'.blocks = es[i].liveIn m.blocks :=
    fun i hi => StackEntry.liveIn_congr fun b hb => hold b (hlay.ids i hi b hb)
  obtain ⟨hlim0, hord0, hids0, hres0⟩ := hlay
  simp only at hlim0 hord0 hids0 hres0
  generalize stackEnd (es.popWhile (deadIn m.blocks)) = d at *
  generalize es.popWhile (deadIn m.blocks) = H at *
  have hnl : ({ block := o, base := d, charge := ch } : StackEntry).liveIn m'.blocks = true := by
    cases o with
    | none => rfl
    | some b =>
      obtain ⟨-, blk', hb', hl'⟩ := hoid b rfl
      simp [StackEntry.liveIn, hb', hl']
  -- the old entries at their indices
  have hpush : ∀ i (hi : i < (H.push { block := o, base := d, charge := ch }).size),
      (hk : i < H.size) → (H.push { block := o, base := d, charge := ch })[i] = es[i]'(by omega) :=
    fun i hi hk => by rw [Array.getElem_push_lt hk]; exact hHget i hk (by omega)
  have htop : ∀ (hi : H.size < (H.push { block := o, base := d, charge := ch }).size),
      (H.push { block := o, base := d, charge := ch })[H.size] = { block := o, base := d, charge := ch } :=
    fun _ => Array.getElem_push_eq
  have hkey : ∀ i (hi : i < es.size), es[i].liveIn m.blocks = true →
      entKey t es[i] (L i) ≠ .sp t ∧ entKey t es[i] (L i) ≠ newKey t o D := by
    intro i hi hl
    obtain ⟨hc0, -, hle, -⟩ := hent.live i hi hl
    refine ⟨by unfold entKey; split <;> simp, ?_⟩
    unfold entKey newKey
    cases hbi : es[i].block with
    | some b' =>
      cases o with
      | none => simp
      | some b =>
        have := hids0 i hi b' hbi
        have := (hoid b rfl).1
        simp; omega
    | none =>
      cases o with
      | some b => simp
      | none => simp; omega
  refine ⟨D + ch, hsp, ⟨Nat.le_trans hlim0 hlim, ?_, ?_, ?_⟩,
    fun i => if i < H.size then L i else D, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- the entries are pushed in order
    intro i j hi hj
    simp only [Array.size_push] at hi
    by_cases hk : i < H.size
    · rw [hpush i (by simpa using hi) hk, hpush j (by simp; omega) (by omega)]
      exact hord0 i j (by omega) hj
    · have e : i = H.size := by omega
      subst e
      rw [htop (by simp), hpush j (by simp; omega) hj]
      exact hHend j (by omega) hj
  · -- block ids
    intro i hi b hbi
    simp only [Array.size_push] at hi
    by_cases hk : i < H.size
    · rw [hpush i (by simpa using hi) hk] at hbi
      exact Nat.lt_of_lt_of_le (hids0 i (by omega) b hbi) hsz
    · have e : i = H.size := by omega
      subst e
      rw [htop (by simp)] at hbi
      obtain ⟨-, blk', hb', -⟩ := hoid b hbi
      exact (Array.getElem?_eq_some_iff.mp hb').1
  · -- blocks in the reserve
    intro b blk' hb' hclr
    by_cases hbs : b < m.blocks.size
    · rw [hold b hbs] at hb'
      obtain ⟨i, hi, hbi, e1, e2⟩ := hres0 b blk' hb' hclr
      have hl : es[i].liveIn m.blocks = true := by
        simp [StackEntry.liveIn, hbi, hb', (Block.clearOf_false_iff.mp hclr).1]
      have hk := hHlive i hi hl
      exact ⟨i, by simp; omega, by rw [hpush i (by simp; omega) hk]; exact hbi,
        by rw [hpush i (by simp; omega) hk]; exact e1, by rw [hpush i (by simp; omega) hk]; exact e2⟩
    · rcases hnew b blk' hb' (by omega) with hc' | ⟨ho, e1, e2⟩
      · rw [hc'] at hclr; cases hclr
      · exact ⟨H.size, by simp, by rw [htop (by simp)]; exact ho, by rw [htop (by simp)]; exact e1,
          by rw [htop (by simp)]; exact e2⟩
  · -- live entries carry their tokens
    intro i hi hl
    simp only [Array.size_push] at hi
    by_cases hk : i < H.size
    · rw [hpush i (by simpa using hi) hk] at hl ⊢
      rw [hlv i (by omega)] at hl
      obtain ⟨h1, h2, h3, h4⟩ := hent.live i (by omega) hl
      obtain ⟨k1, k2⟩ := hkey i (by omega) hl
      simp only [hk, ite_true]
      exact ⟨h1, h2, by omega, by rw [hc _ _ k1 k2]; exact h4⟩
    · have e : i = H.size := by omega
      subst e
      rw [htop (by simp)]
      simp only [Nat.lt_irrefl, ite_false]
      refine ⟨hch, hdep, Nat.le_refl _, ?_⟩
      have : entKey t { block := o, base := d, charge := ch } D = newKey t o D := by
        unfold entKey newKey; cases o <;> rfl
      rw [this]; exact hnk
  · -- in push order
    intro i j hi hj hl hl'
    simp only [Array.size_push] at hi
    by_cases hk : i < H.size
    · rw [hpush i (by simpa using hi) hk] at hl
      rw [hpush j (by simp; omega) (by omega)] at hl' ⊢
      rw [hlv i (by omega)] at hl
      rw [hlv j (by omega)] at hl'
      simp only [hk, ite_true, show j < H.size by omega]
      exact hent.order i j (by omega) hj hl hl'
    · have e : i = H.size := by omega
      subst e
      rw [hpush j (by simp; omega) hj] at hl' ⊢
      rw [hlv j (by omega)] at hl'
      simp only [Nat.lt_irrefl, ite_false, hj, ite_true]
      exact (hent.live j (by omega) hl').2.2.1
  · -- frame tokens name live frames
    intro ℓ v hv
    by_cases hnk' : AKey.frm t ℓ = newKey t o D
    · cases o with
      | some b => simp [newKey] at hnk'
      | none =>
        simp only [newKey, AKey.frm.injEq, true_and] at hnk'
        subst hnk'
        exact ⟨H.size, by simp, by rw [htop (by simp)]; exact hnl, by rw [htop (by simp)],
          by simp⟩
    · rw [hc _ _ (by simp) hnk'] at hv
      obtain ⟨i, hi, hl, hbi, hL⟩ := hent.frm ℓ v hv
      have hk := hHlive i hi hl
      refine ⟨i, by simp; omega, ?_, by rw [hpush i (by simp; omega) hk]; exact hbi, by simp [hk, hL]⟩
      rw [hpush i (by simp; omega) hk, hlv i hi]; exact hl
  · -- block tokens name blocks, a live one an entry
    intro b v hv
    by_cases hnk' : AKey.blk t b = newKey t o D
    · cases o with
      | none => simp [newKey] at hnk'
      | some b' =>
        simp only [newKey, AKey.blk.injEq, true_and] at hnk'
        subst hnk'
        obtain ⟨-, blk', hb', -⟩ := hoid b rfl
        exact ⟨(Array.getElem?_eq_some_iff.mp hb').1, fun _ =>
          ⟨H.size, by simp, by rw [htop (by simp)]⟩⟩
    · rw [hc _ _ (by simp) hnk'] at hv
      obtain ⟨hbs, hex⟩ := hent.blk b v hv
      refine ⟨Nat.lt_of_lt_of_le hbs hsz, fun hl => ?_⟩
      rw [hold b hbs] at hl
      obtain ⟨i, hi, hbi⟩ := hex hl
      have hli : es[i].liveIn m.blocks = true := by
        simp only [StackEntry.liveIn, hbi]; exact hl
      have hk := hHlive i hi hli
      exact ⟨i, by simp; omega, by rw [hpush i (by simp; omega) hk]; exact hbi⟩

/-! ## Placement facts -/

theorem all_getD {ss : Array StackState} {f : StackState → Bool} (h : ss.all f = true)
    (hd : f default = true) (t : Nat) : f (ss.getD t default) = true := by
  rw [Array.getD_eq_getD_getElem?]
  cases hx : ss[t]? with
  | none => simpa using hd
  | some x =>
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hx
    exact (Array.all_eq_true.mp h) t hi

/-- A reserve that `reserveClear` admits is apart from the range. -/
theorem reserveClear_budget {s : StackState} {A n S : Nat} (h : s.reserveClear A n = true)
    (hb : s.budget = some S) : n = 0 ∨ S = 0 ∨ A + n ≤ s.base ∨ s.base + S ≤ A := by
  unfold StackState.reserveClear at h
  rw [hb] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h.1 with ((h | h) | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

/-- A block apart from a reserve is clear of it. -/
theorem clearOf_of_apart {blk : Block} {base S : Nat}
    (h : blk.bytes.size = 0 ∨ S = 0 ∨ blk.addr + blk.bytes.size ≤ base ∨ base + S ≤ blk.addr) :
    blk.clearOf base S = true := by
  cases hc : blk.clearOf base S
  · obtain ⟨-, h2, h3, h4, h5⟩ := Block.clearOf_false_iff.mp hc
    omega
  · rfl

/-- **A placed block is apart from every reserve**: the placement's address of a block of any
kind (its own native stack for a stack block, `Mem.homeOk`, or anywhere valid, `Mem.placeOk`)
meets no thread's budget reserve. -/
theorem placedFor?_apart {m : Mem} {kind : BlockKind} {size align A : Nat}
    (h : m.placedFor? kind size align = some A) (t S : Nat) (hb : (m.stackOf t).budget = some S) :
    size = 0 ∨ S = 0 ∨ A + size ≤ (m.stackOf t).base ∨ (m.stackOf t).base + S ≤ A := by
  unfold Mem.placedFor? at h
  split at h
  · split at h
    · cases h
      rename_i A' _ hor
      rcases Bool.or_eq_true_iff.mp hor with hh | hp
      · unfold Mem.homeOk at hh
        split at hh
        · simp only [Bool.and_eq_true] at hh
          have := all_getD hh.2 rfl t
          rw [getD_setStackAt] at this
          split at this
          · rename_i e
            subst e
            exact reserveClear_budget (s := { (m.stackOf m.current) with native := none }) this hb
          · exact reserveClear_budget this hb
        · cases hh
      · simp only [Mem.placeOk, Bool.and_eq_true] at hp
        exact reserveClear_budget (all_getD hp.2 rfl t) hb
    · cases h
  · cases h

/-- Every reserve ends below `Mem.top`. -/
theorem lt_top_of_budget {m : Mem} {t S : Nat} (hb : (m.stackOf t).budget = some S) :
    (m.stackOf t).base + S < m.top := by
  have ht : t < m.stacks.size := by
    refine Nat.lt_of_not_le fun h => ?_
    have : m.stackOf t = default := by
      simp [Mem.stackOf, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
    rw [this] at hb; cases hb
  have := Mem.reserveEnd_le_top (m := m) (t := t) (Array.getElem?_eq_getElem ht)
  have e : m.stackOf t = m.stacks[t] := by
    simp [Mem.stackOf, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
  rw [← e] at this
  have h2 : (m.stackOf t).base + S + 1 ≤ (m.stackOf t).reserveEnd := by
    unfold StackState.reserveEnd; rw [hb]; exact Nat.le_max_left _ _
  omega

/-- **The block of an `alloc` without a stack budget is apart from every reserve.** -/
theorem allocAddr_apart_none {m : Mem} {kind : BlockKind} {size align : Nat}
    (hk : m.stackBudget? kind = none) (t S : Nat) (hb : (m.stackOf t).budget = some S) :
    size = 0 ∨ S = 0 ∨ m.allocAddr kind size align + size ≤ (m.stackOf t).base ∨
      (m.stackOf t).base + S ≤ m.allocAddr kind size align := by
  rw [Mem.allocAddr_of_none hk]
  cases hp : m.placedFor? kind size align with
  | some A => exact placedFor?_apart hp t S hb
  | none =>
    have := lt_top_of_budget hb
    have := le_alignUp m.top align
    simp only [Option.getD_none]
    omega

/-! ## Steps -/

theorem exAt_ne {k k' : AKey} {v v' : Nat × Nat} (h : k ≠ k') : (ACell.exAt k' v : KCell).ex k v' = 0 := by
  simp [h]

/-- **`alloc` without a stack budget keeps `StackAuth`** (every kind but a stack block of a
thread with a budget): its block is apart from every reserve. -/
theorem StackAuth.allocOther {m : Mem} {c : KCell} {kind : BlockKind} {size align : Nat}
    (h : StackAuth m c) (hk : m.stackBudget? kind = none) :
    StackAuth (m.afterAlloc kind size align) c := by
  have hst : (m.afterAlloc kind size align).stacks = m.stacks := by
    simp [Mem.afterAlloc, Mem.stacksAfterAlloc, hk]
  have hso : ∀ t, (m.afterAlloc kind size align).stackOf t = m.stackOf t := fun t => by
    simp [Mem.stackOf, hst]
  refine ⟨fun t => (h.thread t).transfer (hso t) (Nat.le_refl _) (by simp [Mem.afterAlloc])
    (fun b blk' hb' _ hbs => ?_) (fun b blk' hb' hbs S hS => ?_) (fun _ _ _ => rfl), ?_⟩
  · have : (m.afterAlloc kind size align).blocks[b]? = m.blocks[b]? := by
      simp [Mem.afterAlloc, Array.getElem?_push, Nat.ne_of_lt hbs]
    rw [this] at hb'
    exact ⟨blk', hb', ‹_›, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩
  · have hb : b = m.blocks.size := by
      have := (Array.getElem?_eq_some_iff.mp hb').1
      simp [Mem.afterAlloc] at this; omega
    subst hb
    simp only [Mem.afterAlloc, Array.getElem?_push_size, Option.some.injEq] at hb'
    subst hb'
    exact clearOf_of_apart (by simpa using allocAddr_apart_none hk t S hS)
  · intro t t' S S' hne hS hS'
    rw [hso, hso] at *
    exact h.apart t t' S S' hne hS hS'

/-- The counts after replacing the exclusive fragment of `k₁` and adding one of `K`. -/
theorem ex_push {k₁ K : AKey} {v₁ v₁' w : Nat × Nat} {G : KCell} (hne : K ≠ k₁)
    (h₁ : ∀ v, G.ex k₁ v = 0) (hK : ∀ v, G.ex K v = 0) :
    ((ACell.exAt k₁ v₁').add ((ACell.exAt K w).add G)).ex k₁ v₁' = 1 ∧
      ((ACell.exAt k₁ v₁').add ((ACell.exAt K w).add G)).ex K w = 1 ∧
      ∀ k v, k ≠ k₁ → k ≠ K →
        ((ACell.exAt k₁ v₁').add ((ACell.exAt K w).add G)).ex k v = ((ACell.exAt k₁ v₁).add G).ex k v := by
  refine ⟨by simp [hne.symm, h₁], by simp [hne, hK], fun k v h1 h2 => by simp [h1, h2]⟩

theorem AKey.ne_of_tid {k k' : AKey} {t t' : Nat} (hk : k.tid = some t) (hk' : k'.tid = some t')
    (h : t ≠ t') : k ≠ k' := by
  rintro rfl; rw [hk] at hk'; exact h (Option.some.inj hk')

/-- **A stack block from `sp`** (the memory side of the total `allocStack` rule): the running
thread `t` with `sp t S D` and `D + c ≤ S` has room (`Mem.allocOk`), and after `alloc` the
memory authorizes `sp t S (D + c)` and the new block's entry token `ent t b D c` in place of
`sp t S D` (`b` the new block, `c = stackCharge size align`). -/
theorem StackAuth.alloc {m : Mem} {G : KCell} {t S D size align : Nat}
    (h : StackAuth m ((spCell t S D).add G)) (hv : ((spCell t S D).add G).Valid)
    (hcur : m.current = t) (hS : (m.stackOf t).budget = some S)
    (hfit : D + stackCharge size align ≤ S) :
    m.allocOk .stack size align = true ∧
      ((spCell t S (D + stackCharge size align)).add
        ((entCell t (some m.blocks.size) D (stackCharge size align)).add G)).Valid ∧
      StackAuth (m.afterAlloc .stack size align) ((spCell t S (D + stackCharge size align)).add
        ((entCell t (some m.blocks.size) D (stackCharge size align)).add G)) := by
  have hD : 0 < ((spCell t S D).add G).ex (.sp t) (S, D) := by simp [spCell]; omega
  have hroom := h.allocOk hv hcur hS hD hfit
  obtain ⟨-, hlay, L, hent⟩ := h.of_budget hv hS hD
  have hGsp : ∀ v, G.ex (.sp t) v = 0 := hv.ex_zero
  have hGb : ∀ v, G.ex (.blk t m.blocks.size) v = 0 := fun v => by
    refine Nat.eq_zero_of_not_pos fun hp => ?_
    have := (hent.blk m.blocks.size v (by simp [spCell]; omega)).1
    omega
  obtain ⟨c1, c2, c3⟩ := ex_push (k₁ := .sp t) (K := .blk t m.blocks.size) (v₁ := (S, D))
    (v₁' := (S, D + stackCharge size align)) (w := (D, stackCharge size align)) (G := G)
    (by simp) hGsp hGb
  refine ⟨hroom, ACell.Valid.add_ex _ (ACell.Valid.add_ex _ hv.of_add_right hGb)
    (fun v => by simp [entCell, hGsp]), ?_⟩
  subst hcur
  have hso : ∀ t', (m.afterAlloc .stack size align).stackOf t' =
      if t' = m.current then { (m.stackOf m.current) with entries :=
        (((m.stackOf m.current).entries.popWhile (deadIn m.blocks)).push
          { block := some m.blocks.size, base := m.stackDepth m.current,
            charge := stackCharge size align }) }
      else m.stackOf t' := fun t' => by
    show (m.stacksAfterAlloc .stack size align).getD t' default = _
    simp only [Mem.stacksAfterAlloc, Mem.stackBudget?, hS, Mem.pushEntry]
    rw [getD_setStackAt]; rfl
  have hbk : ∀ t', ((m.afterAlloc .stack size align).stackOf t').budget = (m.stackOf t').budget ∧
      ((m.afterAlloc .stack size align).stackOf t').base = (m.stackOf t').base := fun t' => by
    rw [hso]; split <;> (rename_i e; try subst e) <;> exact ⟨rfl, rfl⟩
  have hold : ∀ b, b < m.blocks.size → (m.afterAlloc .stack size align).blocks[b]? = m.blocks[b]? :=
    fun b hb => by simp [Mem.afterAlloc, Array.getElem?_push, Nat.ne_of_lt hb]
  -- the new block, and where it lies
  have hnb : ∀ (b : Nat) (blk' : Block), (m.afterAlloc .stack size align).blocks[b]? = some blk' →
      m.blocks.size ≤ b → b = m.blocks.size ∧ blk'.addr = m.allocAddr .stack size align ∧
        blk'.bytes.size = size ∧ blk'.live = true := by
    intro b blk' hb' hbs
    have hb := (Array.getElem?_eq_some_iff.mp hb').1
    simp only [Mem.afterAlloc, Array.size_push] at hb
    have e : b = m.blocks.size := by omega
    subst e
    simp only [Mem.afterAlloc, Array.getElem?_push_size, Option.some.injEq] at hb'
    subst hb'
    exact ⟨rfl, rfl, by simp, rfl⟩
  have hdep : m.stackDepth m.current ≤ D := hent.depth_le
  have hfb := fallback_bounds (base := (m.stackOf m.current).base)
    (h := Nat.le_trans (Nat.add_le_add_right hdep (stackCharge size align)) hfit)
  have haddr : m.allocAddr .stack size align =
      (m.placedFor? .stack size align).getD (m.stackFallback S size align) := by
    simp [Mem.allocAddr, Mem.stackBudget?, hS]
  have hch : 0 < stackCharge size align := by
    show 0 < size + Nat.max align 1
    have : 1 ≤ Nat.max align 1 := Nat.le_max_right align 1
    omega
  refine ⟨fun t' => ?_, fun t₁ t₂ S₁ S₂ hne h₁ h₂ => ?_⟩
  · by_cases e : t' = m.current
    · subst e
      refine ThreadOk.push (o := some m.blocks.size) (L := L) hS hlay hent
        (by rw [hso, if_pos rfl]) (Nat.le_refl _) (by simp [Mem.afterAlloc]) hold
        (fun b blk' hb' hbs => ?_) (fun b hb => ?_) hch c1 c2 (fun k v h1 h2 => c3 k v h1 h2)
      · obtain ⟨rfl, ha, hs, -⟩ := hnb b blk' hb' hbs
        rw [haddr] at ha
        cases hp : m.placedFor? .stack size align with
        | some A =>
          rw [hp] at ha
          exact .inl (clearOf_of_apart (by rw [ha, hs]; exact placedFor?_apart hp _ S hS))
        | none =>
          rw [hp] at ha
          simp only [Option.getD_none, Mem.stackFallback] at ha
          refine .inr ⟨rfl, ?_, ?_⟩ <;> (rw [ha]; try rw [hs]) <;> omega
      · obtain rfl := Option.some.inj hb
        exact ⟨Nat.le_refl _, by simp [Mem.afterAlloc]⟩
    · refine (h.thread t').transfer (by rw [hso, if_neg e]) (Nat.le_refl _)
        (by simp [Mem.afterAlloc]) (fun b blk' hb' hl hbs => ?_) (fun b blk' hb' hbs S' hS' => ?_)
        (fun k v hk => ?_)
      · rw [hold b hbs] at hb'
        exact ⟨blk', hb', hl, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩
      · obtain ⟨-, ha, hs, -⟩ := hnb b blk' hb' hbs
        refine clearOf_of_apart ?_
        rw [ha, hs, haddr]
        cases hp : m.placedFor? .stack size align with
        | some A => exact placedFor?_apart hp t' S' hS'
        | none =>
          simp only [Option.getD_none, Mem.stackFallback]
          rcases h.apart m.current t' S S' (Ne.symm e) hS hS' with h0 | h0 | h0 | h0 <;> omega
      · exact c3 k v (AKey.ne_of_tid hk rfl e) (AKey.ne_of_tid hk rfl e)
  · rw [(hbk t₁).1] at h₁; rw [(hbk t₂).1] at h₂
    rw [(hbk t₁).2, (hbk t₂).2]
    exact h.apart t₁ t₂ S₁ S₂ hne h₁ h₂

/-! ## Steps that keep every thread's entries -/

/-- **A step that keeps the stack states keeps `StackAuth`**: the stack states and the tokens
stay; a live block of the new memory was live before at the same place (or is clear of every
reserve), and a new block is clear of every reserve. Stores, loads and `free` meet these
premises (`StackAuth.keep_shape`, `StackAuth.free`). `mmap`/`munmap`/`mremap` should meet them
too (they place and resize blocks clear of every reserve: `Mem.placeOk`, `Mem.growFree`); that is
proved per primitive at the wiring step. The thread primitives change stack states and are not
covered. -/
theorem StackAuth.keep {m m' : Mem} {c : KCell} (h : StackAuth m c) (hst : m'.stacks = m.stacks)
    (hlim : m.place.addrLimit ≤ m'.place.addrLimit) (hsz : m.blocks.size ≤ m'.blocks.size)
    (hold : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → blk'.live = true →
      b < m.blocks.size → ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
        ((∀ t S, (m.stackOf t).budget = some S → blk'.clearOf (m.stackOf t).base S = true) ∨
          (blk.addr = blk'.addr ∧ blk'.bytes.size ≤ blk.bytes.size ∧
            blk.kind.mappedLo ≤ blk'.kind.mappedLo)))
    (hnew : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → m.blocks.size ≤ b →
      ∀ t S, (m.stackOf t).budget = some S → blk'.clearOf (m.stackOf t).base S = true) :
    StackAuth m' c := by
  have hso : ∀ t, m'.stackOf t = m.stackOf t := fun t => by simp [Mem.stackOf, hst]
  refine ⟨fun t => (h.thread t).transfer (hso t) hlim hsz (fun b blk' hb' hl hbs => ?_)
    (fun b blk' hb' hbs S hS => hnew b blk' hb' hbs t S hS) (fun _ _ _ => rfl), ?_⟩
  · obtain ⟨blk, hb, hl', hor⟩ := hold b blk' hb' hl hbs
    exact ⟨blk, hb, hl', hor.imp (fun h S hS => h t S hS) id⟩
  · intro t t' S S' hne hS hS'
    rw [hso, hso] at *
    exact h.apart t t' S S' hne hS hS'

/-- A step that keeps the stack states, the address space and every block's liveness, address,
size and kind (stores, loads, accesses) keeps `StackAuth`. -/
theorem StackAuth.keep_shape {m m' : Mem} {c : KCell} (h : StackAuth m c)
    (hst : m'.stacks = m.stacks) (hlim : m'.place.addrLimit = m.place.addrLimit)
    (hsz : m'.blocks.size = m.blocks.size)
    (hb : ∀ (b : Nat) (blk' : Block), m'.blocks[b]? = some blk' → ∃ blk, m.blocks[b]? = some blk ∧
      blk'.live = blk.live ∧ blk'.addr = blk.addr ∧ blk'.bytes.size = blk.bytes.size ∧
        blk'.kind = blk.kind) :
    StackAuth m' c :=
  h.keep hst (by omega) (by omega) (fun b blk' hb' hl _ => by
      obtain ⟨blk, hbk, e1, e2, e3, e4⟩ := hb b blk' hb'
      exact ⟨blk, hbk, by rw [← e1]; exact hl, .inr ⟨e2.symm, by omega, by rw [e4]; exact Nat.le_refl _⟩⟩)
    (fun b blk' hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by omega))

/-- `free` succeeded: the block was live, and only its liveness changed. -/
theorem free_ok_live {m m' : Mem} {p : Ptr} {x : Unit}
    (h : ((Zig.free p).run m).run = some (.ok (x, m'))) :
    ∃ b blk, p.block = some b ∧ m.blocks[b]? = some blk ∧ blk.live = true ∧
      m' = { m with blocks := m.blocks.set! b { blk with live := false } } := by
  unfold Zig.free at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
  split at h₁
  · exact (Conc.Proto.MemM.throw_ok h₁).elim
  · rename_i b hb
    split at h₁
    · rename_i blk hblk
      split at h₁
      · rename_i hc
        split at h₁
        · exact (Conc.Proto.MemM.throw_ok h₁).elim
        · exact ⟨b, blk, hb, hblk, hc.1, Conc.Proto.MemM.set_ok h₁⟩
      · exact (Conc.Proto.MemM.throw_ok h₁).elim
    · exact (Conc.Proto.MemM.throw_ok h₁).elim

theorem getElem?_set!_dead {bs : Array Block} {b b' : Nat} {blk blk' : Block}
    (hb : bs[b]? = some blk) (h : (bs.set! b { blk with live := false })[b']? = some blk') :
    (b' = b ∧ blk'.live = false) ∨ (b' ≠ b ∧ bs[b']? = some blk') := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
  by_cases e : b = b'
  · subst e
    have := (Array.getElem?_eq_some_iff.mp hb).1
    simp [this] at h
    exact .inl ⟨rfl, by rw [← h]⟩
  · simp [e] at h
    exact .inr ⟨Ne.symm e, h⟩

theorem live_set!_dead {bs : Array Block} {b b' : Nat} {blk : Block} (hb : bs[b]? = some blk)
    (h : ((bs.set! b { blk with live := false })[b']?.map (·.live)).getD false = true) :
    b' ≠ b ∧ (bs[b']?.map (·.live)).getD false = true := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
  by_cases e : b = b'
  · subst e
    have := (Array.getElem?_eq_some_iff.mp hb).1
    simp [this] at h
  · simp only [e, ite_false] at h
    exact ⟨Ne.symm e, h⟩

/-- **`free` keeps `StackAuth`** with the same tokens: a dead block holds no reserve. (A free of
a stack block without its entry token leaves the token behind; it names a dead block forever.) -/
theorem StackAuth.free {m m' : Mem} {c : KCell} {p : Ptr} {x : Unit} (h : StackAuth m c)
    (hrun : ((Zig.free p).run m).run = some (.ok (x, m'))) : StackAuth m' c := by
  obtain ⟨b, blk, -, hb, -, rfl⟩ := free_ok_live hrun
  refine h.keep rfl (Nat.le_refl _) (by simp) (fun b' blk' hb' hl _ => ?_)
    (fun b' blk' hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by simp; omega))
  rcases getElem?_set!_dead hb hb' with ⟨-, hd⟩ | ⟨-, hb''⟩
  · rw [hd] at hl; cases hl
  · exact ⟨blk', hb'', hl, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩

/-! ## The thread that pops an entry -/

/-- **Popping the top entry** `i₀` (pushed at logical depth `ℓ` with charge `c`, the token
`sp t S (ℓ + c)` held): every other live entry ends at or below `ℓ`, so the entries stay valid
below `ℓ` once `i₀` is dead and its token is gone. -/
theorem EntOk.pop {c c' : KCell} {blocks blocks' : Array Block} {t ℓ ch i₀ : Nat}
    {es es' : Array StackEntry} {L : Nat → Nat}
    (hent : EntOk c blocks t es (ℓ + ch) L) (hv : c.Valid) (hsz : es'.size = es.size)
    (hsame : ∀ i (hi : i < es.size) (hi' : i < es'.size), es'[i].block = es[i].block ∧
      es'[i].base = es[i].base ∧ es'[i].charge = es[i].charge)
    (hlv : ∀ i (hi : i < es.size) (hi' : i < es'.size), es'[i].liveIn blocks' = true →
      es[i].liveIn blocks = true ∧ i ≠ i₀)
    (hfr : ∀ i (hi : i < es.size) (hi' : i < es'.size), i ≠ i₀ → es[i].block = none →
      es[i].liveIn blocks = true → es'[i].liveIn blocks' = true)
    (hi₀ : i₀ < es.size) (hl₀ : es[i₀].liveIn blocks = true) (hL : L i₀ = ℓ)
    (hch : es[i₀].charge = ch) (hbs : blocks.size ≤ blocks'.size)
    (hbl : ∀ (b : Nat), (blocks'[b]?.map (·.live)).getD false = true →
      (blocks[b]?.map (·.live)).getD false = true)
    (hc : ∀ k v, k ≠ .sp t → k ≠ entKey t es[i₀] ℓ → c'.ex k v = c.ex k v)
    (hK : ∀ v, c'.ex (entKey t es[i₀] ℓ) v = 0) :
    EntOk c' blocks' t es' ℓ L := by
  obtain ⟨-, -, -, ht₀⟩ := hent.live i₀ hi₀ hl₀
  rw [hL, hch] at ht₀
  -- every other live entry lies below `ℓ`
  have below : ∀ i (hi : i < es.size), es[i].liveIn blocks = true → i ≠ i₀ →
      L i + es[i].charge ≤ ℓ := by
    intro i hi hl hne
    obtain ⟨hc0, -, hle, -⟩ := hent.live i hi hl
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := hent.order i₀ i hi₀ hlt hl₀ hl; omega
    · have := hent.order i i₀ hi hgt hl hl₀; omega
  have hkey : ∀ i (hi : i < es.size), es[i].liveIn blocks = true → i ≠ i₀ →
      entKey t es[i] (L i) ≠ entKey t es[i₀] ℓ := by
    intro i hi hl hne e
    obtain ⟨hc0, -, -, hti⟩ := hent.live i hi hl
    have := below i hi hl hne
    rw [e] at hti
    have := (hv (entKey t es[i₀] ℓ)).2.2.2.2 _ _ (by omega : 0 < c.ex _ (L i, es[i].charge))
      (by omega : 0 < c.ex _ (ℓ, ch))
    simp at this; omega
  have hspk : ∀ e ℓ', entKey t e ℓ' ≠ .sp t := fun e ℓ' => by unfold entKey; split <;> simp
  refine ⟨fun i hi' hl' => ?_, fun i j hi' hj hl hl' => ?_, fun ℓ' v hv' => ?_, fun b v hv' => ?_⟩
  · have hi : i < es.size := by omega
    obtain ⟨hl, hne⟩ := hlv i hi hi' hl'
    obtain ⟨s1, s2, s3⟩ := hsame i hi hi'
    obtain ⟨h1, h2, -, h4⟩ := hent.live i hi hl
    have hk : entKey t es'[i] (L i) = entKey t es[i] (L i) := by unfold entKey; rw [s1]
    rw [s2, s3, hk, hc _ _ (hspk _ _) (hkey i hi hl hne)]
    exact ⟨h1, h2, below i hi hl hne, h4⟩
  · have hi : i < es.size := by omega
    obtain ⟨hl₁, -⟩ := hlv i hi hi' hl
    obtain ⟨hl₂, -⟩ := hlv j (by omega) (by omega) hl'
    rw [(hsame j (by omega) (by omega)).2.2]
    exact hent.order i j hi hj hl₁ hl₂
  · by_cases e : AKey.frm t ℓ' = entKey t es[i₀] ℓ
    · rw [e, hK] at hv'; cases hv'
    · rw [hc _ _ (by simp) e] at hv'
      obtain ⟨i, hi, hl, hbi, hLi⟩ := hent.frm ℓ' v hv'
      have hne : i ≠ i₀ := by
        rintro rfl; apply e; unfold entKey; simp only [hbi]; rw [← hLi, hL]
      exact ⟨i, by omega, hfr i hi (by omega) hne hbi hl, by rw [(hsame i hi (by omega)).1]; exact hbi,
        hLi⟩
  · by_cases e : AKey.blk t b = entKey t es[i₀] ℓ
    · rw [e, hK] at hv'; cases hv'
    · rw [hc _ _ (by simp) e] at hv'
      obtain ⟨hbs', hex⟩ := hent.blk b v hv'
      refine ⟨Nat.lt_of_lt_of_le hbs' hbs, fun hl => ?_⟩
      obtain ⟨i, hi, hbi⟩ := hex (hbl b hl)
      exact ⟨i, by omega, by rw [(hsame i hi (by omega)).1]; exact hbi⟩

/-- A thread with an `sp` token has a budget. -/
theorem StackAuth.budget_of_sp {m : Mem} {c : KCell} {t S D : Nat} (h : StackAuth m c)
    (hv : c.Valid) (hD : 0 < c.ex (.sp t) (S, D)) : (m.stackOf t).budget = some S := by
  have := h.thread t
  unfold ThreadOk at this
  cases hb : (m.stackOf t).budget with
  | none => rw [hb] at this; have := this.1 (S, D); omega
  | some S' =>
    rw [hb] at this
    obtain ⟨D', h1, -⟩ := this
    have := (hv (.sp t)).2.2.2.2 (S, D) (S', D') hD (by omega)
    simp at this; rw [this.1]

/-- **Freeing the top stack block returns its charge** (the memory side of the `free` rule
with tokens): with `sp t S (ℓ + c)` and the block's entry token `ent t b ℓ c`, after `free` the
memory authorizes `sp t S ℓ` in place of both. -/
theorem StackAuth.free_top {m m' : Mem} {G : KCell} {t S ℓ ch b : Nat} {p : Ptr} {x : Unit}
    (h : StackAuth m ((spCell t S (ℓ + ch)).add ((entCell t (some b) ℓ ch).add G)))
    (hv : ((spCell t S (ℓ + ch)).add ((entCell t (some b) ℓ ch).add G)).Valid)
    (hp : p.block = some b) (hrun : ((Zig.free p).run m).run = some (.ok (x, m'))) :
    ((spCell t S ℓ).add G).Valid ∧ StackAuth m' ((spCell t S ℓ).add G) := by
  obtain ⟨b', blk, hpb, hb, hlive, rfl⟩ := free_ok_live hrun
  rw [hp] at hpb; cases hpb
  have hGsp : ∀ v, G.ex (.sp t) v = 0 := fun v => by
    have := hv.ex_zero v; simp [entCell] at this; exact this
  have hGb : ∀ v, G.ex (.blk t b) v = 0 := hv.of_add_right.ex_zero
  have hc' : ((spCell t S ℓ).add G).Valid := ACell.Valid.add_ex _ hv.of_add_right.of_add_right hGsp
  refine ⟨hc', ?_⟩
  have hsp0 : 0 < ((spCell t S (ℓ + ch)).add ((entCell t (some b) ℓ ch).add G)).ex (.sp t)
      (S, ℓ + ch) := by simp [spCell]; omega
  have hS := h.budget_of_sp hv hsp0
  obtain ⟨-, hlay, L, hent⟩ := h.of_budget hv hS hsp0
  -- the entry of `b`
  obtain ⟨-, hex⟩ := hent.blk b (ℓ, ch) (by simp [entCell]; omega)
  obtain ⟨i₀, hi₀, hb₀⟩ := hex (by simp [hb, hlive])
  have hl₀ : (m.stackOf t).entries[i₀].liveIn m.blocks = true := by
    simp [StackEntry.liveIn, hb₀, hb, hlive]
  obtain ⟨-, -, -, ht₀⟩ := hent.live i₀ hi₀ hl₀
  have hk₀ : entKey t (m.stackOf t).entries[i₀] (L i₀) = .blk t b := by unfold entKey; rw [hb₀]
  have hk₀' : entKey t (m.stackOf t).entries[i₀] ℓ = .blk t b := by unfold entKey; rw [hb₀]
  rw [hk₀] at ht₀
  have huq := (hv (.blk t b)).2.2.2.2 (L i₀, (m.stackOf t).entries[i₀].charge) (ℓ, ch)
    (by rw [ht₀]; omega) (by simp [spCell, entCell]; omega)
  simp only [Prod.mk.injEq] at huq
  obtain ⟨hL, hch⟩ := huq
  -- the cells agree off `sp t` and `blk t b`
  have hcx : ∀ k v, k ≠ .sp t → k ≠ .blk t b →
      ((spCell t S ℓ).add G).ex k v = ((spCell t S (ℓ + ch)).add ((entCell t (some b) ℓ ch).add G)).ex k v :=
    fun k v h1 h2 => by simp [spCell, entCell, h1, h2]
  have hdead : ∀ (b'' : Nat) (blk' : Block),
      ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).blocks[b'']? = some blk' →
        blk'.live = true → b'' < m.blocks.size → ∃ blk₀, m.blocks[b'']? = some blk₀ ∧
          blk₀.live = true ∧ blk₀.addr = blk'.addr ∧ blk'.bytes.size ≤ blk₀.bytes.size ∧
            blk₀.kind.mappedLo ≤ blk'.kind.mappedLo ∧ b'' ≠ b := by
    intro b'' blk' hb' hl _
    rcases getElem?_set!_dead hb hb' with ⟨-, hd⟩ | ⟨hne, hb''⟩
    · rw [hd] at hl; cases hl
    · exact ⟨blk', hb'', hl, rfl, Nat.le_refl _, Nat.le_refl _, hne⟩
  have hsz : ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).blocks.size =
      m.blocks.size := by simp
  refine ⟨fun t' => ?_, fun t₁ t₂ S₁ S₂ hne h₁ h₂ => h.apart t₁ t₂ S₁ S₂ hne h₁ h₂⟩
  have hold : ∀ (b'' : Nat) (blk' : Block),
      ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).blocks[b'']? = some blk' →
        blk'.live = true → b'' < m.blocks.size → ∃ blk₀, m.blocks[b'']? = some blk₀ ∧
          blk₀.live = true ∧ ((∀ S', (m.stackOf t').budget = some S' →
            blk'.clearOf (m.stackOf t').base S' = true) ∨ (blk₀.addr = blk'.addr ∧
              blk'.bytes.size ≤ blk₀.bytes.size ∧ blk₀.kind.mappedLo ≤ blk'.kind.mappedLo)) :=
    fun b'' blk' hb' hl hbs => by
      obtain ⟨blk₀, h1, h2, h3, h4, h5, -⟩ := hdead b'' blk' hb' hl hbs
      exact ⟨blk₀, h1, h2, .inr ⟨h3, h4, h5⟩⟩
  have hnew : ∀ (b'' : Nat) (blk' : Block),
      ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).blocks[b'']? = some blk' →
        m.blocks.size ≤ b'' → ∀ S', (m.stackOf t').budget = some S' →
          blk'.clearOf (m.stackOf t').base S' = true :=
    fun b'' blk' hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by rw [hsz]; omega)
  by_cases e : t' = t
  · subst e
    have hT := (h.thread t').transfer (m' := { m with blocks := m.blocks.set! b { blk with live := false } })
      rfl (Nat.le_refl _) (by simp) hold hnew (fun _ _ _ => rfl)
    have hso : ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).stackOf t' =
        m.stackOf t' := rfl
    unfold ThreadOk at hT ⊢
    rw [hso] at hT ⊢
    simp only [hS] at hT ⊢
    obtain ⟨-, -, hlay', -⟩ := hT
    refine ⟨ℓ, by simp [spCell, hGsp], hlay', L, ?_⟩
    refine EntOk.pop (c := (spCell t' S (ℓ + ch)).add ((entCell t' (some b) ℓ ch).add G))
      (i₀ := i₀) hent hv rfl (fun i hi _ => ⟨rfl, rfl, rfl⟩) (fun i hi _ hl => ?_)
      (fun i hi _ hne hbi hl => by simp [StackEntry.liveIn, hbi] at hl ⊢; exact hl)
      hi₀ hl₀ hL hch (by simp) (fun b'' hl => ?_) (fun k v h1 h2 => ?_) (fun v => ?_)
    · unfold StackEntry.liveIn at hl ⊢
      split at hl
      · rename_i b'' hbi
        obtain ⟨hne, hl'⟩ := live_set!_dead hb hl
        refine ⟨by rw [hbi]; exact hl', fun e => ?_⟩
        subst e; rw [hb₀] at hbi; exact hne (Option.some.inj hbi).symm
      · rename_i hbi
        refine ⟨by simp [hbi] at hl ⊢; exact hl, fun e => ?_⟩
        subst e; rw [hb₀] at hbi; cases hbi
    · exact (live_set!_dead hb hl).2
    · rw [hk₀'] at h2
      exact hcx k v h1 h2
    · rw [hk₀']; simp [spCell, hGb]
  · exact (h.thread t').transfer rfl (Nat.le_refl _) (by simp) hold hnew
      (fun k v hk => hcx k v (AKey.ne_of_tid hk rfl e) (AKey.ne_of_tid hk rfl e))

/-! ## Frames of recursive calls -/

/-- **A frame from `sp`** (the memory side of a total `enterFrame` rule): the running thread `t`
with `sp t S D` and `D + frameBase ≤ S` enters the frame, and the memory then authorizes
`sp t S (D + frameBase)` and the frame's token `ent t none D frameBase` in place of `sp t S D`. -/
theorem StackAuth.enterFrame {m : Mem} {G : KCell} {t S D : Nat}
    (h : StackAuth m ((spCell t S D).add G)) (hv : ((spCell t S D).add G).Valid)
    (hcur : m.current = t) (hS : (m.stackOf t).budget = some S) (hfit : D + frameBase ≤ S) :
    enterFrame.run m = pure ((), { m with stacks := m.pushEntry none frameBase }) ∧
      ((spCell t S (D + frameBase)).add ((entCell t none D frameBase).add G)).Valid ∧
      StackAuth { m with stacks := m.pushEntry none frameBase }
        ((spCell t S (D + frameBase)).add ((entCell t none D frameBase).add G)) := by
  have hD : 0 < ((spCell t S D).add G).ex (.sp t) (S, D) := by simp [spCell]; omega
  obtain ⟨-, hlay, L, hent⟩ := h.of_budget hv hS hD
  have hdep : m.stackDepth t ≤ D := hent.depth_le
  have hGsp : ∀ v, G.ex (.sp t) v = 0 := hv.ex_zero
  have hGf : ∀ v, G.ex (.frm t D) v = 0 := fun v => by
    refine Nat.eq_zero_of_not_pos fun hp => ?_
    obtain ⟨i, hi, hl, -, hL⟩ := hent.frm D v (by simp [spCell]; omega)
    have := hent.live i hi hl
    omega
  obtain ⟨c1, c2, c3⟩ := ex_push (k₁ := .sp t) (K := .frm t D) (v₁ := (S, D))
    (v₁' := (S, D + frameBase)) (w := (D, frameBase)) (G := G) (by simp) hGsp hGf
  subst hcur
  refine ⟨enterFrame_run_fits hS (by omega), ACell.Valid.add_ex _
    (ACell.Valid.add_ex _ hv.of_add_right hGf) (fun v => by simp [entCell, hGsp]), ?_⟩
  have hso : ∀ t', ({ m with stacks := m.pushEntry none frameBase } : Mem).stackOf t' =
      if t' = m.current then { (m.stackOf m.current) with entries :=
        (((m.stackOf m.current).entries.popWhile (deadIn m.blocks)).push
          { block := none, base := m.stackDepth m.current, charge := frameBase }) }
      else m.stackOf t' := fun t' => by
    show (m.pushEntry none frameBase).getD t' default = _
    unfold Mem.pushEntry
    rw [getD_setStackAt]; rfl
  have hbk : ∀ t', (({ m with stacks := m.pushEntry none frameBase } : Mem).stackOf t').budget =
      (m.stackOf t').budget ∧
      (({ m with stacks := m.pushEntry none frameBase } : Mem).stackOf t').base = (m.stackOf t').base :=
    fun t' => by rw [hso]; split <;> (rename_i e; try subst e) <;> exact ⟨rfl, rfl⟩
  refine ⟨fun t' => ?_, fun t₁ t₂ S₁ S₂ hne h₁ h₂ => ?_⟩
  · by_cases e : t' = m.current
    · subst e
      exact ThreadOk.push (o := none) (L := L) hS hlay hent (by rw [hso, if_pos rfl])
        (Nat.le_refl _) (Nat.le_refl _) (fun _ _ => rfl)
        (fun b blk' hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by simp; omega))
        (fun b hb => by cases hb) (by decide) c1 c2 (fun k v h1 h2 => c3 k v h1 h2)
    · exact (h.thread t').transfer (by rw [hso, if_neg e]) (Nat.le_refl _) (Nat.le_refl _)
        (fun b blk' hb' hl _ => ⟨blk', hb', hl, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩)
        (fun b blk' hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by simp; omega))
        (fun k v hk => c3 k v (AKey.ne_of_tid hk rfl e) (AKey.ne_of_tid hk rfl e))
  · rw [(hbk t₁).1] at h₁; rw [(hbk t₂).1] at h₂
    rw [(hbk t₁).2, (hbk t₂).2]
    exact h.apart t₁ t₂ S₁ S₂ hne h₁ h₂

/-- `closeFrame s i` closes the topmost open frame entry below index `i`, if there is one. -/
theorem closeFrame_spec (s : StackState) : ∀ i, i ≤ s.entries.size →
    ((∀ j (hj : j < s.entries.size), j < i →
        ¬ (s.entries[j].block = none ∧ s.entries[j].closed = false)) ∧ s.closeFrame i = s) ∨
    ∃ k, ∃ hk : k < s.entries.size, k < i ∧ s.entries[k].block = none ∧
      s.entries[k].closed = false ∧
      (∀ j (hj : j < s.entries.size), k < j → j < i →
        ¬ (s.entries[j].block = none ∧ s.entries[j].closed = false)) ∧
      s.closeFrame i = { s with entries := s.entries.set! k { s.entries[k] with closed := true } } := by
  intro i
  induction i with
  | zero => intro _; exact .inl ⟨fun j _ hj => absurd hj (Nat.not_lt_zero _), rfl⟩
  | succ i ih =>
    intro hi
    have hi' : i < s.entries.size := by omega
    have hc : s.closeFrame (i + 1) =
        if (s.entries[i].block.isNone && !s.entries[i].closed) = true then
          { s with entries := s.entries.set! i { s.entries[i] with closed := true } }
        else s.closeFrame i := by
      rw [StackState.closeFrame, Array.getElem?_eq_getElem hi']
    rw [hc]
    by_cases ho : s.entries[i].block = none ∧ s.entries[i].closed = false
    · have : (s.entries[i].block.isNone && !s.entries[i].closed) = true := by simp [ho.1, ho.2]
      rw [if_pos this]
      exact .inr ⟨i, hi', by omega, ho.1, ho.2, fun j _ h1 h2 => absurd h2 (by omega), rfl⟩
    · have : ¬ (s.entries[i].block.isNone && !s.entries[i].closed) = true := by
        intro h; apply ho
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not,
          Bool.not_true] at h
        exact h
      rw [if_neg this]
      rcases ih (by omega) with ⟨hn, he⟩ | ⟨k, hk, hki, hb, hcl, hn, he⟩
      · refine .inl ⟨fun j hj hji => ?_, he⟩
        by_cases e : j = i
        · subst e; exact ho
        · exact hn j hj (by omega)
      · refine .inr ⟨k, hk, by omega, hb, hcl, fun j hj h1 h2 => ?_, he⟩
        by_cases e : j = i
        · subst e; exact ho
        · exact hn j hj h1 (by omega)

theorem leaveFrame_run_some {m : Mem} {S : Nat} (h : (m.stackOf m.current).budget = some S) :
    leaveFrame.run m =
      pure ((), { m with stacks := setStackAt m.stacks m.current (m.stackOf m.current).closeFrame }) := by
  simp [leaveFrame, h, StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    pure, ExceptT.pure, ExceptT.mk]

theorem getElem_set!_close {es : Array StackEntry} {k i : Nat} (hk : k < es.size)
    (hi : i < (es.set! k { es[k] with closed := true }).size) :
    (es.set! k { es[k] with closed := true })[i] =
      if k = i then { es[k] with closed := true } else es[i]'(by simpa using hi) := by
  simp only [Array.set!_eq_setIfInBounds]
  exact Array.getElem_setIfInBounds (by simpa using hi)

/-- **Leaving a frame returns its charge** (the memory side of a `leaveFrame` rule with
tokens): the running thread `t` with `sp t S (ℓ + c)` and its frame's token `ent t none ℓ c`
closes that frame (it is the topmost open one), and the memory then authorizes `sp t S ℓ`. -/
theorem StackAuth.leaveFrame {m : Mem} {G : KCell} {t S ℓ ch : Nat}
    (h : StackAuth m ((spCell t S (ℓ + ch)).add ((entCell t none ℓ ch).add G)))
    (hv : ((spCell t S (ℓ + ch)).add ((entCell t none ℓ ch).add G)).Valid) (hcur : m.current = t) :
    ∃ m', leaveFrame.run m = pure ((), m') ∧ ((spCell t S ℓ).add G).Valid ∧
      StackAuth m' ((spCell t S ℓ).add G) := by
  have hGsp : ∀ v, G.ex (.sp t) v = 0 := fun v => by
    have := hv.ex_zero v; simp [entCell] at this; exact this
  have hGf : ∀ v, G.ex (.frm t ℓ) v = 0 := hv.of_add_right.ex_zero
  have hc' : ((spCell t S ℓ).add G).Valid := ACell.Valid.add_ex _ hv.of_add_right.of_add_right hGsp
  have hsp0 : 0 < ((spCell t S (ℓ + ch)).add ((entCell t none ℓ ch).add G)).ex (.sp t)
      (S, ℓ + ch) := by simp [spCell]; omega
  have hS := h.budget_of_sp hv hsp0
  obtain ⟨-, hlay, L, hent⟩ := h.of_budget hv hS hsp0
  -- the frame's entry
  obtain ⟨i₀, hi₀, hl₀, hb₀, hL⟩ := hent.frm ℓ (ℓ, ch) (by simp [entCell]; omega)
  obtain ⟨hch₀, -, hle₀, ht₀⟩ := hent.live i₀ hi₀ hl₀
  have hk₀ : entKey t (m.stackOf t).entries[i₀] ℓ = .frm t ℓ := by unfold entKey; rw [hb₀]
  rw [hL, hk₀] at ht₀
  have huq := (hv (.frm t ℓ)).2.2.2.2 (ℓ, (m.stackOf t).entries[i₀].charge) (ℓ, ch)
    (by rw [ht₀]; omega) (by simp [spCell, entCell]; omega)
  simp only [Prod.mk.injEq, true_and] at huq
  have hopen : ∀ i (hi : i < (m.stackOf t).entries.size), (m.stackOf t).entries[i].block = none →
      (m.stackOf t).entries[i].closed = false →
      (m.stackOf t).entries[i].liveIn m.blocks = true := fun i hi hb hc => by
    simp [StackEntry.liveIn, hb, hc]
  have hcl₀ : (m.stackOf t).entries[i₀].closed = false := by
    simp [StackEntry.liveIn, hb₀] at hl₀; exact hl₀
  -- `closeFrame` closes exactly `i₀`
  rcases closeFrame_spec (m.stackOf t) _ (Nat.le_refl _) with ⟨hn, -⟩ | ⟨k, hk, -, hbk, hck, hn, hcf⟩
  · exact absurd ⟨hb₀, hcl₀⟩ (hn i₀ hi₀ hi₀)
  have hk : k = i₀ := by
    rcases Nat.lt_trichotomy k i₀ with hlt | heq | hgt
    · exact absurd ⟨hb₀, hcl₀⟩ (hn i₀ hi₀ hlt hi₀)
    · exact heq
    · have hlk := hopen k hk hbk hck
      have := hent.order k i₀ hk hgt hlk hl₀
      have := hent.live k hk hlk
      omega
  subst hk
  subst hcur
  refine ⟨_, leaveFrame_run_some hS, hc', ?_⟩
  rw [hcf]
  generalize hes' : (m.stackOf m.current).entries.set! k
    { (m.stackOf m.current).entries[k] with closed := true } = es' at *
  have hes'sz : es'.size = (m.stackOf m.current).entries.size := by rw [← hes']; simp
  have hget : ∀ i (hi : i < es'.size), es'[i] = if k = i then
      { (m.stackOf m.current).entries[k] with closed := true }
      else (m.stackOf m.current).entries[i]'(by omega) := fun i hi => by
    subst hes'; exact getElem_set!_close hk hi
  have hso : ∀ t', ({ m with stacks := (setStackAt m.stacks m.current
      { (m.stackOf m.current) with entries := es' }) } : Mem).stackOf t' =
      if t' = m.current then { (m.stackOf m.current) with entries := es' } else m.stackOf t' :=
    fun t' => getD_setStackAt _ _ _ _
  have hbk' : ∀ t', (({ m with stacks := (setStackAt m.stacks m.current
      { (m.stackOf m.current) with entries := es' }) } : Mem).stackOf t').budget =
      (m.stackOf t').budget ∧ (({ m with stacks := (setStackAt m.stacks m.current
      { (m.stackOf m.current) with entries := es' }) } : Mem).stackOf t').base =
        (m.stackOf t').base :=
    fun t' => by rw [hso]; split <;> (rename_i e; try subst e) <;> exact ⟨rfl, rfl⟩
  have hfields : ∀ i (hi : i < (m.stackOf m.current).entries.size) (hi' : i < es'.size),
      es'[i].block = (m.stackOf m.current).entries[i].block ∧
      es'[i].base = (m.stackOf m.current).entries[i].base ∧
      es'[i].charge = (m.stackOf m.current).entries[i].charge := fun i hi hi' => by
    rw [hget i hi']; split <;> (rename_i e; try subst e) <;> exact ⟨rfl, rfl, rfl⟩
  have hcx : ∀ k' v, k' ≠ .sp m.current → k' ≠ .frm m.current ℓ →
      ((spCell m.current S ℓ).add G).ex k' v =
        ((spCell m.current S (ℓ + ch)).add ((entCell m.current none ℓ ch).add G)).ex k' v :=
    fun k' v h1 h2 => by simp [spCell, entCell, h1, h2]
  refine ⟨fun t' => ?_, fun t₁ t₂ S₁ S₂ hne h₁ h₂ => ?_⟩
  · by_cases e : t' = m.current
    · subst e
      unfold ThreadOk
      rw [hso, if_pos rfl]
      simp only [hS]
      refine ⟨ℓ, by simp [spCell, hGsp], ⟨hlay.limit, fun i j hi hj => ?_, fun i hi b hbi => ?_,
        fun b blk hb hclr => ?_⟩, L, ?_⟩
      · simp only at hi
        rw [(hfields i (by omega) hi).2.1, (hfields j (by omega) (by omega)).2.1,
          (hfields j (by omega) (by omega)).2.2]
        exact hlay.order i j (by omega) hj
      · simp only at hi
        rw [(hfields i (by omega) hi).1] at hbi
        exact hlay.ids i (by omega) b hbi
      · obtain ⟨i, hi, hbi, e1, e2⟩ := hlay.inRes b blk hb hclr
        obtain ⟨f1, f2, f3⟩ := hfields i hi (by omega)
        exact ⟨i, by simp only; omega, by rw [f1]; exact hbi, by rw [f2, f3]; exact e1,
          by rw [f2]; exact e2⟩
      · refine EntOk.pop (i₀ := k) hent hv hes'sz (fun i hi hi' => hfields i hi hi')
          (fun i hi hi' hl => ?_) (fun i hi hi' hne _ hl => ?_) hi₀ hl₀ hL huq (Nat.le_refl _)
          (fun _ h => h) (fun k' v h1 h2 => ?_) (fun v => ?_)
        · have e2 : es'[i] = if k = i then
              { (m.stackOf m.current).entries[k] with closed := true }
              else (m.stackOf m.current).entries[i] := hget i hi'
          by_cases e : k = i
          · subst e; rw [e2, if_pos rfl] at hl
            simp [StackEntry.liveIn, hb₀] at hl
          · rw [e2, if_neg e] at hl; exact ⟨hl, Ne.symm e⟩
        · rw [hget i hi', if_neg (Ne.symm hne)]; exact hl
        · rw [hk₀] at h2; exact hcx k' v h1 h2
        · rw [hk₀]; simp [spCell, hGf]
    · exact (h.thread t').transfer (by rw [hso, if_neg e]) (Nat.le_refl _) (Nat.le_refl _)
        (fun b blk' hb' hl _ => ⟨blk', hb', hl, .inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩)
        (fun b blk' hb' hbs => absurd (Array.getElem?_eq_some_iff.mp hb').1 (by simp only; omega))
        (fun k' v hk' => hcx k' v (AKey.ne_of_tid hk' rfl e) (AKey.ne_of_tid hk' rfl e))
  · rw [(hbk' t₁).1] at h₁; rw [(hbk' t₂).1] at h₂
    rw [(hbk' t₁).2, (hbk' t₂).2]
    exact h.apart t₁ t₂ S₁ S₂ hne h₁ h₂

/-! ## Introduction: the start memory -/

/-- **The introduction of `sp`** (the other is a later step's spawn rule): the start memory with
the main thread's budget `S` (`Mem.withStack`) authorizes `sp 0 S 0` next to a cell without
stack tokens. The reserve is clear of every block (`Mem.reserveAt?`), and no entry exists yet. -/
theorem StackAuth.withStack {m : Mem} {c : KCell} {S base : Nat}
    (hb : ∀ t, (m.stackOf t).budget = none) (hc : ∀ k v, k ≠ .cred → c.ex k v = 0)
    (hr : m.reserveAt? 0 S = some base) : StackAuth (m.withStack S) ((spCell 0 S 0).add c) := by
  have hp := Mem.reserveAt?_placeOk hr
  simp only [Mem.placeOk, Mem.fitOk, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨-, -⟩, hlim⟩, hfree⟩, -⟩ := hp
  have hws : m.withStack S = { m with stacks := setStackAt m.stacks 0 { budget := some S, base } } := by
    simp only [Mem.withStack, hr]
  have hso : ∀ t, (m.withStack S).stackOf t =
      if t = 0 then ({ budget := some S, base } : StackState) else m.stackOf t := fun t => by
    rw [hws]; exact getD_setStackAt _ _ _ _
  have hcx : ∀ k v, k ≠ .sp 0 → ((spCell 0 S 0).add c).ex k v = c.ex k v := fun k v hk => by
    simp [spCell, hk]
  refine ⟨fun t => ?_, fun t t' S₁ S₂ hne h₁ h₂ => ?_⟩
  · unfold ThreadOk
    rw [hso]
    by_cases e : t = 0
    · subst e
      simp only [ite_true]
      refine ⟨0, by simp [spCell, hc (.sp 0) (S, 0) (by simp)], ⟨by simpa [hws] using hlim,
        fun i j hi => by simp at hi, fun i hi => by simp at hi, fun b blk hb' hclr => ?_⟩, fun _ => 0,
        ⟨fun i hi => by simp at hi, fun i j hi => by simp at hi, fun ℓ v hv => ?_, fun b v hv => ?_⟩⟩
      · rw [hws] at hb'
        rw [Mem.addrFree_iff.mp hfree b blk hb'] at hclr
        cases hclr
      · rw [hcx _ _ (by simp), hc _ _ (by simp)] at hv; cases hv
      · rw [hcx _ _ (by simp), hc _ _ (by simp)] at hv; cases hv
    · simp only [e, ite_false, hb t]
      exact ⟨fun v => by rw [hcx _ _ (by simp [e]), hc _ _ (by simp)],
        fun b v => by rw [hcx _ _ (by simp), hc _ _ (by simp)],
        fun ℓ v => by rw [hcx _ _ (by simp), hc _ _ (by simp)]⟩
  · rw [hso] at h₁ h₂
    split at h₁ <;> split at h₂
    · rename_i e₁ e₂; exact absurd (e₁.trans e₂.symm) hne
    · rw [hb] at h₂; cases h₂
    · rw [hb] at h₁; cases h₁
    · rw [hb] at h₁; cases h₁

end Full
end Zig
