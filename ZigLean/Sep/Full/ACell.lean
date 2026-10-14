/-!
# The authoritative counter cell (`docs/sep-full-state.md` §Authoritative counters)

One generic ghost cell for every counted, non-mintable resource of the full-state logic. Per key
`k : κ` it has

* **counted fragments** `frag k : Nat` (`◯n`), which split and join by addition;
* **exclusive fragments** `ex k v` (how many fragments hold the value `v : ν`): at most one per
  key is valid, so whoever holds it knows the key's value exactly;
* **frame authorities** `auth k N` (how many `●N`): at most one per key, and the counted
  fragments are at most its value.

Composition is pointwise addition of the three counts, so it is total, associative and
commutative, with the empty cell as unit; validity (`ACell.Valid`) is closed under dropping a
part (`ACell.Valid.of_add`).

The cell has two **modes**, chosen per key by who holds the authority:

* **Frame authority** (the credits, `£n`): `●N` is a fragment like any other. No judgment can
  create a counted fragment, because every judgment quantifies over every frame, among them one
  that holds `●N` with all `N` fragments out (`ACell.frag_le`). Only an adequacy theorem puts
  `●N` into the frame and `◯N` into the program's resource (`ACell.Valid.addAuth`). With the
  step ticks the memory also meters a frame authority: the counted fragments plus the steps run
  so far stay at most its value (`TickAuth`, `ZigLean/Sep/Full/MemAuth.lean`).
* **Memory authority** (the stack depth `sp`): the memory decides which
  exclusive fragment exists (`ACell.MemEx`: exactly one fragment whose value the memory
  satisfies, or none). A judgment cannot create such a fragment either: the memory demands
  exactly one, and a second one is invalid (`ACell.MemEx.no_mint`).

So both modes share the cell and its validity; the memory adds one conjunct about the cell
(`MemAuth`), next to the validity. The ghost state of the full-state logic holds one such cell
(`Ghost.ac`); its keys are `AKey` (`ZigLean/Sep/Full/StackDepth.lean`).
-/

namespace Zig
namespace Full

/-- **The authoritative counter cell** (module doc): per key, counted fragments, exclusive
fragments by value, and frame authorities by value. -/
@[ext] structure ACell (κ ν : Type) where
  frag : κ → Nat
  ex : κ → ν → Nat
  auth : κ → Nat → Nat

namespace ACell

variable {κ ν : Type}

def unit : ACell κ ν := ⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩

def add (a b : ACell κ ν) : ACell κ ν :=
  ⟨fun k => a.frag k + b.frag k, fun k v => a.ex k v + b.ex k v, fun k n => a.auth k n + b.auth k n⟩

@[simp] theorem add_frag (a b : ACell κ ν) (k : κ) : (a.add b).frag k = a.frag k + b.frag k := rfl
@[simp] theorem add_ex (a b : ACell κ ν) (k : κ) (v : ν) : (a.add b).ex k v = a.ex k v + b.ex k v := rfl
@[simp] theorem add_auth (a b : ACell κ ν) (k : κ) (n : Nat) :
    (a.add b).auth k n = a.auth k n + b.auth k n := rfl
@[simp] theorem unit_frag (k : κ) : (unit : ACell κ ν).frag k = 0 := rfl
@[simp] theorem unit_ex (k : κ) (v : ν) : (unit : ACell κ ν).ex k v = 0 := rfl
@[simp] theorem unit_auth (k : κ) (n : Nat) : (unit : ACell κ ν).auth k n = 0 := rfl

theorem add_comm (a b : ACell κ ν) : a.add b = b.add a := by
  ext <;> simp [Nat.add_comm]

theorem add_assoc (a b c : ACell κ ν) : (a.add b).add c = a.add (b.add c) := by
  ext <;> simp [Nat.add_assoc]

theorem add_left_comm (a b c : ACell κ ν) : a.add (b.add c) = b.add (a.add c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

@[simp] theorem add_unit (a : ACell κ ν) : a.add unit = a := by ext <;> simp

@[simp] theorem unit_add (a : ACell κ ν) : unit.add a = a := by ext <;> simp

/-- Key `k` is valid: at most one frame authority, the counted fragments at most its value, and
at most one exclusive fragment. -/
def KValid (c : ACell κ ν) (k : κ) : Prop :=
  (∀ n, c.auth k n ≤ 1) ∧ (∀ n n', 0 < c.auth k n → 0 < c.auth k n' → n = n') ∧
    (∀ n, 0 < c.auth k n → c.frag k ≤ n) ∧
    (∀ v, c.ex k v ≤ 1) ∧ ∀ v v', 0 < c.ex k v → 0 < c.ex k v' → v = v'

/-- Every key is valid (`KValid`). -/
def Valid (c : ACell κ ν) : Prop := ∀ k, c.KValid k

theorem valid_unit : (unit : ACell κ ν).Valid := fun _ =>
  ⟨fun _ => Nat.zero_le _, fun _ _ h => absurd h (by simp), fun _ h => absurd h (by simp),
    fun _ => Nat.zero_le _, fun _ _ h => absurd h (by simp)⟩

theorem KValid.of_add {a b : ACell κ ν} {k : κ} (h : (a.add b).KValid k) : a.KValid k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [add_auth, add_frag, add_ex] at h1 h2 h3 h4 h5
  exact ⟨fun n => by have := h1 n; omega, fun n n' hn hn' => h2 n n' (by omega) (by omega),
    fun n hn => by have := h3 n (by omega); omega, fun v => by have := h4 v; omega,
    fun v v' hv hv' => h5 v v' (by omega) (by omega)⟩

/-- Validity is closed under dropping a part. -/
theorem Valid.of_add {a b : ACell κ ν} (h : (a.add b).Valid) : a.Valid := fun k => (h k).of_add

theorem Valid.of_add_right {a b : ACell κ ν} (h : (a.add b).Valid) : b.Valid :=
  Valid.of_add (b := a) (by rw [add_comm]; exact h)

/-- Only key `k`'s validity depends on key `k`'s counts. -/
theorem KValid.congr {a b : ACell κ ν} {k : κ} (hf : b.frag k = a.frag k)
    (he : ∀ v, b.ex k v = a.ex k v) (ha : ∀ n, b.auth k n = a.auth k n) (h : a.KValid k) :
    b.KValid k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun n => ?_, fun n n' => ?_, fun n => ?_, fun v => ?_, fun v v' => ?_⟩ <;>
    simp only [hf, he, ha] <;> first | exact h1 n | exact h2 n n' | exact h3 n | exact h4 v | exact h5 v v'

/-! ## Point cells -/

section Points

variable [DecidableEq κ]

/-- `n` counted fragments of key `k` (`◯n`). -/
def fragAt (k : κ) (n : Nat) : ACell κ ν := { (unit : ACell κ ν) with frag := fun k' => if k' = k then n else 0 }

/-- The frame authority `●N` of key `k`. -/
def authAt (k : κ) (N : Nat) : ACell κ ν :=
  { (unit : ACell κ ν) with auth := fun k' n => if k' = k ∧ n = N then 1 else 0 }

/-- The exclusive fragment of key `k` with the value `v`. -/
def exAt [DecidableEq ν] (k : κ) (v : ν) : ACell κ ν :=
  { (unit : ACell κ ν) with ex := fun k' v' => if k' = k ∧ v' = v then 1 else 0 }

@[simp] theorem fragAt_frag (k k' : κ) (n : Nat) :
    (fragAt k n : ACell κ ν).frag k' = if k' = k then n else 0 := rfl
@[simp] theorem fragAt_ex (k k' : κ) (n : Nat) (v : ν) : (fragAt k n : ACell κ ν).ex k' v = 0 := rfl
@[simp] theorem fragAt_auth (k k' : κ) (n N : Nat) : (fragAt k n : ACell κ ν).auth k' N = 0 := rfl
@[simp] theorem authAt_frag (k k' : κ) (N : Nat) : (authAt k N : ACell κ ν).frag k' = 0 := rfl
@[simp] theorem authAt_ex (k k' : κ) (N : Nat) (v : ν) : (authAt k N : ACell κ ν).ex k' v = 0 := rfl
@[simp] theorem authAt_auth (k k' : κ) (N n : Nat) :
    (authAt k N : ACell κ ν).auth k' n = if k' = k ∧ n = N then 1 else 0 := rfl

section
variable [DecidableEq ν]
@[simp] theorem exAt_frag (k k' : κ) (v : ν) : (exAt k v : ACell κ ν).frag k' = 0 := rfl
@[simp] theorem exAt_ex (k k' : κ) (v v' : ν) :
    (exAt k v : ACell κ ν).ex k' v' = if k' = k ∧ v' = v then 1 else 0 := rfl
@[simp] theorem exAt_auth (k k' : κ) (v : ν) (n : Nat) : (exAt k v : ACell κ ν).auth k' n = 0 := rfl
end

/-- Counted fragments split and join. -/
theorem fragAt_add (k : κ) (a b : Nat) :
    (fragAt k a : ACell κ ν).add (fragAt k b) = fragAt k (a + b) := by
  ext k' <;> simp only [add_frag, fragAt_frag, add_ex, fragAt_ex, add_auth, fragAt_auth] <;> split <;> rfl

@[simp] theorem fragAt_zero (k : κ) : (fragAt k 0 : ACell κ ν) = unit := by
  ext k' <;> simp

/-! ## Frame authority: counted fragments are bounded by `●N` -/

/-- **Counted fragments are bounded by the authority**: a valid cell with `n` fragments and `●N`
of key `k` has `n ≤ N`. -/
theorem frag_le {k : κ} {n N : Nat} {G : ACell κ ν}
    (h : ((fragAt k n).add ((authAt k N).add G)).Valid) : n ≤ N := by
  have := (h k).2.2.1 N (by simp <;> omega)
  simp at this; omega

/-- **The adequacy step of a frame-authority key**: a valid cell without fragments or authority
at `k` stays valid with `N` counted fragments and `●N` added. No judgment can do this: the frame
is fixed. -/
theorem Valid.addAuth {c : ACell κ ν} {k : κ} (N : Nat) (h : c.Valid) (hf : c.frag k = 0)
    (ha : ∀ n, c.auth k n = 0) : ((fragAt k N).add ((authAt k N).add c)).Valid := by
  intro k'
  by_cases e : k' = k
  · subst e
    obtain ⟨-, -, -, h4, h5⟩ := h k'
    refine ⟨fun n => ?_, fun n n' hn hn' => ?_, fun n hn => ?_, fun v => ?_, fun v v' => ?_⟩
    · simp only [add_auth, fragAt_auth, authAt_auth, ha]; split <;> omega
    · simp only [add_auth, fragAt_auth, authAt_auth, ha] at hn hn'
      split at hn <;> split at hn' <;> simp_all
    · simp only [add_auth, fragAt_auth, authAt_auth, ha] at hn
      split at hn
      · simp_all
      · omega
    · simpa using h4 v
    · simpa using h5 v v'
  · exact (h k').congr (by simp [e]) (by simp) (by simp [e])

/-- `Valid.addAuth` with fewer fragments than the authority's value. -/
theorem Valid.addAuthLe {c : ACell κ ν} {k : κ} {N L : Nat} (hNL : N ≤ L) (h : c.Valid)
    (hf : c.frag k = 0) (ha : ∀ n, c.auth k n = 0) : ((fragAt k N).add ((authAt k L).add c)).Valid := by
  intro k'
  by_cases e : k' = k
  · subst e
    obtain ⟨-, -, -, h4, h5⟩ := h k'
    refine ⟨fun n => ?_, fun n n' hn hn' => ?_, fun n hn => ?_, fun v => ?_, fun v v' => ?_⟩
    · simp only [add_auth, fragAt_auth, authAt_auth, ha]; split <;> omega
    · simp only [add_auth, fragAt_auth, authAt_auth, ha] at hn hn'
      split at hn <;> split at hn' <;> simp_all
    · simp only [add_auth, fragAt_auth, authAt_auth, ha] at hn
      split at hn
      · rename_i hc; obtain ⟨-, rfl⟩ := hc; simp [hf]; omega
      · omega
    · simpa using h4 v
    · simpa using h5 v v'
  · exact (h k').congr (by simp [e]) (by simp) (by simp [e])

/-! ## Exclusive fragments -/

section
variable [DecidableEq ν]

/-- Two exclusive fragments of one key are invalid. -/
theorem exAt_excl {k : κ} {v v' : ν} {G : ACell κ ν} :
    ¬ ((exAt k v).add ((exAt k v').add G)).Valid := fun h => by
  obtain ⟨-, -, -, h4, h5⟩ := h k
  by_cases e : v = v'
  · subst e; have := h4 v; simp at this; omega
  · exact e (h5 v v' (by simp <;> omega) (by simp <;> omega))

/-- Next to an exclusive fragment of `k` the rest holds none of `k`. -/
theorem Valid.ex_zero {k : κ} {v : ν} {G : ACell κ ν} (h : ((exAt k v).add G).Valid) (v' : ν) :
    G.ex k v' = 0 := by
  obtain ⟨-, -, -, h4, h5⟩ := h k
  by_cases e : v' = v
  · subst e; have := h4 v'; simp at this; omega
  · refine Classical.byContradiction fun hne => e (h5 v' v ?_ (by simp <;> omega))
    simp [e]; omega

/-- A key without exclusive fragments takes one. -/
theorem Valid.add_ex {k : κ} (v : ν) {G : ACell κ ν} (h : G.Valid) (h0 : ∀ v', G.ex k v' = 0) :
    ((exAt k v).add G).Valid := by
  intro k'
  by_cases e : k' = k
  · subst e
    obtain ⟨h1, h2, h3, -, -⟩ := h k'
    refine ⟨fun n => ?_, fun n n' => ?_, fun n => ?_, fun v' => ?_, fun v₁ v₂ h₁ h₂ => ?_⟩
    · simp only [add_auth, exAt_auth, Nat.zero_add]; exact h1 n
    · simp only [add_auth, exAt_auth, Nat.zero_add]; exact h2 n n'
    · simp only [add_auth, exAt_auth, add_frag, exAt_frag, Nat.zero_add]; exact h3 n
    · have := h0 v'; show (exAt k' v).ex k' v' + G.ex k' v' ≤ 1
      rw [exAt_ex]; split <;> omega
    · have e1 := h0 v₁; have e2 := h0 v₂
      change 0 < (exAt k' v).ex k' v₁ + G.ex k' v₁ at h₁
      change 0 < (exAt k' v).ex k' v₂ + G.ex k' v₂ at h₂
      rw [exAt_ex] at h₁ h₂
      split at h₁ <;> split at h₂ <;> simp_all
  · exact (h k').congr (by simp) (by simp [e]) (by simp)

/-- An exclusive fragment changes its value: validity stays. -/
theorem Valid.swap_ex {k : κ} {v : ν} (v' : ν) {G : ACell κ ν} (h : ((exAt k v).add G).Valid) :
    ((exAt k v').add G).Valid :=
  Valid.add_ex v' h.of_add_right h.ex_zero

end

/-! ## Memory authority -/

/-- **Memory authority of key `k`**: the memory demands exactly one exclusive fragment of `k`,
whose value satisfies `P` (`own = some P`), or none (`own = none`). -/
def MemEx (c : ACell κ ν) (k : κ) : Option (ν → Prop) → Prop
  | none => ∀ v, c.ex k v = 0
  | some P => ∃ v, c.ex k v = 1 ∧ P v

/-- **No fragment of a memory-authority key can be created**: next to a cell that meets the
memory's demand at `k`, one more exclusive fragment of `k` either is invalid or breaks the
demand. So no judgment produces one from nothing (every judgment keeps the memory's demand and
validity against every frame). -/
theorem MemEx.no_mint [DecidableEq ν] {c : ACell κ ν} {k : κ} {own : Option (ν → Prop)} (v : ν)
    (h : c.MemEx k own) (hv : ((exAt k v).add c).Valid) : ¬ ((exAt k v).add c).MemEx k own := by
  cases own with
  | none => intro h'; have := h' v; simp at this
  | some P =>
    obtain ⟨w, hw, -⟩ := h
    have := hv.ex_zero w; omega

end Points

end ACell

end Full
end Zig
