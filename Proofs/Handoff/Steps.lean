import Proofs.Handoff.Protocol

/-!
# The steps of `handoff`'s protocol

The facts of `Proofs/Handoff/Protocol.lean` that each version's walk of `main` and the producer
uses, once for every layout and every implementation of the sync objects:

- **No deadlock** (`live_of`): while the producer has not ended, a sleeping thread is not the
  last one. It discharges the `hlive` premises of `CondImpl.wait_wp` and `EventImpl.wait_wp`.
- **The program places** (`U_relabel`, `inv_ev`, `inv_joins`, `inv_hl`, `inv_v7`, `inv_rdy`,
  `inv_sg`, `inv_st`, `inv_end`): a thread's step in its own code at the same memory moves its
  `Ph`; the shared words and the futex queue stay.
- **The contracts' client premises** at `main`'s condition wait (`hone_c`, `hhb_c`, `hent_c`,
  `hlive_c`), its event wait (`hone_e`, `hhb_e`, `hlive_e`) and the producer's signal (`hseen`).
-/

namespace Zig
namespace Handoff

open Conc Conc.Proto Full Full.FAssn

variable {Lo : Layout} {Tgt : Type} {prodOf : Tgt → Option Ptr}

/-- A thread out of the lock's code with the part `r` at the places `x`. -/
def gO (r : Res) (x : X) : Gh := (⟨.out, r, rnil⟩, x)

/-- A thread with the part `r` at the places `x` that holds the mutex and its resource `rL`. -/
def gH (r rL : Res) (x : X) : Gh := (⟨.holds, r, rL⟩, x)

/-! ## No deadlock -/

/-- After the spawn, the producer is at a producer's place. -/
theorem Shape.two {Y : ThreadId → X} {m : Mem} (h : Shape Y m) (hs : m.threads.size = 2) :
    (Y 1).ph.isProd = true := by
  obtain ⟨-, ⟨h1, -⟩ | ⟨-, -, -, -, hp, -⟩⟩ := h
  · rw [h1] at hs; cases hs
  · exact hp

/-- `main` past its spawn: the producer runs. -/
theorem Shape.size {Y : ThreadId → X} {m : Mem} (h : Shape Y m) (h0 : (Y 0).ph ≠ .pre) :
    m.threads.size = 2 := by
  obtain ⟨-, ⟨-, hy, -⟩ | ⟨hs, -⟩⟩ := h
  · rw [hy] at h0; exact absurd rfl h0
  · exact hs

/-- **No deadlock while the producer has not ended**: the producer has not ended, it does not
wait at a join, and it sleeps at no futex (at the mutex, `FitsOn.noWaits`; never at the epoch,
`places`, or at the event, `FEvent.wx`). -/
theorem live_of {G : ThreadId → Gh} {m : Mem} {t : ThreadId} (hi : (proto Lo prodOf).inv G m)
    (hf : (G 1).2.ph ≠ .fin) (hs : m.threads.size = 2) : (proto Lo prodOf).Live t G m := by
  intro _ hall
  obtain ⟨rX, hL, hu⟩ := hi
  have hp : (G 1).2.ph.isProd = true := hu.shape.two hs
  rcases hall 1 (by rw [hs]; decide) with h | h | h
  · exact hf (by rw [h.2])
  · obtain ⟨w, hw, he⟩ := Array.any_eq_true'.mp h
    have e : w.1 = 1 := by simpa using he
    rcases hu.q w hw with hq | hq | hq
    · exact (fitsL (Lo := Lo) (prodOf := prodOf)).noWaits hL hall
        (Array.any_eq_true'.mpr ⟨w, hw, by simp [hq]⟩)
    · obtain ⟨i, jr, e', h1, -⟩ := hu.cinv.q w hw hq
      have hw1 : ((G 1).2.c).waits = true := by
        rw [← e]; show ((C Lo).ph (G w.1)).waits = true; rw [h1]; rfl
      rw [hu.places] at hw1; cases hw1
    · have h1 := (hu.einv.q w hw hq).1
      have hx : (G 1).2.ph = .ev ∨ (G 1).2.ph = .joins := by
        rw [← e]; exact hu.einv.wx w.1 (Or.inr h1)
      rcases hx with hx | hx <;> rw [hx] at hp <;> cases hp
  · rw [h.2] at hp; cases hp

/-! ## The program places -/

/-- `R` reads `v` and `ready` only. -/
theorem R_eq {Y Y' : ThreadId → X} (hv : (Y' 1).ph.hasV = (Y 1).ph.hasV)
    (hr : (Y' 1).ph.hasR = (Y 1).ph.hasR) : R Lo Y' = R Lo Y := by
  unfold R vOf; rw [hv, hr]

/-- **A change of thread `t`'s program place** at the same memory, out of the condition's and
the event's code: `U` holds with the new ghost value `g₁` given its fields that read the
program places (the threads' shape, `ep1`, `ent`, `hold`, `reg`, `lvc`, `fin`) and the event's
roles. -/
theorem U_relabel {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {g₀ g₁ : Gh}
    (hu : U Lo (upd G t g₀) rX m) (hc₀ : g₀.2.c = .out) (hc₁ : g₁.2.c = .out)
    (he₀ : g₀.2.e = .out) (he₁ : g₁.2.e = .out)
    (hwx : (E Lo).wx g₀ → (E Lo).wx g₁) (hsx : (E Lo).sx g₀ → (E Lo).sx g₁)
    (hsh : Shape (fun u => (upd G t g₁ u).2) m)
    (hep1 : (upd G t g₁ 1).2.ph.sigd = false → (Lo.WE.hist m).size = 1)
    (hent : ((upd G t g₁ 0).2.c).crit → (upd G t g₁ 1).2.ph = .lk)
    (hhold : (upd G t g₁ 1).2.ph = .hl ∨ (upd G t g₁ 1).2.ph = .v7 → (upd G t g₁ 1).1.ph = .holds)
    (hreg : ∀ i jr sn e, (upd G t g₁ 0).2.c = .reg i jr sn e →
      VClock.le (Lo.WS.hist m)[jr]!.clock (m.clocks[1]!) = true ∨
      ((upd G t g₁ 1).2.ph = .lk ∧ (((upd G t g₁ 0).1.ph = .holds ∧
        VClock.le (Lo.WS.hist m)[jr]!.clock (m.clocks[0]!) = true) ∨
        (L Lo).Before m (Lo.WS.hist m)[jr]!.clock)))
    (hlvc : ((upd G t g₁ 0).2.c).waits → (upd G t g₁ 1).2.ph = .st ∨ (upd G t g₁ 1).2.ph = .fin →
      (C Lo).Signalled m)
    (hfin : (upd G t g₁ 1).2.ph = .fin → (E Lo).IsSet m) :
    U Lo (upd G t g₁) rX m := by
  have hcg : (C Lo).ph g₁ = .out := hc₁
  have hct : (C Lo).ph (upd G t g₀ t) = .out := by rw [upd_self]; exact hc₀
  have hI := hu.cinv.moveT (t := t) (g' := g₁) rfl rfl rfl apE.ptr_ne (fun _ _ h => h)
    (fun _ => VClock.le_refl _) (by rw [hcg]; intro h; cases h) (by rw [hcg]; intro h; cases h)
    (by rw [hcg, hct]; intro h; rcases h with h | h <;> cases h) (by rw [hcg]; intro h; cases h)
    (fun _ _ => by rw [hcg]; intro h; cases h) (fun _ _ _ _ => by rw [hcg]; intro h; cases h)
    (fun _ _ _ _ => by rw [hct]; intro h; cases h)
    (fun _ _ _ => ⟨(by rw [hcg]; intro h; cases h), fun _ => by rw [hcg, hct]⟩)
  rw [upd_upd] at hI
  have hJ := hu.einv.relabel (G' := upd G t g₁) (t := t)
    (fun u hu => by rw [upd_ne _ _ hu, upd_ne _ _ hu])
    (by rw [upd_self, upd_self]; show g₁.2.e = g₀.2.e; rw [he₀, he₁])
    (fun h => absurd (by rw [upd_self]; exact he₁) h)
    (fun h => by rw [upd_self] at h ⊢; exact hwx h) (fun h => by rw [upd_self] at h ⊢; exact hsx h)
  refine ⟨hsh, hu.io, hu.rest, hu.blk, hu.ws, hu.we, hu.wv, hI, hJ, ?_, hep1, hu.ep0, hent,
    hhold, hreg, hlvc, hfin, hu.q, fun u hu' => ?_⟩
  · by_cases e : t = 1
    · subst e; rw [upd_self, hc₁]; rfl
    · rw [upd_ne _ _ (Ne.symm e)]; have := hu.places; rwa [upd_ne _ _ (Ne.symm e)] at this
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu'; exact absurd hc₁ hu'
    · rw [upd_ne _ _ e] at hu' ⊢; have := hu.xc u; rw [upd_ne _ _ e] at this; exact this hu'

/-- `R` after a change of `t`'s ghost value with the same `v` and `ready`. -/
theorem R_upd {G : ThreadId → Gh} {t : ThreadId} {g₀ g₁ : Gh} {r : Res}
    (hv : (upd G t g₁ 1).2.ph.hasV = (upd G t g₀ 1).2.ph.hasV)
    (hr : (upd G t g₁ 1).2.ph.hasR = (upd G t g₀ 1).2.ph.hasR)
    (h : (L Lo).R (upd G t g₀) r) : (L Lo).R (upd G t g₁) r := by
  have h' : R Lo (fun u => (upd G t g₀ u).2) r := h
  show R Lo (fun u => (upd G t g₁ u).2) r
  rw [R_eq (Y := fun u => (upd G t g₀ u).2) hv hr]; exact h'

/-- **A change of `t`'s program place at the same lock place** keeps the protocol's invariant,
given `U` after it (`U_relabel`) and the same `v` and `ready`. -/
theorem inv_relabel {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g₀ g₁ : Gh}
    (hi : (proto Lo prodOf).inv (upd G t g₀) m) (h1 : g₁.1 = g₀.1)
    (hv : (upd G t g₁ 1).2.ph.hasV = (upd G t g₀ 1).2.ph.hasV)
    (hr : (upd G t g₁ 1).2.ph.hasR = (upd G t g₀ 1).2.ph.hasR)
    (hU : ∀ rX, (L Lo).Inv (upd G t g₀) rX m → U Lo (upd G t g₀) rX m → U Lo (upd G t g₁) rX m) :
    (proto Lo prodOf).inv (upd G t g₁) m := by
  obtain ⟨rX, hL, hu⟩ := hi
  have hL' := hL.relabel (t := t) (g := g₁) (by rw [upd_self]; show g₁.1.ph = g₀.1.ph; rw [h1])
    (by rw [upd_self]; show g₁.1.part = g₀.1.part; rw [h1])
    (by rw [upd_self]; show g₁.1.held = g₀.1.held; rw [h1])
    (fun r hR => by rw [upd_upd]; exact R_upd hv hr hR)
  rw [upd_upd] at hL'
  exact ⟨rX, hL', hU rX hL hu⟩

theorem upd0_1 (G : ThreadId → Gh) (g : Gh) : upd G 0 g 1 = G 1 := upd_ne _ _ (by decide)
theorem upd1_0 (G : ThreadId → Gh) (g : Gh) : upd G 1 g 0 = G 0 := upd_ne _ _ (by decide)

/-- **`main`'s program place** moves (out of the condition's and the event's code; it may wait
at the event from `ev` on). -/
theorem U_main {G : ThreadId → Gh} {rX : Res} {m : Mem} {a : FLG} {x₀ x₁ : X}
    (hu : U Lo (upd G 0 (a, x₀)) rX m) (hc₀ : x₀.c = .out) (hc₁ : x₁.c = .out)
    (he₀ : x₀.e = .out) (he₁ : x₁.e = .out) (hp₀ : x₀.ph ≠ .pre) (hm : x₁.ph.isMain = true)
    (hp₁ : x₁.ph ≠ .pre) (hwx : x₀.ph = .ev ∨ x₀.ph = .joins → x₁.ph = .ev ∨ x₁.ph = .joins) :
    U Lo (upd G 0 (a, x₁)) rX m := by
  obtain ⟨h00, ⟨-, hy, -⟩ | ⟨hs, h1, hmn, -, hpr, hrest⟩⟩ := hu.shape
  · have h : (upd G 0 (a, x₀) 0).2 = { ph := .pre } := hy
    rw [upd_self] at h
    exact absurd (by rw [show x₀ = { ph := .pre } from h]) hp₀
  have hm₀ : x₀.ph.isMain = true := by
    have : (upd G 0 (a, x₀) 0).2.ph.isMain = true := hmn; rwa [upd_self] at this
  refine U_relabel hu hc₀ hc₁ he₀ he₁ hwx (fun h => ?_) ⟨h00, .inr ⟨hs, h1,
      by show (upd G 0 (a, x₁) 0).2.ph.isMain = true; rw [upd_self]; exact hm,
      by show (upd G 0 (a, x₁) 0).2.ph ≠ .pre; rw [upd_self]; exact hp₁,
      by show (upd G 0 (a, x₁) 1).2.ph.isProd = true; rw [upd0_1]
         have : (upd G 0 (a, x₀) 1).2.ph.isProd = true := hpr; rwa [upd0_1] at this,
      fun u hu' => by
        show (upd G 0 (a, x₁) u).2 = {}
        have : (upd G 0 (a, x₀) u).2 = {} := hrest u hu'
        have hu0 : u ≠ 0 := by unfold ThreadId at *; omega
        rwa [upd_ne _ _ hu0] at this ⊢⟩⟩
    (fun h => by rw [upd0_1] at h; have := hu.ep1; rw [upd0_1] at this; exact this h)
    (fun h => by rw [upd_self] at h; rw [hc₁] at h; cases h)
    (fun h => by rw [upd0_1] at h ⊢; have := hu.hold; rw [upd0_1] at this; exact this h)
    (fun _ _ _ _ h => by rw [upd_self] at h; rw [hc₁] at h; cases h)
    (fun h => by rw [upd_self] at h; rw [hc₁] at h; cases h)
    (fun h => by rw [upd0_1] at h; have := hu.fin; rw [upd0_1] at this; exact this h)
  have h' : x₀.ph = .st ∨ x₀.ph = .fin := h
  rcases h' with h' | h' <;> rw [h'] at hm₀ <;> cases hm₀

/-- **`main`'s program place** moves: the protocol's invariant. -/
theorem inv_main {G : ThreadId → Gh} {m : Mem} {a : FLG} {x₀ x₁ : X}
    (hi : (proto Lo prodOf).inv (upd G 0 (a, x₀)) m) (hc₀ : x₀.c = .out) (hc₁ : x₁.c = .out)
    (he₀ : x₀.e = .out) (he₁ : x₁.e = .out) (hp₀ : x₀.ph ≠ .pre) (hm : x₁.ph.isMain = true)
    (hp₁ : x₁.ph ≠ .pre) (hwx : x₀.ph = .ev ∨ x₀.ph = .joins → x₁.ph = .ev ∨ x₁.ph = .joins) :
    (proto Lo prodOf).inv (upd G 0 (a, x₁)) m :=
  inv_relabel hi rfl (by rw [upd0_1, upd0_1]) (by rw [upd0_1, upd0_1]) fun _ _ hu =>
    U_main hu hc₀ hc₁ he₀ he₁ hp₀ hm hp₁ hwx

/-- `main` after its `unlock`: to the event's wait. -/
theorem inv_ev {G : ThreadId → Gh} {m : Mem} {a : FLG}
    (hi : (proto Lo prodOf).inv (upd G 0 (a, { ph := .run })) m) :
    (proto Lo prodOf).inv (upd G 0 (a, { ph := .ev })) m :=
  inv_main hi rfl rfl rfl rfl (by decide) rfl (by decide) fun _ => .inl rfl

/-- `main` after the event's wait: to its join. -/
theorem inv_joins {G : ThreadId → Gh} {m : Mem} {a : FLG}
    (hi : (proto Lo prodOf).inv (upd G 0 (a, { ph := .ev })) m) :
    (proto Lo prodOf).inv (upd G 0 (a, { ph := .joins })) m :=
  inv_main hi rfl rfl rfl rfl (by decide) rfl (by decide) fun _ => .inr rfl

/-- **The producer's program place** moves (out of the condition's and the event's code), given
the fields of `U` that read it. -/
theorem U_prod {G : ThreadId → Gh} {rX : Res} {m : Mem} {a₀ a₁ : FLG} {x₀ x₁ : X}
    (hu : U Lo (upd G 1 (a₀, x₀)) rX m) (hc₀ : x₀.c = .out) (hc₁ : x₁.c = .out)
    (he₀ : x₀.e = .out) (he₁ : x₁.e = .out) (hp₀ : x₀.ph.isProd = true)
    (hp₁ : x₁.ph.isProd = true)
    (hsx : x₀.ph = .st ∨ x₀.ph = .fin → x₁.ph = .st ∨ x₁.ph = .fin)
    (hep1 : x₁.ph.sigd = false → x₀.ph.sigd = false)
    (hent : ((G 0).2.c).crit → x₁.ph = .lk)
    (hhold : x₁.ph = .hl ∨ x₁.ph = .v7 → a₁.ph = .holds)
    (hreg : ∀ i jr sn e, (G 0).2.c = .reg i jr sn e →
      VClock.le (Lo.WS.hist m)[jr]!.clock (m.clocks[1]!) = true)
    (hlvc : ((G 0).2.c).waits → x₁.ph = .st ∨ x₁.ph = .fin → (C Lo).Signalled m)
    (hfin : x₁.ph = .fin → (E Lo).IsSet m) :
    U Lo (upd G 1 (a₁, x₁)) rX m := by
  obtain ⟨h00, ⟨-, -, hy⟩ | ⟨hs, h1, hmn, hnp, -, hrest⟩⟩ := hu.shape
  · have h : (upd G 1 (a₀, x₀) 1).2 = {} := hy 1 (Nat.le_refl _)
    rw [upd_self] at h
    rw [show x₀ = {} from h] at hp₀; cases hp₀
  refine U_relabel hu hc₀ hc₁ he₀ he₁ (fun h => ?_) hsx ⟨h00, .inr ⟨hs, h1,
      by show (upd G 1 (a₁, x₁) 0).2.ph.isMain = true; rw [upd1_0]
         have : (upd G 1 (a₀, x₀) 0).2.ph.isMain = true := hmn; rwa [upd1_0] at this,
      by show (upd G 1 (a₁, x₁) 0).2.ph ≠ .pre; rw [upd1_0]
         have : (upd G 1 (a₀, x₀) 0).2.ph ≠ .pre := hnp; rwa [upd1_0] at this,
      by show (upd G 1 (a₁, x₁) 1).2.ph.isProd = true; rw [upd_self]; exact hp₁,
      fun u hu' => by
        show (upd G 1 (a₁, x₁) u).2 = {}
        have : (upd G 1 (a₀, x₀) u).2 = {} := hrest u hu'
        have hu1 : u ≠ 1 := by unfold ThreadId at *; omega
        rwa [upd_ne _ _ hu1] at this ⊢⟩⟩
    (fun h => by
      rw [upd_self] at h
      have := hu.ep1; rw [upd_self] at this; exact this (hep1 h))
    (fun h => by rw [upd1_0] at h; rw [upd_self]; exact hent h)
    (fun h => by rw [upd_self] at h ⊢; exact hhold h)
    (fun i jr sn e h => by rw [upd1_0] at h; exact .inl (hreg i jr sn e h))
    (fun h h' => by rw [upd1_0] at h; rw [upd_self] at h'; exact hlvc h h')
    (fun h => by rw [upd_self] at h; exact hfin h)
  have h' : x₀.ph = .ev ∨ x₀.ph = .joins := h
  rcases h' with h' | h' <;> rw [h'] at hp₀ <;> cases hp₀

/-- Two threads do not hold the mutex. -/
theorem one_holder {G : ThreadId → Gh} {rX : Res} {m : Mem} (hL : (L Lo).Inv G rX m)
    (h0 : (G 0).1.ph = .holds) (h1 : (G 1).1.ph = .holds) : False := by
  have := hL.w.one 0 1 h0 h1; cases this

/-- The producer's program place does not leave `lk` or `hl` while `main` is registered: the
registration happened before the producer. -/
theorem U.reg_lk {G : ThreadId → Gh} {rX : Res} {m : Mem} (hL : (L Lo).Inv G rX m)
    (hu : U Lo G rX m) (hh : (G 1).1.ph = .holds) {i jr : Nat} {sn : Bool} {e : BitVec 32}
    (hr : (G 0).2.c = .reg i jr sn e) :
    VClock.le (Lo.WS.hist m)[jr]!.clock (m.clocks[1]!) = true := by
  rcases hu.reg i jr sn e hr with h | ⟨-, ⟨h0, -⟩ | ⟨k, l, hl, hle⟩⟩
  · exact h
  · exact (one_holder hL h0 hh).elim
  · exact VClock.le_trans hle ((hL.w.rel k l hl).2 1 hh)

/-- **The producer, holding the mutex,** goes from `lk`, `hl` or `v7` to `hl`, `v7` or `rdy`
(its lock's return and its two stores). -/
theorem U_held {G : ThreadId → Gh} {rX : Res} {m : Mem} {rp rL : Res} {x₀ x₁ : X}
    (hL : (L Lo).Inv (upd G 1 (gH rp rL x₀)) rX m) (hu : U Lo (upd G 1 (gH rp rL x₀)) rX m)
    (hc₀ : x₀.c = .out) (hc₁ : x₁.c = .out) (he₀ : x₀.e = .out) (he₁ : x₁.e = .out)
    (hp₀ : x₀.ph = .lk ∨ x₀.ph = .hl ∨ x₀.ph = .v7)
    (hp₁ : x₁.ph = .hl ∨ x₁.ph = .v7 ∨ x₁.ph = .rdy) :
    U Lo (upd G 1 (gH rp rL x₁)) rX m := by
  have hh : (upd G 1 (gH rp rL x₀) 1).1.ph = .holds := by rw [upd_self]; rfl
  have hnc : ((G 0).2.c).crit → False := fun h => by
    have h' := hu.cinv.crit 0 (by show ((upd G 1 (gH rp rL x₀) 0).2.c).crit = true; rw [upd1_0]; exact h)
    exact one_holder hL h' hh
  refine U_prod hu hc₀ hc₁ he₀ he₁ ?_ ?_ ?_ ?_ (fun h => (hnc h).elim) (fun _ => rfl)
    (fun i jr sn e h => U.reg_lk hL hu hh (by rw [upd1_0]; exact h)) ?_ ?_
  · rcases hp₀ with h | h | h <;> rw [h] <;> rfl
  · rcases hp₁ with h | h | h <;> rw [h] <;> rfl
  · intro h; rcases hp₀ with h' | h' | h' <;> rcases h with h | h <;> rw [h'] at h <;> cases h
  · intro _; rcases hp₀ with h | h | h <;> rw [h] <;> rfl
  · intro _ h; rcases hp₁ with h' | h' | h' <;> rcases h with h | h <;> rw [h'] at h <;> cases h
  · intro h; rcases hp₁ with h' | h' | h' <;> rw [h'] at h <;> cases h

/-- The producer after its `lock`: it holds the mutex. -/
theorem inv_hl {G : ThreadId → Gh} {m : Mem} {rp rL : Res}
    (hi : (proto Lo prodOf).inv (upd G 1 (gH rp rL { ph := .lk })) m) :
    (proto Lo prodOf).inv (upd G 1 (gH rp rL { ph := .hl })) m :=
  inv_relabel hi rfl (by rw [upd_self, upd_self]; rfl) (by rw [upd_self, upd_self]; rfl)
    fun _ hL hu => U_held hL hu rfl rfl rfl rfl (.inl rfl) (.inl rfl)

/-- The producer out of the mutex: to its `signal`. -/
theorem inv_sg {G : ThreadId → Gh} {m : Mem} {rp : Res}
    (hi : (proto Lo prodOf).inv (upd G 1 (gO rp { ph := .rdy })) m) :
    (proto Lo prodOf).inv (upd G 1 (gO rp { ph := .sg })) m :=
  inv_relabel hi rfl (by rw [upd_self, upd_self]; rfl) (by rw [upd_self, upd_self]; rfl)
    fun _ _ hu => by
      have hent : ((G 0).2.c).crit → False := fun h => by
        have := hu.ent (by rw [upd1_0]; exact h); rw [upd_self] at this; cases this
      exact U_prod hu rfl rfl rfl rfl rfl rfl (fun h => by rcases h with h | h <;> cases h)
        (fun h => by cases h) (fun h => (hent h).elim) (fun h => by rcases h with h | h <;> cases h)
        (fun i jr sn e h => by
          rcases hu.reg i jr sn e (by rw [upd1_0]; exact h) with h' | ⟨h', -⟩
          · exact h'
          · rw [upd_self] at h'; cases h')
        (fun _ h => by rcases h with h | h <;> cases h) (fun h => by cases h)

/-- A waiter out of the condition's critical code is registered. -/
theorem reg_of' {c : CPh} (hw : c.waits = true) (hc : c.crit = false) :
    ∃ i jr sn e, c = .reg i jr sn e := by
  cases c <;> simp_all [CPh.waits, CPh.crit]

/-- The producer after its `signal`: a registered `main` is signalled (`signal_wp`'s post); to
the event's `set`. -/
theorem inv_st {G : ThreadId → Gh} {m : Mem} {rp : Res}
    (hi : (proto Lo prodOf).inv (upd G 1 (gO rp { ph := .sg })) m)
    (hs : ∀ i jr sn e, (G 0).2.c = .reg i jr sn e → (C Lo).Signalled m) :
    (proto Lo prodOf).inv (upd G 1 (gO rp { ph := .st })) m :=
  inv_relabel hi rfl (by rw [upd_self, upd_self]; rfl) (by rw [upd_self, upd_self]; rfl)
    fun _ _ hu => by
      have hent : ((G 0).2.c).crit = false := by
        cases h : ((G 0).2.c).crit
        · rfl
        · have := hu.ent (by rw [upd1_0]; exact h); rw [upd_self] at this; cases this
      exact U_prod hu rfl rfl rfl rfl rfl rfl (fun _ => .inl rfl) (fun h => by cases h)
        (fun h => by rw [hent] at h; cases h) (fun h => by rcases h with h | h <;> cases h)
        (fun i jr sn e h => by
          rcases hu.reg i jr sn e (by rw [upd1_0]; exact h) with h' | ⟨h', -⟩
          · exact h'
          · rw [upd_self] at h'; cases h')
        (fun hw _ => by
          obtain ⟨i, jr, sn, e, h⟩ := reg_of' hw hent
          exact hs i jr sn e h)
        (fun h => by cases h)

/-- **The producer's end**, after the event's `set`: it is `gone` at `fin`. -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {rp : Res}
    (hi : (proto Lo prodOf).inv (upd G 1 (gO rp { ph := .st })) m) (hset : (E Lo).IsSet m) :
    (proto Lo prodOf).inv (upd G 1 (⟨.gone, rp, rnil⟩, { ph := .fin })) m := by
  obtain ⟨rX, hL, hu⟩ := hi
  have hRk : ∀ r, (L Lo).R (upd G 1 (gO rp { ph := .st })) r →
      (L Lo).R (upd (upd G 1 (gO rp { ph := .st })) 1 (⟨.gone, rp, rnil⟩, { ph := .fin })) r :=
    fun r hR => by
      rw [upd_upd]
      exact R_upd (g₀ := gO rp { ph := .st }) (by rw [upd_self, upd_self]; rfl)
        (by rw [upd_self, upd_self]; rfl) hR
  have hL' := hL.ghost (t := 1) (g := (⟨.gone, rp, rnil⟩, { ph := .fin })) (by rw [upd_self]; rfl)
    (.inr (.inl rfl)) (by rw [upd_self]; rfl) rfl (fun h => absurd rfl h) hRk
  rw [upd_upd] at hL'
  refine ⟨rX, hL', U_prod hu rfl rfl rfl rfl rfl rfl (fun _ => .inr rfl) (fun h => by cases h)
    (fun h => ?_) (fun h => by rcases h with h | h <;> cases h) (fun i jr sn e h => ?_)
    (fun hw _ => ?_) (fun _ => hset)⟩
  · have := hu.ent (by rw [upd1_0]; exact h); rw [upd_self] at this; cases this
  · rcases hu.reg i jr sn e (by rw [upd1_0]; exact h) with h' | ⟨h', -⟩
    · exact h'
    · rw [upd_self] at h'; cases h'
  · exact hu.lvc (by rw [upd1_0]; exact hw) (by rw [upd_self]; exact .inl rfl)

end Handoff
end Zig
