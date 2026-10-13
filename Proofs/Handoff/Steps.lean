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

/-- While the producer holds the mutex, `main`'s registration happened before it (`main` does
not hold the mutex, and its release happened before the producer's lock). `hL` is the lock's
invariant with `G'`, at the same lock places as `G` but for the producer, which holds. -/
theorem U.reg_lk {G G' : ThreadId → Gh} {rX rX' : Res} {m : Mem} (hL : (L Lo).Inv G' rX' m)
    (hu : U Lo G rX m) (h0 : (G' 0).1.ph = (G 0).1.ph) (hh : (G' 1).1.ph = .holds) {i jr : Nat}
    {sn : Bool} {e : BitVec 32} (hr : (G 0).2.c = .reg i jr sn e) :
    VClock.le (Lo.WS.hist m)[jr]!.clock (m.clocks[1]!) = true := by
  rcases hu.reg i jr sn e hr with h | ⟨-, ⟨h0', -⟩ | ⟨k, l, hl, hle⟩⟩
  · exact h
  · exact (one_holder hL (h0.trans h0') hh).elim
  · exact VClock.le_trans hle ((hL.w.rel k l hl).2 1 hh)

/-- **The producer, holding the mutex,** goes from `lk`, `hl` or `v7` to `hl`, `v7` or `rdy`
(its lock's return and its two stores). `hL`: the lock's invariant with any resource and places
of the holder. -/
theorem U_held {G : ThreadId → Gh} {rX rX' : Res} {m : Mem} {rp rL rL' : Res} {x₀ x₁ x' : X}
    (hL : (L Lo).Inv (upd G 1 (gH rp rL' x')) rX' m) (hu : U Lo (upd G 1 (gH rp rL x₀)) rX m)
    (hc₀ : x₀.c = .out) (hc₁ : x₁.c = .out) (he₀ : x₀.e = .out) (he₁ : x₁.e = .out)
    (hp₀ : x₀.ph = .lk ∨ x₀.ph = .hl ∨ x₀.ph = .v7)
    (hp₁ : x₁.ph = .hl ∨ x₁.ph = .v7 ∨ x₁.ph = .rdy) :
    U Lo (upd G 1 (gH rp rL x₁)) rX m := by
  have hh : (upd G 1 (gH rp rL' x') 1).1.ph = .holds := by rw [upd_self]; rfl
  have hnc : ((G 0).2.c).crit → False := fun h => by
    have h' := hu.cinv.crit 0 (by show ((upd G 1 (gH rp rL x₀) 0).2.c).crit = true; rw [upd1_0]; exact h)
    have h'' : (upd G 1 (gH rp rL x₀) 0).1.ph = .holds := h'
    rw [upd1_0] at h''
    exact one_holder hL (by rw [upd1_0]; exact h'') hh
  refine U_prod hu hc₀ hc₁ he₀ he₁ ?_ ?_ ?_ ?_ (fun h => (hnc h).elim) (fun _ => rfl)
    (fun i jr sn e h => U.reg_lk hL hu (by rw [upd1_0, upd1_0]) hh (by rw [upd1_0]; exact h)) ?_ ?_
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

/-! ## The holder's accesses to `v` and `ready` -/

/-- **A step of the mutex's holder `t` on its resource** (`v`, `ready`), a thread triple on
`part ⋆ resource` (`FLock.Inv.wp_liftM`): `t` goes from the places `x₀` to `x₁`, the new
resource has `R` at `x₁` (`hR`), and `U` follows (`hU`: `U_held` for the producer's stores, the
same places for `main`'s loads). -/
theorem wp_held {σ α : Type} {x : MemM α} {s : σ} {t : ThreadId} {rp rL : Res} {x₀ x₁ : X}
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {Pa : FAssn} {Qa : α → FAssn}
    (htt : FTTriple Pa x Qa) (hpa : R Lo (fun u => (upd G t (gH rp rL x₀) u).2) rL → Pa rL)
    (hi : (proto Lo prodOf).inv (upd G t (gH rp rL x₀)) m) (hc : m.current = t)
    {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (hR : ∀ a r, Qa a r → R Lo (fun u => (upd G t (gH rp r x₁) u).2) r)
    (hU : ∀ rX m' r, (L Lo).Inv (upd G t (gH rp r x₁)) rX m' →
      U Lo (upd G t (gH rp r x₀)) rX m' → U Lo (upd G t (gH rp r x₁)) rX m')
    (h : ∀ a m' rQ, m'.current = t → m'.threads = m.threads → Qa a rQ →
      (proto Lo prodOf).inv (upd G t (gH rp rQ x₁)) m' → Q (a, s) G m' d) :
    (proto Lo prodOf).WP t ((liftM x : CM Tgt σ α).run s) Q G m d := by
  obtain ⟨rX, hiL, hu⟩ := hi
  have hh : (L Lo).ph (upd G t (gH rp rL x₀) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨ht, hjt⟩ := hiL.ht (by rw [hh]; decide)
  have hres : R Lo (fun u => (upd G t (gH rp rL x₀) u).2) rL := by
    have := hiL.res t hh; rwa [upd_self] at this
  have hd : FHeap.Disjoint rp.heap rL.heap := by have := hiL.pdisj t; rwa [upd_self] at this
  refine hiL.wp_liftM hc ht hjt (htt.frameL (R := fun r => r = rp))
    (by rw [upd_self]; exact ⟨rp, rL, hd, rfl, rfl, hpa hres⟩) fun a m' r' hr hq hs hc' hk => ?_
  obtain ⟨r₁, rQ, hdQ, e, hr₁, hq'⟩ := hq
  rw [hr₁] at e hdQ
  have hl := hk (gH rp rQ x₁) (by rw [upd_self]; rfl) e.symm hdQ (fun h => absurd rfl h)
    (fun h => absurd hh h) (fun _ => by
      show R Lo (fun u => (upd (upd G t (gH rp rL x₀)) t (gH rp rQ x₁) u).2) rQ
      rw [upd_upd]; exact hR a rQ hq')
  rw [upd_upd] at hl
  have hU' := U_stepIn (g := gH rp rQ x₀) hu hs hl (by rw [upd_self]; rfl) (by rw [upd_self]; rfl)
  rw [upd_upd] at hU'
  exact h a m' rQ hc' hs.threads hq' ⟨rX, hl, hU rX m' rQ hl hU'⟩

/-- The producer's stores of `v` and `ready` (`wp_held`'s `U`). -/
theorem U_store {G : ThreadId → Gh} {rX : Res} {m : Mem} {rp r : Res} {x₀ x₁ : X}
    (hp₀ : x₀ = { ph := .hl } ∨ x₀ = { ph := .v7 }) (hp₁ : x₁ = { ph := .v7 } ∨ x₁ = { ph := .rdy })
    (hL : (L Lo).Inv (upd G 1 (gH rp r x₁)) rX m) (hu : U Lo (upd G 1 (gH rp r x₀)) rX m) :
    U Lo (upd G 1 (gH rp r x₁)) rX m := by
  rcases hp₀ with rfl | rfl <;> rcases hp₁ with rfl | rfl <;>
    exact U_held hL hu rfl rfl rfl rfl (by simp) (by simp)

/-! ## The contracts' premises -/

/-- **`main` holds the mutex and read `ready = false`**: the producer is before its lock. -/
theorem prod_lk {G : ThreadId → Gh} {rX : Res} {m : Mem} (hL : (L Lo).Inv G rX m)
    (hu : U Lo G rX m) (h0 : (G 0).1.ph = .holds) (hs : m.threads.size = 2)
    (hr : (G 1).2.ph.hasR = false) : (G 1).2.ph = .lk := by
  have hp : (G 1).2.ph.isProd = true := hu.shape.two hs
  cases h : (G 1).2.ph with
  | lk => rfl
  | hl => exact (one_holder hL h0 (hu.hold (.inl h))).elim
  | v7 => exact (one_holder hL h0 (hu.hold (.inr h))).elim
  | _ => rw [h] at hp hr; simp [Ph.isProd, Ph.hasR] at hp hr

/-- **`main`'s condition wait**: the premises `hone`, `hhb` and `hent` of `CondImpl.wait_wp`.
`main` holds the mutex at `run` and read `ready = false`. -/
theorem cwait_ok {G : ThreadId → Gh} {m : Mem} {rM rL : Res}
    (hi : (proto Lo prodOf).inv (upd G 0 (gH rM rL { ph := .run })) m)
    (hr : (G 1).2.ph.hasR = false) :
    (∀ u, u ≠ 0 → (C Lo).ph (G u) = .out) ∧
    (∀ j < ((C Lo).Ep.hist m).size,
      VClock.le ((C Lo).Ep.hist m)[j]!.clock (m.clocks[0]!) = true) ∧
    (∀ rX, U Lo (upd G 0 (gH rM rL { ph := .run })) rX m →
      (C Lo).Inv (L Lo) (upd G 0 ((C Lo).set (gH rM rL { ph := .run }) .en)) m →
      U Lo (upd G 0 ((C Lo).set (gH rM rL { ph := .run }) .en)) rX m) := by
  obtain ⟨rX₀, hL, hu⟩ := hi
  have hp0 : (upd G 0 (gH rM rL { ph := .run }) 0).2.ph ≠ .pre := by
    rw [upd_self]; intro h; cases h
  have hs : m.threads.size = 2 := hu.shape.size hp0
  have hlk : (G 1).2.ph = .lk := by
    have := prod_lk hL hu (by rw [upd_self]; rfl) hs (by rw [upd0_1]; exact hr)
    rwa [upd0_1] at this
  refine ⟨fun u hu0 => ?_, fun j hj => ?_, fun rX hU hI => ?_⟩
  · by_cases hc : (G u).2.c = .out
    · exact hc
    · have hx := hu.xc u (by rw [upd_ne _ _ hu0]; exact hc)
      rw [upd_ne _ _ hu0] at hx
      have hp : (G u).2.ph.isProd = true ∨ (G u).2.ph.isMain = true := by
        rcases hx with h | h <;> rw [h] <;> simp [Ph.isProd, Ph.isMain]
      rcases hp with hp | hp
      · have := hu.shape.one (u := u) (by rw [upd_ne _ _ hu0]; exact hp)
        subst this
        rcases hx with h | h <;> rw [hlk] at h <;> cases h
      · exact absurd (hu.shape.zero (u := u) (by rw [upd_ne _ _ hu0]; exact hp)) hu0
  · have h1 := hu.ep1 (by rw [upd0_1, hlk]; rfl)
    have hj0 : j = 0 := by
      have : j < (Lo.WE.hist m).size := hj
      omega
    subst hj0; exact hu.ep0
  · have hX : ∀ u, u ≠ 0 → (upd G 0 ((C Lo).set (gH rM rL { ph := .run }) .en) u).2 =
        (upd G 0 (gH rM rL { ph := .run }) u).2 := fun u h => by rw [upd_ne _ _ h, upd_ne _ _ h]
    have h0 : (upd G 0 ((C Lo).set (gH rM rL { ph := .run }) .en) 0).2 =
        { ph := .run, c := .en } := by rw [upd_self]; rfl
    have hU1 := hU.hold
    have hU2 := hU.ep1
    have hU3 := hU.places
    rw [upd0_1] at hU1 hU2 hU3
    refine ⟨Shape.congr hU.shape rfl (fun u => ?_) (fun u hfr => ?_), hU.io, hU.rest, hU.blk,
      hU.ws, hU.we, hU.wv, hI, ?_, ?_, ?_, hU.ep0, ?_, ?_, ?_, ?_, ?_, hU.q, fun u hu' => ?_⟩
    · by_cases e : u = 0
      · subst e; rw [h0, upd_self]; rfl
      · rw [hX u e]
    · by_cases e : u = 0
      · subst e; rw [upd_self] at hfr
        rcases hfr with h | h <;> cases h
      · exact hX u e
    · exact hU.einv.relabel (fun u hu => by rw [upd_ne _ _ hu, upd_ne _ _ hu])
        (by rw [upd_self, upd_self]; rfl) (fun h => absurd (by rw [upd_self]; rfl) h)
        (fun h => by rw [upd_self] at h ⊢; exact h) (fun h => by rw [upd_self] at h ⊢; exact h)
    · rw [upd0_1]; exact hU3
    · intro h; rw [upd0_1] at h; exact hU2 h
    · intro _; rw [upd0_1]; exact hlk
    · intro h; rw [upd0_1] at h ⊢; exact hU1 h
    · intro i jr sn e h; rw [h0] at h; cases h
    · intro _ h; rw [upd0_1, hlk] at h; rcases h with h | h <;> cases h
    · intro h; rw [upd0_1, hlk] at h; cases h
    · by_cases e : u = 0
      · subst e; rw [h0]; exact .inl rfl
      · rw [hX u e] at hu' ⊢; exact hU.xc u hu'

/-- **`main`'s sleep at the condition** is no deadlock (`hlive` of `CondImpl.wait_wp`): a
registered `main` makes the producer's end signal it (`lvc`). -/
theorem cwait_live (G₁ : ThreadId → Gh) (m₁ : Mem)
    (hreg : ∃ i jr e, (C Lo).ph (G₁ 0) = .reg i jr false e) (_ : (L Lo).ph (G₁ 0) = .away)
    (hi : (proto Lo prodOf).inv G₁ m₁) (hs : ¬ (C Lo).Signalled m₁) :
    (proto Lo prodOf).Live 0 G₁ m₁ := by
  obtain ⟨i, jr, e, hr⟩ := hreg
  have hr' : (G₁ 0).2.c = .reg i jr false e := hr
  obtain ⟨rX, -, hu⟩ := id hi
  have hw : ((G₁ 0).2.c).waits = true := by rw [hr']; rfl
  have hrun : (G₁ 0).2.ph ≠ .pre := by
    rcases hu.xc 0 (by rw [hr']; nofun) with h | h <;> rw [h] <;> decide
  exact live_of hi (fun h => hs (hu.lvc hw (.inr h))) (hu.shape.size hrun)

/-- **`main`'s event wait** at `ev`: the premises `hone` and `hhb` of `EventImpl.wait_wp`. -/
theorem ewait_ok {G : ThreadId → Gh} {m : Mem} {rM : Res}
    (hi : (proto Lo prodOf).inv (upd G 0 (gO rM { ph := .ev })) m) :
    (∀ u, u ≠ 0 → (E Lo).ph (G u) = .out ∨ (E Lo).ph (G u) = .sw) ∧
    (∀ j < ((E Lo).W.hist m).size, ((E Lo).W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le ((E Lo).W.hist m)[j]!.clock (m.clocks[0]!) = true) := by
  obtain ⟨rX, -, hu⟩ := hi
  refine ⟨fun u hu0 => ?_, fun j hj hv => ?_⟩
  · have hE : ∀ p, (E Lo).ph (G u) = p → (p = .w0 ∨ p = .w1) → False := fun p hp hw => by
      have hx := hu.einv.wx u (by rw [upd_ne _ _ hu0]; rw [hp]; exact hw)
      have hx' : (G u).2.ph = .ev ∨ (G u).2.ph = .joins := by
        have : (upd G 0 (gO rM { ph := .ev }) u).2.ph = .ev ∨
          (upd G 0 (gO rM { ph := .ev }) u).2.ph = .joins := hx
        rwa [upd_ne _ _ hu0] at this
      have hm : (G u).2.ph.isMain = true := by rcases hx' with h | h <;> rw [h] <;> rfl
      exact hu0 (hu.shape.zero (u := u) (by rw [upd_ne _ _ hu0]; exact hm))
    cases h : (E Lo).ph (G u) with
    | out => exact .inl rfl
    | sw => exact .inr rfl
    | w0 => exact (hE _ h (.inl rfl)).elim
    | w1 => exact (hE _ h (.inr rfl)).elim
  · obtain ⟨u, hx, hle⟩ := hu.einv.wby j hj hv
    have hm : (upd G 0 (gO rM { ph := .ev }) u).2.ph.isMain = true := by
      have hx' : (upd G 0 (gO rM { ph := .ev }) u).2.ph = .ev ∨
        (upd G 0 (gO rM { ph := .ev }) u).2.ph = .joins := hx
      rcases hx' with h | h <;> rw [h] <;> rfl
    have := hu.shape.zero hm
    subst this; exact hle

/-- **`main`'s sleep at the event** is no deadlock (`hlive` of `EventImpl.wait_wp`): the
producer's end set the event (`fin`). -/
theorem ewait_live (G₁ : ThreadId → Gh) (m₁ : Mem) (hw : (E Lo).ph (G₁ 0) = .w1)
    (_ : (L Lo).ph (G₁ 0) = .away) (hi : (proto Lo prodOf).inv G₁ m₁) (hs : ¬ (E Lo).IsSet m₁) :
    (proto Lo prodOf).Live 0 G₁ m₁ := by
  obtain ⟨rX, -, hu⟩ := id hi
  have hx : (G₁ 0).2.ph = .ev ∨ (G₁ 0).2.ph = .joins := hu.einv.wx 0 (Or.inr hw)
  exact live_of hi (fun h => hs (hu.fin h))
    (hu.shape.size (by rcases hx with h | h <;> rw [h] <;> decide))

/-- **The producer's signal** at `sg`: the premise `hseen` of `CondImpl.signal_wp`. The registered
waiter is `main`; its registration happened before the producer (`reg`: the producer is past its
lock). -/
theorem signal_seen {rp : Res} (G₁ : ThreadId → Gh) (rX : Res) (m₁ : Mem)
    (hg : G₁ 1 = gO rp { ph := .sg }) (hu : U Lo G₁ rX m₁) (u i jr : Nat) (sn : Bool)
    (e : BitVec 32) (hr : (C Lo).ph (G₁ u) = .reg i jr sn e) :
    VClock.le ((C Lo).S.hist m₁)[jr]!.clock (m₁.clocks[1]!) = true := by
  have hr' : (G₁ u).2.c = .reg i jr sn e := hr
  have hu0 : u = 0 := by
    rcases hu.xc u (by rw [hr']; nofun) with h | h
    · exact hu.shape.zero (u := u) (by rw [h]; rfl)
    · have := hu.shape.one (u := u) (by rw [h]; rfl)
      subst this
      have := hu.places; rw [hr'] at this; cases this
  subst hu0
  rcases hu.reg i jr sn e hr' with h | ⟨h, -⟩
  · exact h
  · rw [hg] at h; cases h

end Handoff
end Zig
