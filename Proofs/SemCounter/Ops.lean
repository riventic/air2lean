import Proofs.SemCounter.Steps

/-!
# `wait` and `post` of `semaphoreCounter`

The premises of the semaphore's contract (`SemImpl.wait_wp`, `SemImpl.post_wp`) for this
protocol, once for every implementation. A thread in `semWork` with `k < 2` increments and no
permit (`gW rp k false 0`) waits; it takes the permit with `n` (`T`, at the increments of both
threads, `tot`) and records that value (`gW (rsum rp r) k true (sum Y)`). After its increment it
posts and gives `n` back to the free permit, one increment further (`gW rp (k + 1) false 0`).

- **The count** is 1 while no thread has the permit (`pv`): a take leaves 0, a give 1.
- **The rest after the take or the give**: only the taker's (giver's) place in the program
  changes (`Shape.work`), at most one thread has the permit (`one`), and its recorded value is
  the increments of both threads (`tot`).
- **No deadlock** (`hlive`): at count 0 the permit's holder (thread 0 or 1, not the waiter) is
  neither asleep at the epoch (only a waiter sleeps there, and a waiter has no permit, `wtx`)
  nor at the mutex (`FLock.Fits.noWaits`), and it has not ended.
-/

namespace Zig
namespace SemCounter

open Conc Conc.Proto Full Full.FAssn

/-- A thread in `semWork` out of the mutex: its part `r`, `k` increments, the permit `b` with the
recorded value `s`. -/
def gW (r : Res) (k : Nat) (b : Bool) (s : Nat) : Gh := (⟨.out, r, rnil⟩, { ph := .work k b s })

/-- The cell of `n` with the increments of both threads (`sum Y`). -/
def Tn (Y : ThreadId → Ph) : FAssn := up (pts nPtr 4 (BitVec.ofNat 32 (sum Y)))

/-- The client parts after two updates of `t` with the same client part. -/
theorem xs_upd_ph {G : ThreadId → Gh} {t : ThreadId} {g g' : Gh} (h : g.2.ph = g'.2.ph) :
    xs (upd G t g) = xs (upd G t g') := by
  funext u; unfold xs upd; split
  · exact h
  · rfl

/-! ## The count -/

theorem held_of {Y : ThreadId → Ph} {t : ThreadId} (ht : t < 2) (h : (Y t).holds = true) :
    held Y = true := by
  unfold held
  rcases t with _ | _ | t
  · simp [h]
  · simp [h]
  · unfold ThreadId at *; omega

theorem held_not {Y : ThreadId → Ph} (h : held Y = false) (u : ThreadId) (hu : u < 2) :
    (Y u).holds = false := by
  unfold held at h
  rcases u with _ | _ | u
  · simp_all
  · simp_all
  · unfold ThreadId at *; omega

theorem pv_ne {Y : ThreadId → Ph} (h : pv Y ≠ 0) : held Y = false := by
  unfold pv at h; cases e : held Y
  · rfl
  · rw [e] at h; exact absurd rfl h

theorem pv_zero {Y : ThreadId → Ph} (h : pv Y = 0) : held Y = true := by
  unfold pv at h; cases e : held Y
  · rw [e] at h; cases h
  · rfl

/-- The increments of both threads after `t`'s count rose by `j` (thread 0 or 1). -/
theorem sum_upd {Y Y' : ThreadId → Ph} {t : ThreadId} (ht : t < 2) (hY : ∀ u, u ≠ t → Y' u = Y u)
    {j : Nat} (hc : (Y' t).count = (Y t).count + j) : sum Y' = sum Y + j := by
  unfold sum
  by_cases h0 : t = 0
  · subst h0; rw [hY 1 (by decide), hc]; omega
  · have h1 : t = 1 := by unfold ThreadId at *; omega
    subst h1; rw [hY 0 (by decide), hc]; omega

/-- The threads' shape after `t`'s move between places in `semWork`. -/
theorem Shape.work {Y Y' : ThreadId → Ph} {m : Mem} {t : ThreadId} (h : Shape Y m) {k s : Nat}
    {b b' : Bool} {k' s' : Nat} (ht : Y t = .work k b s) (hk : k' ≤ 2)
    (ht' : Y' t = .work k' b' s') (hY : ∀ u, u ≠ t → Y' u = Y u) : Shape Y' m := by
  obtain ⟨h0, ⟨hsz, hy0, hyu⟩ | ⟨hsz, h1, hm, hp, hyu⟩⟩ := h
  · rcases t with _ | t
    · rw [hy0] at ht; cases ht
    · rw [hyu (t + 1) (by unfold ThreadId; omega)] at ht; cases ht
  · refine ⟨h0, .inr ⟨hsz, h1, ?_, ?_, fun u hu => ?_⟩⟩
    · rcases t with _ | t
      · exact .inr ⟨k', hk, b', s', ht'⟩
      · rw [hY 0 (by unfold ThreadId; omega)]; exact hm
    · rcases t with _ | _ | t
      · rw [hY 1 (by decide)]; exact hp
      · exact .inr ⟨k', hk, b', s', ht'⟩
      · rw [hyu (t + 2) (by unfold ThreadId; omega)] at ht; cases ht
    · by_cases e : u = t
      · subst e; rw [hyu u hu] at ht; cases ht
      · rw [hY u e]; exact hyu u hu

/-- A thread at a place of `semWork` is thread 0 or 1. -/
theorem Shape.lt {Y : ThreadId → Ph} {m : Mem} (h : Shape Y m) {u k s : Nat} {b : Bool}
    (hu : Y u = .work k b s) : u < 2 ∧ m.threads.size = 2 := by
  obtain ⟨-, ⟨-, hy0, hyu⟩ | ⟨hsz, -, -, -, hyu⟩⟩ := h
  · rcases u with _ | u
    · rw [hy0] at hu; cases hu
    · rw [hyu (u + 1) (by unfold ThreadId; omega)] at hu; cases hu
  · refine ⟨Classical.byContradiction fun hne => ?_, hsz⟩
    rw [hyu u (by unfold ThreadId at *; omega)] at hu; cases hu

/-! ## The take of a permit -/

variable {Tgt : Type} {semOf : Tgt → Option Ptr}

/-- **The rest after the take** (`SemImpl.wait_wp`'s `hU`): the taker `t` has the permit with the
increments of both threads. -/
theorem U_take {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {rp r h₁ h₂ : Res}
    {k : Nat} {sh : Array Word.Entry} {sc : VClock} (hk : k < 2)
    (hcnt : S.cnt (upd G t (gW rp k false 0)) ≠ 0)
    (hu : U (upd G t (S.set (L.set (gW rp k false 0) .holds h₁) (.pst sh sc))) rX m)
    (hci : C.Inv L (upd G t (S.set (L.set (gW (rsum rp r) k true
      (sum (xs (upd G t (gW rp k false 0))))) .holds h₂) (.pst sh sc))) m)
    (hsi : S.Inv (upd G t (S.set (L.set (gW (rsum rp r) k true
      (sum (xs (upd G t (gW rp k false 0))))) .holds h₂) (.pst sh sc))) m) :
    U (upd G t (S.set (L.set (gW (rsum rp r) k true (sum (xs (upd G t (gW rp k false 0)))))
      .holds h₂) (.pst sh sc))) rX m := by
  obtain ⟨G₁, hG₁⟩ : ∃ G₁, G₁ = upd G t (S.set (L.set (gW rp k false 0) .holds h₁) (.pst sh sc)) :=
    ⟨_, rfl⟩
  obtain ⟨G₂, hG₂⟩ : ∃ G₂, G₂ = upd G t (S.set (L.set (gW (rsum rp r) k true
      (sum (xs (upd G t (gW rp k false 0))))) .holds h₂) (.pst sh sc)) := ⟨_, rfl⟩
  rw [← hG₁] at hu; rw [← hG₂] at hci hsi ⊢
  have hX₁ : xs G₁ = xs (upd G t (gW rp k false 0)) := by
    rw [hG₁]; exact xs_upd_ph rfl
  have hne : ∀ u, u ≠ t → G₂ u = G₁ u := fun u e => by rw [hG₂, hG₁, upd_ne _ _ e, upd_ne _ _ e]
  have h₁t : (G₁ t).2.ph = .work k false 0 := by rw [hG₁, upd_self]; rfl
  have h₂t : (G₂ t).2.ph = .work k true (sum (xs (upd G t (gW rp k false 0)))) := by
    rw [hG₂, upd_self]; rfl
  have h₂s : (G₂ t).2.sp = .pst sh sc := by rw [hG₂, upd_self]; rfl
  have ht2 : t < 2 := (hu.um.shape.lt (u := t) (by show (G₁ t).2.ph = _; rw [h₁t])).1
  have hheld : held (xs G₁) = false := by rw [hX₁]; exact pv_ne hcnt
  have hsum : sum (xs G₂) = sum (xs G₁) := by
    have := sum_upd (Y := xs G₁) (Y' := xs G₂) (j := 0) ht2
      (fun u e => by show (G₂ u).2.ph = (G₁ u).2.ph; rw [hne u e])
      (by show (G₂ t).2.ph.count = (G₁ t).2.ph.count + 0; rw [h₁t, h₂t]; rfl)
    omega
  have hc : ∀ u, (G₂ u).2.c = (G₁ u).2.c := fun u => by
    by_cases e : u = t
    · subst e; rw [hG₁, hG₂, upd_self, upd_self]; rfl
    · rw [hne u e]
  have hP : ∀ u, (G₂ u).1.ph = (G₁ u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [hG₁, hG₂, upd_self, upd_self]; rfl
    · rw [hne u e]
  refine ⟨⟨hu.um.shape.work (k' := k) (by show (G₁ t).2.ph = _; rw [h₁t]) (by omega)
      (by show (G₂ t).2.ph = _; rw [h₂t]) fun u e => by show (G₂ u).2.ph = _; rw [hne u e],
    hu.um.io, hu.um.rest, hu.um.blk, hu.um.ws, hu.um.we, hu.um.q⟩, hci, hsi,
    hu.lg.relabel hc rfl rfl ?_ ?_ ?_ (fun j hj => hb_same hP (hu.lg.ehb j hj))⟩
  · -- one: the other thread has no permit
    by_cases h0 : t = 0
    · subst h0; exact .inr (by rw [hne 1 (by decide)]; exact held_not hheld 1 (by decide))
    · have h1 : t = 1 := by unfold ThreadId at *; omega
      subst h1; exact .inl (by rw [hne 0 (by decide)]; exact held_not hheld 0 (by decide))
  · -- tot
    intro u k' s h
    rw [hsum]
    by_cases e : u = t
    · subst e; rw [h₂t] at h; cases h; rw [hX₁]
    · rw [hne u e] at h; exact hu.lg.tot u k' s h
  · intro u h
    by_cases e : u = t
    · subst e; rw [h₂s] at h; cases h
    · rw [hne u e] at h ⊢; exact hu.lg.wtx u h

/-- At most two threads are registered: the waiters' room (`SemImpl.wait_wp`'s `hroom`). -/
theorem nreg_lt {G : ThreadId → Gh} {rX : Res} {m : Mem} (hI : C.Inv L G m) (hu : UM G rX m)
    {n : Nat} (hn : ∀ u, n ≤ u → C.ph (G u) = .out) : C.nreg G n < 65535 := by
  have h2 : ∀ u, 2 ≤ u → C.ph (G u) = .out := fun u hu' => Classical.byContradiction fun hne => by
    have := hI.ex u hne
    obtain ⟨-, ⟨hs, -⟩ | ⟨hs, -⟩⟩ := hu.shape <;> (unfold ThreadId at *; omega)
  rw [← FCond.nreg_ext hn (Nat.le_max_left n 2), FCond.nreg_ext h2 (Nat.le_max_right n 2)]
  have : C.nreg G 2 ≤ tsum 2 (fun _ => 1) := tsum_le fun u _ => by
    show (if _ then 1 else 0) ≤ 1
    split <;> omega
  have e : tsum 2 (fun _ => 1) = 2 := rfl
  omega

/-- **No deadlock at the condition** (`SemImpl.wait_wp`'s `hlive`): at count 0 the permit's holder
runs. -/
theorem live_of {G : ThreadId → Gh} {m : Mem} {t : ThreadId} (hi : (proto semOf).inv G m)
    (hcnt : S.cnt G = 0) : (proto semOf).Live t G m := by
  intro _ hall
  obtain ⟨rX, hL, hu⟩ := id hi
  have hh : held (xs G) = true := pv_zero hcnt
  -- the holder
  obtain ⟨v, hv⟩ : ∃ v, (G v).2.ph.holds = true := by
    unfold held xs at hh
    cases e : (G 0).2.ph.holds
    · rw [e] at hh; exact ⟨1, by simpa using hh⟩
    · exact ⟨0, e⟩
  obtain ⟨k, s, hks⟩ : ∃ k s, (G v).2.ph = .work k true s := by
    cases e : (G v).2.ph with
    | work k b s => rw [e] at hv; cases hv; exact ⟨k, s, rfl⟩
    | _ => rw [e] at hv; cases hv
  obtain ⟨hv2, hsz⟩ := hu.um.shape.lt hks
  rcases hall v (by rw [hsz]; exact hv2) with h | h | h
  · have : (G v).2.ph = .fin := by rw [h.2.1]
    rw [hks] at this; cases this
  · obtain ⟨w, hw, he⟩ := Array.any_eq_true'.mp h
    have e : w.1 = v := by simpa using he
    rcases hu.um.q w hw with hq | hq
    · exact ((fits (semOf := semOf)).noWaits hL hu hall)
        (Array.any_eq_true'.mpr ⟨w, hw, by simp [hq]⟩)
    · obtain ⟨i, jr, e', h1, -⟩ := hu.cinv.q w hw hq
      have hw1 : ((G v).2.c).waits = true := by
        rw [← e]; show (C.ph (G w.1)).waits = true; rw [h1]; rfl
      obtain ⟨k', s', -, hx⟩ := hu.lg.wtx v (hu.sinv.wt v hw1)
      rw [hks] at hx; cases hx
  · have : (G v).2.ph = .joins := by rw [h.2]
    rw [hks] at this; cases this

/-- **`wait` of a thread in `semWork`** (`SemImpl.wait_wp` with this protocol's premises): it takes
the permit with `n` at the increments of both threads. -/
theorem wp_wait (I : SemImpl Tgt) (hLc : L.c = I.c) {p : Ptr} (hp : p = S.p) (t : ThreadId)
    {k : Nat} (hk : k < 2) {rp : Res} (hpl : rp.Plain) (io : Io) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (hi : (proto semOf).inv (upd G t (gW rp k false 0)) m) (hc : m.current = t) :
    (proto semOf).WP t (I.wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ ∃ Y r,
      Tn Y r ∧ FHeap.Disjoint rp.heap r.heap ∧
      (proto semOf).inv (upd G' t (gW (rsum rp r) k true (sum Y))) m') G m d := by
  have ht2 : t < 2 := by
    obtain ⟨rX, -, hu⟩ := id hi
    exact (hu.um.shape.lt (u := t) (k := k) (b := false) (s := 0) (by
      show (upd G t (gW rp k false 0) t).2.ph = _; rw [upd_self]; rfl)).1
  refine I.wait_wp fits rfl hLc hp t (gW rp k false 0) (fun Y => gW rp k true (sum Y)) Tn rfl rfl
    rfl ⟨k, 0, hk, rfl⟩ ⟨rfl, .inl rfl⟩ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => ⟨rfl, .inl rfl⟩) (fun G rL m _ hne => ?_) (fun G rL m _ hne r hr => ?_)
    (fun G rX m h₁ h₂ r sh sc hne _ _ hu hL hsi hci => U_take hk hne hu hci hsi)
    (fun G₁ rL m₁ hi₁ _ n hn => ?_) (fun _ _ _ _ hi₁ _ _ hcnt => live_of hi₁ hcnt)
    io G m d hpl hi hc
  · -- the count: 1 before the take, 0 after it
    have h1 : held (xs (upd G t (gW rp k false 0))) = false := pv_ne hne
    have h2 : held (xs (upd G t (gW rp k true (sum (S.xs (upd G t (gW rp k false 0))))))) = true :=
      held_of ht2 (by show ((upd G t (gW rp k true _) t).2.ph).holds = true; rw [upd_self]; rfl)
    show pv (xs _) = pv (xs _) - 1
    unfold pv; rw [h1, h2]; decide
  · -- the pool: `n` before the take, nothing after it
    have h1 : held (xs (upd G t (gW rp k false 0))) = false := pv_ne hne
    have h2 : held (xs (upd G t (gW rp k true (sum (S.xs (upd G t (gW rp k false 0))))))) = true :=
      held_of ht2 (by show ((upd G t (gW rp k true _) t).2.ph).holds = true; rw [upd_self]; rfl)
    have hp : Pool (xs (upd G t (gW rp k true (sum (S.xs (upd G t (gW rp k false 0))))))) = emp := by
      unfold Pool; rw [h2]; simp only [↓reduceIte]
    have hr' : Tn (xs (upd G t (gW rp k false 0))) r := by
      have : Pool (xs (upd G t (gW rp k false 0))) r := hr
      unfold Pool at this; rw [h1] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this; exact this
    show (Pool (xs _) ⋆ Tn (xs _)) r
    rw [hp]
    exact Full.sep_comm (Full.sep_emp.mpr hr')
  · obtain ⟨rX, -, hu⟩ := hi₁
    have hc : ∀ u, C.ph (upd G₁ t (L.set (S.set (gW rp k false 0) .wt) .holds rL) u) =
        C.ph (upd G₁ t (gW rp k false 0) u) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, upd_self]; rfl
      · rw [upd_ne _ _ e, upd_ne _ _ e]
    rw [← FCond.nreg_congr (C := C) hc]
    exact nreg_lt hu.cinv hu.um fun u hu' => (hc u).trans (hn u hu')

/-! ## The give of a permit -/

/-- The permit's holder `t`: the other thread has none. -/
theorem other_free {G : ThreadId → Gh} {m : Mem} {t : ThreadId} (hl : Lg G m) (ht2 : t < 2)
    (hh : (G t).2.ph.holds = true) (u : ThreadId) (hu : u < 2) (e : u ≠ t) :
    (G u).2.ph.holds = false := by
  rcases hl.one with h | h
  · by_cases h0 : t = 0
    · subst h0; exact absurd hh (by rw [h]; decide)
    · have : u = 0 := by unfold ThreadId at *; omega
      subst this; exact h
  · by_cases h1 : t = 1
    · subst h1; exact absurd hh (by rw [h]; decide)
    · have : u = 1 := by unfold ThreadId at *; omega
      subst this; exact h

/-- **The rest after the give** (`SemImpl.post_wp`'s `hU`): the giver `t` has no permit, one
increment further. -/
theorem U_give {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {rp rT h₁ h₂ : Res}
    {k s : Nat} {sh : Array Word.Entry} {sc : VClock} (hk : k < 2)
    (hu : U (upd G t (S.set (L.set (gW (rsum rp rT) k true s) .holds h₁) (.pst sh sc))) rX m)
    (hci : C.Inv L (upd G t (S.set (L.set (gW rp (k + 1) false 0) .holds h₂) (.pst sh sc))) m)
    (hsi : S.Inv (upd G t (S.set (L.set (gW rp (k + 1) false 0) .holds h₂) (.pst sh sc))) m) :
    U (upd G t (S.set (L.set (gW rp (k + 1) false 0) .holds h₂) (.pst sh sc))) rX m := by
  obtain ⟨G₁, hG₁⟩ : ∃ G₁, G₁ = upd G t (S.set (L.set (gW (rsum rp rT) k true s) .holds h₁)
      (.pst sh sc)) := ⟨_, rfl⟩
  obtain ⟨G₂, hG₂⟩ : ∃ G₂, G₂ = upd G t (S.set (L.set (gW rp (k + 1) false 0) .holds h₂)
      (.pst sh sc)) := ⟨_, rfl⟩
  rw [← hG₁] at hu; rw [← hG₂] at hci hsi ⊢
  have hne : ∀ u, u ≠ t → G₂ u = G₁ u := fun u e => by rw [hG₂, hG₁, upd_ne _ _ e, upd_ne _ _ e]
  have h₁t : (G₁ t).2.ph = .work k true s := by rw [hG₁, upd_self]; rfl
  have h₂t : (G₂ t).2.ph = .work (k + 1) false 0 := by rw [hG₂, upd_self]; rfl
  have h₂s : (G₂ t).2.sp = .pst sh sc := by rw [hG₂, upd_self]; rfl
  have ht2 : t < 2 := (hu.um.shape.lt (u := t) (by show (G₁ t).2.ph = _; rw [h₁t])).1
  have hc : ∀ u, (G₂ u).2.c = (G₁ u).2.c := fun u => by
    by_cases e : u = t
    · subst e; rw [hG₁, hG₂, upd_self, upd_self]; rfl
    · rw [hne u e]
  have hP : ∀ u, (G₂ u).1.ph = (G₁ u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [hG₁, hG₂, upd_self, upd_self]; rfl
    · rw [hne u e]
  refine ⟨⟨hu.um.shape.work (k' := k + 1) (by show (G₁ t).2.ph = _; rw [h₁t]) (by omega)
      (by show (G₂ t).2.ph = _; rw [h₂t]) fun u e => by show (G₂ u).2.ph = _; rw [hne u e],
    hu.um.io, hu.um.rest, hu.um.blk, hu.um.ws, hu.um.we, hu.um.q⟩, hci, hsi,
    hu.lg.relabel hc rfl rfl ?_ ?_ ?_ (fun j hj => hb_same hP (hu.lg.ehb j hj))⟩
  · -- one: the giver has no permit
    have hf : (G₂ t).2.ph.holds = false := by rw [h₂t]; rfl
    by_cases h0 : t = 0
    · subst h0; exact .inl hf
    · have h1 : t = 1 := by unfold ThreadId at *; omega
      subst h1; exact .inr hf
  · -- tot: no other thread has the permit
    intro u k' s' h
    by_cases e : u = t
    · subst e; rw [h₂t] at h; cases h
    · rw [hne u e] at h
      have hu2 := (hu.um.shape.lt (u := u) h).1
      have := other_free hu.lg ht2 (by rw [h₁t]; rfl) u hu2 e
      rw [h] at this; cases this
  · intro u h
    by_cases e : u = t
    · subst e; rw [h₂s] at h; cases h
    · rw [hne u e] at h ⊢; exact hu.lg.wtx u h

/-- **`post` of the permit's holder in `semWork`** (`SemImpl.post_wp` with this protocol's
premises): it gives `n`, one increment further (`rT`), back to the free permit. -/
theorem wp_post (I : SemImpl Tgt) (hLc : L.c = I.c) {p : Ptr} (hp : p = S.p) (t : ThreadId)
    {k s : Nat} (hk : k < 2) {rp rT : Res} (hpl : rp.Plain)
    (hdj : FHeap.Disjoint rp.heap rT.heap) (hrT : up (pts nPtr 4 (BitVec.ofNat 32 (s + 1))) rT)
    (io : Io) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : (proto semOf).inv (upd G t (gW (rsum rp rT) k true s)) m) (hc : m.current = t) :
    (proto semOf).WP t (I.post p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      (proto semOf).inv (upd G' t (gW rp (k + 1) false 0)) m') G m d := by
  have ht2 : t < 2 := by
    obtain ⟨rX, -, hu⟩ := id hi
    exact (hu.um.shape.lt (u := t) (k := k) (b := true) (s := s) (by
      show (upd G t (gW (rsum rp rT) k true s) t).2.ph = _; rw [upd_self]; rfl)).1
  -- at the holder's states: the other thread has no permit, and `s` is the increments
  have facts : ∀ G rL m, (proto semOf).inv (upd G t (L.set (gW (rsum rp rT) k true s) .holds rL)) m →
      held (xs (upd G t (gW rp (k + 1) false 0))) = false ∧
      s = sum (xs (upd G t (gW (rsum rp rT) k true s))) := fun G rL m hi' => by
    obtain ⟨rX, -, hu⟩ := hi'
    have ht' : (upd G t (L.set (gW (rsum rp rT) k true s) .holds rL) t).2.ph = .work k true s := by
      rw [upd_self]; rfl
    refine ⟨?_, ?_⟩
    · unfold held xs
      have hf : ∀ u, u < 2 → (upd G t (gW rp (k + 1) false 0) u).2.ph.holds = false := fun u hu' => by
        by_cases e : u = t
        · subst e; rw [upd_self]; rfl
        · have := other_free hu.lg ht2 (by rw [ht']; rfl) u hu' e
          rw [upd_ne _ _ e] at this ⊢; exact this
      rw [hf 0 (by decide), hf 1 (by decide)]; rfl
    · have := hu.lg.tot t k s ht'
      rwa [xs_upd_ph (G := G) (t := t) (g := L.set (gW (rsum rp rT) k true s) .holds rL)
        (g' := gW (rsum rp rT) k true s) rfl] at this
  have hhold : ∀ G : ThreadId → Gh, held (xs (upd G t (gW (rsum rp rT) k true s))) = true := by
    intro G
    refine held_of ht2 ?_
    show ((upd G t (gW (rsum rp rT) k true s) t).2.ph).holds = true
    rw [upd_self]; rfl
  refine I.post_wp fits rfl hLc hp t (gW (rsum rp rT) k true s) (gW rp (k + 1) false 0) rT rfl rfl
    rfl ⟨rfl, .inl rfl⟩ rfl rfl rfl rfl ⟨rfl, .inl rfl⟩ rfl hdj (fun G rL m hi' => ?_)
    (fun G rL m hi' r hr => ?_) (fun G rX m h₁ h₂ sh sc hu _ hsi hci => U_give hk hu hci hsi)
    io G m d hpl.2 hi hc
  · obtain ⟨hf, -⟩ := facts G rL m hi'
    show pv (xs _) = pv (xs _) + 1 ∧ (pv (xs _)).toNat + 1 < 2 ^ 64
    unfold pv; rw [hf, hhold G]; decide
  · obtain ⟨hf, hs⟩ := facts G rL m hi'
    have hp0 : Pool (xs (upd G t (gW (rsum rp rT) k true s))) = emp := by
      unfold Pool; rw [hhold G]; simp only [↓reduceIte]
    have hr' : r = rT := by
      have : ((fun r => r = rT) ⋆ Pool (xs (upd G t (gW (rsum rp rT) k true s)))) r := hr
      rw [hp0] at this; exact (Full.sep_emp (P := fun r => r = rT) (r := r)).mp this
    subst hr'
    show Pool (xs _) r
    unfold Pool; rw [hf]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hsum : sum (xs (upd G t (gW rp (k + 1) false 0))) = s + 1 := by
      rw [hs]
      refine sum_upd ht2 (fun u e => ?_) ?_
      · show (upd G t _ u).2.ph = (upd G t _ u).2.ph
        rw [upd_ne _ _ e, upd_ne _ _ e]
      · show (upd G t _ t).2.ph.count = (upd G t _ t).2.ph.count + 1
        rw [upd_self, upd_self]; rfl
    rw [hsum]; exact hrT

/-! ## The increment of `n` -/

/-- Both threads did at most two increments each. -/
theorem Shape.sum_le {Y : ThreadId → Ph} {m : Mem} (h : Shape Y m) : sum Y ≤ 4 := by
  have hw : ∀ p : Ph, (∃ k ≤ 2, ∃ b s, p = .work k b s) → p.count ≤ 2 := by
    rintro p ⟨k, hk, b, s, rfl⟩; exact hk
  obtain ⟨-, ⟨-, hy0, hyu⟩ | ⟨-, -, hm, hk, -⟩⟩ := h
  · unfold sum; rw [hy0, hyu 1 (by decide)]; decide
  · unfold sum
    have h0 : (Y 0).count ≤ 2 := by
      rcases hm with e | e
      · rw [e]; decide
      · exact hw _ e
    have h1 : (Y 1).count ≤ 2 := by
      rcases hk with e | e
      · rw [e]; decide
      · exact hw _ e
    omega

/-- The permit's holder recorded at most 4 increments (`tot`, `Shape.sum_le`): the bound of the
increment of `n`. -/
theorem hold_le {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {r : Res} {k s : Nat}
    (hi : (proto semOf).inv (upd G t (gW r k true s)) m) : s ≤ 4 := by
  obtain ⟨rX, -, hu⟩ := hi
  rw [hu.lg.tot t k s (by rw [upd_self]; rfl)]
  exact hu.um.shape.sum_le

/-- **A step of the permit's holder on its own part** (`FCond.wp_liftPart`): its part after the
step is the step's post. -/
theorem wp_own {α : Type} {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → Gh) → Mem → Nat → Prop} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {t : ThreadId} {r : Res} {k s : Nat}
    (hi : (proto semOf).inv (upd G t (gW r k true s)) m) (hc : m.current = t)
    (htt : FTTriple Pa x Qa) (hp : Pa r)
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      (proto semOf).inv (upd G t (gW r' k true s)) m' → Q a G m' d) :
    (proto semOf).WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d :=
  FCond.wp_liftPart (fits (semOf := semOf)).toC.toFits (.inl rfl) hi hc htt hp
    (fun a m' r' hx hq hc' _ _ hi' => h a m' r' hx hq hc' hi')

/-- **The first step of the permit's holder on its own part** after the take (`wp_wait`'s
post): it owns `n` with the value it recorded, next to its part `rp`. -/
theorem wp_ownN {α : Type} {x : MemM α} {Qa : α → FAssn}
    {Q : α → (ThreadId → Gh) → Mem → Nat → Prop} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {t : ThreadId} {rp r : Res} {k s : Nat}
    (hi : (proto semOf).inv (upd G t (gW (rsum rp r) k true s)) m) (hc : m.current = t)
    (hr : up (pts nPtr 4 (BitVec.ofNat 32 s)) r) (hdj : FHeap.Disjoint rp.heap r.heap)
    (htt : FTTriple ((fun x => x = rp) ⋆ up (pts nPtr 4 (BitVec.ofNat 32 s))) x Qa)
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      (proto semOf).inv (upd G t (gW r' k true s)) m' → Q a G m' d) :
    (proto semOf).WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d :=
  wp_own hi hc htt ⟨rp, r, hdj, rfl, rfl, hr⟩ h

/-- **`post` after the increment** (`wp_post`): the holder's part is `rp` and `n`, one increment
further. -/
theorem wp_postN (I : SemImpl Tgt) (hLc : L.c = I.c) {p : Ptr} (hp : p = S.p) (t : ThreadId)
    {k s : Nat} (hk : k < 2) {rp r' : Res} (hpl : rp.Plain)
    (hr' : ((fun x => x = rp) ⋆ up (pts nPtr 4 (BitVec.ofNat 32 (s + 1)))) r')
    (io : Io) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : (proto semOf).inv (upd G t (gW r' k true s)) m) (hc : m.current = t) :
    (proto semOf).WP t (I.post p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      (proto semOf).inv (upd G' t (gW rp (k + 1) false 0)) m') G m d := by
  obtain ⟨_, rT, hdj, rfl, rfl, hrT⟩ := hr'
  exact wp_post I hLc hp t hk hpl hdj hrT io G m d hi hc

end SemCounter
end Zig
