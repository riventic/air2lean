import ZigLean.Sep.Full.ThreadStep
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AutoAttr

/-!
# Step ticks (`docs/sep-full-state.md` §Step ticks)

`Zig.tick` counts one step (`Mem.ticks`): the translator is to put it at the start of every loop
body and at the entry of every function of a recursive call group (not emitted yet). The memory
meters the credits (`TickAuth`, `ZigLean/Sep/Full/MemAuth.lean`): with a credit authority `●L` in
a frame, the credits held plus the steps run are at most `L`. So a step needs a credit or the
plain mode:

* `FTotalTriple.tick_credit`: `credits 1` becomes a receipt `spent 1`;
* `FTotalTriple.tick_unmetered`: `unmetered` (no meter runs) stays, with a receipt;
* `FTotalTriple.tick_plain`: the same for the plain mode `plain` (no meter, no stack budget).

A step without either is not provable: `tests/roadmap/sep-full/TicksCX.lean` (`tick_without_credit`).
The thread rules are `FTTotalTriple.tick_*` (`ThreadLocal.tick`). Receipts and credits that a
postcondition does not use are dropped (`@[fsym_drop]`); the plain mode is duplicable
(`EUpd.plain_dup`).

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

open FAssn

/-! ## The memory side -/

/-- The memory after one step. -/
abbrev _root_.Zig.Mem.ticked (m : Mem) : Mem := { m with ticks := m.ticks + 1 }

theorem tick_run' (m : Mem) : Zig.tick.run m = pure ((), m.ticked) := tick_run m

theorem _root_.Zig.Mem.FSeq.ticked {m : Mem} (hs : m.FSeq) : m.ticked.FSeq :=
  ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩

/-- **A change of the counter cell at one step**: the ledgers, extents and byte claims stay, and
the new cell is valid and authorized in the memory after the step. -/
theorem GOk.ticked {m : Mem} {g gF g' : Ghost} (h : GOk m g gF) (hl : g'.led = g.led)
    (hx : g'.extent = g.extent) (hc : g'.cl = g.cl) (hv : (g'.add gF).ac.Valid)
    (hM : MemAuth m.ticked (g'.add gF).ac) : GOk m.ticked g' gF := by
  obtain ⟨⟨hV, hF⟩, ht, hcf, -⟩ := h
  replace ht := ht.keep (m' := m.ticked) (KeepsExt.of_blocks rfl)
  replace hcf := hcf.mono (m' := m.ticked) (Nat.le_refl _)
  have el : (g'.add gF).led = (g.add gF).led := by simp only [Ghost.add, hl]
  have ex : (g'.add gF).extent = (g.add gF).extent := by simp only [Ghost.add, hx]
  have ec : (g'.add gF).cl = (g.add gF).cl := by simp only [Ghost.add, hc]
  unfold GOk Ghost.Ok
  generalize g.add gF = G at hV hF ht hcf el ex ec
  generalize g'.add gF = G' at el ex ec hv hM ⊢
  obtain ⟨l, x, c, ac⟩ := G'
  subst el ex ec
  exact ⟨⟨⟨hV.1, hV.2.1, hV.2.2.1, hv⟩, hF⟩, ht, hcf, hM⟩

/-- The ghost state with one receipt. -/
abbrev Ghost.spent1 : Ghost := Ghost.ofAC (ACell.fragAt .spent 1)

/-- `StackAuth` does not read the step count. -/
theorem StackAuth.ticked {m : Mem} {c : KCell} (h : StackAuth m c) : StackAuth m.ticked c :=
  h.keep_shape rfl rfl rfl fun _ blk' hb' => ⟨blk', hb', rfl, rfl, rfl, rfl⟩

/-- **One step in the plain mode**: a resource with `unmetered` takes a receipt. -/
theorem Holds.tick_unmetered {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hu : 0 < r.gh.ac.frag .unmetered) :
    Holds m.ticked ⟨r.heap, r.know, r.gh.add Ghost.spent1⟩ rF := by
  obtain ⟨hd, hm, hk, hkF, hg⟩ := hh
  have hM := hg.2.2.2
  have hV : (r.gh.add rF.gh).ac.Valid := hg.1.1.2.2.2
  have hu' : 0 < (r.gh.add rF.gh).ac.frag .unmetered := by simp only [Ghost.add_ac, ACell.add_frag]; omega
  have hna := hM.tick.plain hu'
  have ho := hM.onlyCred
  generalize hcg : (r.gh.add rF.gh).ac = c at hM hV hu' hna ho
  have e : ((r.gh.add Ghost.spent1).add rF.gh).ac = (ACell.fragAt .spent 1).add c := by
    rw [← hcg]; ext <;> simp <;> omega
  refine ⟨hd, hm, hk, hkF, hg.ticked ?_ ?_ ?_ ?_ ?_⟩
  · funext γ; simp [Ghost.add, Ghost.ofAC, Ghost.unit]
  · funext b; simp [Ghost.add, Ghost.ofAC, Ghost.unit]
  · funext b x; simp [Ghost.add, Ghost.ofAC, Ghost.unit]
  · rw [e]; intro k
    by_cases hk : k = .spent
    · subst hk
      obtain ⟨h1, h2, -, h4, h5⟩ := hV .spent
      exact ⟨by simpa using h1, by simpa using h2, fun n hn => by simp [ho .spent n (by decide)] at hn,
        by simpa using h4, by simpa using h5⟩
    · exact (hV k).congr (by simp [hk]) (by simp) (by simp)
  · rw [e]
    obtain ⟨hs, ⟨-, t2, t3⟩, hn, -⟩ := hM
    refine ⟨(hs.congr (fun k v => by simp)).ticked, ⟨fun L hL => ?_, ?_, fun hp L => ?_⟩,
      fun hp => hn (by simpa using hp), fun k L hk => by simpa using ho k L hk⟩
    · simp [hna L] at hL
    · simp; omega
    · simpa using hna L

/-- **One step paid by a credit**: a resource with `credits 1` gives it for a receipt. -/
theorem Holds.tick_credit {m : Mem} {r₀ rF : Res} (hh : Holds m ⟨r₀.heap, r₀.know, r₀.gh.add (Ghost.cred 1)⟩ rF) :
    Holds m.ticked ⟨r₀.heap, r₀.know, r₀.gh.add Ghost.spent1⟩ rF := by
  obtain ⟨hd, hm, hk, hkF, hg⟩ := hh
  have hM := hg.2.2.2
  have hV := hg.1.1.2.2.2
  have ho := hM.onlyCred
  generalize hcg : (r₀.gh.add rF.gh).ac = c
  have e0 : ((⟨r₀.heap, r₀.know, r₀.gh.add (Ghost.cred 1)⟩ : Res).gh.add rF.gh).ac =
      (ACell.fragAt .cred 1).add c := by
    rw [← hcg]; simp only [Ghost.add_ac, Ghost.cred, Ghost.ofAC_ac]; ext <;> simp <;> omega
  have e : ((r₀.gh.add Ghost.spent1).add rF.gh).ac = (ACell.fragAt .spent 1).add c := by
    rw [← hcg]; ext <;> simp <;> omega
  rw [e0] at hM hV ho
  refine ⟨hd, hm, hk, hkF, hg.ticked ?_ ?_ ?_ ?_ ?_⟩
  · funext γ; simp [Ghost.add, Ghost.ofAC, Ghost.cred, Ghost.unit]
  · funext b; simp [Ghost.add, Ghost.ofAC, Ghost.cred, Ghost.unit]
  · funext b x; simp [Ghost.add, Ghost.ofAC, Ghost.cred, Ghost.unit]
  · rw [e]; intro k
    by_cases hks : k = .spent
    · subst hks
      obtain ⟨h1, h2, -, h4, h5⟩ := hV .spent
      exact ⟨by simpa using h1, by simpa using h2,
        fun n hn => by simp [show c.auth .spent n = 0 by simpa using ho .spent n (by decide)] at hn,
        by simpa using h4, by simpa using h5⟩
    · by_cases hkc : k = .cred
      · subst hkc
        obtain ⟨h1, h2, h3, h4, h5⟩ := hV .cred
        exact ⟨by simpa using h1, by simpa using h2,
          fun n hn => by have := h3 n (by simpa using hn); simp at this ⊢; omega,
          by simpa using h4, by simpa using h5⟩
      · exact (hV k).congr (by simp [hks, hkc]) (by simp) (by simp)
  · rw [e]
    obtain ⟨hs, ⟨t1, t2, t3⟩, hn, -⟩ := hM
    refine ⟨(hs.congr (fun k v => by simp)).ticked, ⟨fun L hL => ?_, ?_, fun hp L => ?_⟩,
      fun hp => hn (by simpa using hp), fun k L hk => ?_⟩
    · have := t1 L (by simpa using hL); simp at this ⊢; omega
    · have := t2; simp at this ⊢; omega
    · simpa using t3 (by simpa using hp) L
    · have := ho k L hk; simp at this ⊢; omega

/-! ## Assertions -/

attribute [fsym_atom] plain

@[simp] theorem Ghost.spent1_ac : Ghost.spent1.ac = ACell.fragAt .spent 1 := rfl

/-- Receipts split and join. -/
theorem spent_add (a b : Nat) : spent (a + b) = (spent a ⋆ spent b) := by
  funext r; apply propext; constructor
  · rintro ⟨h, k, g⟩
    exact ⟨⟨FHeap.empty, Know.none, Ghost.ofAC (ACell.fragAt .spent a)⟩,
      ⟨FHeap.empty, Know.none, Ghost.ofAC (ACell.fragAt .spent b)⟩, FHeap.disjoint_empty _,
      by rw [res_eta r, h, k, g, Ghost.ofAC_add, ACell.fragAt_add]; simp [Know.union_none],
      ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  · rintro ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩
    exact ⟨by simp [h1, h2], by simp [k1, k2, Know.union_none],
      by simp [g1, g2, Ghost.ofAC_add, ACell.fragAt_add]⟩

theorem spent_zero : spent 0 = emp := by funext r; simp [spent, emp]

/-- **Receipts and credits that are not used are dropped.** -/
@[fsym_drop] theorem EUpd.spent_drop {n : Nat} {R : FAssn} : EUpd (spent n ⋆ R) R :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm h)
    (EUpd.drop fun _ h => ⟨h.1, h.2.1, by rw [h.2.2]; exact fun _ _ => rfl⟩)

@[fsym_drop] theorem EUpd.credits_drop {n : Nat} {R : FAssn} : EUpd (credits n ⋆ R) R :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm h)
    (EUpd.drop fun _ h => ⟨h.1, h.2.1, by rw [h.2.2]; exact fun _ _ => rfl⟩)

/-- **The plain mode is duplicable**: a copy next to the one held (`Holds.dupPlain`). -/
theorem EUpd.plain_dup : EUpd plain (plain ⋆ plain) := fun m r rF hh hp _ => by
  have hs := hh.swap
  have hns := hh.noStack (plain_noStack (sep_emp.mpr hp))
  have hu : 0 < r.gh.ac.frag .unmetered := by
    obtain ⟨r₁, r₂, -, rfl, ⟨-, -, g1⟩, ⟨-, -, g2⟩⟩ := hp
    simp [g1, g2, Ghost.ofAC]
  have hna : ∀ L, (r.gh.add rF.gh).ac.auth .cred L = 0 :=
    hh.ghost.2.2.2.tick.plain (by simp only [Ghost.add_ac, ACell.add_frag]; omega)
  exact ⟨_, hh.addPlain hns hna, by
    have := sep_plain_intro hp
    simpa using this⟩

/-! ## Step rules -/

/-- **A step in the plain mode without a meter** (`unmetered`). -/
theorem FTotalTriple.tick_unmetered : FTotalTriple unmetered Zig.tick (fun _ => unmetered ⋆ spent 1) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    obtain ⟨h0, k0, g0⟩ := hp
    refine ⟨(), m.ticked, ⟨r.heap, r.know, r.gh.add Ghost.spent1⟩, tick_run' m,
      hh.tick_unmetered (by simp [g0, Ghost.ofAC]),
      ⟨r, ⟨FHeap.empty, Know.none, Ghost.spent1⟩, fun _ => .inr rfl, by simp [FHeap.union_empty,
        Know.union_none], ⟨h0, k0, g0⟩, rfl, rfl, rfl⟩, hs.ticked⟩

/-- **A step paid by a credit.** -/
theorem FTotalTriple.tick_credit : FTotalTriple (credits 1) Zig.tick (fun _ => spent 1) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    obtain ⟨h0, k0, g0⟩ := hp
    have hh' : Holds m ⟨(⟨FHeap.empty, Know.none, Ghost.unit⟩ : Res).heap,
        (⟨FHeap.empty, Know.none, Ghost.unit⟩ : Res).know,
        (⟨FHeap.empty, Know.none, Ghost.unit⟩ : Res).gh.add (Ghost.cred 1)⟩ rF := by
      rw [res_eta r, h0, k0, g0] at hh; simpa using hh
    exact ⟨(), m.ticked, _, tick_run' m, hh'.tick_credit, ⟨rfl, rfl, by simp⟩, hs.ticked⟩

/-- **A step in the plain mode** (`plain`: no meter runs). -/
theorem FTotalTriple.tick_plain : FTotalTriple plain Zig.tick (fun _ => plain ⋆ spent 1) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    have hu : 0 < r.gh.ac.frag .unmetered := by
      obtain ⟨r₁, r₂, -, rfl, ⟨-, -, g1⟩, ⟨-, -, g2⟩⟩ := hp
      simp [g1, g2, Ghost.ofAC]
    refine ⟨(), m.ticked, ⟨r.heap, r.know, r.gh.add Ghost.spent1⟩, tick_run' m, hh.tick_unmetered hu,
      ⟨r, ⟨FHeap.empty, Know.none, Ghost.spent1⟩, fun _ => .inr rfl, by simp [FHeap.union_empty,
        Know.union_none], hp, rfl, rfl, rfl⟩, hs.ticked⟩

/-! ## Thread rules -/

/-- **A step is local**: it reads no record and touches no byte. -/
theorem ThreadLocal.tick {P : FAssn} : ThreadLocal P Zig.tick :=
  ThreadLocal.intro fun m _ _ _ _ _ _ => ⟨rfl, fun v m₀ e => by
    rw [tick_run'] at e
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
    exact ⟨.of_stepIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
      Nat.le_refl _, fun _ he => .inl he, fun _ he => .inl he⟩ (fun _ _ h => h) (fun _ he hn => absurd he hn),
      fun _ _ _ h => h⟩⟩

@[fsym] theorem FTTotalTriple.tick_unmetered :
    FTTotalTriple unmetered Zig.tick (fun _ => unmetered ⋆ spent 1) :=
  FTTotalTriple.ofSeq FTotalTriple.tick_unmetered ThreadLocal.tick

@[fsym] theorem FTTotalTriple.tick_credit : FTTotalTriple (credits 1) Zig.tick (fun _ => spent 1) :=
  FTTotalTriple.ofSeq FTotalTriple.tick_credit ThreadLocal.tick

@[fsym] theorem FTTotalTriple.tick_plain : FTTotalTriple plain Zig.tick (fun _ => plain ⋆ spent 1) :=
  FTTotalTriple.ofSeq FTotalTriple.tick_plain ThreadLocal.tick

attribute [fsym] FTotalTriple.tick_plain FTotalTriple.tick_unmetered FTotalTriple.tick_credit

end Full
end Zig
