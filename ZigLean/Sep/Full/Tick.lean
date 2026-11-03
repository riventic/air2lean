import ZigLean.Sep.Full.ThreadStep
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.Loop
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
In a thread, `fsym` derives the thread rules from these (`FTTotalTriple.ofSeq`) with the locality
provider `ThreadLocal.tick` (`@[fsym_provider]`, `Full/AutoThread.lean`). Receipts and credits that a
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
    obtain ⟨hs, ⟨-, t2, t3⟩, hn, -, hcur⟩ := hM
    refine ⟨(hs.congr (fun k v => by simp)).ticked, ⟨fun L hL => ?_, ?_, fun hp L => ?_⟩,
      fun hp => hn (by simpa using hp), fun k L hk => by simpa using ho k L hk,
      fun v hv => hcur v (by simpa using hv)⟩
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
    obtain ⟨hs, ⟨t1, t2, t3⟩, hn, -, hcur⟩ := hM
    refine ⟨(hs.congr (fun k v => by simp)).ticked, ⟨fun L hL => ?_, ?_, fun hp L => ?_⟩,
      fun hp => hn (by simpa using hp), fun k L hk => ?_, fun v hv => hcur v (by simpa using hv)⟩
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

/-- **The plain mode splits off a resource that holds its fragments** (`Res.Plain`,
`Holds.splitPlain`): a precondition whose resources hold the plain mode (an exact thread part, a
protocol's part) shows `plain` next to it, e.g. for a stack block (`FTriple.allocStackDrop`). -/
theorem EUpd.plain_split {P : FAssn} (hP : ∀ r, P r → r.Plain) : EUpd P (P ⋆ plain) :=
  fun _ r _ hh hp _ => ⟨_, hh.splitPlain (hP r hp), sep_plain_intro hp⟩

/-- **The plain mode is duplicable**: a copy next to the one held (`Holds.dupPlain`). -/
theorem EUpd.plain_dup : EUpd plain (plain ⋆ plain) :=
  EUpd.plain_split fun _ => Res.plain_of

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
  (FLogic.frameL (L := FLogic.total) (R := noStack) FTotalTriple.tick_unmetered).post
    fun _ _ h => sep_assoc' h

/-! ## Credits under the plain mode

Where `unmetered` is held no meter runs (`TickAuth.plain`), so credits bound nothing there and
any number of them can be added. A proof that pays its steps with credits (a cost bound) therefore
gives the plain-mode statement of the same program without a second proof. -/

/-- **Credits next to the plain mode**: a memory whose resources hold `unmetered` holds them with
`n` more credits. -/
theorem Holds.mintCredits {m : Mem} {r rF : Res} (n : Nat) (hh : Holds m r rF)
    (hu : 0 < (r.gh.add rF.gh).ac.frag .unmetered) :
    Holds m ⟨r.heap, r.know, r.gh.add (Ghost.cred n)⟩ rF := by
  obtain ⟨hd, hm, hk, hkF, hg⟩ := hh
  have hM := hg.2.2.2
  have hV : (r.gh.add rF.gh).ac.Valid := hg.1.1.2.2.2
  have ha := hM.tick.plain hu
  have ho := hM.onlyCred
  generalize hcg : (r.gh.add rF.gh).ac = c at hu hM hV ha ho
  have e : ((r.gh.add (Ghost.cred n)).add rF.gh).ac = (ACell.fragAt .cred n).add c := by
    rw [← hcg]; ext <;> simp [Ghost.cred] <;> omega
  refine ⟨hd, hm, hk, hkF, hg.ac_change ?_ ?_ ?_ ?_ ?_⟩
  · funext γ; simp [Ghost.add, Ghost.ofAC, Ghost.cred, Ghost.unit]
  · funext b; simp [Ghost.add, Ghost.ofAC, Ghost.cred, Ghost.unit]
  · funext b x; simp [Ghost.add, Ghost.ofAC, Ghost.cred, Ghost.unit]
  · rw [e]; intro k
    by_cases hkc : k = .cred
    · subst hkc
      obtain ⟨h1, h2, -, h4, h5⟩ := hV .cred
      exact ⟨by simpa using h1, by simpa using h2, fun L hL => by simp [ha L] at hL,
        by simpa using h4, by simpa using h5⟩
    · exact (hV k).congr (by simp [hkc]) (by simp) (by simp)
  · rw [e]
    obtain ⟨hs, ⟨-, t2, -⟩, hn, -, hcur⟩ := hM
    exact ⟨hs.congr fun k v => by simp, ⟨fun L hL => by simp [ha L] at hL, by simpa using t2,
      fun _ L => by simpa using ha L⟩, fun hp => hn (by simpa using hp),
      fun k L hk => by simpa using ho k L hk, fun v hv => hcur v (by simpa using hv)⟩

/-- A resource with `n` credits added. -/
theorem sep_credits_intro {P : FAssn} {r : Res} (hp : P r) (n : Nat) :
    (P ⋆ credits n) ⟨r.heap, r.know, r.gh.add (Ghost.cred n)⟩ :=
  ⟨r, ⟨FHeap.empty, Know.none, Ghost.cred n⟩, fun _ => .inr rfl,
    by simp [FHeap.union_empty, Know.union_none], hp, rfl, rfl, rfl⟩

/-- **Credits are free in the plain mode.** -/
theorem EUpd.credits_mint (n : Nat) : EUpd unmetered (unmetered ⋆ credits n) :=
  fun _ r _ hh hp _ => by
    obtain ⟨h0, k0, g0⟩ := hp
    exact ⟨_, hh.mintCredits n (by simp [g0, Ghost.ofAC]), sep_credits_intro ⟨h0, k0, g0⟩ n⟩

/-- **A cost proof gives the plain-mode proof**: a program proved with `n` credits runs in the
plain mode, with the same postcondition. -/
theorem FTotalTriple.of_credits_unmetered {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    {n : Nat} (h : FTotalTriple (P ⋆ credits n) c Q) :
    FTotalTriple (P ⋆ unmetered) c (fun v => Q v ⋆ unmetered) :=
  FTotalTriple.eupd ((EUpd.credits_mint n).frameL.trans (EUpd.of_imp fun _ h => by
    rwa [show (P ⋆ (unmetered ⋆ credits n)) = ((P ⋆ credits n) ⋆ unmetered) by ac_rfl] at h))
    h.frame

/-- `of_credits_unmetered` in the plain mode. -/
theorem FTotalTriple.of_credits_plain {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    {n : Nat} (h : FTotalTriple (P ⋆ credits n) c Q) :
    FTotalTriple (P ⋆ plain) c (fun v => Q v ⋆ plain) := by
  have h' : FTotalTriple ((P ⋆ noStack) ⋆ credits n) c (fun v => Q v ⋆ noStack) := by
    rw [show ((P ⋆ noStack) ⋆ credits n) = ((P ⋆ credits n) ⋆ noStack) by ac_rfl]
    exact h.frame
  refine (FTotalTriple.of_credits_unmetered h').conseq (fun _ hr => ?_) fun v _ hr => ?_
  · unfold plain at hr
    rwa [show (P ⋆ (noStack ⋆ unmetered)) = ((P ⋆ noStack) ⋆ unmetered) by ac_rfl] at hr
  · unfold plain
    rwa [show (Q v ⋆ (noStack ⋆ unmetered)) = ((Q v ⋆ noStack) ⋆ unmetered) by ac_rfl]

/-! ## Exact step counts

A run proved with `N` credits makes at most `N` steps, and a run that returns `N` receipts makes at
least `N`. So a statement with both counts its steps exactly, and no proof pays the same run with
fewer credits: the bound is tight. The start is a memory whose resources hold no credit, receipt,
meter or plain mode (`CreditFree`); the adequacy steps (`Holds.addCredits`, `Holds.addSpent`) put
the meter and the receipts of the steps run so far in the frame. -/

/-- **The adequacy step of receipts**: a memory whose resources hold no receipt holds them with the
receipts of every step run so far, `spent m.ticks`, in the frame. Only an adequacy theorem uses
it: no judgment can (the frame is fixed). -/
theorem Holds.addSpent {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hs : (r.gh.add rF.gh).ac.frag .spent = 0) :
    Holds m r ⟨rF.heap, rF.know, rF.gh.add (Ghost.ofAC (ACell.fragAt .spent m.ticks))⟩ := by
  obtain ⟨hd, hm, hk, hkF, hg⟩ := hh
  have hM := hg.2.2.2
  have hV : (r.gh.add rF.gh).ac.Valid := hg.1.1.2.2.2
  have ho := hM.onlyCred
  generalize hcg : (r.gh.add rF.gh).ac = c at hs hM hV ho
  have e : (r.gh.add (rF.gh.add (Ghost.ofAC (ACell.fragAt .spent m.ticks)))).ac =
      (ACell.fragAt .spent m.ticks).add c := by
    rw [← hcg]; ext <;> simp <;> omega
  refine ⟨hd, hm, hk, hkF, hg.ac_change ?_ ?_ ?_ ?_ ?_⟩
  · funext γ; simp [Ghost.add, Ghost.ofAC, Ghost.unit]
  · funext b; simp [Ghost.add, Ghost.ofAC, Ghost.unit]
  · funext b x; simp [Ghost.add, Ghost.ofAC, Ghost.unit]
  · rw [e]; intro k
    by_cases hks : k = .spent
    · subst hks
      obtain ⟨h1, h2, -, h4, h5⟩ := hV .spent
      exact ⟨by simpa using h1, by simpa using h2,
        fun n hn => by simp [ho .spent n (by decide)] at hn, by simpa using h4, by simpa using h5⟩
    · exact (hV k).congr (by simp [hks]) (by simp) (by simp)
  · rw [e]
    obtain ⟨hst, ⟨t1, -, t3⟩, hn, -, hcur⟩ := hM
    exact ⟨hst.congr fun k v => by simp, ⟨fun L hL => by simpa using t1 L (by simpa using hL),
      by simp [hs], fun hp L => by simpa using t3 (by simpa using hp) L⟩,
      fun hp => hn (by simpa using hp), fun k L hk => by simpa using ho k L hk,
      fun v hv => hcur v (by simpa using hv)⟩

/-- A credit-free start: the resources and the frame hold no credit, meter, plain mode or receipt. -/
structure CreditFree (r rF : Res) : Prop where
  cred : (r.gh.add rF.gh).ac.frag .cred = 0
  auth : ∀ L, (r.gh.add rF.gh).ac.auth .cred L = 0
  unmetered : (r.gh.add rF.gh).ac.frag .unmetered = 0
  spent : (r.gh.add rF.gh).ac.frag .spent = 0

/-- **At most `N` steps**: from a credit-free start, a run proved with `N` credits raises the step
count by at most `N`. -/
theorem FTotalTriple.ticks_le {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {N : Nat}
    (h : FTotalTriple (P ⋆ credits N) c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r)
    (hs : m.FSeq) (hc : CreditFree r rF) :
    ∃ v m', c.run m = pure (v, m') ∧ m'.ticks ≤ m.ticks + N := by
  obtain ⟨v, m', r', hr, hh', -, -⟩ :=
    h.runs (Holds.addCredits N hh hc.cred hc.auth hc.unmetered) (sep_credits_intro hp N) hs
  refine ⟨v, m', hr, ?_⟩
  have := hh'.ghost.2.2.2.tick.meter (m.ticks + N) (by simp [Ghost.credAuth])
  omega

/-- **At least `N` steps**: from a start without receipts, a run that returns `N` receipts raises
the step count by at least `N`. -/
theorem FTotalTriple.ticks_ge {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {N : Nat}
    (h : FTotalTriple P c (fun v => Q v ⋆ spent N)) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : P r) (hs : m.FSeq) (hsp : (r.gh.add rF.gh).ac.frag .spent = 0) :
    ∃ v m', c.run m = pure (v, m') ∧ m.ticks + N ≤ m'.ticks := by
  obtain ⟨v, m', r', hr, hh', hq, -⟩ := h.runs (hh.addSpent hsp) hp hs
  refine ⟨v, m', hr, ?_⟩
  obtain ⟨r₁, r₂, -, rfl, -, -, -, g₂⟩ := hq
  have := hh'.ghost.2.2.2.tick.spent
  simp [g₂] at this
  omega

/-- **The step count is tight**: a run proved with `N` credits and `N` receipts cannot be paid
with fewer credits, from any credit-free start that holds the precondition. -/
theorem FTotalTriple.not_fewer_credits {α : Type} {P : FAssn} {c : MemM α} {Q Q' : α → FAssn}
    {N M : Nat} (h : FTotalTriple (P ⋆ credits N) c (fun v => Q v ⋆ spent N)) (hM : M < N)
    {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq) (hc : CreditFree r rF) :
    ¬ FTotalTriple (P ⋆ credits M) c Q' := fun h' => by
  obtain ⟨v₁, m₁, hr₁, hle⟩ := h'.ticks_le hh hp hs hc
  obtain ⟨v₂, m₂, hr₂, hge⟩ := h.ticks_ge (Holds.addCredits N hh hc.cred hc.auth hc.unmetered)
    (sep_credits_intro hp N) hs (by simpa [Ghost.cred, Ghost.credAuth] using hc.spent)
  rw [hr₁] at hr₂
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj hr₂)
  omega

/-! ## Loops that count their body runs

The translator puts a step at every run of a loop body. A loop whose measure drops by exactly one
per repeat and is zero at the exit runs its body exactly `n + 1` times from the measure `n`: it
spends `n + 1` credits and returns `n + 1` receipts. -/

section LoopExact

variable {σ ε : Type} {body : MM σ ε} {again : ε → Bool} {inv : σ → Nat → FAssn}
  {post : ε × σ → FAssn}

/-- One body run of `loop_exact`, given the loop from the next measure. -/
private theorem loop_exact_run
    (step : ∀ s n, FTotalTriple (inv s n ⋆ credits 1) (body.run s) (fun r =>
      (if again r.1 then FAssn.ex fun n' => ⟪n = n' + 1⟫ ⋆ inv r.2 n' else ⟪n = 0⟫ ⋆ post r) ⋆
        spent 1))
    (s : σ) (n : Nat) (hrest : ∀ n', n = n' + 1 → ∀ s', FTotalTriple (inv s' n' ⋆ credits (n' + 1))
      ((Zig.loop body again).run s') (fun r => post r ⋆ spent (n' + 1))) :
    FTotalTriple (inv s n ⋆ credits (n + 1)) ((Zig.loop body again).run s)
      (fun r => post r ⋆ spent (n + 1)) := by
  rw [loop_run]
  refine FTotalTriple.bind ((step s n).frame (R := credits n) |>.pre fun _ h => ?_)
    fun ⟨e, s'⟩ => ?_
  · rw [credits_add n 1] at h
    rwa [show (inv s n ⋆ (credits n ⋆ credits 1)) = ((inv s n ⋆ credits 1) ⋆ credits n) by ac_rfl] at h
  cases ha : again e
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    refine (FTotalTriple.ret (Q := fun r => post r ⋆ spent (n + 1)) (e, s')).pre fun _ h => ?_
    rw [show (((⟪n = 0⟫ ⋆ post (e, s')) ⋆ spent 1) ⋆ credits n) =
      (⟪n = 0⟫ ⋆ ((post (e, s') ⋆ spent 1) ⋆ credits n)) by ac_rfl] at h
    obtain ⟨rfl, h⟩ := sep_lift.mp h
    rw [credits_zero] at h
    exact sep_emp.mp h
  · simp only [ha, ↓reduceIte]
    refine FTotalTriple.pre (P := FAssn.ex fun n' =>
      ⟪n = n' + 1⟫ ⋆ ((inv s' n' ⋆ credits n) ⋆ spent 1)) ?_ fun _ h => ?_
    · refine FTotalTriple.ex fun n' => FTotalTriple.lift fun hn => ?_
      subst hn
      refine ((hrest n' rfl s').frame (R := spent 1)).post fun _ _ h => ?_
      rw [spent_add]
      exact sep_assoc h
    · obtain ⟨n', h⟩ := sep_ex.mp (sep_assoc h)
      refine ⟨n', ?_⟩
      rwa [show ((⟪n = n' + 1⟫ ⋆ inv s' n') ⋆ (spent 1 ⋆ credits n)) =
        (⟪n = n' + 1⟫ ⋆ ((inv s' n' ⋆ credits n) ⋆ spent 1)) by ac_rfl] at h

/-- **A loop that counts its body runs** (total correctness and an exact step count): one run of
the body pays one credit and returns its receipt, and either repeats with the measure lowered by
exactly one or exits at zero. From the measure `n` and `n + 1` credits the loop runs its body
`n + 1` times and returns `n + 1` receipts, so `FTotalTriple.not_fewer_credits` shows that `n`
credits do not pay it. -/
theorem FTotalTriple.loop_exact
    (step : ∀ s n, FTotalTriple (inv s n ⋆ credits 1) (body.run s) (fun r =>
      (if again r.1 then FAssn.ex fun n' => ⟪n = n' + 1⟫ ⋆ inv r.2 n' else ⟪n = 0⟫ ⋆ post r) ⋆
        spent 1)) :
    ∀ s n, FTotalTriple (inv s n ⋆ credits (n + 1)) ((Zig.loop body again).run s)
      (fun r => post r ⋆ spent (n + 1)) := by
  intro s n
  induction n generalizing s with
  | zero => exact loop_exact_run step s 0 fun n' h => absurd h (by omega)
  | succ n ih => exact loop_exact_run step s (n + 1) fun n' h => by
      obtain rfl : n = n' := by omega
      exact ih

end LoopExact

/-! ## Thread locality (`fsym` derives the thread rules) -/

/-- **A step is local**: it reads no record and touches no byte. -/
@[fsym_provider] theorem ThreadLocal.tick {P : FAssn} : ThreadLocal P Zig.tick :=
  ThreadLocal.intro fun m _ _ _ _ _ _ => ⟨rfl, fun v m₀ e => by
    rw [tick_run'] at e
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
    exact ⟨.of_stepIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
      Nat.le_refl _, fun _ he => .inl he, fun _ he => .inl he⟩ (fun _ _ h => h) (fun _ he hn => absurd he hn)
      (fun _ h => h), fun _ _ _ h => h⟩⟩

attribute [fsym] FTotalTriple.tick_plain FTotalTriple.tick_unmetered FTotalTriple.tick_credit

end Full
end Zig
