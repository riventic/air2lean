import ZigLean.Sep.Full.Tick
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Witness
import ZigLean.Sep.Full.Conc

/-!
# Step counts: cost bounds over step ticks (`docs/sep-full-state.md` §Step ticks)

The translator is to put a step (`Zig.tick`) at every run of a loop body and at the entry of every
function of a recursive call group (L8b). A step needs a credit or the plain mode
(`ZigLean/Sep/Full/Tick.lean`). This module turns that into cost statements:

* **Credits under the plain mode.** Where `unmetered` is held no meter runs (`TickAuth.plain`), so
  credits bound nothing and any number can be added (`Holds.mintCredits`, `EUpd.credits_mint`). A
  proof that pays its steps with credits therefore gives the plain-mode statement of the same
  program without a second proof (`FTotalTriple.of_credits_unmetered`, `of_credits_plain`).
* **Exact step counts.** A run proved with `N` credits makes at most `N` steps
  (`FTotalTriple.ticks_le`), and a run that returns `N` receipts makes at least `N`
  (`FTotalTriple.ticks_ge`), from a start whose resources hold no credit, meter, receipt or
  `unmetered` fragment (`CreditFree`; the adequacy steps `Holds.addCredits` and `Holds.addSpent` put the meter and
  the receipts of the steps run so far in the frame). A statement with both counts its steps
  exactly (`FTotalTriple.ticks_eq`), and no proof pays the same run with fewer credits:
  `FTotalTriple.not_fewer_credits` makes a bound tight.
* **Counted loops.** `FTotalTriple.loop_exact`: a loop whose measure drops by exactly one per body
  run and is zero at the exit runs its body `n + 1` times from the measure `n`; it spends `n + 1`
  credits and returns `n + 1` receipts. The client proves one body run with `fsym`
  (`tick_credit` pays the step).
* **Admissible inputs** with the plain mode or with credits (`FAdmit.of_mem_plain`,
  `FAdmit.up_plain`, `FAdmit.of_mem_credits`).

The unit is the step of the model, not CPU time: straight-line code outside a loop body or a
recursive entry takes none, and pure code (`Zig.M`, `Result`) takes none (plan decision D5).

The counts are read off sequential runs (`FTotalTriple.runs`); a thread's steps pay with the same
rules, and their counts are not read off yet.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Credits under the plain mode -/

/-- **Credits next to the plain mode**: a memory whose resources or frame hold `unmetered` holds the
resources with `n` more credits. -/
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
    exact ⟨_, hh.mintCredits n (by simp [g0, Ghost.ofAC]; omega), sep_credits_intro ⟨h0, k0, g0⟩ n⟩

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

/-! ## Exact step counts -/

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

/-- A meter-free start: the resources and the frame hold no credit, meter or `unmetered`
fragment, so a meter can be added (`Holds.addCredits`). -/
structure MeterFree (r rF : Res) : Prop where
  cred : (r.gh.add rF.gh).ac.frag .cred = 0
  auth : ∀ L, (r.gh.add rF.gh).ac.auth .cred L = 0
  unmetered : (r.gh.add rF.gh).ac.frag .unmetered = 0

/-- A credit-free start: meter-free, and without receipts, so the receipts of the steps run so far
can be added (`Holds.addSpent`). -/
structure CreditFree (r rF : Res) : Prop extends MeterFree r rF where
  spent : (r.gh.add rF.gh).ac.frag .spent = 0

/-- **At most `N` steps, for a run that returns**: from a meter-free start, a run proved with `N`
credits (partial correctness) that returns raises the step count by at most `N`. -/
theorem FTriple.ticks_le {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {N : Nat}
    (h : FTriple (P ⋆ credits N) c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r)
    (hs : m.FSeq) (hc : MeterFree r rF) {v : α} {m' : Mem} (hr : c.run m = pure (v, m')) :
    m'.ticks ≤ m.ticks + N := by
  have h' := h m _ _ (Holds.addCredits N hh hc.cred hc.auth hc.unmetered) (sep_credits_intro hp N) hs
  rw [hr] at h'
  obtain ⟨r', hh', -, -⟩ := h'
  have := hh'.ghost.2.2.2.tick.meter (m.ticks + N) (by simp [Ghost.credAuth]; omega)
  omega

/-- **At least `N` steps, for a run that returns**: from a start without receipts, a run that
returns `N` receipts (partial correctness) raises the step count by at least `N`. -/
theorem FTriple.ticks_ge {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {N : Nat}
    (h : FTriple P c (fun v => Q v ⋆ spent N)) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : P r) (hs : m.FSeq) (hsp : (r.gh.add rF.gh).ac.frag .spent = 0) {v : α} {m' : Mem}
    (hr : c.run m = pure (v, m')) : m.ticks + N ≤ m'.ticks := by
  have h' := h m _ _ (hh.addSpent hsp) hp hs
  rw [hr] at h'
  obtain ⟨r', hh', hq, -⟩ := h'
  obtain ⟨r₁, r₂, -, rfl, -, -, -, g₂⟩ := hq
  have := hh'.ghost.2.2.2.tick.spent
  simp [g₂] at this
  omega

/-- **Exactly `N` steps, and the memory, for a run that returns**: from a credit-free start, a run
proved with `N` credits and `N` receipts (partial correctness) that returns raises the step count by
exactly `N`, and its memory's live bytes are a part `r'` that holds the postcondition and the
frame's bytes (`FMatch`: the frame is untouched). -/
theorem FTriple.ticks_eq_post {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {N : Nat}
    (h : FTriple (P ⋆ credits N) c (fun v => Q v ⋆ spent N)) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : P r) (hs : m.FSeq) (hc : CreditFree r rF) {v : α} {m' : Mem}
    (hr : c.run m = pure (v, m')) :
    m'.ticks = m.ticks + N ∧ ∃ r', FHeap.Disjoint r'.heap rF.heap ∧
      FMatch m' (r'.heap ∪ rF.heap) ∧ Q v r' ∧ m'.FSeq := by
  have hle := h.ticks_le hh hp hs hc.toMeterFree hr
  have hge := h.ticks_ge (Holds.addCredits N hh hc.cred hc.auth hc.unmetered)
    (sep_credits_intro hp N) hs (by simpa [Ghost.cred, Ghost.credAuth] using hc.spent) hr
  have h' := h m _ _ (Holds.addCredits N hh hc.cred hc.auth hc.unmetered) (sep_credits_intro hp N) hs
  rw [hr] at h'
  obtain ⟨r', hh', hq, hs'⟩ := h'
  obtain ⟨r₁, r₂, -, rfl, hq, h0, -, -⟩ := hq
  have hd := hh'.disj
  have hm := hh'.heap
  simp only [h0, FHeap.union_empty] at hd hm
  exact ⟨by omega, r₁, hd, hm, hq, hs'⟩

/-- **At most `N` steps**: from a meter-free start, a run proved with `N` credits raises the step
count by at most `N`. -/
theorem FTotalTriple.ticks_le {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {N : Nat}
    (h : FTotalTriple (P ⋆ credits N) c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r)
    (hs : m.FSeq) (hc : MeterFree r rF) :
    ∃ v m', c.run m = pure (v, m') ∧ m'.ticks ≤ m.ticks + N := by
  obtain ⟨v, m', -, hr, -⟩ :=
    h.runs (Holds.addCredits N hh hc.cred hc.auth hc.unmetered) (sep_credits_intro hp N) hs
  exact ⟨v, m', hr, h.toPartial.ticks_le hh hp hs hc hr⟩

/-- **At least `N` steps**: from a start without receipts, a run that returns `N` receipts raises
the step count by at least `N`. -/
theorem FTotalTriple.ticks_ge {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {N : Nat}
    (h : FTotalTriple P c (fun v => Q v ⋆ spent N)) {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : P r) (hs : m.FSeq) (hsp : (r.gh.add rF.gh).ac.frag .spent = 0) :
    ∃ v m', c.run m = pure (v, m') ∧ m.ticks + N ≤ m'.ticks := by
  obtain ⟨v, m', -, hr, -⟩ := h.runs hh hp hs
  exact ⟨v, m', hr, h.toPartial.ticks_ge hh hp hs hsp hr⟩

/-- **Exactly `N` steps, and the memory**: from a credit-free start, a run proved with `N` credits
and `N` receipts returns, raises the step count by exactly `N`, and its memory's live bytes are a
part that holds the postcondition and the frame's bytes (`FTriple.ticks_eq_post`). -/
theorem FTotalTriple.ticks_eq_post {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {N : Nat}
    (h : FTotalTriple (P ⋆ credits N) c (fun v => Q v ⋆ spent N)) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : P r) (hs : m.FSeq) (hc : CreditFree r rF) :
    ∃ v m', c.run m = pure (v, m') ∧ m'.ticks = m.ticks + N ∧ ∃ r', FHeap.Disjoint r'.heap rF.heap ∧
      FMatch m' (r'.heap ∪ rF.heap) ∧ Q v r' ∧ m'.FSeq := by
  obtain ⟨v, m', -, hr, -⟩ :=
    h.runs (Holds.addCredits N hh hc.cred hc.auth hc.unmetered) (sep_credits_intro hp N) hs
  exact ⟨v, m', hr, h.toPartial.ticks_eq_post hh hp hs hc hr⟩

/-- **Exactly `N` steps**: from a credit-free start, a run proved with `N` credits and `N` receipts
raises the step count by exactly `N`. -/
theorem FTotalTriple.ticks_eq {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {N : Nat}
    (h : FTotalTriple (P ⋆ credits N) c (fun v => Q v ⋆ spent N)) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : P r) (hs : m.FSeq) (hc : CreditFree r rF) :
    ∃ v m', c.run m = pure (v, m') ∧ m'.ticks = m.ticks + N := by
  obtain ⟨v, m', hr, ht, -⟩ := h.ticks_eq_post hh hp hs hc
  exact ⟨v, m', hr, ht⟩

/-- **The step count is tight**: a run proved with `N` credits and `N` receipts cannot be paid
with fewer credits: a credit-free start that holds the precondition refutes it. -/
theorem FTotalTriple.not_fewer_credits {α : Type} {P : FAssn} {c : MemM α} {Q Q' : α → FAssn}
    {N M : Nat} (h : FTotalTriple (P ⋆ credits N) c (fun v => Q v ⋆ spent N)) (hM : M < N)
    {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq) (hc : CreditFree r rF) :
    ¬ FTotalTriple (P ⋆ credits M) c Q' := fun h' => by
  obtain ⟨v₁, m₁, hr₁, hle⟩ := h'.ticks_le hh hp hs hc.toMeterFree
  obtain ⟨v₂, m₂, hr₂, heq⟩ := h.ticks_eq hh hp hs hc
  rw [hr₁] at hr₂
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj hr₂)
  omega

/-! ## Loops that count their body runs -/

section LoopExact

variable {σ ε : Type} {body : MM σ ε} {again : ε → Bool} {inv : σ → Nat → FAssn}
  {post : ε × σ → FAssn}

/-- The assertion after one counted body run: repeat with the invariant at the measure lowered by
exactly one, or exit at zero (`floopNext` with an exact measure). -/
def floopExact (again : ε → Bool) (inv : σ → Nat → FAssn) (post : ε × σ → FAssn) (n : Nat)
    (r : ε × σ) : FAssn :=
  if again r.1 then FAssn.ex fun n' => ⟪n = n' + 1⟫ ⋆ inv r.2 n' else ⟪n = 0⟫ ⋆ post r

theorem floopExact_repeat {n : Nat} {e : ε} {s : σ} {r : Res} (ha : again e = true)
    (hi : inv s n r) : floopExact again inv post (n + 1) (e, s) r := by
  simp only [floopExact, ha, ↓reduceIte]
  exact ⟨n, sep_lift.mpr ⟨rfl, hi⟩⟩

theorem floopExact_exit {e : ε} {s : σ} {r : Res} (ha : again e = false) (hp : post (e, s) r) :
    floopExact again inv post 0 (e, s) r := by
  simp only [floopExact, ha, Bool.false_eq_true, ↓reduceIte]
  exact sep_lift.mpr ⟨by trivial, hp⟩

/-- One body run of `loop_exact`, given the loop from the next measure. -/
private theorem loop_exact_run
    (step : ∀ s n, FTotalTriple (inv s n ⋆ credits 1) (body.run s)
      (fun r => floopExact again inv post n r ⋆ spent 1))
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
  · simp only [floopExact, ha, Bool.false_eq_true, ↓reduceIte]
    refine (FTotalTriple.ret (Q := fun r => post r ⋆ spent (n + 1)) (e, s')).pre fun _ h => ?_
    rw [show (((⟪n = 0⟫ ⋆ post (e, s')) ⋆ spent 1) ⋆ credits n) =
      (⟪n = 0⟫ ⋆ ((post (e, s') ⋆ spent 1) ⋆ credits n)) by ac_rfl] at h
    obtain ⟨rfl, h⟩ := sep_lift.mp h
    rw [credits_zero] at h
    exact sep_emp.mp h
  · simp only [floopExact, ha, ↓reduceIte]
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
    (step : ∀ s n, FTotalTriple (inv s n ⋆ credits 1) (body.run s)
      (fun r => floopExact again inv post n r ⋆ spent 1)) :
    ∀ s n, FTotalTriple (inv s n ⋆ credits (n + 1)) ((Zig.loop body again).run s)
      (fun r => post r ⋆ spent (n + 1)) := by
  intro s n
  induction n generalizing s with
  | zero => exact loop_exact_run step s 0 fun n' h => absurd h (by omega)
  | succ n ih =>
    refine loop_exact_run step s (n + 1) fun n' h => ?_
    obtain rfl : n = n' := by omega
    exact ih

/-- **A loop that counts its body runs, for a call of a concurrent function** (`CTriple`, partial
correctness): as `FTotalTriple.loop_exact`, one run of the body pays one credit and returns its
receipt, and either repeats with the measure lowered by exactly one or exits at zero. From the
measure `n` and `n + 1` credits, a run of the loop that exits has run its body `n + 1` times and
returns `n + 1` receipts. The invariant of `CTriple.loop` carries the credits of the runs left and
the receipts of the runs so far. -/
theorem CTriple.loop_exact {Tgt : Type} {cbody : CM Tgt σ ε}
    (step : ∀ s n, CTriple (inv s n ⋆ credits 1) (cbody.run s)
      (fun r => floopExact again inv post n r ⋆ spent 1)) (s : σ) (N : Nat) :
    CTriple (inv s N ⋆ credits (N + 1)) ((Zig.loop cbody again).run s)
      (fun r => post r ⋆ spent (N + 1)) := by
  refine (CTriple.loop (fun s => FAssn.ex fun n => ⟪n ≤ N⟫ ⋆
      (inv s n ⋆ (credits (n + 1) ⋆ spent (N - n))))
    (fun r => post r ⋆ spent (N + 1)) (fun s => ?_) s).pre fun _ h =>
      ⟨N, sep_lift.mpr ⟨Nat.le_refl _, ?_⟩⟩
  · refine CTriple.ex fun n => CTriple.lift fun hn => ?_
    refine ((step s n).frame (R := credits n ⋆ spent (N - n))).conseq (fun _ h => ?_)
      fun ⟨e, s'⟩ _ h => ?_
    · rw [credits_add n 1] at h
      exact (show (inv s n ⋆ ((credits n ⋆ credits 1) ⋆ spent (N - n))) =
        ((inv s n ⋆ credits 1) ⋆ (credits n ⋆ spent (N - n))) by ac_rfl) ▸ h
    · cases ha : again e
      · simp only [floopExact, ha, Bool.false_eq_true, ↓reduceIte] at h ⊢
        have h := (show (((⟪n = 0⟫ ⋆ post (e, s')) ⋆ spent 1) ⋆ (credits n ⋆ spent (N - n))) =
          (⟪n = 0⟫ ⋆ ((post (e, s') ⋆ credits n) ⋆ (spent (N - n) ⋆ spent 1))) by ac_rfl) ▸ h
        obtain ⟨rfl, h⟩ := sep_lift.mp h
        rw [credits_zero, ← spent_add, Nat.sub_zero] at h
        exact sep_mono_left (fun _ h => sep_emp.mp h) h
      · simp only [floopExact, ha, ↓reduceIte] at h ⊢
        obtain ⟨n', h⟩ := sep_ex.mp (sep_assoc h)
        have h := (show ((⟪n = n' + 1⟫ ⋆ inv s' n') ⋆ (spent 1 ⋆ (credits n ⋆ spent (N - n)))) =
          (⟪n = n' + 1⟫ ⋆ (inv s' n' ⋆ (credits n ⋆ (spent (N - n) ⋆ spent 1)))) by ac_rfl) ▸ h
        obtain ⟨rfl, h⟩ := sep_lift.mp h
        refine ⟨n', sep_lift.mpr ⟨by omega, ?_⟩⟩
        rwa [← spent_add, show N - (n' + 1) + 1 = N - n' by omega] at h
  · rw [Nat.sub_self, spent_zero]
    exact sep_mono_right (fun _ h => sep_emp.mpr h) h

end LoopExact

end Full

/-! ## Admissible inputs -/

namespace Witness

open Full FAssn

/-- `holds_mem` with its frame named: the empty frame, which holds no meter. -/
theorem holds_mem_empty (m : Mem) (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    Holds m ⟨m.fheap, Know.none, Ghost.unit⟩ ⟨FHeap.empty, Know.none, Ghost.unit⟩ := by
  simpa only [Ghost.exts_none] using
    (holds_exts (E := fun _ => none) (FMatch.fheap m) (fun _ h => h.elim)
      (exts_true (fun _ _ _ h => nomatch h)) hns)

/-- `FAdmit.of_mem` in the plain mode (`Holds.addPlain`). -/
theorem FAdmit.of_mem_plain {P : FAssn} {m : Mem} (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩)
    (hs : m.FSeq) (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) : FAdmit (P ⋆ plain) :=
  ⟨m, _, _, (holds_mem_empty m hns).addPlain hns fun _ => by simp, sep_plain_intro hp, hs, trivial⟩

/-- `FAdmit.up` in the plain mode. -/
theorem FAdmit.up_plain {P : Assn} {m : Mem} (hp : P m.heap) (hs : m.FSeq)
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) : FAdmit (FAssn.up P ⋆ plain) :=
  FAdmit.of_mem_plain ⟨by simpa using hp, rfl, rfl⟩ hs hns

/-- `FAdmit.of_mem` with `n` credits (`Holds.addCredits`): the frame holds the meter `●n`. -/
theorem FAdmit.of_mem_credits {P : FAssn} {m : Mem} (n : Nat)
    (hp : P ⟨m.fheap, Know.none, Ghost.unit⟩) (hs : m.FSeq)
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) : FAdmit (P ⋆ credits n) :=
  ⟨m, _, _, Holds.addCredits n (holds_mem_empty m hns) (by simp) (by simp) (by simp),
    sep_credits_intro hp n, hs, trivial⟩

end Witness
end Zig
