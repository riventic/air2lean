import ZigLean.Sep.Full.Block

/-!
# Total stack pushes from the stack depth token (`docs/sep-full-state.md` §Stack depth, step 5)

The rules of a thread's stack budget (MM-18) over the tokens of `Full/Ghost` (`sp`, `ent`, `cur`)
and their memory side (`Full/StackDepth`):

* `FTotalTriple.allocStack_sp`: the running thread `t` (`cur t`) with `sp t S D` and
  `D + stackCharge size align ≤ S` makes the stack block (total: the room follows from the token,
  `StackAuth.allocOk`); it holds `sp t S (D + c)` and the block's entry token `ent t (some b) D c`.
* `FTotalTriple.free_sp`: `free` of that block with its entry token and `sp t S (ℓ + c)` gives
  `sp t S ℓ` back (the block is the top of the stack, `StackAuth.free_top`).
* `FTotalTriple.enterFrame_sp`, `FTotalTriple.leaveFrame_sp`: the same for the frame of a recursive
  call (`frameBase`).

They are `@[fsym]` rules, registered after the plain-mode rules of `Full/Block`, so `fsym` tries
them first and falls back to the plain mode when the precondition has no stack token. In a thread
`fsym` derives their thread rules (`FTTotalTriple.ofSeq`) with the providers `ThreadLocal.allocStack`,
`ThreadLocal.free_of` and the frame providers below; a thread gets `cur t` for its own steps from
the thread rules (`WP.liftMem_fownedCurS`).

Each rule changes the counter cell together with the memory: `Holds.reAC` (a cell change with
the stack states) and, for the new block, `Holds.push` in the memory without stack budgets
followed by `Holds.reAC` into the memory after `alloc`.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Ghost-only resources -/

/-- The resource that holds exactly the ghost state `g`. -/
abbrev gres (g : Ghost) : Res := ⟨FHeap.empty, Know.none, g⟩

theorem gres_of {r : Res} {g : Ghost} (h : r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = g) :
    r = gres g := by
  obtain ⟨h1, h2, h3⟩ := h; rw [res_eta r, h1, h2, h3]

theorem gres_sep {P Q : FAssn} {g₁ g₂ : Ghost} (hP : P (gres g₁)) (hQ : Q (gres g₂)) :
    (P ⋆ Q) (gres (g₁.add g₂)) :=
  ⟨gres g₁, gres g₂, FHeap.disjoint_empty _, by simp [FHeap.union_empty, Know.union_none], hP, hQ⟩

theorem gres_of_sep {P Q : FAssn} {g₁ g₂ : Ghost} {r : Res}
    (hP : ∀ r, P r → r = gres g₁) (hQ : ∀ r, Q r → r = gres g₂) (h : (P ⋆ Q) r) :
    r = gres (g₁.add g₂) := by
  obtain ⟨r₁, r₂, -, rfl, h1, h2⟩ := h
  rw [hP _ h1, hQ _ h2]; simp [FHeap.union_empty, Know.union_none]

theorem sp_gres {t S D : Nat} {r : Res} (h : sp t S D r) : r = gres (Ghost.ofAC (spCell t S D)) :=
  gres_of h
theorem ent_gres {t ℓ c : Nat} {o : Option BlockId} {r : Res} (h : ent t o ℓ c r) :
    r = gres (Ghost.ofAC (entCell t o ℓ c)) := gres_of h
theorem cur_gres {t : Nat} {r : Res} (h : cur t r) : r = gres (Ghost.cur t) := gres_of h

theorem sp_intro (t S D : Nat) : sp t S D (gres (Ghost.ofAC (spCell t S D))) := ⟨rfl, rfl, rfl⟩
theorem ent_intro (t : Nat) (o : Option BlockId) (ℓ c : Nat) :
    ent t o ℓ c (gres (Ghost.ofAC (entCell t o ℓ c))) := ⟨rfl, rfl, rfl⟩
theorem cur_intro (t : Nat) : cur t (gres (Ghost.cur t)) := ⟨rfl, rfl, rfl⟩

/-- A ghost state of the counter cell only changes no ledger, extent or claim. -/
theorem ofAC_parts (a : KCell) (g : Ghost) :
    ((Ghost.ofAC a).add g).led = g.led ∧ ((Ghost.ofAC a).add g).extent = g.extent ∧
      ((Ghost.ofAC a).add g).cl = g.cl ∧ ((Ghost.ofAC a).add g).ac = a.add g.ac := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;> funext x <;> (try funext y) <;>
    simp [Ghost.add, Ghost.ofAC, Ghost.unit]

/-! ## The memory without stack budgets -/

/-- `m` without stack states: no budget. -/
abbrev _root_.Zig.Mem.unstacked (m : Mem) : Mem := { m with stacks := #[] }

/-- **A resource without stack tokens holds in the memory without stack budgets** with a frame
whose counter cell is emptied. -/
theorem Holds.unstack {m : Mem} {r rF : Res} (hh : Holds m r rF) (hr : r.gh = Ghost.ofAC r.gh.ac) :
    Holds m.unstacked ⟨r.heap, r.know, Ghost.unit⟩ ⟨rF.heap, rF.know, { rF.gh with ac := ACell.unit }⟩ := by
  refine hh.reAC rfl rfl ?_ ?_ ?_ (by simpa using ACell.valid_unit)
    (by simpa using MemAuth.unit (m := m.unstacked) (Mem.noStack_of_stacks rfl))
  · rw [hr]; funext γ; simp [Ghost.add, Ghost.ofAC, Ghost.unit]
  · rw [hr]; funext b; simp [Ghost.add, Ghost.ofAC, Ghost.unit]
  · rw [hr]; funext b x; simp [Ghost.add, Ghost.ofAC, Ghost.unit]

/-! ## The rules -/

/-- Memory facts of a stack token next to the running thread's token. -/
theorem Holds.stackFacts {m : Mem} {r rF : Res} {t S D : Nat} (hh : Holds m r rF)
    (hr : r = gres ((Ghost.cur t).add (Ghost.ofAC (spCell t S D)))) :
    m.current = t ∧ (m.stackOf t).budget = some S ∧
      (r.gh.add rF.gh).ac = (spCell t S D).add ((curCell t).add rF.gh.ac) := by
  subst hr
  have e : (((Ghost.cur t).add (Ghost.ofAC (spCell t S D))).add rF.gh).ac =
      (spCell t S D).add ((curCell t).add rF.gh.ac) := by
    ext <;> simp [Ghost.cur] <;> omega
  have hM := hh.ghost.2.2.2
  have hV := hh.ghost.1.1.2.2.2
  simp only at hM hV
  rw [e] at hM hV
  refine ⟨hh.current (R := sp t S D) (gres_sep (cur_intro t) (sp_intro t S D)), ?_, e⟩
  exact hM.stack.budget_of_sp (t := t) (S := S) (D := D) hV (by simp [spCell] <;> omega)

/-- **The stack block of an escaping local, from the stack token** (total): the running thread
`t` with `sp t S D` and `D + stackCharge size align ≤ S` makes the block (its room follows from
the token: `StackAuth.allocOk`), and holds its bytes, its full extent, `sp t S (D + c)` and the
block's entry token `ent t (some b) D c` (`c = stackCharge size align`). -/
theorem FTotalTriple.allocStack_sp {t S D : Nat} (size align : Nat) (ha : 0 < align)
    (hpos : 0 < size) (hfit : D + stackCharge size align ≤ S) :
    FTotalTriple (cur t ⋆ sp t S D) (Zig.allocStack size align)
      (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
        ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
          ((up (bytesAt p A size .stack (Array.replicate size .undef)) ⋆ bext b size .stack) ⋆
            (cur t ⋆ (sp t S (D + stackCharge size align) ⋆
              ent t (some b) D (stackCharge size align))))) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    have hr := gres_of_sep (fun _ => cur_gres) (fun _ => sp_gres) hp
    obtain ⟨hcur, hS, e⟩ := hh.stackFacts hr
    have hM := hh.ghost.2.2.2
    have hV := hh.ghost.1.1.2.2.2
    rw [e] at hM hV
    obtain ⟨hroom, hv', hsa'⟩ := StackAuth.alloc hM.stack hV hcur hS hfit
    let c := stackCharge size align
    let a' : KCell := (curCell t).add ((spCell t S (D + c)).add (entCell t (some m.blocks.size) D c))
    let nb := m.allocBlock .stack size align
    -- the block pushed in the memory without stack budgets, then the cells of `alloc`'s memory
    have hu := hh.unstack (by rw [hr]; simp only [Ghost.cur, Ghost.ofAC_add, Ghost.ofAC_ac])
    rw [hr] at hu
    have h0 := Holds.push (m := m.unstacked) (r := gres Ghost.unit) hu ⟨rfl, rfl, rfl⟩
      (nb := nb) rfl (by simp [nb, Mem.allocBlock, BlockKind.mappedLo, hpos])
      (MemAuth.Keep.of_noStack (Mem.noStack_of_stacks rfl) (Mem.noStack_of_stacks rfl) rfl)
    have ecell : (((pushRes m.blocks.size nb).gh.add (Ghost.ofAC a')).add rF.gh).ac =
        (spCell t S (D + c)).add ((entCell t (some m.blocks.size) D c).add
          ((curCell t).add rF.gh.ac)) := by
      ext <;> simp [pushRes, a', Ghost.exts] <;> omega
    have h1 := h0.reAC (m' := m.afterAlloc .stack size align)
      (g := (pushRes m.blocks.size nb).gh.add (Ghost.ofAC a')) (gF := rF.gh) rfl rfl
      (by funext γ; simp [pushRes, Ghost.add, Ghost.ofAC, Ghost.unit, Ghost.exts])
      (by funext b; simp [pushRes, Ghost.add, Ghost.ofAC, Ghost.unit, Ghost.exts])
      (by funext b x; simp [pushRes, Ghost.add, Ghost.ofAC, Ghost.unit, Ghost.exts])
      (by rw [ecell]; exact hv')
      (by
        rw [ecell]
        refine hM.restack hsa' rfl rfl (fun h => absurd (h t) (by rw [hS]; simp))
          (fun k => by simp [spCell, entCell]) (fun k n => by simp [spCell, entCell])
          (fun v => by simp [spCell, entCell]))
    refine ⟨⟨some m.blocks.size, 0⟩, m.afterAlloc .stack size align, _, alloc_run_eq m hroom, h1,
      ⟨m.allocAddr .stack size align, m.blocks.size, sep_lift.mpr ⟨⟨rfl, rfl,
        m.allocAddr_mod .stack size align ha⟩, ⟨pushRes m.blocks.size nb, gres (Ghost.ofAC a'),
          fun _ => .inr rfl, by simp [FHeap.union_empty, Know.union_none, pushRes], ?_, ?_⟩⟩⟩,
      ⟨⟨hs.1.single⟩, hs.2.1, LDMono.alloc hroom rfl (by simp) rfl hs.2.2⟩⟩
    · have hq := pushRes_up m.blocks.size nb
      simpa [nb, Mem.allocBlock, BlockKind.mappedLo, Array.extract_replicate] using hq
    · have : Ghost.ofAC a' = (Ghost.cur t).add ((Ghost.ofAC (spCell t S (D + c))).add
          (Ghost.ofAC (entCell t (some m.blocks.size) D c))) := by
        simp only [a', Ghost.cur, Ghost.ofAC_add]
      rw [this]
      exact gres_sep (cur_intro t) (gres_sep (sp_intro t S (D + c)) (ent_intro t _ D c))

/-- **`free` of the top stack block** (total): with its entry token `ent t (some b) ℓ c` and
`sp t S D` at `D = ℓ + c` (nothing above it), its bytes and its full extent go and the depth
returns to `ℓ` (`StackAuth.free_top`). -/
theorem FTotalTriple.free_sp {p : Ptr} {A Sz : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    {t S D ℓ c : Nat} (hpb : p.block = some b) (hS : bs.size = Sz) (h0 : p.off = 0) (hpos : 0 < Sz)
    (hK : K ≠ .constGlobal) (hD : D = ℓ + c) :
    FTotalTriple ((up (bytesAt p A Sz K bs) ⋆ bext b Sz K) ⋆ (ent t (some b) ℓ c ⋆ sp t S D))
      (Zig.free p) (fun _ => sp t S ℓ) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    subst hD
    obtain ⟨r₁, r₂, hd, rfl, hp₁, hp₂⟩ := hp
    have hr₂ := gres_of_sep (fun _ => ent_gres) (fun _ => sp_gres) hp₂
    subst hr₂
    have hft := FTotalTriple.free (A := A) hpb hS h0 hpos hK
    have hh₁ := Holds.split hd hh
    obtain ⟨v, m', hrun⟩ := hft.2 m r₁ _ hh₁ hp₁ hs
    have hpost := hft.1 m r₁ _ hh₁ hp₁ hs
    rw [hrun] at hpost
    obtain ⟨r₁', hh₁', he, hs'⟩ := hpost
    have hj := Holds.join (r₁ := r₁') (r₂ := gres ((Ghost.ofAC (entCell t (some b) ℓ c)).add
      (Ghost.ofAC (spCell t S (ℓ + c))))) (by rw [he.1]; exact fun _ => .inl rfl)
      (fun _ => .inl rfl) hh₁'
    have er : (⟨r₁'.heap ∪ FHeap.empty, r₁'.know.union Know.none,
        r₁'.gh.add ((Ghost.ofAC (entCell t (some b) ℓ c)).add (Ghost.ofAC (spCell t S (ℓ + c))))⟩ : Res) =
        gres ((Ghost.ofAC (entCell t (some b) ℓ c)).add (Ghost.ofAC (spCell t S (ℓ + c)))) := by
      rw [he.1, he.2.1, he.2.2]; simp [FHeap.union_empty, Know.union_none]
    rw [er] at hj
    -- the memory side: the free of the top block returns its charge
    have hM₀ := hh.ghost.2.2.2
    have hV₀ := hh.ghost.1.1.2.2.2
    have e₀ : ((⟨r₁.heap ∪ FHeap.empty, r₁.know.union Know.none, r₁.gh.add
        ((Ghost.ofAC (entCell t (some b) ℓ c)).add (Ghost.ofAC (spCell t S (ℓ + c))))⟩ : Res).gh.add
          rF.gh).ac = (spCell t S (ℓ + c)).add ((entCell t (some b) ℓ c).add rF.gh.ac) := by
      obtain ⟨-, -, hg₁⟩ := up_sep_bext hp₁
      simp only; rw [hg₁]; ext <;> simp [Ghost.exts] <;> omega
    rw [e₀] at hM₀ hV₀
    have hrun' : ((Zig.free p).run m).run = some (.ok (v, m')) := by rw [hrun]; rfl
    obtain ⟨hv', hsa'⟩ := StackAuth.free_top hM₀.stack hV₀ hpb hrun'
    have e₁ : (((Ghost.ofAC (entCell t (some b) ℓ c)).add (Ghost.ofAC (spCell t S (ℓ + c)))).add
        rF.gh).ac = (spCell t S (ℓ + c)).add ((entCell t (some b) ℓ c).add rF.gh.ac) := by
      ext <;> simp <;> omega
    have hM₁ := hj.ghost.2.2.2
    simp only at hM₁
    rw [e₁] at hM₁
    have h₂ := hj.reAC (m' := m') (g := Ghost.ofAC (spCell t S ℓ)) (gF := rF.gh) rfl rfl
      (by funext γ; simp [Ghost.add, Ghost.ofAC, Ghost.unit])
      (by funext x; simp [Ghost.add, Ghost.ofAC, Ghost.unit])
      (by funext x y; simp [Ghost.add, Ghost.ofAC, Ghost.unit])
      (by simpa using hv')
      (by
        simp only [Ghost.add_ac, Ghost.ofAC_ac]
        exact hM₁.restack hsa' rfl rfl id (fun k => by simp [spCell, entCell])
          (fun k n => by simp [spCell, entCell]) (fun v => by simp [spCell, entCell]))
    exact ⟨v, m', _, hrun, h₂, ⟨rfl, rfl, rfl⟩, hs'⟩

/-- **A frame of a recursive call, from the stack token** (total): the running thread `t` with
`sp t S D` and `D + frameBase ≤ S` enters the frame and holds `sp t S (D + frameBase)` and the
frame's entry token `ent t none D frameBase` (`StackAuth.enterFrame`). -/
theorem FTotalTriple.enterFrame_sp {t S D : Nat} (hfit : D + frameBase ≤ S) :
    FTotalTriple (cur t ⋆ sp t S D) Zig.enterFrame
      (fun _ => cur t ⋆ (sp t S (D + frameBase) ⋆ ent t none D frameBase)) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    have hr := gres_of_sep (fun _ => cur_gres) (fun _ => sp_gres) hp
    obtain ⟨hcur, hS, e⟩ := hh.stackFacts hr
    have hM := hh.ghost.2.2.2
    have hV := hh.ghost.1.1.2.2.2
    rw [e] at hM hV
    obtain ⟨hrun, hv', hsa'⟩ := StackAuth.enterFrame hM.stack hV hcur hS hfit
    subst hr
    let g' : Ghost := (Ghost.cur t).add ((Ghost.ofAC (spCell t S (D + frameBase))).add
      (Ghost.ofAC (entCell t none D frameBase)))
    have ecell : (g'.add rF.gh).ac = (spCell t S (D + frameBase)).add
        ((entCell t none D frameBase).add ((curCell t).add rF.gh.ac)) := by
      ext <;> simp [g', Ghost.cur] <;> omega
    have h₁ := hh.reAC (m' := { m with stacks := m.pushEntry none frameBase }) (g := g')
      (gF := rF.gh) rfl rfl
      (by funext γ; simp [g', Ghost.cur, Ghost.add, Ghost.ofAC, Ghost.unit])
      (by funext x; simp [g', Ghost.cur, Ghost.add, Ghost.ofAC, Ghost.unit])
      (by funext x y; simp [g', Ghost.cur, Ghost.add, Ghost.ofAC, Ghost.unit])
      (by rw [ecell]; exact hv')
      (by
        rw [ecell]
        exact hM.restack hsa' rfl rfl (fun h => absurd (h t) (by rw [hS]; simp))
          (fun k => by simp [spCell, entCell]) (fun k n => by simp [spCell, entCell])
          (fun v => by simp [spCell, entCell]))
    exact ⟨(), _, _, hrun, h₁,
      gres_sep (cur_intro t) (gres_sep (sp_intro t S (D + frameBase)) (ent_intro t none D frameBase)),
      ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩⟩

/-- **Leaving a frame returns its charge** (total): the running thread `t` with its frame's entry
token `ent t none ℓ c` and `sp t S D` at `D = ℓ + c` leaves the frame and holds `sp t S ℓ`
(`StackAuth.leaveFrame`). -/
theorem FTotalTriple.leaveFrame_sp {t S D ℓ c : Nat} (hD : D = ℓ + c) :
    FTotalTriple (cur t ⋆ (ent t none ℓ c ⋆ sp t S D)) Zig.leaveFrame (fun _ => cur t ⋆ sp t S ℓ) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    subst hD
    have hr := gres_of_sep (fun _ => cur_gres)
      (fun _ h => gres_of_sep (fun _ => ent_gres) (fun _ => sp_gres) h) hp
    subst hr
    have hcur : m.current = t := hh.current (R := ent t none ℓ c ⋆ sp t S (ℓ + c))
      (gres_sep (cur_intro t) (gres_sep (ent_intro t none ℓ c) (sp_intro t S (ℓ + c))))
    have hM := hh.ghost.2.2.2
    have hV := hh.ghost.1.1.2.2.2
    have e : (((Ghost.cur t).add ((Ghost.ofAC (entCell t none ℓ c)).add
        (Ghost.ofAC (spCell t S (ℓ + c))))).add rF.gh).ac =
        (spCell t S (ℓ + c)).add ((entCell t none ℓ c).add ((curCell t).add rF.gh.ac)) := by
      ext <;> simp [Ghost.cur] <;> omega
    simp only at hM hV
    rw [e] at hM hV
    obtain ⟨m', hrun, hv', hsa'⟩ := StackAuth.leaveFrame hM.stack hV hcur
    have hS := hM.stack.budget_of_sp (t := t) (S := S) (D := ℓ + c) hV (by simp [spCell] <;> omega)
    rw [← hcur] at hS
    have hm' := hrun.symm.trans (leaveFrame_run_some hS)
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj hm')
    let g' : Ghost := (Ghost.cur t).add (Ghost.ofAC (spCell t S ℓ))
    have ecell : (g'.add rF.gh).ac = (spCell t S ℓ).add ((curCell t).add rF.gh.ac) := by
      ext <;> simp [g', Ghost.cur] <;> omega
    let ss := setStackAt m.stacks m.current (m.stackOf m.current).closeFrame
    have h₁ := hh.reAC (m' := { m with stacks := ss }) (g := g') (gF := rF.gh) rfl rfl
      (by funext γ; simp [g', Ghost.cur, Ghost.add, Ghost.ofAC, Ghost.unit])
      (by funext x; simp [g', Ghost.cur, Ghost.add, Ghost.ofAC, Ghost.unit])
      (by funext x y; simp [g', Ghost.cur, Ghost.add, Ghost.ofAC, Ghost.unit])
      (by rw [ecell]; exact hv')
      (by
        rw [ecell]
        exact hM.restack hsa' rfl rfl (fun h => absurd (h m.current) (by rw [hS]; simp))
          (fun k => by simp [spCell, entCell]) (fun k n => by simp [spCell, entCell])
          (fun v => by simp [spCell, entCell]))
    exact ⟨(), _, _, hrun, h₁, gres_sep (cur_intro t) (sp_intro t S ℓ),
      ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩⟩

/-! ## Thread locality of the frame steps -/

/-- `enterFrame` reads and changes only the stack states: its run with a record in front. -/
theorem RunFp.enterFrame {F : Array FootprintEntry} {m₀ : Mem} : RunFp F m₀ Zig.enterFrame := by
  unfold RunFp
  have hb : ((m₀.withFp F).stackOf (m₀.withFp F).current).budget = (m₀.stackOf m₀.current).budget :=
    rfl
  cases h : (m₀.stackOf m₀.current).budget with
  | none => rw [enterFrame_run_none h, enterFrame_run_none (hb.trans h)]; rfl
  | some S =>
    by_cases hf : m₀.stackDepth m₀.current + frameBase ≤ S
    · rw [enterFrame_run_fits h hf, enterFrame_run_fits (hb.trans h) hf]; rfl
    · rw [enterFrame_overflow h (Nat.lt_of_not_le hf),
        enterFrame_overflow (hb.trans h) (Nat.lt_of_not_le hf)]; rfl

/-- A change of the stack states only is a step outside every frame that revives no byte. -/
theorem stacksStep {m : Mem} (hF : Heap) (ss : Array StackState) :
    FStepIn hF m { m with stacks := ss } ∧ m.NoRevive { m with stacks := ss } :=
  ⟨.of_stepIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
      Nat.le_refl _, fun _ he => .inl he, fun _ he => .inl he⟩ (fun _ _ h => h)
      (fun _ he hn => absurd he hn) (fun _ h => h), fun _ _ _ h => h⟩

/-- **Entering a frame is local**: it touches no byte and reads no record. -/
@[fsym_provider] theorem ThreadLocal.enterFrame {P : FAssn} : ThreadLocal P Zig.enterFrame :=
  ThreadLocal.intro fun m _ _ _ _ _ _ => ⟨RunFp.enterFrame, fun v m₀ e => by
    cases h : (m.noFp.stackOf m.noFp.current).budget with
    | none =>
      rw [enterFrame_run_none h] at e
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      exact ⟨FStepIn.refl _ _, fun _ _ _ h => h⟩
    | some S =>
      by_cases hf : m.noFp.stackDepth m.noFp.current + frameBase ≤ S
      · rw [enterFrame_run_fits h hf] at e
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
        exact ⟨(stacksStep _ _).1, fun _ _ _ h => h⟩
      · have := enterFrame_overflow h (by omega)
        rw [e] at this; cases this⟩

/-- `leaveFrame` reads and changes only the stack states: its run with a record in front. -/
theorem RunFp.leaveFrame {F : Array FootprintEntry} {m₀ : Mem} : RunFp F m₀ Zig.leaveFrame := by
  unfold RunFp
  have hb : ((m₀.withFp F).stackOf (m₀.withFp F).current).budget = (m₀.stackOf m₀.current).budget :=
    rfl
  cases h : (m₀.stackOf m₀.current).budget with
  | none => rw [leaveFrame_run_none h, leaveFrame_run_none (hb.trans h)]; rfl
  | some S => rw [leaveFrame_run_some h, leaveFrame_run_some (hb.trans h)]; rfl

/-- **Leaving a frame is local**: it touches no byte and reads no record. -/
@[fsym_provider] theorem ThreadLocal.leaveFrame {P : FAssn} : ThreadLocal P Zig.leaveFrame :=
  ThreadLocal.intro fun m _ _ _ _ _ _ => ⟨RunFp.leaveFrame, fun v m₀ e => by
    cases h : (m.noFp.stackOf m.noFp.current).budget with
    | none =>
      rw [leaveFrame_run_none h] at e
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      exact ⟨FStepIn.refl _ _, fun _ _ _ h => h⟩
    | some S =>
      rw [leaveFrame_run_some h] at e
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      exact ⟨(stacksStep _ _).1, fun _ _ _ h => h⟩⟩

attribute [fsym] FTotalTriple.allocStack_sp FTotalTriple.free_sp FTotalTriple.enterFrame_sp
  FTotalTriple.leaveFrame_sp

/-- A stack block's charge for the arithmetic solver (`omega` reads `max`, not `Nat.max`). -/
@[fsym_arith] theorem stackCharge_eq (size align : Nat) :
    stackCharge size align = size + Max.max align 1 :=
  rfl

end Full
end Zig
