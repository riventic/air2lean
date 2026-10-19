import ZigLean.Sep.Full.AutoAll

/-! The token rules of a stack budget (`docs/sep-full-state.md` §Stack depth, step 5,
`ZigLean/Sep/Full/Stack.lean`): kernel-checked instances on the start memory with a main-thread
budget of 16 bytes (`FTotalTriple.run_init_stack`'s memory).

* `start_holds`: the start memory holds `main`'s stack mode `cur 0 ⋆ sp 0 16 0 ⋆ unmetered`
  (`initRes_holds_stack`).
* `cur_stop_cx`: after a stop at thread 1 the same resource is not held: `cur 0` names the
  running thread, so a thread's part may hold it only while the thread runs (the parts of
  `FOwned` hold none, `FOwned.noCur`; the thread rules hand it to a step).
* `cur_no_mint`: `¬ EUpd emp (cur 0)`: next to a frame that holds `cur 0` a second one is
  invalid, so no judgment creates the running thread's token.
* `push_over_cx`: no total push from `sp 0 16 16` (a frame of 16 bytes when the budget is used
  up): in the memory after one frame the push overflows. So the fit premise `D + c ≤ S` of the
  push rules is needed.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

namespace StackRules

/-- An address space of 4096 + 256 bytes. -/
def small : Placement := { propose := fun _ => none, addrLimit := 4096 + 256 }

theorem reserve₀ : ((Mem.ofGlobals small []).reserveAt? 0 16).isSome := by decide +kernel

/-- The start memory with a main-thread budget of 16 bytes. -/
abbrev m₀ : Mem := (Mem.ofGlobals small []).withStack 16

/-- `main`'s resource at the start. -/
abbrev r₀ : Res := ⟨(initRes small []).heap, (initRes small []).know,
  (initRes small []).gh.add (Ghost.stackStart 16)⟩

abbrev e₀ : Res := ⟨FHeap.empty, Know.none, Ghost.unit⟩

theorem start_holds : Holds m₀ r₀ e₀ ∧ (globals [] ⋆ stackStart 16) r₀ :=
  initRes_holds_stack small [] (by simp) 16 reserve₀

theorem fseq₀ : m₀.FSeq := (Mem.init_fseq small [] (by simp [Mem.GlobalsFit])).withStack 16

theorem cur₀ : 0 < (r₀.gh.add e₀.gh).ac.ex .cur (0, 0) := by
  simp [Ghost.stackStart, Ghost.cur, curCell]; omega

/-- **`cur 0` names the running thread**: a stop at thread 1 does not keep what the start
memory holds. -/
theorem cur_stop_cx : ¬ Holds { m₀ with current := 1 } r₀ e₀ := fun hh => by
  have := hh.ghost.2.2.2.cur (0, 0) cur₀
  simp at this

/-- **No `cur` from nothing**: a frame may hold the running thread's token, and then a second
one is invalid. -/
theorem cur_no_mint : ¬ EUpd emp (cur 0) := fun hu => by
  obtain ⟨r', hh', hc⟩ := hu m₀ e₀ r₀ start_holds.1.swap ⟨rfl, rfl, rfl⟩ fseq₀
  have hv := (hh'.ghost.1.1.2.2.2 .cur).2.2.2.1 (0, 0)
  obtain ⟨-, -, hg⟩ := hc
  have h1 : (r'.gh.add r₀.gh).ac.ex .cur (0, 0) = r'.gh.ac.ex .cur (0, 0) + r₀.gh.ac.ex .cur (0, 0) := rfl
  have h2 : r'.gh.ac.ex .cur (0, 0) = 1 := by rw [hg]; simp [Ghost.cur, curCell]
  have h3 : 0 < r₀.gh.ac.ex .cur (0, 0) := by simpa using cur₀
  omega

/-- One frame from the start: `main` holds `sp 0 16 16`, the frame's token and the rest. -/
theorem frame₁ : FTotalTriple (globals [] ⋆ stackStart 16) Zig.enterFrame
    (fun _ => (cur 0 ⋆ sp 0 16 16) ⋆ (ent 0 none 0 16 ⋆ (globals [] ⋆ unmetered))) := by
  unfold stackStart
  fsym

theorem budget₀ : (m₀.stackOf m₀.current).budget = some 16 := by decide +kernel

theorem depth₀ : m₀.stackDepth m₀.current + frameBase ≤ 16 := by decide +kernel

theorem over₁ : 16 < ({ m₀ with stacks := m₀.pushEntry none frameBase } : Mem).stackDepth
    ({ m₀ with stacks := m₀.pushEntry none frameBase } : Mem).current + frameBase := by decide +kernel

theorem budget₁ : (({ m₀ with stacks := m₀.pushEntry none frameBase } : Mem).stackOf
    ({ m₀ with stacks := m₀.pushEntry none frameBase } : Mem).current).budget = some 16 := by
  decide +kernel

/-- **No total push without room**: from `sp 0 16 16` (the budget used up by one frame) no
frame returns, whatever the postcondition. -/
theorem push_over_cx (Q : Unit → FAssn) : ¬ FTotalTriple (cur 0 ⋆ sp 0 16 16) Zig.enterFrame Q :=
  fun ht => by
    obtain ⟨hh, hp⟩ := start_holds
    obtain ⟨v, m₁, r₁, hrun, hh₁, hq, hs₁⟩ := frame₁.runs hh hp fseq₀
    have hm₁ : m₁ = { m₀ with stacks := m₀.pushEntry none frameBase } := by
      have := hrun.symm.trans (enterFrame_run_fits budget₀ depth₀)
      exact (Prod.mk.inj (Result.pure_inj this)).2
    subst hm₁
    obtain ⟨ra, rb, hd, rfl, ha, -⟩ := hq
    obtain ⟨w, m₂, hrun₂⟩ := ht.2 _ ra _ (Holds.split hd hh₁) ha hs₁
    have hov := enterFrame_overflow budget₁ over₁
    rw [hrun₂] at hov
    cases hov

end StackRules

#print axioms StackRules.start_holds
#print axioms StackRules.cur_stop_cx
#print axioms StackRules.cur_no_mint
#print axioms StackRules.push_over_cx
