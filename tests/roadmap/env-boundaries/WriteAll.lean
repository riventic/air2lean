import ZigLean.Env

/-!
# E03 write-all client under the selected environment contract

`writeAllClose_spec` holds for every state type, every `Ops` and every allowed error list
that satisfy `Contract`: it either writes the whole buffer or returns the first error, and
in both cases closes the handle exactly once. `Scripted` is a non-vacuous contract instance
driven by an explicit result oracle whose wall clock runs backwards.
-/
namespace Zig.Env.Client
open Zig.Env

/-- Every event is a write to `h`. -/
def OnlyWrites (h : Handle) (evs : List Event) : Prop := ∀ ev ∈ evs, ∃ c, ev = .wrote h c

theorem OnlyWrites.cons {h c evs} (hw : OnlyWrites h evs) :
    OnlyWrites h (.wrote h c :: evs) := by
  intro ev hev
  rcases List.mem_cons.mp hev with rfl | hev
  · exact ⟨c, rfl⟩
  · exact hw ev hev

theorem OnlyWrites.not_closed {h evs} (hw : OnlyWrites h evs) : Event.closed h ∉ evs := by
  intro hm
  obtain ⟨_, hc⟩ := hw _ hm
  cases hc

theorem writeAll_spec {σ : Type} {ops : Ops σ} {errs : List IoError} (hc : Contract ops errs)
    (h : Handle) (buf : List UInt8) (w : World σ) (hopen : ops.isOpen w.env h = true) :
    ∃ r w' evs, writeAll ops h buf w = .ok (r, w') ∧ w'.log = w.log ++ evs ∧
      (∀ h', ops.isOpen w'.env h' = ops.isOpen w.env h') ∧
      ops.monotonicNow w.env ≤ ops.monotonicNow w'.env ∧
      ((r = .ok () ∧ OnlyWrites h evs ∧ written evs = buf) ∨
       (∃ e pre rest, r = .error e ∧ e ∈ errs ∧ evs = pre ++ [.failed h e] ∧
          OnlyWrites h pre ∧ written pre ++ rest = buf ∧ rest ≠ [])) := by
  rw [writeAll]
  by_cases hb : buf.isEmpty = true
  · have hnil : buf = [] := List.isEmpty_iff.mp hb
    subst hnil
    refine ⟨.ok (), w, [], by simp, by simp, fun _ => rfl, Nat.le_refl _, Or.inl ⟨rfl, ?_, rfl⟩⟩
    intro ev hev
    cases hev
  · have hne : buf ≠ [] := fun hnil => hb (by simp [hnil])
    simp only [hb, hopen, ite_true, Bool.false_eq_true, ite_false]
    have hframe := fun h' => hc.writeFrame w.env h buf h' hopen
    have hmono := hc.writeMonotone w.env h buf
    rcases hw : ops.write w.env h buf with ⟨res, s⟩
    rw [hw] at hframe hmono
    cases res with
    | error e =>
      refine ⟨.error e, ⟨s, w.log ++ [.failed h e]⟩, [.failed h e], rfl, rfl,
        hframe, hmono, Or.inr ⟨e, [], buf, rfl, hc.writeError _ _ _ _ _ hopen hw, rfl,
        ?_, by simp [written], hne⟩⟩
      intro ev hev
      cases hev
    | ok n =>
      obtain ⟨hpos, hle⟩ := hc.writeProgress _ _ _ _ _ hopen hne hw
      simp only [hpos, hle, and_self, dite_true]
      have hopen' : ops.isOpen s h = true := by rw [hframe h]; exact hopen
      obtain ⟨r, w', evs, hrun, hlog, ho, hm, hcase⟩ :=
        writeAll_spec hc h (buf.drop n) ⟨s, w.log ++ [.wrote h (buf.take n)]⟩ hopen'
      refine ⟨r, w', .wrote h (buf.take n) :: evs, hrun, by simp [hlog],
        fun h' => by rw [ho h', hframe h'], Nat.le_trans hmono hm, ?_⟩
      rcases hcase with ⟨hr, hws, hwr⟩ | ⟨e, pre, rest, hr, he, hevs, hws, hwr, hrest⟩
      · exact Or.inl ⟨hr, hws.cons, by simp [written, hwr]⟩
      · refine Or.inr ⟨e, .wrote h (buf.take n) :: pre, rest, hr, he, by simp [hevs], hws.cons,
          ?_, hrest⟩
        simp [written, hwr]
termination_by buf.length
decreasing_by simp only [List.length_drop]; omega

/-- The E03 client theorem: under the contract only, `writeAllClose` never faults, writes
the whole buffer or stops at its first error, closes `h` exactly once, leaves other handles
unchanged and does not move the monotonic clock backwards. -/
theorem writeAllClose_spec {σ : Type} {ops : Ops σ} {errs : List IoError}
    (hc : Contract ops errs) (h : Handle) (buf : List UInt8) (w : World σ)
    (hopen : ops.isOpen w.env h = true) :
    ∃ r w' evs, writeAllClose ops h buf w = .ok (r, w') ∧
      w'.log = w.log ++ evs ++ [.closed h] ∧
      (evs ++ [.closed h]).count (.closed h) = 1 ∧
      ops.isOpen w'.env h = false ∧
      (∀ h', h' ≠ h → ops.isOpen w'.env h' = ops.isOpen w.env h') ∧
      ops.monotonicNow w.env ≤ ops.monotonicNow w'.env ∧
      ((r = .ok () ∧ OnlyWrites h evs ∧ written evs = buf) ∨
       (∃ e pre rest, r = .error e ∧ e ∈ errs ∧ evs = pre ++ [.failed h e] ∧
          OnlyWrites h pre ∧ written pre ++ rest = buf ∧ rest ≠ [])) := by
  obtain ⟨r, w', evs, hrun, hlog, ho, hm, hcase⟩ := writeAll_spec hc h buf w hopen
  have hopen' : ops.isOpen w'.env h = true := by rw [ho h]; exact hopen
  refine ⟨r, ⟨ops.close w'.env h, w'.log ++ [.closed h]⟩, evs, ?_, by simp [hlog], ?_,
    hc.closeReleases _ _ hopen', fun h' hne => by rw [hc.closeFrame _ _ _ hne, ho h'],
    Nat.le_trans hm (hc.closeMonotone _ _), hcase⟩
  · simp [writeAllClose, hrun, closeOnce, hopen']
  · have hnot : Event.closed h ∉ evs := by
      rcases hcase with ⟨_, hws, _⟩ | ⟨e, pre, _, _, _, hevs, hws, _, _⟩
      · exact hws.not_closed
      · subst hevs
        intro hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hws.not_closed hmem
        · simp at hmem
    simp [List.count_append, List.count_eq_zero.mpr hnot]

/-! ## A non-vacuous scripted instance

Write results come from an explicit oracle script. A scripted count is clamped into the
contract range; an exhausted script accepts everything. The wall clock decreases at every
operation while the monotonic clock increases, so the contract does not order them. -/

structure Scripted where
  script : List (Except IoError Nat)
  opened : Handle → Bool
  mono : Nat
  wall : Int

def Scripted.tick (s : Scripted) : Scripted := { s with mono := s.mono + 1, wall := s.wall - 1 }

def scriptedOps : Ops Scripted where
  monotonicNow s := s.mono
  wallNow s := s.wall
  isOpen s h := s.opened h
  read s _ _ := (.ok [], s.tick)
  write s _ buf :=
    match s.script with
    | [] => (.ok buf.length, s.tick)
    | .error e :: rest => (.error e, { s.tick with script := rest })
    | .ok n :: rest => (.ok (max 1 (min n buf.length)), { s.tick with script := rest })
  close s h := { s.tick with opened := fun h' => if h' = h then false else s.opened h' }

def allErrors : List IoError :=
  [.wouldBlock, .brokenPipe, .noSpaceLeft, .accessDenied, .inputOutput, .connectionReset]

theorem mem_allErrors (e : IoError) : e ∈ allErrors := by cases e <;> simp [allErrors]

theorem scripted_contract : Contract scriptedOps allErrors where
  readBound := by intro s h max bytes s' _ hr; simp [scriptedOps] at hr; simp [hr.1]
  readError := by intro s h max e s' _ hr; simp [scriptedOps] at hr
  readFrame := by intro s h max h' _; rfl
  writeProgress := by
    intro s h buf n s' _ hne hw
    have hlen : 0 < buf.length := List.length_pos_iff.mpr hne
    simp only [scriptedOps] at hw
    split at hw
    · simp at hw; omega
    · simp at hw
    · simp at hw; omega
  writeError := fun _ _ _ e _ _ _ => mem_allErrors e
  writeFrame := by
    intro s h buf h' _
    simp only [scriptedOps]
    split <;> rfl
  closeReleases := by intro s h _; simp [scriptedOps]
  closeFrame := by intro s h h' hne; simp [scriptedOps, hne]
  readMonotone := by intro s h max; simp [scriptedOps, Scripted.tick]
  writeMonotone := by
    intro s h buf
    simp only [scriptedOps]
    split <;> simp [Scripted.tick]
  closeMonotone := by intro s h; simp [scriptedOps, Scripted.tick]

theorem scripted_wall_runs_backwards (s : Scripted) (h : Handle) :
    scriptedOps.wallNow (scriptedOps.close s h) < scriptedOps.wallNow s ∧
      scriptedOps.monotonicNow s < scriptedOps.monotonicNow (scriptedOps.close s h) := by
  simp [scriptedOps, Scripted.tick]; omega

def demoWorld (script : List (Except IoError Nat)) : World Scripted :=
  ⟨⟨script, fun h => h == 3, 0, 0⟩, []⟩

/-- Two partial writes, then the rest: five bytes across three events, then one close. -/
theorem demo_partial :
    (writeAllClose scriptedOps 3 [1, 2, 3, 4, 5] (demoWorld [.ok 2, .ok 0])).map
        (fun x => (x.1, x.2.log)) =
      .ok (.ok (), [.wrote 3 [1, 2], .wrote 3 [3], .wrote 3 [4, 5], .closed 3]) := by
  simp [writeAllClose, writeAll, closeOnce, demoWorld, scriptedOps, Scripted.tick, Except.map]

/-- The first error stops the loop; the handle is still closed once. -/
theorem demo_error :
    (writeAllClose scriptedOps 3 [1, 2, 3] (demoWorld [.ok 1, .error .brokenPipe, .ok 9])).map
        (fun x => (x.1, x.2.log)) =
      .ok (.error .brokenPipe, [.wrote 3 [1], .failed 3 .brokenPipe, .closed 3]) := by
  simp [writeAllClose, writeAll, closeOnce, demoWorld, scriptedOps, Scripted.tick, Except.map]

/-- A closed handle faults instead of reaching the environment. -/
theorem demo_closed :
    (writeAllClose scriptedOps 4 [1] (demoWorld [])).map (fun x => (x.1, x.2.log)) =
      .error (.closedHandle 4) := by
  simp [writeAllClose, writeAll, demoWorld, scriptedOps, Scripted.tick, Except.map]

end Zig.Env.Client
