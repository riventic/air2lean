import ZigLean.Conc.Word
import ZigLean.Conc.WeakCasLemmas

namespace Zig
namespace Conc
namespace Word
open Proto
variable {n nb : Nat} {W : Word n nb}

/-- Weak success is an RMW; failure preserves history and may read the expected value. -/
theorem Ok.weakCas {m m' : Mem} {t c : Nat} {succ fail : AtomicOrder} {exp new : BitVec n}
    {r : Option (BitVec n)} (hw : W.Ok m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr exp new).run m).run = some (.ok (r, m'))) :
    W.Ok m' ∧ W.Op t m m' ∧
    ((r = none ∧ (W.hist m)[(W.hist m).size - 1]!.Val exp ∧ W.Holds m' new ∧
      W.hist m' = (W.hist m).push (rmwEnt m' t succ (W.hist m)[(W.hist m).size - 1]! new) ∧
      (succ.isAcq = true →
        VClock.le (W.hist m)[(W.hist m).size - 1]!.relClock (m'.clocks[t]!) = true)) ∨
     (∃ j old, r = some old ∧ True ∧ j < (W.hist m).size ∧ (W.hist m)[j]!.Val old ∧
      Floor (W.hist m) (m.clocks[t]!) j ∧
      (fail.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true) ∧
      W.hist m' = W.hist m)) := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, -, hl, hpos, hold, hcase⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, -, -, -, -, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, hop₁, hh₁, -, -⟩ := hw.prep hc ht hcs rfl hl
  obtain ⟨-, h0, hch, -, -⟩ := hw₁.loc li l hl'
  have hl0 := (loc_get hl').2.2
  have hct : t < m₁.clocks.size := by rw [hop₁.csize, hcs]; exact ht
  have hsz := hist_size hl'
  rcases hcase with ⟨rfl, hsp, rfl, -, hm'⟩ | ⟨hne, rfl, hm'⟩
  · obtain ⟨j, hstrong⟩ := weakCasOpts_strong (by simpa [hsp] using hpos)
    have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hstrong hold
    rw [hl0] at hpl hold hm'
    rw [hpl] at hold hm'
    rw [W.sz_eq] at hm'
    obtain ⟨hw₂, hop₂, hh₂⟩ := hw₁.record hop₁.current
      (by rw [hop₁.threads]; exact ht) (by rw [hop₁.csize, hop₁.threads]; exact hcs)
      (k := .atomicWrite) rfl
    have hl₂ : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li l := hl'
    obtain ⟨hw', hop₃, hU, hh, hacq⟩ := hw₂.rmwAt (M := m') (ord := succ) (new := new) hl₂ hop₂.current
      (by rw [hop₂.threads, hop₁.threads]; exact ht)
      (by rw [hop₂.csize, hop₂.threads, hop₁.csize, hop₁.threads]; exact hcs) hm'
    refine ⟨hw', hop₁.trans (hop₂.trans hop₃), .inl ⟨rfl, ?_, hU,
      by rw [hh, hh₂, hh₁], by rw [← hh₁]; exact hacq⟩⟩
    rw [← hh₁, hsz]; exact val_of hl' (by omega) hold
  · obtain ⟨j, hread⟩ := weakCasOpts_read hpos
    have hlt := readOpts_lt hread
    have hfl := floor_le hread
    rw [hl0] at hlt hold hm'
    rw [hm']
    obtain ⟨hfl', hacq, hh, hw', hop₂⟩ := hw₁.read (ord := fail) hl' hop₁ hct hlt hfl
    refine ⟨hw', hop₁.trans hop₂, .inr ⟨pos, old, rfl, trivial, by rw [← hh₁, hsz]; exact hlt,
      by rw [← hh₁]; exact val_of hl' hlt hold, by rw [← hh₁]; exact hfl',
      by rw [← hh₁]; exact hacq, by rw [hh, hh₁]⟩⟩

theorem Ok.weakCas_noErr {m : Mem} {c : Nat} {succ fail : AtomicOrder} {exp new : BitVec n}
    (hw : W.Ok m) (ht : m.current < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hcr : c < weakCasCount n succ nb W.ptr exp m ∨ weakCasCount n succ nb W.ptr exp m = 0 ∧ c = 0)
    (e : Error) : ((cmpxchgWeakAt c succ fail nb W.ptr exp new).run m).run ≠ some (.error e) := by
  obtain ⟨blk, -, haw, hnr, hloc⟩ := hw.prep_ok ht (k := .atomicRead) rfl
  have hprep : ∀ e, ((weakCasPrep n nb W.ptr exp).run m).run ≠ some (.error e) :=
    weakCasPrep_noErr (casPrep_noErr haw hnr hloc)
  refine cmpxchgWeakAt_noErr hprep (fun li opts m₁ hp => ?_)
    (fun li opts m₁ hp e he => ?_) e
  · obtain ⟨b, blk', o, ha, -, hl, rfl⟩ := weakCasPrep_ok hp
    rw [haw] at ha; cases ha
    obtain ⟨h0, -, hval⟩ := hw.opts ht hcs rfl hl
    have hne := casOpts_ne (e := exp) (m := m₁) (li := li) h0
    have hcnt := weakOptCount_eq (succ := succ) hp
    have hsz : 0 < (weakCasOpts m₁ li exp (casOpts m₁ li exp)).size := by
      simp only [weakCasOpts, Array.size_append, Array.size_map]
      omega
    have hc : c < (weakCasOpts m₁ li exp (casOpts m₁ li exp)).size := by rw [hcnt] at hcr; omega
    let choice := (weakCasOpts m₁ li exp (casOpts m₁ li exp))[c]
    have hchoice : (weakCasOpts m₁ li exp (casOpts m₁ li exp))[c]? = some choice :=
      Array.getElem?_eq_getElem hc
    obtain ⟨j, hread⟩ := weakCasOpts_read hchoice
    exact ⟨choice.1, choice.2, hchoice, hval _ (readOpts_lt hread)⟩


  · obtain ⟨b, blk', o, ha, -, hl, -⟩ := weakCasPrep_ok hp
    rw [haw] at ha; cases ha
    rw [W.sz_eq] at hl
    obtain ⟨l, hl', hw₁, hop₁, -⟩ := hw.prep rfl ht hcs rfl hl
    obtain ⟨blk₁, -, ha₁, hnr₁, -⟩ := hw₁.prep_ok (by rw [hop₁.current, hop₁.threads]; exact ht)
      (k := .atomicWrite) rfl
    rw [casMarkWrite_run ha₁ hnr₁] at he
    cases he

end Word
end Conc
end Zig
