import ZigLean.Sep.Full.RwLockBase

/-!
# The reader/writer lock's base at a fresh lock

(ledger #two-lock-product, item (5).) `FRw.Base` (`ZigLean/Sep/Full/RwLockBase.lean`) is the
reader/writer lock's base in the two-lock product. This file proves that it holds at a fresh lock,
once for every reader/writer lock `W` and every program's facts `E`, so a program's start is the
two-lock pair's start and this lemma, with no proof of its own.

- `Word.Ok.init`: a word no atomic op has touched is `Ok`, with one message, its current value,
  written at no clock. For every word (`Word n nb`), block and live set.
- `FRw.Owns.of_allLe`: a resource whose every access happened before every thread is owned through
  the word.
- `FRw.Base.start`: the base at a fresh lock. Every thread is out of the rwlock's, the condition's
  and the semaphore's code, and out of both mutexes' code or ended; the three words (the state
  word, the condition's state and epoch) are `Ok` with one message each (the state word's
  `RwState.encode 0 0 false`, the condition's state's `0`), the epoch's below every clock; no
  thread is in the futex queue. The rest is the state word's cells, the protected resource `rF`
  (with `R`, owned through the word) and the rest of the rest `rO`, which holds the condition's
  words' cells, a pin of the lock's block and the program's read-shared bytes.
-/

namespace Zig

namespace Conc.Word

variable {n nb : Nat} {W : Word n nb} {A : ThreadId → Prop}

/-- **A word before its first atomic op** (the start of a protocol): its block is live with the
word's bytes aligned in it, no atomic location overlaps it or is at its offset (`hat`), it holds
`v`, and each access to it happened before every thread of the live set `A`. The word is `Ok`
with one message, the value `v`, written at no clock (below every clock). -/
theorem Ok.init {m : Mem} {v : BitVec n}
    (hblk : ∃ blk, m.blocks[W.b]? = some blk ∧ blk.live = true ∧ W.o + nb ≤ blk.bytes.size ∧
      (blk.addr + W.o) % nb = 0 ∧ blk.kind ≠ .constGlobal ∧ blk.kind.mappedLo ≤ W.o)
    (hat : ∀ l ∈ m.atomics, l.block = W.b →
      W.o + nb ≤ l.off ∨ (l.off < W.o ∧ l.off + l.len ≤ W.o))
    (hv : W.Holds m v) (hfp : ∀ e ∈ m.footprint, W.Hits e → AllLeOn A m e.clock) :
    W.Ok m A ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val v ∧
      ∀ c, VClock.le (W.hist m)[0]!.clock c = true := by
  have hnb : 0 < nb := by rcases W.n_ok with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hno : ∀ i l, ¬ W.Loc m i l := fun i l hl => by
    obtain ⟨hi, e, -⟩ := loc_get hl
    obtain ⟨hb, ho⟩ := loc_at hl
    have := hat l (e ▸ Array.getElem_mem hi) hb
    omega
  refine ⟨⟨hblk, fun l hl hb h1 h2 => ?_, fun i l h => absurd h (hno i l), hfp, ⟨v, hv⟩,
    fun i l h => absurd h (hno i l)⟩, ?_, ?_, ?_⟩
  · have := hat l hl hb
    omega
  · rw [hist_none hno]; rfl
  · rw [hist_none hno]; exact hv
  · intro c; rw [hist_none hno]; exact VClock.le_default c

end Conc.Word

namespace Full

open FAssn Conc Proto

namespace FRw

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C} {W : FRw γ X Y M L C S}

/-- **A resource whose every access happened before every thread is owned through the word**
(the start: the one thread that made the resource is every thread's ancestor). -/
theorem Owns.of_allLe {G : ThreadId → γ} {m : Mem} {r : Res}
    (h : ∀ e ∈ m.footprint, (e.Touches r.excl ∨ e.Touches r.shared ∨ m.blocks.size ≤ e.block) →
      AllLe m e.clock) : W.Owns G m r :=
  fun e he ht => .inl fun u hu _ => h e he ht u hu

namespace Base

/-- **The base at a fresh lock** (module doc), for every reader/writer lock and every program's
facts `E`: the rest is the state word's cells, the protected resource `rF` and the rest of the
rest `rO`. `rO` holds the cells of the condition's two words (`hcw`: what the semaphore's
primitive's rest asks), a pin of the lock's block (`hpin`) and the program's read-shared bytes
(`hio`); the program's threads and read-shared region are its own facts (`hthr`, `hsh`). -/
theorem start {E : FClient X} {Sz : Nat} {K : BlockKind} {G : ThreadId → γ} {m : Mem}
    {rF rO : Res} {e0 : BitVec 32}
    (hw : ∀ u, W.ph (G u) = .out) (hc : ∀ u, C.ph (G u) = .out) (hs : ∀ u, S.ph (G u) = .out)
    (hm : ∀ u, M.ph (G u) = .out ∨ M.ph (G u) = .gone)
    (hl : ∀ u, L.ph (G u) = .out ∨ L.ph (G u) = .gone)
    (hst : W.st.Ok m fun u => M.ph (G u) ≠ .gone) (hst1 : (W.st.hist m).size = 1)
    (hst0 : (W.st.hist m)[0]!.Val (RwState.encode 0 0 false))
    (hS : C.S.Ok m) (hS1 : (C.S.hist m).size = 1) (hS0 : (C.S.hist m)[0]!.Val (0 : BitVec 32))
    (hE : C.Ep.Ok m) (hE1 : (C.Ep.hist m).size = 1) (hE0 : (C.Ep.hist m)[0]!.Val e0)
    (hEc : AllLe m (C.Ep.hist m)[0]!.clock) (hq : m.waiters = #[])
    (hR : W.R (W.xs G) rF) (hown : W.Owns G m rF)
    (hoff : ∀ l, W.st.In l → rF.heap l = none ∧ rO.heap l = none)
    (hd : FHeap.Disjoint rF.heap rO.heap)
    (hcw : ∀ Wd : Word 32 4, Wd = C.S ∨ Wd = C.Ep →
      ∃ rY, rO = rsum (Wd.cellsR m) rY ∧ ∀ l, Wd.In l → rY.heap l = none)
    (hpin : rO.Pins W.st.b Sz K)
    (hthr : E.T (W.xs G) m.threads) (hsh : ReadShared E.Rg m)
    (hio : ∃ r, E.Io r ∧ ∀ l fc, r.heap l = some fc → rO.heap l = some fc)
    (hlF : ∀ l, rF.owned l ≠ none → m.heap l ≠ none)
    (hlO : ∀ l, rO.owned l ≠ none → m.heap l ≠ none) :
    W.Base E Sz K G (rsum (W.st.cellsR m) (rsum rF rO)) m := by
  -- a byte of `rO` is no byte of the state word and no byte of `rF`
  have hOst : ∀ l, rO.heap l ≠ none → ¬ W.st.In l := fun l h hin => h (hoff l hin).2
  have hOF : ∀ l, rO.heap l ≠ none → rF.heap l = none := fun l h => (hd l).resolve_right h
  have hWok : ∀ Wd : Word 32 4, Wd = C.S ∨ Wd = C.Ep → Wd.Ok m := fun Wd h => by
    rcases h with rfl | rfl
    · exact hS
    · exact hE
  exact {
    cl := by
      obtain ⟨r, hr, hsub⟩ := hio
      refine ⟨hthr, hsh, r, hr, fun l fc h => ?_⟩
      have hO := hsub l fc h
      have hne : rO.heap l ≠ none := by rw [hO]; nofun
      simp only [FHeap.union_apply, cellsAt_none (hOst l hne), hOF l hne, Option.none_or]
      exact hO
    winv := Inv.start hst hw hst1 hst0 hR hoff hd hown
    sub := ⟨⟨FCond.Inv.start hS1 hS0 hE1 hE0 hc hq, fun Wd hWd => by
        obtain ⟨rY, e, hY⟩ := hcw Wd hWd
        have hin : ∀ l, Wd.In l → rO.heap l ≠ none := fun l hl => by
          rw [e]
          simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
          exact fun h => absurd h (cellsAt_some hl ((hWok Wd hWd).cellIn hl))
        have hdS : FHeap.Disjoint (W.st.cellsR m).heap (Wd.cellsR m).heap := fun l => by
          by_cases hl : Wd.In l
          · exact .inl (cellsAt_none (hOst l (hin l hl)))
          · exact .inr (cellsAt_none hl)
        have hdF : FHeap.Disjoint rF.heap (Wd.cellsR m).heap := fun l => by
          by_cases hl : Wd.In l
          · exact .inl (hOF l (hin l hl))
          · exact .inr (cellsAt_none hl)
        refine ⟨hWok Wd hWd, rsum (W.st.cellsR m) (rsum rF rY), ?_, fun l hl => ?_⟩
        · rw [e, rsum_left_comm hdF, rsum_left_comm hdS]
        · simp only [FHeap.union_apply, cellsAt_none (hOst l (hin l hl)), hOF l (hin l hl),
            hY l hl, Option.none_or]⟩,
      FSem.Inv.start hS1 hS0 hc hs⟩
    win := FCond.Win1.of_out hc fun k hk => by
      obtain rfl : k = 0 := by omega
      exact .inr (.inr fun u hu _ => hEc u hu)
    shares := fun u q H h => by rw [hw u] at h; cases h
    pin := Res.Pins.right (Res.Pins.right hpin)
    wt := fun u h => by rw [hs u] at h; cases h
    nap := fun u h => by
      rcases h with ⟨h1, -, h3⟩ | h
      · rcases hl u with e | e
        · exact absurd e h1
        · exact absurd e h3
      · exact absurd (Prod.ext (hc u) (hs u)) h
    live := fun l h => by
      rcases (Res.owned_sep rfl rfl).mp h with h | h
      · by_cases hin : W.st.In l
        · exact hst.cellIn hin
        · exact absurd (cellsAt_owned_none hin) h
      · rcases (Res.owned_sep rfl rfl).mp h with h | h
        · exact hlF l h
        · exact hlO l h
    rdm := fun u h => by rw [hw u] at h; rcases h with h | h <;> cases h
    mal := fun u h => by rcases hm u with e | e <;> rw [e] at h <;> cases h }

end Base

end FRw

end Full
end Zig
