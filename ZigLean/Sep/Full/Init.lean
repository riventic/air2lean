import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Mmap

/-!
# The memory at program start in the full-state logic (`docs/one-logic.md`, decision D1b)

A full-state triple quantifies over `Mem.FSeq` memories that hold its precondition. This module
shows that the memory at program start (`Mem.ofGlobals σ gs`, under every placement `σ`) is one
(`Mem.init_fseq`), and that it holds, with the empty frame, the resource `initRes σ gs` that owns
every global (`globals gs`): for global `j`, its initial bytes at block `j`, the knowledge of its
address (`known j A`, `A` a multiple of its alignment) and its full extent (`bext`, for a
non-empty global). `FTriple.run_init` applies a triple about the program's entry to the real run
from that memory.

The general pieces are `exts_ok` and `exts_true`: full extents `E` compose with the empty ghost
state, and they are true in a memory whose blocks have them.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Full extents -/

/-- Full extents compose with no other ghost state. -/
theorem exts_ok (E : BlockId → Option (Nat × BlockKind)) : Ghost.Ok (Ghost.exts E) Ghost.unit :=
  Ghost.ok_exts_change (E := fun _ => none) (by rw [Ghost.exts_none]; exact (GOk.unit ({} : Mem)).1)
    (fun _ _ => ECell.dormant_unit _)

/-- Full extents are true in a memory whose blocks have them (live, with a live byte). -/
theorem exts_true {m : Mem} {E : BlockId → Option (Nat × BlockKind)}
    (h : ∀ b S K, E b = some (S, K) → ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      blk.bytes.size = S ∧ blk.kind = K ∧ K.mappedLo < S) :
    ExtTrue m (Ghost.exts E) := fun b => by
  have hls : (Ghost.exts E).ls = Ghost.unit.ls := by
    funext γ e p; simp [Ghost.ls, Ghost.exts, Ghost.unit]
  show ECell.TrueIn (Ghost.exts E).ls m b ((Ghost.exts E).extent b)
  rw [hls]
  cases hE : E b with
  | none =>
    rw [show (Ghost.exts E).extent b = ECell.unit by simp [Ghost.exts, hE]]
    exact ExtTrue.unit m b
  | some SK =>
    obtain ⟨S, K⟩ := SK
    obtain ⟨blk, hb, hl, hs, hk, hlo⟩ := h b S K hE
    rw [show (Ghost.exts E).extent b = ECell.auth1 S K Frac.one by simp [Ghost.exts, hE]]
    refine ⟨fun S' K' hp => ?_, fun k hk' => ?_⟩
    · simp only [ECell.auth1] at hp
      split at hp
      · rename_i he; simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        exact ⟨blk, hb, hl, hs, hk, hlo⟩
      · cases hp
    · have := (ECell.dormant_unit _).req_auth1 (S := S) (K := K) (q := Frac.one) (k := k)
        (by rw [ECell.add_unit]; exact hk')
      subst this; exact ⟨blk, hb, hl, Nat.zero_le _, by rw [hk, hs]; exact hlo⟩

/-- A resource without bytes or knowledge, holding full extents that are true, holds alone. -/
theorem holds_exts {m : Mem} {h : FHeap} {k : Know} {E : BlockId → Option (Nat × BlockKind)}
    (hm : FMatch m h) (hk : Know.Sub k m.kn) (ht : ExtTrue m (Ghost.exts E)) :
    Holds m ⟨h, k, Ghost.exts E⟩ ⟨FHeap.empty, Know.none, Ghost.unit⟩ := by
  refine ⟨FHeap.disjoint_empty _, by simpa using hm, hk, fun _ h => h.elim, ?_, ?_, ?_⟩
  · exact exts_ok E
  · show ExtTrue m ((Ghost.exts E).add Ghost.unit); rw [Ghost.add_unit]; exact ht
  · show ClFresh m ((Ghost.exts E).add Ghost.unit); rw [Ghost.add_unit]; exact fun _ _ _ => rfl

/-! ## The memory at program start -/

/-- **The memory at program start is a `Mem.FSeq` memory**, under every placement, when the
globals fit (`Mem.GlobalsFit`, checked by the translator). -/
theorem _root_.Zig.Mem.init_fseq (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) : (Mem.ofGlobals σ gs).FSeq :=
  ⟨⟨⟨by simp, by simp⟩⟩, by simp [shapes, ShapesWF], Mem.ofGlobals_liveLayout σ gs h⟩

/-- The full extent of a global: `bext` for a non-empty one (an empty block has no live byte). -/
def gext (b : BlockId) (S : Nat) (K : BlockKind) : FAssn := if 0 < S then bext b S K else emp

/-- **Global `j` at program start**: its initial bytes `bs` at block `j`, at an address `A` that
is a multiple of its alignment `a`, the knowledge of `A`, and its full extent. -/
def gblock (j : BlockId) (bs : Array Byte) (a : Nat) (K : BlockKind) : FAssn :=
  FAssn.ex fun A => ⟪0 < a → A % a = 0⟫ ⋆
    (up (bytesAt ⟨some j, 0⟩ A bs.size K bs) ⋆ (known j A ⋆ gext j bs.size K))

/-- Every global at program start (`gblock`). -/
def globals (gs : List (Array Byte × Nat × BlockKind)) : FAssn :=
  sepN gs.length fun j => match gs[j]? with
    | some (bs, a, K) => gblock j bs a K
    | none => emp

private def emptyRes : Res := ⟨FHeap.empty, Know.none, Ghost.unit⟩

private def comb (r₁ r₂ : Res) : Res := ⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩

/-- The bytes of block `j` of `m`. -/
private def heapOf (m : Mem) (j : BlockId) : FHeap := fun l => if l.1 = j then m.fheap l else none

private def gextGh (j : BlockId) (S : Nat) (K : BlockKind) : Ghost :=
  if 0 < S then Ghost.atExt j (ECell.auth1 S K Frac.one) else Ghost.unit

/-- The resource of block `j` of `m`, in the shape of `gblock`. -/
private def gpart (m : Mem) (j : BlockId) : Res :=
  match m.blocks[j]? with
  | some blk => comb emptyRes (comb ⟨heapOf m j, Know.none, Ghost.unit⟩
      (comb ⟨FHeap.empty, Know.single (.addr j blk.addr), Ghost.unit⟩
        ⟨FHeap.empty, Know.none, gextGh j blk.bytes.size blk.kind⟩))
  | none => emptyRes

/-- The resource of blocks `0, …, n - 1` of `m`. -/
private def initR (m : Mem) : Nat → Res
  | 0 => emptyRes
  | n + 1 => comb (gpart m n) (initR m n)

/-- The full extents of the non-empty blocks `0, …, n - 1` of `m`. -/
private def initE (m : Mem) (n : Nat) : BlockId → Option (Nat × BlockKind) := fun b =>
  if b < n then (m.blocks[b]?).bind fun blk =>
    if 0 < blk.bytes.size then some (blk.bytes.size, blk.kind) else none
  else none

/-- The resource that owns every global at program start (`globals`). -/
def initRes (σ : Placement) (gs : List (Array Byte × Nat × BlockKind)) : Res :=
  initR (Mem.ofGlobals σ gs) gs.length

private theorem gpart_heap (m : Mem) (j : BlockId) : (gpart m j).heap = heapOf m j := by
  unfold gpart
  cases hb : m.blocks[j]? with
  | some blk => simp [comb, emptyRes]
  | none =>
    funext l; simp only [emptyRes, heapOf, FHeap.empty]
    split
    · rename_i h; obtain ⟨b, x⟩ := l; simp only at h; subst h
      simp [Mem.fheap, Mem.heap, hb]
    · rfl

private theorem initR_heap (m : Mem) (n : Nat) :
    (initR m n).heap = fun l => if l.1 < n then m.fheap l else none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext l
    show ((gpart m n).heap l).or ((initR m n).heap l) = _
    rw [gpart_heap, ih]; simp only [heapOf]
    by_cases h1 : l.1 = n
    · rw [ite_eq_left h1, ite_eq_right (show ¬ l.1 < n from h1 ▸ Nat.lt_irrefl n), ite_eq_left (show l.1 < n + 1 from h1 ▸ Nat.lt_succ_self n)]
      cases m.fheap l <;> rfl
    · rw [ite_eq_right h1]
      by_cases h2 : l.1 < n
      · rw [ite_eq_left h2, ite_eq_left (Nat.lt_succ_of_lt h2)]; rfl
      · rw [ite_eq_right h2, ite_eq_right (fun h3 => (Nat.lt_succ_iff_lt_or_eq.mp h3).elim h2 h1)]; rfl

private theorem initR_know (m : Mem) (n : Nat) : Know.Sub (initR m n).know m.kn := by
  induction n with
  | zero => exact fun _ h => h.elim
  | succ n ih =>
    refine Know.Sub.union ?_ ih
    unfold gpart
    cases hb : m.blocks[n]? with
    | none => exact fun _ h => h.elim
    | some blk =>
      rintro f (h | h | h | h)
      · exact h.elim
      · exact h.elim
      · subst h; exact ⟨blk, hb, rfl⟩
      · exact h.elim

private theorem gextGh_eq (j : BlockId) (S : Nat) (K : BlockKind) :
    gextGh j S K = Ghost.exts fun b => if b = j ∧ 0 < S then some (S, K) else none := by
  unfold gextGh
  ext1
  · funext γ; split <;> simp [Ghost.atExt, Ghost.exts, Ghost.unit]
  · funext b
    by_cases hb : b = j <;> by_cases hS : 0 < S <;> simp [hb, hS, Ghost.atExt, Ghost.exts, Ghost.unit]
  · funext b x; split <;> simp [Ghost.atExt, Ghost.exts, Ghost.unit]

private theorem exts_add {E E' : BlockId → Option (Nat × BlockKind)}
    (h : ∀ b, E b = none ∨ E' b = none) :
    (Ghost.exts E).add (Ghost.exts E') = Ghost.exts fun b => (E b).or (E' b) := by
  ext1
  · funext γ; simp [Ghost.add, Ghost.exts]
  · funext b
    simp only [Ghost.add, Ghost.exts]
    rcases h b with e | e <;> rw [e] <;> split <;> simp_all
  · funext b x; simp [Ghost.add, Ghost.exts]

private theorem initR_gh (m : Mem) (n : Nat) : (initR m n).gh = Ghost.exts (initE m n) := by
  induction n with
  | zero =>
    rw [show initE m 0 = fun _ => none by funext b; simp [initE], Ghost.exts_none]; rfl
  | succ n ih =>
    have hg : (gpart m n).gh = Ghost.exts fun b => if b = n then (m.blocks[b]?).bind fun blk =>
        if 0 < blk.bytes.size then some (blk.bytes.size, blk.kind) else none else none := by
      unfold gpart
      cases hb : m.blocks[n]? with
      | none =>
        rw [show (fun b => if b = n then (m.blocks[b]?).bind (fun blk : Block =>
            if 0 < blk.bytes.size then some (blk.bytes.size, blk.kind) else none) else none) =
            fun _ => none by funext b; by_cases h : b = n <;> simp [h, hb], Ghost.exts_none]; rfl
      | some blk =>
        simp only [comb, emptyRes, Ghost.unit_add, gextGh_eq]
        congr 1; funext b
        by_cases h : b = n
        · subst h; simp [hb]
        · simp [h]
    show (gpart m n).gh.add (initR m n).gh = _
    rw [hg, ih, exts_add (fun b => by by_cases h : b = n <;> simp [h, initE])]
    congr 1; funext b
    simp only [initE]
    by_cases h : b = n
    · rw [ite_eq_left h, ite_eq_right (show ¬ b < n from h ▸ Nat.lt_irrefl n), ite_eq_left (show b < n + 1 from h ▸ Nat.lt_succ_self n)]
      cases (m.blocks[b]?).bind _ <;> rfl
    · rw [ite_eq_right h]
      by_cases h' : b < n
      · rw [ite_eq_left h', ite_eq_left (Nat.lt_succ_of_lt h')]; rfl
      · rw [ite_eq_right h', ite_eq_right (fun h3 => (Nat.lt_succ_iff_lt_or_eq.mp h3).elim h' h)]; rfl

/-- **The memory at program start holds every global** (`globals gs`) with the empty frame, if
the globals' kinds have no mapping start (the translator's `.global` and `.constGlobal`). -/
theorem initRes_holds (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) :
    Holds (Mem.ofGlobals σ gs) (initRes σ gs) ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧
      globals gs (initRes σ gs) := by
  have hall := Mem.ofGlobals_block σ gs
  have hsize := Mem.ofGlobals_size σ gs
  unfold initRes
  generalize Mem.ofGlobals σ gs = m at hall hsize ⊢
  have hblk : ∀ j blk, m.blocks[j]? = some blk → j < gs.length ∧ gs[j]? = some (blk.bytes, blk.align, blk.kind) ∧
      blk.live = true ∧ blk.kind.mappedLo = 0 := by
    intro j blk hb
    have hj : j < gs.length := by
      have := (Array.getElem?_eq_some_iff.mp hb).1; rwa [hsize] at this
    obtain ⟨A, -, h⟩ := hall j hj
    rw [h] at hb; cases hb
    exact ⟨hj, by simp [List.getElem?_eq_getElem hj], rfl, hK _ (List.getElem_mem hj)⟩
  constructor
  · have hfh : (initR m gs.length).heap = m.fheap := by
      rw [initR_heap]; funext l
      split
      · rfl
      · rename_i h
        have : m.blocks.size ≤ l.1 := by rw [hsize]; omega
        simp [Mem.fheap, Mem.heap, Array.getElem?_eq_none this]
    have := holds_exts (m := m) (h := (initR m gs.length).heap) (k := (initR m gs.length).know) (E := initE m gs.length)
      (by rw [hfh]; exact FMatch.fheap m) (initR_know m _) (exts_true fun b S K hE => ?_)
    · rw [← initR_gh] at this; exact this
    · simp only [initE] at hE
      split at hE
      · cases hb : m.blocks[b]? with
        | none => simp [hb] at hE
        | some blk =>
          simp only [hb, Option.bind_some] at hE
          split at hE
          · rename_i hS; cases hE
            obtain ⟨-, -, hl, hlo⟩ := hblk b blk hb
            exact ⟨blk, rfl, hl, rfl, rfl, by rw [hlo]; exact hS⟩
          · cases hE
      · cases hE
  · unfold globals
    suffices ∀ n, n ≤ gs.length → sepN n (fun j => match gs[j]? with
        | some (bs, a, K) => gblock j bs a K | none => emp) (initR m n) from this _ (Nat.le_refl _)
    intro n hn
    induction n with
    | zero => exact ⟨rfl, rfl, rfl⟩
    | succ n ih =>
      refine ⟨gpart m n, initR m n, fun l => ?_, rfl, ?_, ih (by omega)⟩
      · rw [gpart_heap, initR_heap]; simp only [heapOf]
        by_cases h : l.1 = n
        · exact .inr (by simp [h])
        · exact .inl (by simp [h])
      · obtain ⟨A, hA, hb⟩ := hall n (by omega)
        have hg : gs[n]? = some gs[n] := List.getElem?_eq_getElem (by omega)
        obtain ⟨-, -, -, hlo⟩ := hblk n _ hb
        simp only at hlo
        rw [hg]
        show gblock n gs[n].1 gs[n].2.1 gs[n].2.2 (gpart m n)
        have hgp : gpart m n = comb emptyRes (comb ⟨heapOf m n, Know.none, Ghost.unit⟩
            (comb ⟨FHeap.empty, Know.single (.addr n A), Ghost.unit⟩
              ⟨FHeap.empty, Know.none, gextGh n gs[n].1.size gs[n].2.2⟩)) := by
          simp only [gpart, hb]
        rw [hgp]
        refine ⟨A, emptyRes, _, (FHeap.disjoint_empty _).symm, rfl, ⟨hA, rfl, rfl, rfl⟩,
          ⟨heapOf m n, Know.none, Ghost.unit⟩, _, fun _ => .inr rfl, rfl, ⟨?_, rfl, rfl⟩,
          ⟨FHeap.empty, Know.single (.addr n A), Ghost.unit⟩, _, fun _ => .inl rfl, rfl,
          ⟨rfl, rfl, rfl⟩, ?_⟩
        · refine ⟨n, rfl, Int.le_refl _, fun l => ?_⟩
          obtain ⟨b, x⟩ := l
          simp only [FHeap.erase, heapOf, Mem.fheap]
          by_cases h : b = n
          · subst h
            simp only [if_true, Option.map_map, Mem.heap_of hb, true_and, Int.toNat_zero,
              Nat.zero_le, Nat.zero_add, Nat.sub_zero, hlo]
            split <;> simp_all [getElem!_pos]
          · simp [h]
        · unfold gext gextGh
          split
          · exact ⟨rfl, rfl, rfl⟩
          · exact ⟨rfl, rfl, rfl⟩

/-- **Adequacy at program start**: a triple whose precondition is the globals (`globals gs`)
applies to the run of the program from the memory at program start, under every placement. -/
theorem FTriple.run_init {α : Type} {c : MemM α} {Q : α → FAssn} (σ : Placement)
    (gs : List (Array Byte × Nat × BlockKind)) (h : Mem.GlobalsFit gs)
    (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) (ht : FTriple (globals gs) c Q) :
    match (c.run (Mem.ofGlobals σ gs)).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) => ∃ r', Holds m' r' ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧ Q v r' ∧ m'.FSeq :=
  have hi := initRes_holds σ gs hK
  ht _ _ _ hi.1 hi.2 (Mem.init_fseq σ gs h)

end Full
end Zig
