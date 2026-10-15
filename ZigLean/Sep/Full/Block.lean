import ZigLean.Sep.Full.Claims
import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AutoAttr
import ZigLean.Sep.Full.ThreadStep
import ZigLean.Mem.AllocLemmas

/-!
# Blocks in the full-state logic (`docs/proof-framework.md`, library `Full/Block`)

Step rules for `fsym` about making and ending blocks:

* `FTotalTriple.free`: `free` of a whole block (its bytes and its full extent `bext`) returns and
  leaves nothing (total).
* `FTriple.alloc`, `FTriple.allocStack`: a new block of `size > 0` bytes: its bytes (undefined),
  its full extent and an aligned address. These are partial: `alloc` throws `.stackOverflow`
  when there is no room (`Mem.allocOk`: the address space, and for a stack block of a thread
  with a budget its reserve; premise STK-01), which a partial triple counts as no result. A
  total rule needs the room as a resource of the precondition: that resource does not exist yet
  (docs/proof-framework.md: "stack room").

The rules are proved on `Holds` directly (no legacy lifting): `Holds.push` (the memory with a new
live block pushed holds its live bytes and full extent, `pushRes`, with the same frame) and
`Holds.free` (the memory with a block ended holds nothing more, from its live bytes and full
extent). The page mappings (`Full/Mmap.lean`: `mmap`, `munmap` of a whole mapping, a moving
`mremap`) use the same two steps. Each rule
is also a thread rule with no copy of its own: `fsym` applies the sequential rule in a thread
with the step's locality (`FTTriple.ofSeq`, the providers `ThreadLocal.alloc`, `ThreadLocal.free_of`
of `Full/AutoThread.lean`), and a term-level bridge takes the step as `(by fsym : FTTriple P _ _)`
(the post of one step is its rule's, `Auto.stepPost`). The byte remap of a whole heap block that
does not move is local (`ThreadLocal.remapByteBuffer`).
-/

namespace Zig
namespace Full

open FAssn

/-! ## Making a block (native) -/

/-- The live bytes after `alloc`: the new block's undefined bytes, and the old ones. -/
theorem afterAlloc_heap (m : Mem) (kind : BlockKind) (size align : Nat) (l : Loc) :
    (m.afterAlloc kind size align).heap l =
      if l.1 = m.blocks.size ∧ l.2 < size ∧ kind.mappedLo ≤ l.2 then
        some ⟨.undef, m.allocAddr kind size align, size, kind⟩
      else m.heap l := by
  obtain ⟨x, y⟩ := l
  by_cases hx : x = m.blocks.size
  · subst hx
    have hn : m.heap (m.blocks.size, y) = none := by simp [Mem.heap]
    rw [hn]
    simp only [Mem.heap, Mem.afterAlloc, Array.getElem?_push_size, true_and, Array.size_replicate]
    by_cases hc : y < size ∧ kind.mappedLo ≤ y
    · rw [dite_eq_left hc, ite_eq_left hc]; simp
    · rw [dite_eq_right hc, ite_eq_right hc]
  · simp only [Mem.heap, Mem.afterAlloc, Array.getElem?_push, hx, ↓reduceIte, false_and]

/-- The resource of a new live block `b` in state `nb`: its live bytes (from its mapping start,
as `Mem.heap` shows them) and its full extent. -/
def pushRes (b : BlockId) (nb : Block) : Res :=
  ⟨fun l => if h : l.1 = b ∧ l.2 < nb.bytes.size ∧ nb.kind.mappedLo ≤ l.2 then
      some ⟨⟨nb.bytes[l.2]'h.2.1, nb.addr, nb.bytes.size, nb.kind⟩, none⟩ else none,
    Know.none, Ghost.exts (extOne b nb.bytes.size nb.kind)⟩

/-- **A new block** (`alloc`, `mmap`, a moved `mremap`): the memory with the live block `nb`
pushed holds its live bytes and full extent (`pushRes`) with the same frame. The frame has no byte
of the block and no claim on it: it did not exist. The push keeps the counter cell's authority
(`MemAuth.Keep`: the block lies clear of every stack reserve, `MemAuth.Keep.push`). -/
theorem Holds.push {m : Mem} {r rF : Res} (hh : Holds m r rF) (hr : emp r) {nb : Block}
    (hl : nb.live = true) (hlo : nb.kind.mappedLo < nb.bytes.size)
    (hk : MemAuth.Keep m { m with blocks := m.blocks.push nb }) :
    Holds { m with blocks := m.blocks.push nb } (pushRes m.blocks.size nb) rF := by
  obtain ⟨hr0, -, hrg⟩ := hr
  obtain ⟨b, hbe⟩ : ∃ b, b = m.blocks.size := ⟨_, rfl⟩
  rw [← hbe]
  have hget : ∀ x, ({ m with blocks := m.blocks.push nb } : Mem).blocks[x]? =
      if x = b then some nb else m.blocks[x]? := fun x => by
    simp only [Array.getElem?_push]; by_cases hx : x = b <;> simp [hx, hbe]
  have hnone : m.blocks[b]? = none := by simp [hbe]
  -- the frame's bytes and claims are on old blocks
  have hFb : ∀ l fc, rF.heap l = some fc → l.1 ≠ b := fun l fc hl e => by
    obtain ⟨blk, hb, -⟩ := hh.swap.block (b := l.1) (x := l.2) hl
    rw [e, hnone] at hb; cases hb
  have hok : Ghost.Ok (Ghost.exts fun _ => none) rF.gh := by
    rw [Ghost.exts_none, ← hrg]; exact hh.ghost.1
  have hdorm : (rF.gh.extent b).Dormant rF.gh.ls := by
    have hv := hok.1.2.1 b
    rw [show ((Ghost.exts fun _ => none).add rF.gh).extent b = rF.gh.extent b by simp,
      Ghost.ls_exts_add] at hv
    refine ECell.dormant_of_not_claims (fun hc => ?_) hv.2.2
    have ht := hh.ghost.2.1 b
    rw [hrg, Ghost.unit_add] at ht
    rcases hc with ⟨S, K, h⟩ | ⟨k, h⟩
    · obtain ⟨blk, hb, -⟩ := ht.1 S K h; rw [hnone] at hb; cases hb
    · obtain ⟨blk, hb, -⟩ := ht.2 k h; rw [hnone] at hb; cases hb
  refine ⟨fun l => ?_, ⟨fun l => ?_, fun l fc hfc => ?_⟩, Know.sub_none _,
    hh.knowF.trans (KMono.push rfl), ⟨Ghost.ok_exts_change hok fun x hx => ?_, fun x => ?_, ?_,
      by have := hh.ghost.2.2.2.keep hk; rw [hrg] at this; simpa [pushRes] using this⟩⟩
  · -- disjoint: the frame has no byte of `b`
    by_cases hc : l.1 = b
    · right
      cases e : rF.heap l with
      | none => rfl
      | some fc => exact absurd hc (hFb l fc e)
    · left; simp only [pushRes]; rw [dif_neg fun h => hc h.1]
  · -- the cells up to `Cell.norm`
    rw [Mem.heap_push, ← hbe]
    simp only [FHeap.union_apply, pushRes, hl, true_and]
    by_cases hc : l.1 = b
    · have hFn : rF.heap l = none := by
        cases e : rF.heap l with
        | none => rfl
        | some fc => exact absurd hc (hFb l fc e)
      rw [if_pos hc, hFn, Option.or_none]
      by_cases hc' : l.2 < nb.bytes.size ∧ nb.kind.mappedLo ≤ l.2
      · rw [dif_pos hc', dif_pos ⟨hc, hc'⟩]; rfl
      · rw [dif_neg hc', dif_neg fun h => hc' h.2]; rfl
    · rw [if_neg hc, dif_neg fun h => hc h.1, Option.none_or]
      have := hh.heap.1 l
      rwa [FHeap.union_apply, hr0, FHeap.empty, Option.none_or] at this
  · -- tags: the new cells have none, the frame's are as before
    simp only [FHeap.union_apply, pushRes] at hfc
    split at hfc
    · cases hfc; trivial
    · exact hh.tagF (by simpa using hfc)
  · -- the frame has no claim on the new block
    have : x = b := Classical.byContradiction fun hne => by simp [extOne, hne] at hx
    subst this; exact hdorm
  · -- the extent claims hold in the new memory
    show ECell.TrueIn _ _ _ _
    simp only [pushRes]
    rw [Ghost.ls_exts_add]
    have ht := hh.ghost.2.1 x
    rw [hrg, Ghost.unit_add] at ht
    by_cases hx : x = b
    · rw [hx]
      rw [show ((Ghost.exts (extOne b nb.bytes.size nb.kind)).add rF.gh).extent b =
        (ECell.auth1 nb.bytes.size nb.kind Frac.one).add (rF.gh.extent b) by
          simp [Ghost.add, Ghost.exts, extOne]]
      refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
      · simp only [ECell.add, hdorm.1, Nat.add_zero, ECell.auth1] at hp'
        split at hp'
        · rename_i he; simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
          exact ⟨nb, by rw [hget, if_pos rfl], hl, rfl, rfl, hlo⟩
        · cases hp'
      · rw [hdorm.req_auth1 hk']
        exact ⟨nb, by rw [hget, if_pos rfl], hl, Nat.zero_le _, hlo⟩
    · rw [show ((Ghost.exts (extOne b nb.bytes.size nb.kind)).add rF.gh).extent x = rF.gh.extent x by
        simp [Ghost.add, Ghost.exts, extOne, hx]]
      refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
      · obtain ⟨blk, hb, rest⟩ := ht.1 S' K' hp'
        exact ⟨blk, by rw [hget, if_neg hx]; exact hb, rest⟩
      · obtain ⟨blk, hb, rest⟩ := ht.2 k hk'
        exact ⟨blk, by rw [hget, if_neg hx]; exact hb, rest⟩
  · -- no byte claim on a block not yet made
    have hc := ClFresh.frame (hrg ▸ hh.ghost.2.2.1 : ClFresh m (Ghost.unit.add rF.gh))
    exact (hc.mono (by simp)).congr (Ghost.exts_add_cl _ _)

/-- A new block's resource (`pushRes`) is its live bytes from its mapping start and its full
extent. -/
theorem pushRes_up (b : BlockId) (nb : Block) :
    (up (bytesAt ⟨some b, (nb.kind.mappedLo : Int)⟩ nb.addr nb.bytes.size nb.kind
        (nb.bytes.extract nb.kind.mappedLo nb.bytes.size)) ⋆ bext b nb.bytes.size nb.kind)
      (pushRes b nb) := by
  refine ⟨⟨(pushRes b nb).heap, Know.none, Ghost.unit⟩,
    ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.auth1 nb.bytes.size nb.kind Frac.one)⟩,
    FHeap.disjoint_empty _, ?_, ⟨⟨b, rfl, by simp, fun l => ?_⟩, rfl, rfl⟩, rfl, rfl, rfl⟩
  · simp only [pushRes, FHeap.union_empty, Know.union_none, Ghost.unit_add, Ghost.exts_extOne]
  · obtain ⟨x, y⟩ := l
    simp only [FHeap.erase, pushRes, Int.toNat_natCast, Array.size_extract, Nat.min_self]
    by_cases hc : x = b ∧ y < nb.bytes.size ∧ nb.kind.mappedLo ≤ y
    · rw [dif_pos hc, if_pos ⟨hc.1, hc.2.2, by omega⟩]
      simp only [Option.map_some, Option.some.injEq, Cell.mk.injEq, and_true]
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
      simp [show nb.kind.mappedLo + (y - nb.kind.mappedLo) = y by omega,
        show y - nb.kind.mappedLo < nb.bytes.size - nb.kind.mappedLo by omega,
        Array.getElem?_eq_getElem hc.2.1]
    · rw [dite_eq_right_iff.mpr fun h => absurd h hc,
        ite_eq_right_iff.mpr fun h => absurd ⟨h.1, by omega, h.2.1⟩ hc]; rfl

/-- A block kind that no stack budget charges (every kind but `.stack`). -/
theorem _root_.Zig.Mem.stackBudget?_of_ne {m : Mem} {kind : BlockKind} (hks : kind ≠ .stack) :
    m.stackBudget? kind = none := by
  cases kind <;> first | rfl | exact absurd rfl hks

/-- The block that `alloc` makes (`Mem.afterAlloc`). -/
def _root_.Zig.Mem.allocBlock (m : Mem) (kind : BlockKind) (size align : Nat) : Block :=
  { bytes := Array.replicate size .undef, align := align, kind := kind, live := true,
    addr := m.allocAddr kind size align }

/-- **A new block from `alloc`** that no stack budget charges (`size > 0`, a kind without a mapping
start): the memory after it holds the new block's bytes and full extent. The block lies clear of
every reserve and no stack state changes (`MemAuth.Keep`). -/
theorem Holds.alloc {m : Mem} {r rF : Res} {kind : BlockKind} {size align : Nat}
    (hh : Holds m r rF) (hp : emp r) (hkm : m.stackBudget? kind = none) (hk : kind.mappedLo = 0)
    (hpos : 0 < size) :
    Holds (m.afterAlloc kind size align) (pushRes m.blocks.size (m.allocBlock kind size align)) rF :=
  Holds.congrMem (m := { m with blocks := m.blocks.push (m.allocBlock kind size align) }) rfl rfl
    (hh.push hp rfl (by simp [Mem.allocBlock, hk, hpos])
      (MemAuth.Keep.push rfl rfl rfl rfl fun t S hS => clearOf_of_apart (by
        simpa [Mem.allocBlock] using
          allocAddr_apart_none (size := size) (align := align) hkm t S hS)))
    (MemAuth.Keep.of_blocks rfl (by simp [Mem.afterAlloc, Mem.stacksAfterAlloc, hkm]) rfl rfl)

/-- `alloc` of `size > 0` bytes: the bytes and the new block's full extent (every kind but
`.stack`, whose block a stack budget charges: `FTriple.allocStack`). -/
theorem FTriple.alloc' (kind : BlockKind) (size align : Nat) (ha : 0 < align) (hpos : 0 < size)
    (hks : kind ≠ .stack) (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTriple emp (alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ bext b size kind)) := by
  intro m r rF hh hp hs
  cases hroom : m.allocOk kind size align
  · rw [alloc_run_noRoom m hroom]
  rw [alloc_run_eq m hroom]
  let nb : Block :=
    { bytes := Array.replicate size .undef, align := align, kind := kind, live := true,
      addr := m.allocAddr kind size align }
  have hq := pushRes_up m.blocks.size nb
  simp only [nb, hk, Array.size_replicate, Int.ofNat_zero, Array.extract_replicate, Nat.min_self,
    Nat.sub_zero] at hq
  exact ⟨_, hh.alloc hp (Mem.stackBudget?_of_ne hks) hk hpos,
    ⟨m.allocAddr kind size align, m.blocks.size,
      sep_lift.mpr ⟨⟨rfl, rfl, m.allocAddr_mod kind size align ha⟩, hq⟩⟩,
    ⟨⟨hs.1.single⟩, hs.2.1, LDMono.alloc hroom rfl (by simp) rfl hs.2.2⟩⟩

/-- **The stack block of an escaping local in the plain mode** (`plain`: no thread has a stack
budget, so the block charges nothing): its bytes, its full extent and an aligned address
(partial: the address space can be full, premise STK-01). Under a budget a stack block needs the
thread's stack token (`tests/roadmap/stack-region/Tokens.lean`, `push_without_sp_cx`; the token
rules are step 5). -/
theorem FTriple.allocStack' (size align : Nat) (ha : 0 < align) (hpos : 0 < size) :
    FTriple plain (alloc .stack size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        ((up (bytesAt p A size .stack (Array.replicate size .undef)) ⋆ bext b size .stack) ⋆
          plain)) := by
  intro m r rF hh hp hs
  have hns : m.NoStack := hh.noStack (plain_noStack (sep_emp.mpr hp))
  have hkm : m.stackBudget? .stack = none := by simp [Mem.stackBudget?, hns m.current]
  cases hroom : m.allocOk .stack size align
  · rw [alloc_run_noRoom m hroom]
  rw [alloc_run_eq m hroom]
  let nb : Block :=
    { bytes := Array.replicate size .undef, align := align, kind := .stack, live := true,
      addr := m.allocAddr .stack size align }
  have hq := pushRes_up m.blocks.size nb
  simp only [nb, BlockKind.mappedLo, Array.size_replicate, Int.ofNat_zero, Array.extract_replicate,
    Nat.min_self, Nat.sub_zero] at hq
  have hpr : r = ⟨FHeap.empty ∪ r.heap, Know.none.union r.know, Ghost.unit.add r.gh⟩ := by
    simp [FHeap.empty_union, Know.none_union, Ghost.unit_add]
  rw [hpr] at hh
  have h0 := Holds.split (r₁ := ⟨FHeap.empty, Know.none, Ghost.unit⟩) (r₂ := r)
    (FHeap.disjoint_empty _).symm hh
  have h1 := h0.alloc ⟨rfl, rfl, rfl⟩ hkm rfl hpos (align := align)
  have hd : FHeap.Disjoint (pushRes m.blocks.size nb).heap r.heap := fun l => by
    rw [(plain_ghost hp).1]; exact .inr rfl
  have hrF : FHeap.Disjoint r.heap rF.heap := fun l => by
    rw [(plain_ghost hp).1]; exact .inl rfl
  exact ⟨_, Holds.join hd hrF h1,
    ⟨m.allocAddr .stack size align, m.blocks.size, sep_lift.mpr ⟨⟨rfl, rfl,
      m.allocAddr_mod .stack size align ha⟩, ⟨pushRes m.blocks.size nb, r, hd, rfl, hq, hp⟩⟩⟩,
    ⟨⟨hs.1.single⟩, hs.2.1, LDMono.alloc hroom rfl (by simp) rfl hs.2.2⟩⟩

/-- `FTriple.allocStack'` that uses the plain mode up (its last use: `plain` is dropped). Not
`@[fsym]` (the walk keeps the plain mode, `FTriple.allocStack`): a caller that uses it up passes it,
`fsym [FTriple.allocStackDrop]`, in a thread too (`ofSeq`). -/
theorem FTriple.allocStackDrop (size align : Nat) (ha : 0 < align) (hpos : 0 < size) :
    FTriple plain (Zig.allocStack size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size .stack (Array.replicate size .undef)) ⋆ bext b size .stack)) :=
  FTriple.drop (K := fun _ => plain)
    ((FTriple.allocStack' size align ha hpos).post fun _ _ h => by
      obtain ⟨A, b, h⟩ := h
      exact sep_ex.mpr ⟨A, sep_ex.mpr ⟨b, sep_assoc' h⟩⟩)
    fun _ _ h => ⟨(plain_ghost h).1, (plain_ghost h).2.2⟩

/-- After `alloc` of no bytes that no stack budget charges, the memory holds what it held: the
new block has no live byte. -/
theorem Holds.allocZero {m : Mem} {r rF : Res} (hh : Holds m r rF) (kind : BlockKind) (align : Nat)
    (hkm : m.stackBudget? kind = none) : Holds (m.afterAlloc kind 0 align) r rF := by
  have e : (m.afterAlloc kind 0 align).heap = m.heap := funext fun l => by
    rw [afterAlloc_heap]; exact ite_eq_right fun h => absurd h.2.1 (Nat.not_lt_zero _)
  exact ⟨hh.disj, ⟨fun l => by rw [e]; exact hh.heap.1 l, fun l fc h => hh.heap.2 l fc h⟩,
    hh.know.trans (KMono.push rfl), hh.knowF.trans (KMono.push rfl),
    hh.ghost.keep (KeepsExt.push rfl) (by simp [Mem.afterAlloc]) (MemAuth.Keep.allocOther hkm)⟩

/-- `alloc` of no bytes: a pointer to offset 0 of a new block (every kind but `.stack`). The
block has no byte, so there is nothing to own (an extent needs a live byte: `Holds.bauth`). -/
theorem FTriple.allocZero (kind : BlockKind) (align : Nat) (hks : kind ≠ .stack) :
    FTriple emp (alloc kind 0 align) (fun p => ⟪p.block.isSome ∧ p.off = 0⟫) := by
  intro m r rF hh hp hs
  cases hroom : m.allocOk kind 0 align
  · rw [alloc_run_noRoom m hroom]
  rw [alloc_run_eq m hroom]
  exact ⟨r, hh.allocZero kind align (Mem.stackBudget?_of_ne hks), ⟨⟨rfl, rfl⟩, hp⟩,
    ⟨⟨hs.1.single⟩, hs.2.1, LDMono.alloc hroom rfl (by simp) rfl hs.2.2⟩⟩

/-- A run of `alloc` creates the block it returns. -/
theorem alloc_fresh {kind : BlockKind} {size align : Nat} {m m' : Mem} {p : Ptr} {b : BlockId}
    (h : ((alloc kind size align).run m).run = some (.ok (p, m'))) (hb : p.block = some b) :
    m.blocks.size ≤ b ∧ b < m'.blocks.size := by
  unfold alloc at h
  obtain ⟨_, m₁, h1, h2⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h1
  split at h2
  · obtain ⟨_, m₂, h3, h4⟩ := Conc.Proto.MemM.bind_ok h2
    have e := Conc.Proto.MemM.set_ok h3
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.pure_ok h4
    subst e
    cases hb
    simp [Mem.afterAlloc]
  · exact (Conc.Proto.MemM.throw_ok h2).elim

/-- **`alloc` with the claim on the new block's bytes** (`FTriple.mintClaimOpt`): the bytes, the
full extent and the exclusive claim on `[0, size)`. -/
theorem FTriple.allocC (kind : BlockKind) (size align : Nat) (ha : 0 < align) (hpos : 0 < size)
    (hks : kind ≠ .stack) (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTriple emp (alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ (bext b size kind ⋆ bclaim b 0 size))) := by
  refine (FTriple.mintClaimOpt (fun p => p.block) (fun _ => 0) (fun _ => size)
    (FTriple.alloc' kind size align ha hpos hks hk) (fun m v m' b h e => alloc_fresh h e)
    fun _ b r _ hq => noCl_ex (fun A => noCl_ex fun b => noCl_sep (noCl_lift _)
      (noCl_sep (noCl_up _) (noCl_bauth _ _ _ _))) r hq b).post fun p r h => ?_
  obtain ⟨A, h⟩ := sep_ex.mp h
  obtain ⟨b, h⟩ := sep_ex.mp h
  obtain ⟨hφ, h⟩ := sep_lift.mp (sep_assoc h)
  rw [hφ.1] at h
  exact ⟨A, b, sep_lift.mpr ⟨hφ, sep_assoc h⟩⟩

theorem noCl_plain : NoCl plain := by
  rintro _ ⟨r₁, r₂, -, rfl, ⟨-, -, g1⟩, ⟨-, -, g2⟩⟩ b x
  simp [g1, g2, Ghost.ofAC, Ghost.add, Ghost.unit]

/-- `allocStack` (a stack local whose address escapes) with the claim on its bytes, in the plain
mode (`FTriple.allocStack'`). -/
theorem FTriple.allocStackC (size align : Nat) (ha : 0 < align) (hpos : 0 < size) :
    FTriple plain (allocStack size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        ((up (bytesAt p A size .stack (Array.replicate size .undef)) ⋆ (bext b size .stack ⋆ bclaim b 0 size)) ⋆
          plain)) := by
  refine (FTriple.mintClaimOpt (fun p => p.block) (fun _ => 0) (fun _ => size)
    (FTriple.allocStack' size align ha hpos) (fun m v m' b h e => alloc_fresh h e)
    fun _ b r _ hq => noCl_ex (fun A => noCl_ex fun b => noCl_sep (noCl_lift _)
      (noCl_sep (noCl_sep (noCl_up _) (noCl_bauth _ _ _ _)) noCl_plain)) r hq b).post fun p r h => ?_
  obtain ⟨A, h⟩ := sep_ex.mp h
  obtain ⟨b, h⟩ := sep_ex.mp h
  obtain ⟨hφ, h⟩ := sep_lift.mp (sep_assoc h)
  rw [hφ.1] at h
  refine ⟨A, b, sep_lift.mpr ⟨hφ, ?_⟩⟩
  -- `((bytes ⋆ bext) ⋆ plain) ⋆ claim` to `(bytes ⋆ (bext ⋆ claim)) ⋆ plain`
  exact of_eq (by ac_rfl) h

/-! ## Ending a block (native) -/

/-- **A block ends under its bytes and its full extent**: the resource owns every live byte of
block `b` (the `S` bytes from offset `p.off`, at or below the block's mapping start) and its full
extent. The memory with `b` dead holds nothing with the same frame: the frame has no byte of `b`
and only dormant claims on it. -/
theorem Holds.free {m : Mem} {r rF : Res} {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} {b : BlockId} {blk : Block} (hh : Holds m r rF)
    (hp : (up (bytesAt p A S K bs) ⋆ bext b S K) r) (hpb : p.block = some b)
    (hS : p.off.toNat + bs.size = S) (hlo : p.off.toNat ≤ K.mappedLo)
    (hb : m.blocks[b]? = some blk) (hK : blk.kind ≠ .constGlobal) :
    Holds { m with blocks := m.blocks.set! b { blk with live := false } }
      ⟨FHeap.empty, Know.none, Ghost.unit⟩ rF := by
  obtain ⟨⟨b', hb', -, hl⟩, -, hrg⟩ := up_sep_bext hp
  rw [hpb] at hb'; cases hb'
  replace hrg : r.gh = Ghost.exts (extOne b S K) := hrg
  obtain ⟨blk', hb₁, -, hsz, hbk, -⟩ := hh.bauth (sep_comm hp)
  rw [hb] at hb₁; cases hb₁
  have hget := blocks_set_get hb (m' := { m with blocks := m.blocks.set! b { blk with live := false } }) rfl
  -- the resource owns exactly the live bytes `[p.off, S)` of `b`; the frame none of `b`
  have hown : ∀ y, K.mappedLo ≤ y → y < S → r.heap (b, y) ≠ none := fun y hy hy' => by
    have e := hl (b, y)
    rw [ite_eq_left ⟨rfl, by omega, by omega⟩] at e
    intro hn; simp [FHeap.erase, hn] at e
  have hrb : ∀ l : Loc, l.1 ≠ b → r.heap l = none := fun l hx => by
    have e := hl l
    rw [ite_eq_right fun h => hx h.1] at e
    simpa [FHeap.erase] using e
  have hFb : ∀ y, rF.heap (b, y) = none := fun y => by
    cases e : rF.heap (b, y) with
    | none => rfl
    | some fc =>
      obtain ⟨blk', hb', -, hy, hylo, -⟩ := hh.swap.block e
      rw [hb] at hb'; cases hb'
      exact absurd ((hh.disj (b, y)).resolve_left (hown y (hbk ▸ hylo) (by omega))) (by simp [e])
  have hok : Ghost.Ok (Ghost.exts (extOne b S K)) rF.gh := hrg ▸ hh.ghost.1
  have hdorm : (rF.gh.extent b).Dormant rF.gh.ls := by
    have := full_excl hok (b := b) (S := S) (K := K) (by simp [Ghost.exts, extOne])
    rwa [Ghost.ls_exts_add] at this
  have hheap : ∀ l : Loc, ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).heap l =
      if l.1 = b then none else m.heap l := fun ⟨x, y⟩ => by
    simp only [Mem.heap, hget]
    by_cases hx : x = b <;> simp [hx]
  refine ⟨fun _ => .inl rfl, ⟨fun l => ?_, fun l fc hfc => ?_⟩, Know.sub_none _,
    hh.knowF.trans (KMono.set (blk' := { blk with live := false }) hb rfl hK rfl),
    ⟨?_, fun x => ?_, ?_, by
      have := hh.ghost.2.2.2.keep
        (MemAuth.Keep.kill (m' := { m with blocks := m.blocks.set! b { blk with live := false } })
          hb rfl rfl rfl rfl)
      rw [hrg] at this; simpa using this⟩⟩
  · -- the frame's cells, outside `b`
    rw [hheap, FHeap.empty_union]
    by_cases hx : l.1 = b
    · rw [ite_eq_left hx, show l = (b, l.2) from Prod.ext hx rfl, hFb]; rfl
    · rw [ite_eq_right hx]
      have := hh.heap.1 l
      rwa [FHeap.union_apply, hrb l hx, Option.none_or] at this
  · exact hh.tagF (by simpa [FHeap.empty] using hfc)
  · -- the ghost states compose without `b`'s extent
    have := Ghost.ok_exts_change (E' := fun _ => none) hok fun _ h => by simp at h
    rwa [Ghost.exts_none] at this
  · -- the frame's extent claims hold: on `b` it has none
    show ECell.TrueIn _ _ _ _
    rw [Ghost.unit_add]
    by_cases hx : x = b
    · subst hx
      exact ⟨fun S' K' h => absurd (hdorm.1 (S', K') ▸ h) (Nat.lt_irrefl 0),
        fun k h => (hdorm.2.1 k h).elim⟩
    · have ht := hh.ghost.2.1 x
      rw [hrg, Ghost.ls_exts_add,
        show ((Ghost.exts (extOne b S K)).add rF.gh).extent x = rF.gh.extent x by
          simp [Ghost.add, Ghost.exts, extOne, hx]] at ht
      refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
      · obtain ⟨blk₀, hb₀, rest⟩ := ht.1 S' K' hp'
        exact ⟨blk₀, by rw [hget, ite_eq_right hx]; exact hb₀, rest⟩
      · obtain ⟨blk₀, hb₀, rest⟩ := ht.2 k hk'
        exact ⟨blk₀, by rw [hget, ite_eq_right hx]; exact hb₀, rest⟩
  · -- no byte claim on a block not yet made
    rw [Ghost.unit_add]
    exact (ClFresh.frame hh.ghost.2.2.1).mono (by simp)

/-! ## Step rules (`fsym`) -/

-- `hpos` is not needed (an extent of no bytes does not exist), but the rule keeps its statement.
set_option linter.unusedVariables false in
/-- **`free` of a whole block, with the knowledge that it is dead** (total): its bytes and its
full extent go, and the block is dead from now on (`dead`). A `const` global is never freed
(`free` of one is illegal). -/
theorem FTotalTriple.free_dead {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {b : BlockId} (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) (fun _ => dead b) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    obtain ⟨blk, hb, hl, hsz, hk, -⟩ := hh.bauth (sep_comm hp)
    have hK' : blk.kind ≠ .constGlobal := hk ▸ hK
    have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    have hdk : ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).kn (.dead b) :=
      ⟨{ blk with live := false }, by simp [Array.set!_eq_setIfInBounds, hlt], rfl⟩
    refine ⟨(), _, _, ?_, (hh.free hp hpb (by rw [h0]; simpa using hS) (by simp [h0]) hb hK').addKnow
        (Know.sub_single hdk),
      ⟨rfl, Know.none_union _, rfl⟩,
      ⟨⟨hs.1.single⟩, hs.2.1, (LDMono.set (nb := { blk with live := false }) hb
        (fun h => by cases h) rfl (Nat.le_refl _) rfl) hs.2.2⟩⟩
    simp [Zig.free, hpb, hb, hl, h0, hsz, hK', freeRaces_of_singleThread hs.1.single, zig_unfold,
      set, StateT.set, MonadStateOf.set]

/-- **`free` of a whole block** (total): its bytes and its full extent go. A `const` global is
never freed (`free` of one is illegal). -/
@[fsym] theorem FTotalTriple.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {b : BlockId} (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) (fun _ => emp) :=
  (FTotalTriple.free_dead hpb hS h0 hpos hK).eupd_post fun _ => EUpd.dead_drop

/-- `free` of a whole block, not a `const` global: its bytes and its full extent go. -/
theorem FTriple.free' {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal := by decide) :
    FTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (free p) (fun _ => emp) :=
  (FTotalTriple.free hpb hS h0 hpos hK).1

/-- `free` returns from every memory that holds a whole block with its full extent. -/
theorem FReturns.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal) :
    FReturns (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) :=
  (FTotalTriple.free hpb hS h0 hpos hK).2


/-! ## The byte remap of a heap block (`remapByteBuffer`), locality

Not moving (`AllocPolicy.byteRemap` is `.fail` or `.inPlace`), the remap of a whole heap block
records a write of its bytes and resizes it in place (`Mem.afterByteRemap`): a shrink retires
the atomic locations over the cut bytes, a growth brings bytes past the old end to life with
their history forgotten (`Mem.forgetFrom`), as a page growth in place does. -/

/-- `throw` is no result. -/
theorem _root_.Zig.Result.throw_ne_pure {α : Type} {e : Error} {x : α} :
    (throw e : Result α) ≠ pure x := by
  intro h
  have := congrArg ExceptT.run h
  simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure, ExceptT.run] at this

/-- **A byte remap that does not move is local** when `P` owns the whole heap block that the
slice accesses. -/
theorem ThreadLocal.remapByteBuffer {P : FAssn} {s : Slice} {n : Nat}
    (hown : ∀ m r rF, Holds m r rF → P r → m.allocPolicy.byteRemap ≠ .move ∧
      ∀ b blk o, m.access s.ptr s.len.toNat 1 = Pure.pure (b, blk, o) →
        ∀ x, x < blk.bytes.size → r.heap.erase (b, x) ≠ none) :
    ThreadLocal P (Zig.remapByteBuffer s n) := by
  intro m r rF hh hp hc ho
  obtain ⟨hmv, hin⟩ := hown m r rF hh hp
  have hacc0 : m.noFp.access s.ptr s.len.toNat 1 = m.access s.ptr s.len.toNat 1 := rfl
  have hst₀ : ∀ v m', (Zig.remapByteBuffer s n).run m = Pure.pure (v, m') →
      (Zig.remapByteBuffer s n).run m = Pure.pure (none, m) →
      FStepIn rF.heap.erase m m' ∧ m.RevivesOwned m' := fun v m' e h1 => by
    rw [h1] at e
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
    exact ⟨FStepIn.refl _ _, (Mem.NoRevive.refl m).revivesOwned⟩
  cases hpol : m.allocPolicy.byteRemap with
  | move => exact absurd hpol hmv
  | fail =>
    have h1 := remapByteBuffer_default_run (m := m) s n hpol
    have h0 := remapByteBuffer_default_run (m := m.noFp) s n hpol
    exact ⟨by rw [h1, h0]; rfl, fun v m' e => hst₀ v m' e h1⟩
  | inPlace =>
    have hpol' : m.noFp.allocPolicy.byteRemap = .inPlace := hpol
    rcases access_cases m s.ptr s.len.toNat 1 with hacc | ⟨b, blk, o, hacc⟩
    · have h1 := remapByteBuffer_inPlace_throw (n := n) hpol hacc
      have h0 := remapByteBuffer_inPlace_throw (n := n) hpol' (hacc0.trans hacc)
      exact ⟨by rw [h1, h0], fun v m' e => absurd (h1.symm.trans e) Result.throw_ne_pure⟩
    by_cases hbad : blk.kind ≠ .heap ∨ o ≠ 0 ∨ blk.bytes.size ≠ s.len.toNat
    · have h1 := remapByteBuffer_inPlace_illegal (n := n) hpol hacc hbad
      have h0 := remapByteBuffer_inPlace_illegal (n := n) hpol' (hacc0.trans hacc) hbad
      exact ⟨by rw [h1, h0], fun v m' e => absurd (h1.symm.trans e) Result.throw_ne_pure⟩
    by_cases hnone : (blk.align ≠ 1 ∨ n = 0 ∨ m.allocPolicy.maxBytes < n) ∨
        (blk.bytes.size < n ∧ m.growFree b blk n ≠ true)
    · have h1 := remapByteBuffer_inPlace_none hpol hacc hbad hnone
      have h0 := remapByteBuffer_inPlace_none hpol' (hacc0.trans hacc) hbad hnone
      exact ⟨by rw [h1, h0]; rfl, fun v m' e => hst₀ v m' e h1⟩
    -- in place: the owned write of the whole block, then the resize
    simp only [not_or, not_and, Decidable.not_not, ne_eq] at hbad hnone
    obtain ⟨hK, rfl, hsz⟩ := hbad
    obtain ⟨⟨hal, hpos, hcap⟩, hgrow⟩ := hnone
    obtain ⟨-, hb, hl, -, -, -, -⟩ := access_eq hacc
    have hbs : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    have hin' : ∀ x, 0 ≤ x → x < 0 + blk.bytes.size → r.heap.erase (b, x) ≠ none :=
      fun x _ h2 => hin b blk 0 hacc x (by omega)
    have hnr := noRace_owned (k := .write) hc ho hin'
    rw [Mem.noFp_withFp] at hnr
    have h1 := remapByteBuffer_inPlace_run hpol hacc hK hsz hal hpos (Nat.le_of_not_lt hcap) hgrow hnr.2
    have h0 := remapByteBuffer_inPlace_run hpol' (hacc0.trans hacc) hK hsz hal hpos
      (Nat.le_of_not_lt hcap) hgrow hnr.1
    refine ⟨by rw [h1, h0]; rfl, fun v m' e => ?_⟩
    rw [h1] at e
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
    let mr := m.recordAt b 0 blk.bytes.size .write
    let mf := (mr.forgetFrom b blk.bytes.size).retire b n (blk.bytes.size - n)
    have hrec : FStepIn rF.heap.erase m mr :=
      FStepIn.recordAt hc.1 (FHeap.erase_disjoint hh.disj) hin' hbs fun _ ⟨blk', e1, e2⟩ => by
        rw [hb] at e1; cases e1; rw [hK] at e2; cases e2
    have hret : FStepIn rF.heap.erase (mr.forgetFrom b blk.bytes.size) mf :=
      FStepIn.retire fun x h1 h2 =>
        ((FHeap.erase_disjoint hh.disj) (b, x)).resolve_left (hin' x (by omega) (by omega))
    have hset : FStepIn rF.heap.erase mf (mr.afterByteRemap b blk n) :=
      FStepIn.setBlock (m := mf) (fun h => by simp [hK] at h) fun l hl e hlen ⟨blk', h1, h2⟩ => by
        -- a location of the block that the shrink keeps lies before the new end
        obtain ⟨-, hnh⟩ := Mem.mem_retire hl
        have h1' : m.blocks[b]? = some blk' := by rw [← e]; exact h1
        rw [hb] at h1'; cases h1'
        have hs : (remapBytes blk.bytes n).size = n := by
          simp only [remapBytes, padTo, Array.size_append, Array.size_extract, Array.size_replicate]
          omega
        rw [hs]
        refine Nat.le_of_not_lt fun hlt => ?_
        have hh' : l.hits b n (blk.bytes.size - n) = true := by
          unfold ALoc.hits
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          exact ⟨⟨⟨⟨e, by omega⟩, hlen⟩, by omega⟩, by omega⟩
        rw [hnh] at hh'; cases hh'
    refine ⟨((hrec.trans (FStepIn.forgetFrom _ _ fun blk' h => by
        have h' : m.blocks[b]? = some blk' := h
        rw [hb] at h'; cases h'; exact Nat.le_refl _)).trans hret).trans hset,
      Mem.RevivesOwned.of_forgetFrom (m₁ := mr) rfl fun b' x hb' hl' hd => ?_⟩
    have hget := blocks_set_get (m := m) (m' := mr.afterByteRemap b blk n) hb rfl
    by_cases e' : b' = b
    · subst e'
      refine ⟨rfl, Nat.le_of_not_lt fun hlt => ?_⟩
      rw [Mem.heap_of hb, dif_pos ⟨hl, hlt, by simp [hK, BlockKind.mappedLo]⟩] at hd
      cases hd
    · exfalso; apply hl'
      have e2 : (mr.afterByteRemap b blk n).heap (b', x) = m.heap (b', x) := by
        unfold Mem.heap; dsimp only; rw [hget, if_neg e']
      rw [e2]; exact hd

/-- **`alloc` of `size > 0` bytes** (partial: no room is a stack overflow): the bytes, the full
extent of the new block and an aligned address. -/
@[fsym] theorem FTriple.alloc (kind : BlockKind) (size align : Nat) (ha : 0 < align)
    (hpos : 0 < size) (hks : kind ≠ .stack) (hk : kind.mappedLo = 0) :
    FTriple emp (Zig.alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ bext b size kind)) :=
  FTriple.alloc' kind size align ha hpos hks hk

/-- **The stack block of an escaping local** (`allocStack`, partial as `FTriple.alloc`), in the
plain mode: no thread has a stack budget (`plain`, `FTriple.allocStack'`). Under a budget the
push needs the thread's stack token (step 5). -/
@[fsym] theorem FTriple.allocStack (size align : Nat) (ha : 0 < align) (hpos : 0 < size) :
    FTriple plain (Zig.allocStack size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        ((up (bytesAt p A size .stack (Array.replicate size .undef)) ⋆ bext b size .stack) ⋆ plain)) :=
  FTriple.allocStack' size align ha hpos

/-! ## Frames of recursive calls in the plain mode

Without a stack budget `enterFrame` and `leaveFrame` change nothing (`enterFrame_run_none`,
`leaveFrame_run_none`), so in the plain mode they return and keep every resource. Under a budget
a frame needs the thread's stack token (step 5). -/

/-- A step that leaves a memory without stack budgets as it is: the plain mode and a frame stay. -/
theorem FTotalTriple.of_noStack {c : MemM Unit} {R : FAssn}
    (hc : ∀ m : Mem, m.NoStack → c.run m = pure ((), m)) :
    FTotalTriple (plain ⋆ R) c (fun _ => plain ⋆ R) :=
  FTotalTriple.of_run fun m r _ hh hp hs =>
    ⟨(), m, r, hc m (hh.noStack (plain_noStack hp)), hh, hp, hs⟩

/-- **Entering a frame in the plain mode** returns and changes nothing. -/
@[fsym] theorem FTotalTriple.enterFrame_plain :
    FTotalTriple plain Zig.enterFrame (fun _ => plain) :=
  (FTotalTriple.of_noStack (R := emp) fun m h => enterFrame_run_none (h m.current)).conseq
    (fun _ h => sep_emp.mpr h) (fun _ _ h => sep_emp.mp h)

/-- **Leaving a frame in the plain mode** returns and changes nothing. -/
@[fsym] theorem FTotalTriple.leaveFrame_plain :
    FTotalTriple plain Zig.leaveFrame (fun _ => plain) :=
  (FTotalTriple.of_noStack (R := emp) fun m h => leaveFrame_run_none (h m.current)).conseq
    (fun _ h => sep_emp.mpr h) (fun _ _ h => sep_emp.mp h)

/-! ## Heap blocks: `rawAlloc` and `poisonFree` (`ZigLean/Mem/Alloc.lean`) -/

/-- What `rawAlloc n align` returns: `null` and nothing, or a new heap block of `n` undefined
bytes with its full extent at an `align`-aligned address. -/
def rawAllocPost (n align : Nat) : Option Ptr → FAssn
  | none => emp
  | some p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A n .heap (Array.replicate n .undef)) ⋆ bext b n .heap)

/-- The memory after the attempt count of `rawAlloc` holds what the memory held. -/
theorem allocs_holds {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq) :
    Holds { m with allocs := m.allocs + 1 } r rF ∧ ({ m with allocs := m.allocs + 1 } : Mem).FSeq :=
  ⟨Holds.congrMem (m := m) rfl rfl hh, ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩⟩

/-- **`rawAlloc` of `n > 0` bytes** (total, for every failure policy): `null` and nothing (the
failure decision, or no room in the address space), or a new heap block. -/
@[fsym] theorem FTotalTriple.rawAlloc (n align : Nat) (ha : 0 < align) (hpos : 0 < n) :
    FTotalTriple emp (Zig.rawAlloc n align) (rawAllocPost n align) := by
  classical
  refine FTotalTriple.of_run fun m r rF hh hp hs => ?_
  obtain ⟨hh₁, hs₁⟩ := allocs_holds hh hs
  rw [rawAlloc_eq]
  by_cases hdn : m.allocDenied n
  · exact ⟨none, _, r, by simp only [hdn, ↓reduceIte], hh₁, hp, hs₁⟩
  cases hroom : m.roomFor n align
  · exact ⟨none, _, r, by simp only [hdn, ↓reduceIte]; rfl, hh₁, hp, hs₁⟩
  have hrun := alloc_run_eq { m with allocs := m.allocs + 1 } (kind := .heap)
    (by simpa using hroom)
  have ht := FTriple.alloc .heap n align ha hpos (by decide) rfl _ r rF hh₁ hp hs₁
  rw [hrun] at ht
  obtain ⟨r', hh', hq, hs'⟩ := ht
  exact ⟨some _, _, r', by simp [hdn, hrun], hh', hq, hs'⟩

/-- **`rawAlloc` of no bytes** (total): `null`, or a pointer to offset 0 of a new block without
bytes, which nothing can own. -/
theorem FTotalTriple.rawAllocZero (align : Nat) :
    FTotalTriple emp (Zig.rawAlloc 0 align)
      (fun q => ⟪∀ p, q = some p → p.block.isSome ∧ p.off = 0⟫) := by
  classical
  refine FTotalTriple.of_run fun m r rF hh hp hs => ?_
  obtain ⟨hh₁, hs₁⟩ := allocs_holds hh hs
  rw [rawAlloc_eq]
  by_cases hdn : m.allocDenied 0
  · exact ⟨none, _, r, by simp only [hdn, ↓reduceIte], hh₁, ⟨by simp, hp⟩, hs₁⟩
  cases hroom : m.roomFor 0 align
  · exact ⟨none, _, r, by simp only [hdn, ↓reduceIte]; rfl, hh₁, ⟨by simp, hp⟩, hs₁⟩
  have hrun := alloc_run_eq { m with allocs := m.allocs + 1 } (kind := .heap)
    (by simpa using hroom)
  have ht := FTriple.allocZero .heap align (by decide) _ r rF hh₁ hp hs₁
  rw [hrun] at ht
  obtain ⟨r', hh', hq, hs'⟩ := ht
  exact ⟨some ⟨some m.blocks.size, 0⟩, _, r', by simp [hdn, hrun], hh',
    ⟨fun p e => by cases e; exact hq.1, hq.2⟩, hs'⟩

/-- **`poisonFree` of a whole heap block** (total): the poison write and the free. Its bytes and
its full extent go. -/
@[fsym] theorem FTotalTriple.poisonFree {p : Ptr} {A S : Nat} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) :
    FTotalTriple (up (bytesAt p A S .heap bs) ⋆ bext b S .heap) (Zig.poisonFree p S)
      (fun _ => emp) := by
  refine FTotalTriple.of_runEq fun m r rF hh hp hs => ?_
  obtain ⟨blk, hb, hl, hsz, hK, hlo⟩ := hh.bauth (sep_comm hp)
  simp only [BlockKind.mappedLo] at hlo
  have hacc : m.access p S 1 = pure (b, blk, 0) := by
    simp [Mem.access, hpb, hb, hl, h0, hsz, hK, BlockKind.mappedLo, Nat.mod_one]
  let m₂ := m.recordAt b 0 S .write
  have hacc₂ : m₂.access p S 1 = pure (b, blk, 0) := hacc
  refine ⟨Zig.free p, m₂, ?_, Holds.congrMem (m := m) rfl rfl hh,
    ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩, hs.2.1, hs.2.2⟩,
    FTotalTriple.free hpb hS h0 hlo (by decide)⟩
  have e1 : (Zig.poisonFree p S).run m = (recordAccess b 0 S .write >>= fun _ => rawFree p S).run m := by
    simp [Zig.poisonFree, zig_unfold, hacc, hK, hsz, get, getThe, MonadStateOf.get, StateT.get]
  have e2 : (rawFree p S).run m₂ = (Zig.free p).run m₂ := by
    simp [rawFree, zig_unfold, hacc₂, hK, hsz, get, getThe, MonadStateOf.get, StateT.get]
  rw [e1, StateT.run_bind, recordAccess_run (noRace_of_singleThread hs.1.single _ _ _ _)]
  exact e2

end Full
end Zig
