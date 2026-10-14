import ZigLean.Sep.Full.Atomic

/-!
# Why the arena's node header words are `wpts`, not `apts` (kernel-checked failure scenario)

A node of `std.heap.ArenaAllocator` is memory its child allocator handed out. The child's
`alloc` contract (`FAllocSpec`/`CAllocSpec`) grants a plain region (`granted`, `up` bytes): it
says nothing about the atomic layout over those bytes. Native code may have used them before
for an atomic object of another size (a client's `u128` atomic in a buffer of a
`FixedBufferAllocator` child, freed and handed out again), and the memory model keeps that
location until an atomic op over the bytes retires it.

The arena then writes the node header with plain stores (`reset`'s retaining modes and `alloc`'s
new-node path: `node.size = …; node.end_index = 0`). A plain store keeps every location. So the
header word is owned, holds its value and is 8-aligned, but the location over it is the stale one:

* `apts N v` (tag constraint `(N.off, 8)`: "the location over the word is `(N.off, 8)` or none")
  is **false** in that memory: `TagSat` fails (`no_apts`), so no proof can establish it after the
  header stores (`no_header_apts_triple`);
* `wpts N v` (an owned word with any tag constraint) is **true** (`header_wpts`); the atomic
  rules take a `wpts` (`FTTriple.atomicLoadW`, `cmpxchgHitW`, …), leaving an `apts`.

In a thread a `wpts` word has its rules too (MM-21, `HeaderMixCX.lean`: a mixed-size op retires
the stale location by the bytes it shares with it), so the arena's header words can be `wpts`:
the basis of `reset`'s retaining modes in `docs/alloc-arena.md`.

The memory `m0`: one 16-byte heap block (the fresh node's header) with one 16-byte atomic location
over it, the stale one.
-/

namespace Zig.Full.HeaderTagCX
open FAssn

def z8 : Array Byte := Array.replicate 8 (.int 0)
def z16 : Array Byte := Array.replicate 16 (.int 0)
def blk0 : Block := { bytes := z16, align := 16, kind := .heap, live := true, addr := 16 }
def msg0 : Msg := Msg.mk 0 z16 #[] #[] none none
/-- The stale location: a 16-byte atomic object over the whole node header. -/
def loc0 : ALoc := ALoc.mk 0 0 16 #[msg0]
def m0 : Mem := { blocks := #[blk0], atomics := #[loc0], nextMsg := 1 }
/-- The fresh node: its size word at offset 0, its `end_index` word at offset 8. -/
def N0 : Ptr := ⟨some 0, 0⟩

/-- The header stores of the new-node path (`Node.size` is a `u64` word). -/
def initHeader : MemM Unit := do
  Zig.store (α := BitVec 64) 8 N0 (16 : BitVec 64)
  Zig.store (α := BitVec 64) 8 (N0.add 8) (0 : BitVec 64)

/-- The plain stores run and keep the stale location. -/
theorem initHeader_shapes :
    ((initHeader.run m0).run.map fun r => r.map fun x => shapes x.2) = some (.ok [(0, 0, 16)]) := by
  decide +kernel

theorem m0_heap (l : Loc) :
    m0.heap l = if l.1 = 0 ∧ l.2 < 16 then some ⟨.int 0, 16, 16, .heap⟩ else none := by
  obtain ⟨b, o⟩ := l
  simp only [Mem.heap, m0, blk0, z16]
  rcases b with _ | b
  · by_cases ho : o < 16 <;> simp [ho, BlockKind.mappedLo]
  · simp

theorem tag_m0 {o : Nat} (ho : o < 16) : tagOf [(0, 0, 16)] 0 o = some (0, 16) := by
  simp [tagOf, Covers, List.find?, ho]

theorem m0_shapes : shapes m0 = [(0, 0, 16)] := rfl

theorem m0_fseq : m0.FSeq := by
  refine ⟨⟨⟨by decide, by simp [m0]⟩⟩, ⟨by simp [shapes, m0, loc0, ALoc.shape],
    by simp [shapes, m0, loc0, ALoc.shape]⟩, ?_, fun b blk hb _ => ?_⟩
  · intro b b' blk blk' hne hb hb' _
    simp only [m0] at hb hb'
    rcases b with _ | b <;> rcases b' with _ | b' <;> simp at hb hb' hne
  · simp only [m0] at hb
    rcases b with _ | b <;> simp at hb
    subst hb; simp [blk0, z16]

/-- The node's bytes owned with the memory's own tags; nothing in the frame. -/
def r0 : Res := ⟨m0.fheap, Know.none, Ghost.unit⟩
def rE : Res := ⟨FHeap.empty, Know.none, Ghost.unit⟩

theorem holds0 : Holds m0 r0 rE :=
  ⟨FHeap.disjoint_empty _, by simpa [r0, rE] using FMatch.fheap m0, Know.sub_none _,
    Know.sub_none _, GOk.unit⟩

/-- **The fresh node is what the child grants**: plain owned bytes (`up`), in a memory that holds. -/
theorem fresh_node : Holds m0 r0 rE ∧ up (bytesAt N0 16 16 .heap z16) r0 := by
  refine ⟨holds0, ⟨0, rfl, by decide, fun l => ?_⟩, rfl, rfl⟩
  obtain ⟨b, o⟩ := l
  show m0.fheap.erase (b, o) = _
  rw [fheap_erase, m0_heap]
  by_cases hb : b = 0
  · subst hb
    by_cases ho : o < 16
    · simp [ho, N0, z16]
    · simp [ho, N0, z16]
  · simp [hb]

/-- **No `apts` at the header word**: in `m0`, no resource owns the size word with the tag
constraint `(0, 8)`, whatever the value and the rest: the location over byte 0 is `(0, 16)`. -/
theorem no_apts_at {m : Mem} (hs : shapes m = [(0, 0, 16)]) (v : BitVec 64) (Q : FAssn)
    {r rF : Res} (hh : Holds m r rF) : ¬ (apts N0 v ⋆ Q) r := by
  rintro ⟨r₁, r₂, -, rfl, ⟨A, S, K, bs, -, -, hsz, -, -, -, b, hb, -, hl⟩, -⟩
  cases hb
  have e := hl (0, 0)
  rw [ite_eq_left ⟨rfl, by simp [N0], by simp [N0, hsz]⟩] at e
  have hu : ((r₁.heap ∪ r₂.heap) ∪ rF.heap) (0, 0) =
      some ⟨⟨bs[0 - (N0.off.toNat)]!, A, S, K⟩, some (N0.off.toNat, 8)⟩ := by
    rw [FHeap.union_apply, FHeap.union_apply, e]; rfl
  have ht := hh.heap.2 _ _ hu
  simp only [TagSat, hs, tag_m0 (by decide : (0 : Nat) < 16), N0] at ht
  simp at ht

theorem no_apts (v : BitVec 64) (Q : FAssn) {r rF : Res} (hh : Holds m0 r rF) : ¬ (apts N0 v ⋆ Q) r :=
  no_apts_at m0_shapes v Q hh

/-- **The `apts` header is unprovable**: no triple takes the fresh node's plain bytes through the
header stores to an `apts` size word (with any rest `Q`). -/
theorem no_header_apts_triple (Q : FAssn) :
    ¬ FTriple (up (bytesAt N0 16 16 .heap z16)) initHeader (fun _ => apts N0 16 ⋆ Q) := by
  intro h
  have hx := h m0 r0 rE fresh_node.1 fresh_node.2 m0_fseq
  have hs := initHeader_shapes
  revert hx hs
  generalize (initHeader.run m0).run = x
  rcases x with _ | _ | ⟨⟨⟩, m'⟩
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  intro hx hs
  simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq] at hs
  obtain ⟨r', hh, hq, -⟩ := hx
  exact no_apts_at hs 16 Q hh hq

/-- The two header words of `m0`'s node, each with the memory's tags. -/
def rLo : Res := ⟨fun l => if l.1 = 0 ∧ l.2 < 8 then m0.fheap l else none, Know.none, Ghost.unit⟩
def rHi : Res := ⟨fun l => if l.1 = 0 ∧ 8 ≤ l.2 then m0.fheap l else none, Know.none, Ghost.unit⟩

theorem fheap_m0 (b o : Nat) : m0.fheap (b, o) =
    if b = 0 ∧ o < 16 then some ⟨⟨.int 0, 16, 16, .heap⟩, some (0, 16)⟩ else none := by
  simp only [Mem.fheap, m0_heap, m0_shapes]
  by_cases h : b = 0 ∧ o < 16
  · obtain ⟨rfl, ho⟩ := h
    simp [ho, tag_m0 ho]
  · rw [ite_eq_right h, ite_eq_right h]; rfl

/-- **The header words are `wpts`** in `m0` (constraint: the stale location `(0, 16)`). -/
theorem header_wpts : Holds m0 r0 rE ∧ (wpts N0 0 ⋆ wpts (N0.add 8) 0) r0 := by
  refine ⟨holds0, rLo, rHi, fun l => ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, o⟩ := l
    by_cases h : o < 8
    · right; show (if b = 0 ∧ 8 ≤ o then _ else none) = none; rw [ite_eq_right (by omega)]
    · left; show (if b = 0 ∧ o < 8 then _ else none) = none; rw [ite_eq_right (by omega)]
  · show r0 = ⟨_, _, _⟩
    simp only [r0, rLo, rHi, Know.union_none, Ghost.add_unit]
    congr 1
    funext ⟨b, o⟩
    simp only [FHeap.union_apply, fheap_m0]
    by_cases h1 : b = 0 <;> by_cases h2 : o < 8 <;> by_cases h3 : o < 16 <;>
      simp [h1, h2, h3] <;> omega
  · refine ⟨16, 16, .heap, z8, some (0, 16), by decide, by decide, rfl, rfl,
      rfl, rfl, 0, rfl, by decide, fun ⟨b, o⟩ => ?_⟩
    show (if b = 0 ∧ o < 8 then m0.fheap (b, o) else none) = _
    rw [fheap_m0]
    by_cases h1 : b = 0 <;> by_cases h2 : o < 8 <;> by_cases h3 : o < 16 <;>
      simp [h1, h2, h3, N0, z8] <;> omega
  · refine ⟨16, 16, .heap, z8, some (0, 16), by decide, by decide, rfl, rfl,
      rfl, rfl, 0, rfl, by decide, fun ⟨b, o⟩ => ?_⟩
    show (if b = 0 ∧ 8 ≤ o then m0.fheap (b, o) else none) = _
    rw [fheap_m0]
    by_cases h1 : b = 0
    · subst h1
      by_cases h2 : 8 ≤ o
      · by_cases h3 : o < 16
        · have h4 : o - 8 < 8 := by omega
          simp [h2, h3, h4, N0, z8, Ptr.add]
        · simp [h2, h3, N0, z8, Ptr.add] <;> omega
      · simp [h2, N0, z8, Ptr.add]
    · simp [h1]

end Zig.Full.HeaderTagCX

-- check.sh: only the standard axioms.
#print axioms Zig.Full.HeaderTagCX.fresh_node
#print axioms Zig.Full.HeaderTagCX.no_apts
#print axioms Zig.Full.HeaderTagCX.no_header_apts_triple
#print axioms Zig.Full.HeaderTagCX.header_wpts
