import ZigLean.Sep.AllocSpec.Wrappers

/-!
# `AllocSpec` is satisfiable and not vacuous

* `Bump`: a bump allocator over one buffer, written in the monadic style of generated code. Its
  state is in memory at `ctx`: the buffer pointer (offset 0) and the end index (offset 8, a
  `u64`). `alloc` aligns the next address with `ptrAddr` and `alignUp`; `resize` and `remap`
  refuse (`noResize`, `noRemap`); `free` leaks (as `ArenaAllocator` does for all but the last
  allocation). `Bump.allocSpec`: it satisfies `AllocSpec` in the total logic, for every
  context and buffer.
* `Static`: an allocator that hands out the same buffer on every call (a double issue).
  `Static.not_allocSpec`: no invariant that holds in some memory makes it satisfy `AllocSpec`,
  even in the partial logic: two live grants would overlap.
* `trapFree_alloc_none`: an allocator whose `free` traps can satisfy `AllocSpec` only if its
  `alloc` never succeeds: the specification of `free` is not vacuous.
-/

namespace Zig

open Assn

/-- `ptrAddr` of the start of a nonempty owned range: the block's address plus the offset. -/
theorem ptrAddr_regionIn {q : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    (hpos : 0 < bs.size) :
    TotalTriple (regionIn q A S K a bs) (ptrAddr q)
      (fun r => ⌜r = (A : Int) + q.off⌝ ∗ regionIn q A S K a bs) := by
  intro m hP hF hd hm hp hst
  obtain ⟨b, blk, hqb, hblk, -, hA, -⟩ :=
    Region.bytesAt_block hp.2.2 (Region.Heap.sub_of_eq hm) hpos
  refine ⟨_, m, hP, ?_, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hst⟩
  simp [ptrAddr, hqb, hblk, hA, zig_unfold, get, getThe, MonadStateOf.get, StateT.get]

namespace Bump

/-- Bytes the allocator has given up (padding, leaked regions): any heap. -/
def junk : Assn := fun _ => True

/-- The padding before the next `2 ^ k`-aligned address. -/
def padding (addr : Int) (k : Nat) : Nat := alignUp addr.toNat (2 ^ k) - addr.toNat

def alloc (cap : Nat) (ctx : Ptr) (len : BitVec 64) (k : Nat) (_ra : BitVec 64) :
    MemM (Option Ptr) :=
  load Ptr 8 ctx >>= fun buf =>
  load (BitVec 64) 8 (ctx.add 8) >>= fun e =>
  if cap < e.toNat + len.toNat then pure none else
  ptrAddr (buf.add e.toNat) >>= fun addr =>
  if cap < e.toNat + padding addr k + len.toNat then pure none else
  store 8 (ctx.add 8) (BitVec.ofNat 64 (e.toNat + padding addr k + len.toNat)) >>= fun _ =>
  pure (some (buf.add ((e.toNat + padding addr k : Nat) : Int)))

/-- A bump allocator over a buffer of `cap` bytes. -/
def vtable (cap : Nat) : RawVTable where
  alloc := alloc cap
  resize _ _ _ _ _ := pure false
  remap _ _ _ _ _ := pure none
  free _ _ _ _ := pure ()

/-- The state: the buffer pointer, the end index `e`, and the free bytes from `e` on. -/
def state (ctx buf : Ptr) (e A S : Nat) (K : BlockKind) (tail : Array Byte) : Assn :=
  pts ctx 8 buf ∗ (pts (ctx.add 8) 8 (BitVec.ofNat 64 e) ∗
    (regionIn (buf.add (e : Int)) A S K 1 tail ∗ junk))

def Ok (cap : Nat) (buf : Ptr) (e : Nat) (tail : Array Byte) : Prop :=
  e ≤ cap ∧ tail.size = cap - e ∧ cap < 2 ^ 64 ∧ 0 ≤ buf.off

/-- The invariant. The bump allocator needs no token: it never takes a region back. -/
def inv (cap : Nat) (ctx buf : Ptr) : AllocInv where
  own := Assn.ex fun e => Assn.ex fun A => Assn.ex fun S => Assn.ex fun K => Assn.ex fun tail =>
    ⌜Ok cap buf e tail⌝ ∗ state ctx buf e A S K tail
  tok _ _ _ := emp

theorem own_intro {cap : Nat} {ctx buf : Ptr} {e A S : Nat} {K : BlockKind} {tail : Array Byte}
    {h : Heap} (hok : Ok cap buf e tail) (hs : state ctx buf e A S K tail h) :
    (inv cap ctx buf).own h :=
  ⟨e, A, S, K, tail, sep_lift.mpr ⟨hok, hs⟩⟩

/-- Anything framed onto the state is junk. -/
theorem state_absorb {ctx buf : Ptr} {e A S : Nat} {K : BlockKind} {tail : Array Byte}
    {G : Assn} {h : Heap} (hs : (state ctx buf e A S K tail ∗ G) h) :
    state ctx buf e A S K tail h := by
  unfold state at hs ⊢
  have h2 : (pts ctx 8 buf ∗ (pts (ctx.add 8) 8 (BitVec.ofNat 64 e) ∗
      (regionIn (buf.add (e : Int)) A S K 1 tail ∗ (G ∗ junk)))) h := by
    sep_normalize at hs ⊢; exact hs
  exact sep_mono (fun _ x => x) (sep_mono (fun _ x => x) (sep_mono (fun _ x => x)
    (fun _ _ => trivial))) h2

theorem own_absorb {cap : Nat} {ctx buf : Ptr} {G : Assn} {h : Heap}
    (hs : ((inv cap ctx buf).own ∗ G) h) : (inv cap ctx buf).own h := by
  obtain ⟨h₁, h₂, hd, rfl, ⟨e, A, S, K, tail, hs⟩, hg⟩ := hs
  obtain ⟨hok, hs⟩ := sep_lift.mp hs
  exact own_intro hok (state_absorb ⟨h₁, h₂, hd, rfl, hs, hg⟩)

theorem ptr_size : (0 : Nat) < Enc.size Ptr := by decide

theorem u64_size : (0 : Nat) < Enc.size (BitVec 64) := by decide

theorem alloc_spec (cap : Nat) (ctx buf : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64)
    (hl : 0 < len.toNat) :
    TotalTriple (inv cap ctx buf).own (alloc cap ctx len k ra)
      (allocPost (inv cap ctx buf) len.toNat k) := by
  refine TotalTriple.ex fun e => TotalTriple.ex fun A => TotalTriple.ex fun S =>
    TotalTriple.ex fun K => TotalTriple.ex fun tail => TotalTriple.lift fun hok => ?_
  obtain ⟨he, hts, hcap, hoff⟩ := hok
  have heN : (BitVec.ofNat 64 e).toNat = e := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have back : ∀ h, state ctx buf e A S K tail h → (inv cap ctx buf).own h :=
    fun h hs => own_intro ⟨he, hts, hcap, hoff⟩ hs
  unfold alloc
  -- load the buffer pointer
  refine TotalTriple.bind (TotalTriple.frame (TotalTriple.load (p := ctx) (a := 8) (v := buf)
    ptr_size)) fun b' => ?_
  refine TotalTriple.conseq ?_ (fun h hp => sep_assoc hp) (fun _ _ h => h)
  refine TotalTriple.lift fun hb => ?_
  subst hb
  -- load the end index
  refine TotalTriple.bind (TotalTriple.conseq (TotalTriple.frame
    (R := pts ctx 8 b' ∗ (regionIn (b'.add (e : Int)) A S K 1 tail ∗ junk))
    (TotalTriple.load (p := ctx.add 8) (a := 8) (v := BitVec.ofNat 64 e) u64_size))
    (fun h hp => by rw [sep_left_comm_eq]; exact hp) (fun _ _ h => h)) fun e' => ?_
  refine TotalTriple.conseq ?_ (fun h hp => sep_assoc hp) (fun _ _ h => h)
  refine TotalTriple.lift fun he' => ?_
  subst he'
  simp only [heN]
  split
  · exact Logic.ret' Logic.total _ fun h hp => back h (by unfold state; rw [sep_left_comm_eq]; exact hp)
  rename_i hfit
  have hpos : 0 < tail.size := by omega
  -- the address of the free bytes
  refine TotalTriple.bind (TotalTriple.conseq (TotalTriple.frame
    (R := pts (ctx.add 8) 8 (BitVec.ofNat 64 e) ∗ (pts ctx 8 b' ∗ junk))
    (ptrAddr_regionIn (q := b'.add (e : Int)) (A := A) (S := S) (K := K) (a := 1) hpos))
    (fun h hp => by sep_normalize at hp ⊢; exact hp) (fun _ _ h => h)) fun addr => ?_
  refine TotalTriple.conseq ?_ (fun h hp => sep_assoc hp) (fun _ _ h => h)
  refine TotalTriple.lift fun ha => ?_
  subst ha
  have hoffe : (b'.add (e : Int)).off.toNat = b'.off.toNat + e := by simp [Ptr.add]; omega
  have haddr : ((A : Int) + (b'.add (e : Int)).off).toNat = A + (b'.add (e : Int)).off.toNat := by
    simp [Ptr.add]; omega
  split
  · exact Logic.ret' Logic.total _ fun h hp => back h (by unfold state; sep_normalize at hp ⊢; exact hp)
  rename_i hfit2
  -- store the new end index
  refine TotalTriple.bind (TotalTriple.conseq (TotalTriple.frame
    (R := regionIn (b'.add (e : Int)) A S K 1 tail ∗ (pts ctx 8 b' ∗ junk))
    (TotalTriple.store (p := ctx.add 8) (a := 8) (v := BitVec.ofNat 64 e) u64_size
      (BitVec.ofNat 64 (e + padding ((A : Int) + (b'.add (e : Int)).off) k + len.toNat))))
    (fun h hp => by sep_normalize at hp ⊢; exact hp) (fun _ _ h => h)) fun _ => ?_
  refine Logic.ret' Logic.total _ fun h hp => ?_
  -- carve the free bytes: padding (junk), the new region, the new free bytes
  generalize hpd : padding ((A : Int) + (b'.add (e : Int)).off) k = pad at hp hfit2 ⊢
  have hal : (A + (b'.add (e : Int)).off.toNat + pad) % 2 ^ k = 0 := by
    rw [← hpd, padding, haddr]
    have := le_alignUp (A + (b'.add (e : Int)).off.toNat) (2 ^ k)
    rw [Nat.add_sub_cancel' this]
    exact alignUp_mod _ _ (Nat.two_pow_pos k)
  have hfit3 : pad + len.toNat ≤ tail.size := by omega
  have e3 : e + (pad + len.toNat) = e + pad + len.toNat := by omega
  have hp2 := sep_mono (fun _ x => x) (sep_mono (fun _ x => by
    have hc := Region.regionIn_carve x (pad := pad) (len := len.toNat) hfit3 hal
    rw [Region.Ptr.add_add_nat, Region.Ptr.add_add_nat, e3] at hc
    exact hc) (fun _ x => x)) hp
  have hp3 : ((pts ctx 8 b' ∗ (pts (ctx.add 8) 8 (BitVec.ofNat 64 (e + pad + len.toNat)) ∗
      (regionIn (b'.add ((e + pad + len.toNat : Nat) : Int)) A S K 1
          ((tail.extract pad tail.size).extract len.toNat (tail.extract pad tail.size).size) ∗
        (regionIn (b'.add ((e : Nat) : Int)) A S K 1 (tail.extract 0 pad) ∗ junk)))) ∗
      regionIn (b'.add ((e + pad : Nat) : Int)) A S K (2 ^ k)
        ((tail.extract pad tail.size).extract 0 len.toNat)) h := by
    sep_normalize at hp2 ⊢; exact hp2
  refine sep_mono (fun _ x => own_intro (e := e + pad + len.toNat) ?_ ?_)
    (fun _ x => ⟨(tail.extract pad tail.size).extract 0 len.toNat,
      sep_lift.mpr ⟨by simp; omega, sep_emp.mpr (region_of_regionIn x)⟩⟩) hp3
  · exact ⟨by omega, by simp; omega, hcap, hoff⟩
  · unfold state
    exact sep_mono (fun _ y => y) (sep_mono (fun _ y => y) (sep_mono (fun _ y => y)
      (fun _ _ => trivial))) x

theorem allocSpec (cap : Nat) (ctx buf : Ptr) :
    AllocSpec Logic.total (vtable cap) ctx (inv cap ctx buf) where
  alloc len k ra hl _ := alloc_spec cap ctx buf len k ra hl
  resize _ _ _ _ _ _ _ _ _ := Logic.ret' Logic.total _ fun _ hp => hp
  remap _ _ _ _ _ _ _ _ _ := Logic.ret' Logic.total _ fun _ hp => hp
  free _ _ _ _ _ _ _ := Logic.ret' Logic.total _ fun _ hp => own_absorb hp

/-- So every wrapper contract holds for the bump allocator, e.g. `realloc`. -/
example (cap : Nat) (ctx buf : Ptr) (size k : Nat) (old : Slice) (newN ra : BitVec 64)
    (bs : Array Byte) (hk : k < 64) (hsize : 0 < size) (hsz : bs.size = old.len.toNat * size)
    (hs : bs.size < 2 ^ 64) :
    TotalTriple ((inv cap ctx buf).own ∗ Wrap.owned (inv cap ctx buf) k old.ptr bs)
      (Wrap.realloc (vtable cap) ctx size k old newN ra)
      (Wrap.reallocResult (inv cap ctx buf) k size old newN bs) :=
  Wrap.realloc_spec (allocSpec cap ctx buf) size k old newN ra bs hk hsize hsz hs

end Bump

/-! ## Negative checks -/

namespace Static

/-- Every `alloc` returns the same buffer `p`. -/
def vtable (p : Ptr) : RawVTable where
  alloc _ _ _ _ := pure (some p)
  resize _ _ _ _ _ := pure false
  remap _ _ _ _ _ := pure none
  free _ _ _ _ := pure ()

/-- A granted nonempty region owns the cell at its start. -/
theorem granted_cell {I : AllocInv} {p : Ptr} {k n : Nat} {bs : Array Byte} {h : Heap}
    (hg : (⌜bs.size = n⌝ ∗ granted I p k bs) h) (hn : 0 < n) :
    ∃ b, p.block = some b ∧ h (b, p.off.toNat) ≠ none := by
  obtain ⟨hs, hg⟩ := sep_lift.mp hg
  obtain ⟨h₁, h₂, -, rfl, ⟨A, S, K, -, -, b, hpb, -, hl⟩, -⟩ := hg
  refine ⟨b, hpb, ?_⟩
  rw [Heap.union_apply, hl]
  simp; omega

/-- No invariant that holds in some memory makes the static allocator satisfy `AllocSpec`:
the second `alloc` would grant bytes that the first grant still owns. -/
theorem not_allocSpec (p ctx : Ptr) (I : AllocInv)
    (hsat : ∃ m hP hF, Heap.Disjoint hP hF ∧ m.heap = hP ∪ hF ∧ I.own hP ∧ m.Seq) :
    ¬ AllocSpec Logic.partial (vtable p) ctx I := by
  intro hs
  obtain ⟨m, hP, hF, hd, hm, hI, hst⟩ := hsat
  have t := hs.alloc 1 0 0 (by decide) (by decide)
  have r1 : ∃ hQ, Heap.Disjoint hQ hF ∧ m.heap = hQ ∪ hF ∧
      allocPost I (1 : BitVec 64).toNat 0 (some p) hQ ∧ m.Seq := t m hP hF hd hm hI hst
  obtain ⟨hQ, hd₁, hm₁, ⟨hI₁, hG₁, hdIG, rfl, hI₁', bs₁, hg₁⟩, -⟩ := r1
  obtain ⟨hdIF, hdGF⟩ := Heap.disjoint_union_left.mp hd₁
  have r2 : ∃ hQ, Heap.Disjoint hQ (hG₁ ∪ hF) ∧ m.heap = hQ ∪ (hG₁ ∪ hF) ∧
      allocPost I (1 : BitVec 64).toNat 0 (some p) hQ ∧ m.Seq :=
    t m hI₁ (hG₁ ∪ hF) (Heap.disjoint_union_right.mpr ⟨hdIG, hdIF⟩)
      (by rw [hm₁, Heap.union_assoc]) hI₁' hst
  obtain ⟨hQ₂, hd₂, -, ⟨hI₂, hG₂, -, rfl, -, bs₂, hg₂⟩, -⟩ := r2
  obtain ⟨b, hpb, hc₁⟩ := granted_cell hg₁ (by decide)
  obtain ⟨b', hpb', hc₂⟩ := granted_cell hg₂ (by decide)
  rw [hpb] at hpb'; cases hpb'
  rcases hd₂ (b, p.off.toNat) with e | e
  · simp [e] at hc₂
  · simp [e] at hc₁

end Static

/-- An allocator whose `free` traps satisfies `AllocSpec` only if no `alloc` succeeds. -/
theorem trapFree_alloc_none {vt : RawVTable} {ctx : Ptr} {I : AllocInv}
    (hfree : ∀ s k ra m, (vt.free ctx s k ra).run m = throw .illegal)
    (hs : AllocSpec Logic.partial vt ctx I) {m m' : Mem} {hP hF : Heap} {len : BitVec 64}
    {k : Nat} {ra : BitVec 64} {p : Ptr} (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF)
    (hI : I.own hP) (hst : m.Seq) (hl : 0 < len.toNat) (hk : k < 64)
    (hrun : (vt.alloc ctx len k ra).run m = pure (some p, m')) : False := by
  have r := hs.alloc len k ra hl hk m hP hF hd hm hI hst
  rw [hrun] at r
  obtain ⟨hQ, hd', hm', ⟨hI', hG, hdd, rfl, hI'', bs, hg⟩, hst'⟩ := r
  obtain ⟨hsz, hg⟩ := sep_lift.mp hg
  have f := hs.free ⟨p, len⟩ k ra bs hk (by rw [hsz]) (by omega) m' (hI' ∪ hG) hF hd' hm'
    ⟨hI', hG, hdd, rfl, hI'', hg⟩ hst'
  rw [hfree] at f
  exact f

end Bump

end Zig
