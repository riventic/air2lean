import GlobalInit.Gen
import ZigLean.Sep

/-!
# Clients of explicit external initial state (L12)

`GlobalInit.Gen` is the retained translation of `air/0.16.0`: `extern var counter: u32`,
`extern const limit: u32` and `var scratch: u32 = undefined`. The translator gives `mem0` an
explicit `ext : ExternInit` parameter, one field per `extern` global in block order (counter is
block 0, limit block 1, scratch block 2). Every theorem below about the program start therefore
quantifies over `ext`, and states its assumption about external storage (here: `counter` is not
`maxInt(u32)`) as a hypothesis on `ext`. The `undefined` global is undefined bytes: reading it
before a store throws `.unspecified`.
-/

open GlobalInit Zig Assn

namespace GlobalInitClients

/-- The extern `counter` is block 0 of `mem0 ext`. -/
abbrev counter : Ptr := ⟨some 0, 0⟩

/-- Initialization order: three blocks, extern `counter`, extern `limit` and `scratch`, at
consecutive aligned addresses from 4096, with the kinds the source declares. -/
theorem mem0_blocks (ext : ExternInit) :
    (mem0 ext).blocks.map (fun b => (b.bytes, b.align, b.kind, b.live, b.addr)) =
      #[(Enc.encode ext.counter, 4, .global, true, 4096),
        (Enc.encode ext.limit, 4, .constGlobal, true, 4104),
        (Array.replicate 4 .undef, 4, .global, true, 4112)] := by
  simp [mem0, Mem.ofGlobals, Mem.addGlobal, alignUp, LawfulEnc.size_encode, Enc.size, intSize,
    intAlign]

/-- The memory at program start owns the extern counter with its external initial value. -/
theorem counter_init (ext : ExternInit) :
    ∃ h hF, Heap.Disjoint h hF ∧ (mem0 ext).heap = h ∪ hF ∧ pts counter 4 ext.counter h := by
  have hb : (mem0 ext).blocks[0]? = some ⟨Enc.encode ext.counter, 4, .global, true, 4096⟩ := by
    simp [mem0, Mem.ofGlobals, Mem.addGlobal, alignUp]
  obtain ⟨h, hF, hd, hm, hbytes⟩ := Mem.heap_split hb rfl
  exact ⟨h, hF, hd, hm, 4096, _, _, _, rfl, LawfulEnc.size_encode _, LawfulEnc.decode_encode _,
    hbytes, by simp⟩

/-- `bump` adds 1 to the counter and returns the new value. -/
theorem bump_spec (x : BitVec 32) (hx : x.toNat + 1 < 2 ^ 32) :
    Triple (pts counter 4 x) bump (fun r => ⌜r = x + 1⌝ ∗ pts counter 4 (x + 1)) := by
  apply Triple.of_run
  intro m hP hF hd hm hp hst
  obtain ⟨mA, hl, hmA, hstA⟩ := pts_load_run hp hm (by decide) hst
  obtain ⟨mB, hs, hstB, h', hd', hmB, hp'⟩ := pts_store_run hp hmA hd (by decide) hstA (x + 1#32)
  obtain ⟨mC, hl', hmC, hstC⟩ := pts_load_run hp' hmB (by decide) hstB
  have hov : x.uaddOverflow 1#32 = false := by
    have : x.toNat + 1 < 4294967296 := hx
    simp [BitVec.uaddOverflow]; omega
  refine ⟨x + 1, mC, h', ?_, hd', hmC, sep_lift.mpr ⟨rfl, hp'⟩, hstC⟩
  simp only [StateT.run, counter, pure, ExceptT.pure, ExceptT.mk] at hl hs hl'
  simp [bump, zig_unfold, Zig.add, hl, hs, hl', hov]

/-- `mem0 ext` as one literal memory: block addresses do not depend on the external values. -/
theorem mem0_eq (ext : ExternInit) :
    mem0 ext = { blocks := #[⟨Enc.encode ext.counter, 4, .global, true, 4096⟩,
      ⟨Enc.encode ext.limit, 4, .constGlobal, true, 4104⟩,
      ⟨Array.replicate 4 .undef, 4, .global, true, 4112⟩], nextAddr := 4117 } := by
  simp [mem0, Mem.ofGlobals, Mem.addGlobal, alignUp, LawfulEnc.size_encode, Enc.size, intSize,
    intAlign]

/-- The program start satisfies the sequential memory invariant of `Triple`. -/
theorem mem0_seq (ext : ExternInit) : (mem0 ext).Seq := by
  rw [mem0_eq]
  refine ⟨⟨by simp, by simp⟩, fun l c hc => ?_⟩
  obtain ⟨blk, hb, -, -, rfl⟩ := Mem.heap_some hc
  obtain ⟨b, o⟩ := l
  match b, hb with
  | 0, hb | 1, hb | 2, hb =>
    simp at hb; subst hb; simp [LawfulEnc.size_encode, Enc.size, intSize, intAlign, alignUp]

/-- From program start, `bump` returns the external initial counter plus one. The assumption
about external storage is the explicit hypothesis on `ext.counter`. -/
theorem bump_from_start (ext : ExternInit) (hx : ext.counter.toNat + 1 < 2 ^ 32) :
    match (bump.run (mem0 ext)).run with
    | some (.ok (r, _)) => r = ext.counter + 1
    | some (.error _) => False
    | none => True := by
  obtain ⟨h, hF, hd, hm, hp⟩ := counter_init ext
  have := bump_spec ext.counter hx (mem0 ext) h hF hd hm hp (mem0_seq ext)
  split
  · next r m' heq =>
    rw [heq] at this
    obtain ⟨hQ, -, -, hq, -⟩ := this
    exact (sep_lift.mp hq).1
  · next heq => rw [heq] at this; exact this
  · trivial

/-- The extern `const` reads as its external initial value, whatever that value is. -/
theorem readLimit_from_start (ext : ExternInit) :
    ((readLimit.run (mem0 ext)).run).map (·.map Prod.fst) = some (.ok ext.limit) := by
  have hfull : (Enc.encode ext.limit).extract 0 4 = Enc.encode ext.limit := by
    rw [← show (Enc.encode ext.limit).size = 4 from LawfulEnc.size_encode ext.limit]
    exact Array.extract_size
  rw [mem0_eq]
  simp [readLimit, load, loadBytes, recordAccess, Mem.access, raceAt, Enc.size, intSize,
    intAlign, alignUp, LawfulEnc.size_encode, hfull, LawfulEnc.decode_encode, set,
    MonadStateOf.set, StateT.set, zig_unfold]
  exact ⟨_, rfl, rfl⟩

/-- `undefined` is not a default: the first read of `scratch` from program start is
`.unspecified`, for every external initial state. -/
theorem readScratch_undefined (ext : ExternInit) :
    (readScratch.run (mem0 ext)).run = some (.error .unspecified) := by
  rw [mem0_eq]
  simp [readScratch, load, loadBytes, recordAccess, Mem.access, raceAt, Enc.decode, Enc.size,
    intSize, intAlign, alignUp, intOfBytes, byteBits, set, MonadStateOf.set, StateT.set,
    zig_unfold]
  rfl

end GlobalInitClients
