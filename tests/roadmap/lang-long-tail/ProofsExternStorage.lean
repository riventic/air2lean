import LangLongTail.ExternStorage

/-!
# L12: pointer-bearing `extern` storage, on the retained translation

`LangLongTail.ExternStorage` is the translation of `air/extern_storage/0.16.0` (0.17.0 translates
to the same text; 0.15.2 and 0.14.1 to their own retained files, `check.sh`). The program
declares `extern var ext_counter: u32`, `extern const ext_name: [*:0]const u8`,
`extern var ext_head: ?*Node` and `extern var ext_slot: *u32`; `mem0 σ ext` holds their initial
values from `ext`, in block order, and then the external blocks `ext.storage`. Every theorem
quantifies over the placement `σ` and the external state `ext`: what the external definitions
are, and where their pointers point, are hypotheses on `ext`, never defaults.
-/

open ExternStorage Zig

namespace ExternStorageClients

/-- The program's own blocks: the externs and `local_node`, in declaration order. -/
abbrev globals (ext : ExternInit) : List (Array Byte × Nat × BlockKind) :=
  [(Enc.encode ext.ext_counter, 4, .global), (Enc.encode ext.ext_name, 8, .constGlobal),
   (Enc.encode ext.ext_head, 8, .global),
   (Enc.encode ({ v := 100, next := none } : Node), 8, .global),
   (Enc.encode ext.ext_slot, 8, .global)]

theorem mem0_eq (σ : Placement) (ext : ExternInit) :
    mem0 σ ext = Mem.ofGlobals σ (globals ext ++ ext.storage.map ExternBlock.global) := rfl

/-- Initialization order: the five program blocks, then external block `i` at `5 + i`. -/
theorem mem0_extern (σ : Placement) (ext : ExternInit) (i : Nat) :
    ((mem0 σ ext).blocks[5 + i]?).map (fun b => (b.bytes, b.align, b.kind)) =
      ext.storage[i]?.map fun b => (b.bytes, b.align, if b.writable then .global else .constGlobal) := by
  rw [mem0_eq, show 5 + i = (globals ext).length + i from rfl, Mem.ofGlobals_extern]
  cases ext.storage[i]? <;> simp

/-- The extern `ext_slot` is block 4 and holds its external initial value. -/
theorem mem0_slot (σ : Placement) (ext : ExternInit) :
    ((mem0 σ ext).blocks[4]?).map (fun b => (b.bytes, b.align, b.kind)) =
      some (Enc.encode ext.ext_slot, 8, .global) := by
  rw [mem0_eq, Mem.ofGlobals_getElem?]
  rfl

/-- `slotValue` from program start reads the cell that the external `ext_slot` points to: when
`ext_slot` points to the start of external block `i`, a writable 4-byte cell holding `x`, the
result is `x`, for every placement. -/
theorem slotValue_from_start (σ : Placement) (ext : ExternInit) (i : Nat) (x : BitVec 32)
    (hslot : ext.ext_slot = ⟨some (5 + i), 0⟩)
    (hcell : ext.storage[i]? = some { bytes := Enc.encode x, align := 4, writable := true }) :
    ((slotValue.run (mem0 σ ext)).run).map (·.map Prod.fst) = some (.ok x) := by
  rw [mem0_eq]
  generalize hgs : globals ext ++ ext.storage.map ExternBlock.global = gs
  have h4 : (Mem.ofGlobals σ gs).blocks[4]? =
      some ⟨Enc.encode ext.ext_slot, 8, .global, true, Mem.globalAddr σ gs 4⟩ := by
    rw [Mem.ofGlobals_getElem?, ← hgs]; rfl
  have hi : (Mem.ofGlobals σ gs).blocks[5 + i]? =
      some ⟨Enc.encode x, 4, .global, true, Mem.globalAddr σ gs (5 + i)⟩ := by
    rw [← hgs, show 5 + i = (globals ext).length + i from rfl, Mem.ofGlobals_extern, hcell]; rfl
  have hA4 := Mem.ofGlobals_addr_mod h4 (by simp)
  have hAi := Mem.ofGlobals_addr_mod hi (by simp)
  have hsz : (Enc.encode x).size = 4 := LawfulEnc.size_encode x
  have hfull : (Enc.encode x).extract 0 4 = Enc.encode x := by
    rw [← hsz]; exact Array.extract_size
  have hpfull : (Enc.encode ext.ext_slot).extract 0 8 = Enc.encode ext.ext_slot := by
    rw [← show (Enc.encode ext.ext_slot).size = 8 from LawfulEnc.size_encode _]
    exact Array.extract_size
  rw [hslot] at h4 hpfull
  simp at hA4 hAi
  simp [h4, hi, hA4, hAi, hfull, hpfull, slotValue, load, loadBytes, recordAccessIn, recordAccess,
    Mem.access,
    raceCheck, Mem.solo, raceAt, Enc.size, intSize, intAlign, alignUp, LawfulEnc.size_encode,
    LawfulEnc.decode_encode, set, MonadStateOf.set, StateT.set, zig_unfold]
  exact ⟨_, rfl, rfl⟩

end ExternStorageClients
