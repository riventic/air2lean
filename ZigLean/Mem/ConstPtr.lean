import ZigLean.Mem.Lemmas

/-!
# Constant pointer bases: explicit provenance and offsets (L06)

A Zig pointer constant is an InternPool `{ base_addr, byte_offset }` whose base is either a
root (`nav`/`uav` global, `int` address, comptime-only object) or a projection of another
pointer constant (`field`, `opt_payload`, `eu_payload`; an array element is the parent's
`byte_offset`). A `field` of an `auto` union (tagged or bare) is its payload; a member of an
`extern` or `packed` union is its parent pointer. The exporter (`zig-patch/air-json/json.zig`, `resolvePtr`) walks such a
chain of arbitrary nesting to one existing global identity and a checked byte offset, or to
an explicit `unsupported` reason. The translator emits the result as `⟨some block, off⟩`.

This module states that resolution as an explicit object/provenance model:

* `Path`: a root plus the projections applied to it, nearest the root first
  (`elem ∘ field ∘ errPayload ∘ field` of a global, constant slice pointers, …);
* `resolve`: the constant (exporter) view, a sum of offsets on the root's block, or a
  `Failure` (unbacked `int` address, comptime-only object, unknown global, depth, overflow);
* `runtime`: the runtime view, each projection applied as the instruction that
  `Air2Lean/Emit.lean` emits for it (`Ptr.add`, `errPayloadPtr`, `Ptr.elem`).

Proved: a resolved constant equals the runtime projection chain from its global root
(`resolve_eq_runtime`), keeps that root's block (`resolve_block`), composes under nesting
(`resolve_append`, `resolve_snoc`), and two constants alias exactly when they have the same
root and total offset (`resolve_eq_iff`). Sibling fields, distinct array elements, a payload
and its error code, a union's payload and its tag, and distinct globals are disjoint
(`*_disjoint`); all members of one union alias (`unionMembers_alias`). Unbacked and
comptime-only roots never resolve (`resolve_int`, `resolve_comptimeOnly`), and the model
memory rejects any access through a block-less pointer (`access_unbacked`).

The LLVM section records the Zig 0.14.1–0.17.0 `codegen/llvm.zig` `lowerPtr` offset for an
`eu_payload` constant (it measures the error union type instead of its payload) and proves
exactly which payloads it misplaces (`llvmPayloadOffset_ne_iff`): a nonzero-size payload of
alignment below 2, which it addresses at the error code. The translator rejects such
constants on the `stage2_llvm` profile (`tests/roadmap/const-bases`). Union-member bases:
`tests/roadmap/union-bases`.

Proof-only module: it imports `ZigLean.Mem.Lemmas`, so it is not part of `ZigLean.lean`.
-/

namespace Zig.ConstPtr

/-- One resolved projection of a constant pointer base. -/
inductive Proj where
  /-- `field`: a struct/tuple field at its compiler byte offset, or a slice's `ptr` (0) or
  `len` (8) field. -/
  | field (off : Nat)
  /-- `opt_payload` of a non-pointer-like optional: the payload starts the optional. -/
  | optPayload
  /-- `eu_payload` of `E!T`, where `T` has model size `size` and alignment `align`. -/
  | errPayload (size align : Nat)
  /-- An element of an array or many-item pointer. Sema folds `&a[i]` of a runtime array
  into the parent's `byte_offset`, `stride * index`. -/
  | elem (stride index : Nat)
  /-- `field` of an `auto` union (tagged, or bare with its ReleaseSafe safety tag): member
  `index` is the payload, at `unionPayloadOffset tagSize tagAlign payloadAlign` whatever
  `index` is. An `extern` or `packed` union member is no projection: Sema's `Value.ptrField`
  keeps the parent pointer (`externMember_step`). -/
  | unionPayload (index tagSize tagAlign payloadAlign : Nat)
  deriving DecidableEq, Repr

/-- The payload offset of an `auto` union whose tag has size `ts` and alignment `ta`, and
whose most aligned field has alignment `pa`: the more aligned of tag and payload first, the
tag if equal. This is Zig 0.14.1–0.17.0's `Type.structFieldOffset` of a union with a runtime
tag (also `codegen.lowerPtr` and `codegen/llvm.zig`), and the payload offset of
`Air2Lean/Check.lean`'s `unionLayout`, which the generated `Zig.Enc` of a tagged union uses. -/
def unionPayloadOffset (ts ta pa : Nat) : Nat := if pa ≤ ta then alignUp ts pa else 0

/-- The tag offset of that union, whose largest field has size `ps` (`unionLayout`). -/
def unionTagOffset (ta ps pa : Nat) : Nat := if pa ≤ ta then 0 else alignUp ps ta

/-- The byte offset one projection adds. -/
def Proj.delta : Proj → Nat
  | .field off => off
  | .optPayload => 0
  | .errPayload size align => (errUnionOffsets size align).2
  | .elem stride index => stride * index
  | .unionPayload _ ts ta pa => unionPayloadOffset ts ta pa

/-- The runtime instruction for one projection, as `Air2Lean/Emit.lean` emits it:
`struct_field_ptr`/`ptr_slice_*_ptr` (`Ptr.add`), `optional_payload_ptr` (the same pointer),
`unwrap_errunion_payload_ptr` (`errPayloadPtr`), `ptr_elem_ptr` (`Ptr.elem`) and a union's
`struct_field_ptr` (`Ptr.add` of `FCtx.fieldOffsetIn`'s payload offset). -/
def Proj.step : Proj → Ptr → Ptr
  | .field off, p => p.add off
  | .optPayload, p => p
  | .errPayload size align, p => p.add (errUnionOffsets size align).2
  | .elem stride index, p => p.elem stride (BitVec.ofNat 64 index)
  | .unionPayload _ ts ta pa, p => p.add (unionPayloadOffset ts ta pa)

/-- Where a constant pointer chain ends. -/
inductive Root where
  /-- `nav`/`uav`: an existing global identity (the exporter's global table index). -/
  | global (id : Nat)
  /-- `int`: a fixed address (`@ptrFromInt`) with no backing object. -/
  | int (addr : Nat)
  /-- `comptime_alloc`, `comptime_field`, `arr_elem`: no runtime object. -/
  | comptimeOnly (kind : String)
  deriving DecidableEq, Repr

/-- A constant pointer: a root and its projections, nearest the root first. -/
structure Path where
  root : Root
  projs : List Proj
  deriving DecidableEq, Repr

/-- Why a constant pointer has no object/provenance in the model. Each is an explicit error,
never a fabricated block. -/
inductive Failure where
  | unbacked (addr : Nat)
  | comptimeOnly (kind : String)
  | unknownGlobal (id : Nat)
  | depth
  | overflow
  deriving DecidableEq, Repr

/-- The exporter's projection budget (`pointer-offset.zig`, `Walk.remaining`). -/
def maxDepth : Nat := 64

/-- Offsets are `u64` in the exporter; a sum that does not fit is rejected. -/
def addrLimit : Nat := 2 ^ 64

/-- The total byte offset of a projection chain. -/
def total (ps : List Proj) : Nat := (ps.map Proj.delta).sum

/-- The constant view: resolve a path against the global-to-block map `blocks`. -/
def resolve (blocks : Nat → Option BlockId) (p : Path) : Except Failure Ptr :=
  match p.root with
  | .int addr => .error (.unbacked addr)
  | .comptimeOnly kind => .error (.comptimeOnly kind)
  | .global g =>
    match blocks g with
    | none => .error (.unknownGlobal g)
    | some b =>
      if maxDepth < p.projs.length then .error .depth
      else if addrLimit ≤ total p.projs then .error .overflow
      else .ok ⟨some b, total p.projs⟩

/-- The runtime view: apply each projection's emitted instruction to `root`. -/
def runtime (root : Ptr) (ps : List Proj) : Ptr := ps.foldl (fun p s => s.step p) root

/-! ## Offsets and nesting -/

@[simp] theorem total_nil : total [] = 0 := rfl

@[simp] theorem total_cons (s : Proj) (ps : List Proj) : total (s :: ps) = s.delta + total ps := by
  simp [total]

theorem total_append (ps qs : List Proj) : total (ps ++ qs) = total ps + total qs := by
  simp [total]

/-- Each instruction adds exactly its projection's offset, provided an element offset fits
the 64-bit index (`Ptr.elem` takes a `usize`). -/
theorem Proj.step_eq_add (s : Proj) (p : Ptr) (h : s.delta < addrLimit) :
    s.step p = p.add s.delta := by
  cases s with
  | field off => rfl
  | optPayload => simp [Proj.step, Proj.delta, Ptr.add]
  | errPayload size align => rfl
  | unionPayload _ _ _ _ => rfl
  | elem stride index =>
    have hmod : stride * (index % 2 ^ 64) = stride * index := by
      rcases Nat.eq_zero_or_pos stride with hs | hs
      · simp [hs]
      · have := Nat.le_mul_of_pos_left index hs
        simp only [Proj.delta, addrLimit] at h
        rw [Nat.mod_eq_of_lt (by omega)]
    simp only [Proj.step, Proj.delta, Ptr.elem, BitVec.toNat_ofNat]
    rw [← Int.natCast_mul, hmod]

theorem runtime_append (root : Ptr) (ps qs : List Proj) :
    runtime root (ps ++ qs) = runtime (runtime root ps) qs := by
  simp [runtime, List.foldl_append]

/-- The runtime chain is the root plus the total offset, when that offset fits. -/
theorem runtime_eq_add (root : Ptr) (ps : List Proj) (h : total ps < addrLimit) :
    runtime root ps = root.add (total ps) := by
  induction ps generalizing root with
  | nil => simp [runtime, Ptr.add]
  | cons s ps ih =>
    simp only [total_cons] at h
    have hs : s.delta < addrLimit := by omega
    have hps : total ps < addrLimit := by omega
    show runtime (s.step root) ps = _
    rw [ih _ hps, s.step_eq_add root hs]
    simp [Ptr.add, Int.add_assoc]

/-! ## Identity and offset retention -/

/-- Exactly when a global-rooted path resolves, and to what. -/
theorem resolve_global_eq_ok {blocks : Nat → Option BlockId} {g : Nat} {ps : List Proj}
    {q : Ptr} :
    resolve blocks ⟨.global g, ps⟩ = .ok q ↔ ∃ b, blocks g = some b ∧
      ps.length ≤ maxDepth ∧ total ps < addrLimit ∧ q = ⟨some b, total ps⟩ := by
  simp only [resolve]
  cases hb : blocks g with
  | none => simp
  | some b =>
    by_cases hd : maxDepth < ps.length
    · simp only [hd, ite_true]
      simp only [reduceCtorEq, false_iff, not_exists, not_and, Option.some.injEq]
      intro b' _ h1; omega
    · by_cases ho : addrLimit ≤ total ps
      · simp only [hd, ho, ite_true, ite_false]
        simp only [reduceCtorEq, false_iff, not_exists, not_and, Option.some.injEq]
        intro b' _ _ h2; omega
      · simp only [hd, ho, ite_false, Except.ok.injEq, Option.some.injEq, exists_eq_left']
        constructor
        · rintro rfl; exact ⟨by omega, by omega, rfl⟩
        · rintro ⟨-, -, rfl⟩; rfl

/-- Only a global root resolves. -/
theorem resolve_root {blocks : Nat → Option BlockId} {p : Path} {q : Ptr}
    (h : resolve blocks p = .ok q) : ∃ g, p.root = .global g := by
  obtain ⟨root, ps⟩ := p
  cases root with
  | global g => exact ⟨g, rfl⟩
  | int a => simp [resolve] at h
  | comptimeOnly k => simp [resolve] at h

/-- A resolved constant is the runtime projection chain from its global's root pointer. -/
theorem resolve_eq_runtime {blocks : Nat → Option BlockId} {p : Path} {q : Ptr}
    (h : resolve blocks p = .ok q) :
    ∃ g b, p.root = .global g ∧ blocks g = some b ∧ q = runtime ⟨some b, 0⟩ p.projs := by
  obtain ⟨g, hr⟩ := resolve_root h
  obtain ⟨root, ps⟩ := p
  simp only at hr; subst hr
  obtain ⟨b, hb, -, ho, rfl⟩ := resolve_global_eq_ok.1 h
  refine ⟨g, b, rfl, hb, ?_⟩
  rw [runtime_eq_add _ _ ho]
  simp [Ptr.add]

/-- Resolution keeps the root global's block identity: never a new block, never `none`. -/
theorem resolve_block {blocks : Nat → Option BlockId} {p : Path} {q : Ptr}
    (h : resolve blocks p = .ok q) :
    ∃ g b, p.root = .global g ∧ blocks g = some b ∧ q.block = some b := by
  obtain ⟨g, hr⟩ := resolve_root h
  obtain ⟨root, ps⟩ := p
  simp only at hr; subst hr
  obtain ⟨b, hb, -, -, rfl⟩ := resolve_global_eq_ok.1 h
  exact ⟨g, b, rfl, hb, rfl⟩

/-- The resolved offset is the sum of every projection's offset. -/
theorem resolve_off {blocks : Nat → Option BlockId} {g b : Nat} {ps : List Proj} {q : Ptr}
    (hb : blocks g = some b) (h : resolve blocks ⟨.global g, ps⟩ = .ok q) :
    q = ⟨some b, total ps⟩ := by
  obtain ⟨b', hb', -, -, rfl⟩ := resolve_global_eq_ok.1 h
  rw [hb] at hb'; cases hb'; rfl

/-- Nesting: a constant with more projections is the shorter constant's pointer followed by
the remaining runtime projections (elem of field of payload of a global, …). -/
theorem resolve_append {blocks : Nat → Option BlockId} {r : Root} {ps qs : List Proj} {q : Ptr}
    (h : resolve blocks ⟨r, ps ++ qs⟩ = .ok q) :
    ∃ p, resolve blocks ⟨r, ps⟩ = .ok p ∧ q = runtime p qs := by
  obtain ⟨g, hr⟩ := resolve_root h
  simp only at hr; subst hr
  obtain ⟨b, hb, hd, ho, rfl⟩ := resolve_global_eq_ok.1 h
  rw [total_append] at ho ⊢
  rw [List.length_append] at hd
  refine ⟨⟨some b, total ps⟩, resolve_global_eq_ok.2 ⟨b, hb, by omega, by omega, rfl⟩, ?_⟩
  rw [runtime_eq_add _ qs (by omega)]
  simp [Ptr.add]

/-- One more projection is that projection's instruction on the shorter constant. -/
theorem resolve_snoc {blocks : Nat → Option BlockId} {r : Root} {ps : List Proj} {s : Proj}
    {q : Ptr} (h : resolve blocks ⟨r, ps ++ [s]⟩ = .ok q) :
    ∃ p, resolve blocks ⟨r, ps⟩ = .ok p ∧ q = s.step p := by
  obtain ⟨p, hp, rfl⟩ := resolve_append h
  exact ⟨p, hp, rfl⟩

/-- `eu_payload` resolves to the emitted `unwrap_errunion_payload_ptr` of the payload type. -/
theorem errPayload_step (α : Type) [Enc α] (p : Ptr) :
    (Proj.errPayload (Enc.size α) (Enc.align α)).step p = errPayloadPtr α p := rfl

/-- `opt_payload` keeps the optional's address. -/
theorem optPayload_step (p : Ptr) : Proj.optPayload.step p = p := rfl

/-- A constant slice's pointer field is the slice's constant base pointer, on its global. -/
theorem slice_ptr_field {blocks : Nat → Option BlockId} {r : Root} {ps : List Proj}
    {q : Ptr} (len : BitVec 64) (h : resolve blocks ⟨r, ps⟩ = .ok q) :
    (⟨q, len⟩ : Slice).ptr = q ∧ ∃ g b, r = .global g ∧ blocks g = some b ∧ q.block = some b :=
  ⟨rfl, resolve_block h⟩

/-! ## Aliasing -/

/-- Two constants into the same global alias exactly when their total offsets agree,
whatever projections produced them. -/
theorem resolve_eq_iff {blocks : Nat → Option BlockId} {g b : Nat} {ps qs : List Proj}
    {p q : Ptr} (hb : blocks g = some b)
    (hp : resolve blocks ⟨.global g, ps⟩ = .ok p) (hq : resolve blocks ⟨.global g, qs⟩ = .ok q) :
    p = q ↔ total ps = total qs := by
  rw [resolve_off hb hp, resolve_off hb hq]
  simp only [Ptr.mk.injEq, true_and]
  constructor <;> intro h <;> omega

/-- Byte ranges `[p, p + m)` and `[q, q + n)` cannot overlap. -/
def Disjoint (p : Ptr) (m : Nat) (q : Ptr) (n : Nat) : Prop :=
  p.block ≠ q.block ∨ p.off + m ≤ q.off ∨ q.off + n ≤ p.off

/-- Constants rooted in different globals are disjoint when globals have distinct blocks. -/
theorem distinct_globals_disjoint {blocks : Nat → Option BlockId}
    (hinj : ∀ g h b, blocks g = some b → blocks h = some b → g = h)
    {g h : Nat} {ps qs : List Proj} {p q : Ptr} (m n : Nat) (hgh : g ≠ h)
    (hp : resolve blocks ⟨.global g, ps⟩ = .ok p) (hq : resolve blocks ⟨.global h, qs⟩ = .ok q) :
    Disjoint p m q n := by
  obtain ⟨b, hb, -, -, rfl⟩ := resolve_global_eq_ok.1 hp
  obtain ⟨c, hc, -, -, rfl⟩ := resolve_global_eq_ok.1 hq
  left
  intro hbc
  simp only [Option.some.injEq] at hbc
  subst hbc
  exact hgh (hinj _ _ _ hb hc)

/-- Sibling subobjects at offsets `o₁ + n₁ ≤ o₂` of a common parent are disjoint. -/
theorem sibling_disjoint {blocks : Nat → Option BlockId} {r : Root} {ps : List Proj}
    {o₁ o₂ n₁ n₂ : Nat} {p q : Ptr} (hlt : o₁ + n₁ ≤ o₂)
    (hp : resolve blocks ⟨r, ps ++ [.field o₁]⟩ = .ok p)
    (hq : resolve blocks ⟨r, ps ++ [.field o₂]⟩ = .ok q) :
    Disjoint p n₁ q n₂ := by
  obtain ⟨p₀, hp₀, rfl⟩ := resolve_snoc hp
  obtain ⟨q₀, hq₀, rfl⟩ := resolve_snoc hq
  rw [hp₀] at hq₀; cases hq₀
  right; left
  simp only [Proj.step, Ptr.add]
  omega

/-- Distinct elements of one array (items of at most `stride` bytes) are disjoint. -/
theorem elem_disjoint {blocks : Nat → Option BlockId} {r : Root} {ps : List Proj}
    {stride i j n : Nat} {p q : Ptr} (hn : n ≤ stride) (hij : i ≠ j)
    (hp : resolve blocks ⟨r, ps ++ [.elem stride i]⟩ = .ok p)
    (hq : resolve blocks ⟨r, ps ++ [.elem stride j]⟩ = .ok q) :
    Disjoint p n q n := by
  obtain ⟨g, hr⟩ := resolve_root hp
  simp only at hr; subst hr
  obtain ⟨b, -, -, -, rfl⟩ := resolve_global_eq_ok.1 hp
  obtain ⟨c, -, -, -, rfl⟩ := resolve_global_eq_ok.1 hq
  right
  simp only [total_append, total_cons, total_nil, Proj.delta, Nat.add_zero]
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · left
    have := Nat.mul_le_mul_left stride (show i + 1 ≤ j by omega)
    rw [Nat.mul_succ] at this
    omega
  · right
    have := Nat.mul_le_mul_left stride (show j + 1 ≤ i by omega)
    rw [Nat.mul_succ] at this
    omega

/-- An error union's payload (`eu_payload`) and its error code are disjoint. -/
theorem payload_code_disjoint {blocks : Nat → Option BlockId} {r : Root} {ps : List Proj}
    {size align : Nat} {p q : Ptr}
    (hp : resolve blocks ⟨r, ps ++ [.errPayload size align]⟩ = .ok p)
    (hq : resolve blocks ⟨r, ps ++ [.field (errUnionOffsets size align).1]⟩ = .ok q) :
    Disjoint p size q 2 := by
  obtain ⟨p₀, hp₀, rfl⟩ := resolve_snoc hp
  obtain ⟨q₀, hq₀, rfl⟩ := resolve_snoc hq
  rw [hp₀] at hq₀; cases hq₀
  obtain ⟨-, -, hd⟩ := errUnion_bounds size align
  right
  simp only [Proj.step, Ptr.add]
  omega

/-! ## Union members -/

/-- A member of an `extern` or `packed` union is at byte 0: the runtime `struct_field_ptr`
(`p.add 0`) is the union's pointer, as Sema's constant (the parent pointer) is. -/
theorem externMember_step (p : Ptr) : (Proj.field 0).step p = p := by
  simp [Proj.step, Ptr.add]

/-- A member of an `auto` union is the emitted `struct_field_ptr` at the payload offset. -/
theorem unionPayload_step (i ts ta pa : Nat) (p : Ptr) :
    (Proj.unionPayload i ts ta pa).step p = p.add (unionPayloadOffset ts ta pa) := rfl

/-- All members of one union alias: their constants are the same pointer. -/
theorem unionMembers_alias {blocks : Nat → Option BlockId} {r : Root} {ps qs : List Proj}
    {i j ts ta pa : Nat} :
    resolve blocks ⟨r, ps ++ Proj.unionPayload i ts ta pa :: qs⟩ =
      resolve blocks ⟨r, ps ++ Proj.unionPayload j ts ta pa :: qs⟩ := by
  simp [resolve, total_append, Proj.delta]

/-- The tag and the payload of an `auto` union do not overlap: a member of at most `ps`
bytes (the largest field) is disjoint from the tag's `ts` bytes. -/
theorem unionPayload_tag_disjoint {blocks : Nat → Option BlockId} {r : Root} {ps : List Proj}
    {i ts ta n psz pa : Nat} {p q : Ptr} (hn : n ≤ psz)
    (hp : resolve blocks ⟨r, ps ++ [.unionPayload i ts ta pa]⟩ = .ok p)
    (hq : resolve blocks ⟨r, ps ++ [.field (unionTagOffset ta psz pa)]⟩ = .ok q) :
    Disjoint p n q ts := by
  obtain ⟨p₀, hp₀, rfl⟩ := resolve_snoc hp
  obtain ⟨q₀, hq₀, rfl⟩ := resolve_snoc hq
  rw [hp₀] at hq₀; cases hq₀
  right
  simp only [Proj.step, Ptr.add, unionPayloadOffset, unionTagOffset]
  by_cases h : pa ≤ ta
  · have := le_alignUp ts pa
    simp only [h, ite_true]; right; push_cast; omega
  · have := le_alignUp psz ta
    simp only [h, ite_false]; left; push_cast; omega

/-! ## Invalid provenance -/

/-- A fixed (`@ptrFromInt`) address never resolves, however it is projected. -/
@[simp] theorem resolve_int (blocks : Nat → Option BlockId) (a : Nat) (ps : List Proj) :
    resolve blocks ⟨.int a, ps⟩ = .error (.unbacked a) := rfl

/-- A comptime-only object never resolves. -/
@[simp] theorem resolve_comptimeOnly (blocks : Nat → Option BlockId) (k : String) (ps : List Proj) :
    resolve blocks ⟨.comptimeOnly k, ps⟩ = .error (.comptimeOnly k) := rfl

/-- A global without a block never resolves. -/
theorem resolve_unknown {blocks : Nat → Option BlockId} {g : Nat} (ps : List Proj)
    (h : blocks g = none) : resolve blocks ⟨.global g, ps⟩ = .error (.unknownGlobal g) := by
  simp [resolve, h]

/-- Every access through a block-less pointer is `.illegal`: no valid object is invented. -/
theorem access_unbacked (m : Mem) (off : Int) (n align : Nat) :
    m.access ⟨none, off⟩ n align = throw .illegal := rfl

/-! ## The LLVM backend's `eu_payload` constant offset

`codegen.errUnionPayloadOffset(T)` (Zig 0.14.1–0.17.0, `src/codegen.zig`) is 0 for a payload
without runtime bits or with alignment at least `anyerror`'s (2), else `2` aligned up to the
payload alignment. The generic `codegen.lowerPtr` (self-hosted backends) passes the payload
type. `codegen/llvm.zig` `lowerPtr` passes the error union type itself, whose alignment is
at least 2, so it always adds 0. -/

/-- `codegen.errUnionPayloadOffset` for a payload of model size/alignment `size`/`align`. -/
def compilerPayloadOffset (size align : Nat) : Nat :=
  if size = 0 then 0 else if 2 ≤ align then 0 else alignUp 2 align

/-- The model's payload offset is the compiler's generic one. -/
theorem compilerPayloadOffset_eq (size align : Nat) :
    compilerPayloadOffset size align = (errUnionOffsets size align).2 := by
  unfold compilerPayloadOffset errUnionOffsets
  by_cases hs : size = 0
  · simp [hs]
  · by_cases ha : 2 ≤ align
    · simp [hs, ha]
    · simp [hs, ha]

/-- The LLVM backend's offset: `errUnionPayloadOffset` of the error union type
(size `errUnionSize`, alignment `max align 2`). -/
def llvmPayloadOffset (size align : Nat) : Nat :=
  compilerPayloadOffset (errUnionSize size align) (Max.max align 2)

theorem llvmPayloadOffset_eq_zero (size align : Nat) : llvmPayloadOffset size align = 0 := by
  unfold llvmPayloadOffset compilerPayloadOffset
  split
  · rfl
  · have h2 : 2 ≤ Max.max align 2 := by first | omega | exact Nat.le_max_right _ _
    simp [h2]

/-- The LLVM offset is wrong exactly for a nonzero-size payload of alignment below 2. -/
theorem llvmPayloadOffset_ne_iff (size align : Nat) :
    llvmPayloadOffset size align ≠ (errUnionOffsets size align).2 ↔ 0 < size ∧ align < 2 := by
  rw [llvmPayloadOffset_eq_zero, ← compilerPayloadOffset_eq]
  unfold compilerPayloadOffset alignUp
  constructor
  · intro h
    by_cases hs : size = 0
    · simp [hs] at h
    · by_cases ha : 2 ≤ align
      · simp [hs, ha] at h
      · omega
  · rintro ⟨hs, ha⟩
    have h1 : ¬size = 0 := by omega
    rcases (show align = 0 ∨ align = 1 by omega) with rfl | rfl <;> simp [h1]

/-- In the misplaced case the LLVM constant addresses the error code, not the payload. -/
theorem llvmPayloadOffset_is_code {size align : Nat} (hs : 0 < size) (ha : align < 2) :
    llvmPayloadOffset size align = (errUnionOffsets size align).1 := by
  rw [llvmPayloadOffset_eq_zero]
  unfold errUnionOffsets
  have h1 : ¬size = 0 := by omega
  have h2 : ¬align ≥ 2 := by omega
  simp [h1, h2]

/-- A projection the LLVM backend lowers at a different offset than the model. -/
def Proj.llvmMisplaced : Proj → Bool
  | .errPayload size align => 0 < size && align < 2
  | _ => false

/-- The LLVM backend's offset for one projection. -/
def Proj.llvmDelta : Proj → Nat
  | .errPayload size align => llvmPayloadOffset size align
  | s => s.delta

/-- Without a misplaced `eu_payload` step, LLVM and the model agree on every offset. -/
theorem llvm_total_eq {ps : List Proj} (h : ∀ s ∈ ps, s.llvmMisplaced = false) :
    (ps.map Proj.llvmDelta).sum = total ps := by
  induction ps with
  | nil => rfl
  | cons s ps ih =>
    simp only [List.map_cons, List.sum_cons, total_cons]
    rw [ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    congr 1
    have hs := h s (List.mem_cons_self ..)
    cases s with
    | errPayload size align =>
      simp only [Proj.llvmMisplaced, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hs
      simp only [Proj.llvmDelta, Proj.delta]
      apply Decidable.byContradiction
      intro hne
      have := (llvmPayloadOffset_ne_iff size align).1 hne
      omega
    | field off => rfl
    | optPayload => rfl
    | elem stride index => rfl
    | unionPayload _ _ _ _ => rfl

/-- With one, the LLVM offset of that step is wrong (by `llvmPayloadOffset_ne_iff`). -/
theorem llvm_step_ne {size align : Nat} (h : (Proj.errPayload size align).llvmMisplaced = true) :
    (Proj.errPayload size align).llvmDelta ≠ (Proj.errPayload size align).delta := by
  simp only [Proj.llvmMisplaced, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (llvmPayloadOffset_ne_iff size align).2 h

end Zig.ConstPtr
