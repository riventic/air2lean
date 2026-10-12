import AllocArena.ArenaLinux
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Unroll
import ZigLean.Sep.Full.Reclaim

/-!
# Obstructions O-A, O-E and O-H (kernel-checked)

## O-A: a foreign `free` on an empty arena panics

`ArenaAllocator.free` (Zig 0.16.0) starts with `const node = arena.loadFirstNode().?;`. On an
arena that has no node (`used_list == null`: a fresh arena, or one after `reset(.free_all)`) the
unwrap panics, whatever slice is freed. `resize` (and so `remap`) start the same way.
`arena_foreign_free` (`arena.zig`) frees a slice of the child `FixedBufferAllocator` through a
fresh arena: the translated program panics, as the native one does
(`panic: attempt to use null value`, `ArenaAllocator.zig:615`).

So an `FAllocSpec` invariant `I` of the arena that holds for an empty arena must make
`I.own ⋆ I.granted p k bs` unsatisfiable there: the token must say that the arena issued the region
in its current generation. Owned bytes and duplicable block knowledge cannot say that; the
ghost epoch ledgers of `ZigLean/Sep/Full/Ghost.lean` can: `ArenaSpec.lean`'s token is a ghost token
of the current epoch that names the region, which shows that the arena granted it and so has a
node (`ArenaSpec.free_pre`).

## O-E: `free` after a failed `alloc` forms an out-of-bounds pointer

An `alloc` that does not fit the first node bumps its `end_index` past the buffer; if the child
then fails, that node stays first. `free` computes `buf_ptr + end_index` (a many-pointer
addition: `getelementptr inbounds` natively, `Zig.ptrProject` here), which lies outside the
node's block: `.illegal` (MM-3), and undefined behaviour natively
(`docs/upstream/arena-oob-gep.md`). `arena_oob_free` builds that state by hand (a 64-byte node
with `end_index = 1000`) and frees a foreign slice. `not_fallocSpec_arena` reaches it by the
arena's own `alloc` (the kernel runs its `partial_fixpoint` group cut by `unroll_solo`) and refutes
every `FAllocSpec` of the stock arena whose invariant holds after `init`.
## O-H: an address at the top of the address space overflows `alloc`'s alignment

`alloc`'s fast path aligns `buf.ptr + end_index` with `Alignment.forward`, an addition with an
overflow check. A node buffer that ends at `2^64` makes it overflow (`aligned_index_overflows`);
natively no user address is that high. The model therefore bounds every block, of every kind, by
the placement's `addrLimit` (at most `2^63`, premise SEM-07): a placement cannot put a block above
it (`node_buf_low`, `aligned_index_ok`), an allocation without room has no outcome, and every
memory of the full-state invariant has its live blocks below `2^63` (`Mem.LiveBounded`, which
`memTop` breaks: `memTop_unbounded`).
-/

namespace AllocArena.ArenaObstruction

open Zig Zig.Full Zig.Full.FAssn AllocArena.ArenaLinux

/-- The one-thread schedule of a whole program (oracle `0`). -/
def solo {α : Type} (main : ConcM Tgt α) : Option (Except Error α) :=
  ((Sched.run Sched.soloEnv dispatch 100000 (fun _ => 0) main (mem0 .fresh)).run).map fun r => r.map (·.1)

/-- **O-A.** Freeing a foreign slice through a fresh arena panics. -/
theorem foreign_free_panics : solo arena_foreign_free = some (.error .panic) := by
  decide +kernel

/-- **O-E.** `free` in the state that a failed `alloc` leaves is illegal behaviour. -/
theorem oob_free_illegal : solo arena_oob_free = some (.error .illegal) := by
  decide +kernel

/-- The program's memory at start. -/
def mem00 : Mem := mem0 .fresh

/-- A live 32-byte block at `2^64 - 32`. -/
def topBlock : Block :=
  { bytes := Array.replicate 32 .undef, align := 8, kind := .heap, live := true, addr := 2 ^ 64 - 32 }

/-- A memory whose last block (32 bytes, a node's header and 8 buffer bytes) ends at `2^64`:
the model's old placement admitted such a block (`Mem.placeOk` then checked `A + size ≤ 2^64`),
no native process has it. -/
def memTop : Mem := { mem00 with blocks := mem00.blocks.push topBlock }

/-- The run ends in `.overflow`. -/
def overflows {α : Type} : Option (Except Error α) → Bool
  | some (.error .overflow) => true
  | _ => false

/-- **O-H, why the address-space bound is needed.** `alignedIndex(buf.ptr, end_index, .@"8")`,
which `alloc`'s fast path calls after the reservation check, with the buffer ending at `2^64` and
`end_index = 5`: `Alignment.forward` adds `7` to `2^64 - 3` with an overflow check, so no
`FAllocSpec` of the arena holds in `memTop`. -/
theorem aligned_index_overflows :
    overflows ((heap_ArenaAllocator_alignedIndex ⟨some mem00.blocks.size, 24⟩ 5 mem_Alignment.«8»).run
      memTop).run = true := by
  decide +kernel

/-- **O-H, fixed: `memTop` is outside the full-state invariant.** Its top block ends above `2^63`,
so it breaks `Mem.LiveBounded`, part of `Mem.FSeq`, which every `FTriple` assumes and keeps: every
placement's `addrLimit` is at most `2^63` and no allocation places a block above it. -/
theorem memTop_unbounded : ¬ memTop.LiveBounded := fun h => by
  have := h mem00.blocks.size topBlock (by simp [memTop]) rfl
  simp [topBlock] at this

/-- A placement that proposes `2^64 - 64` for `node_buf` (block 7, 64 bytes, alignment 8): a
nonzero, aligned address whose block ends at `2^64` and is clear of every other global, i.e. one
the old `Mem.placeOk` took. -/
def σTop : Placement := { propose := fun b => if b = 7 then some (2 ^ 64 - 64) else none }

/-- **O-H, fixed: the placement cannot put a block there.** Under `σTop` the program-start memory
does not take the proposal (`2^64 - 64 + 64 > addrLimit`): `node_buf` lies at the fallback
address, low in the address space. -/
theorem node_buf_low : decide (((mem0 σTop).blocks[7]?.map (·.addr)).all (· + 64 ≤ 2 ^ 47)) = true := by
  decide +kernel

/-- **O-H, fixed: the call succeeds.** The same `alignedIndex` on a node in `node_buf` (header
24 bytes, `end_index = 5`) of the memory that `σTop` actually gives returns an index. -/
theorem aligned_index_ok :
    overflows ((heap_ArenaAllocator_alignedIndex ⟨some 7, 24⟩ 5 mem_Alignment.«8»).run
      (mem0 σTop)).run = false := by
  decide +kernel

/-! ## O-E for every invariant: `not_fallocSpec_arena`

`arena_oom_free`'s run refutes every specification of the stock arena, not only `ArenaSpec.lean`'s
invariant: the client below calls the arena's entries (`vt`) from the memory right after `init`
(`mInit`), so an `FAllocSpec` invariant whose `own` held there would give the client a triple
(`client_ct`, composed from the spec's `alloc` and `free` triples), while the kernel computes its
run to `.illegal` (`client_illegal`: `unroll_solo` cuts the arena's `partial_fixpoint` group). -/

/-- The stock arena's four entries. -/
def vt : CVTable Tgt where
  alloc c n k ra := heap_ArenaAllocator_alloc c n ⟨BitVec.ofNat 6 k⟩ ra
  resize c s k n ra := heap_ArenaAllocator_resize c s ⟨BitVec.ofNat 6 k⟩ n ra
  remap c s k n ra := heap_ArenaAllocator_remap c s ⟨BitVec.ofNat 6 k⟩ n ra
  free c s k ra := heap_ArenaAllocator_free c s ⟨BitVec.ofNat 6 k⟩ ra

/-- `arena_oom_free`'s start: a `FixedBufferAllocator` over the 256-byte global `small` and an
arena over it, both on the stack. -/
def setup : MemM Ptr := do
  let fba ← allocStack 24 8
  let arena ← allocStack 32 8
  store (α := heap_FixedBufferAllocator) 8 fba (← heap_FixedBufferAllocator_init ⟨⟨some 0, 0⟩, 256⟩)
  store (α := heap_ArenaAllocator) 8 arena (← heap_ArenaAllocator_init (← heap_FixedBufferAllocator_allocator fba))
  pure arena

/-- The memory after `setup` from the program start. -/
def mInit : Mem := match (setup.run (mem0 .fresh)).run with
  | some (.ok (_, m)) => m
  | _ => default

/-- The arena (`ctx`) that `setup` made. -/
def arena : Ptr := match (setup.run (mem0 .fresh)).run with
  | some (.ok (p, _)) => p
  | _ => default

/-- `arena_oom_free 8` from `mInit` through the entries: `alloc` of 8 bytes, of 4096 bytes (the
child refuses the new node), `free` of the first slice. -/
def client : ConcM Tgt Unit := do
  match ← vt.alloc arena 8 0 0 with
  | none => pure ()
  | some p => do
    let _ ← vt.alloc arena 4096 0 0
    vt.free arena ⟨p, 8⟩ 0 0

theorem mInit_fseq : mInit.FSeq := by decide +kernel

set_option maxRecDepth 100000 in
/-- The client's run in the caller's thread is illegal (O-E): the kernel runs the stock arena's
`alloc`, `alloc`, `free` (`unroll_solo`: the arena's `partial_fixpoint` group cut). -/
theorem client_illegal :
    Witness.errOf ((Sched.soloRun 1000 client).run mInit) = some .illegal := by
  unroll_solo 8

/-- Every resource. -/
def Any : FAssn := fun _ => True

set_option maxRecDepth 20000 in
/-- **The client meets its triple under every `FAllocSpec` of the arena** whose `fits` admits the
two requests: composed from the spec's `alloc` and `free`, with a fee for each `alloc`. -/
theorem client_ct (I : FAllocInv) (h : CAllocSpec vt arena I) (h8 : I.fits 8 0) (h4096 : I.fits 4096 0)
    (φ₁ φ₂ : Frac) : CTriple (I.own ⋆ (I.fee φ₁ ⋆ I.fee φ₂)) client (fun _ => Any) := by
  refine CTriple.pre (CTriple.bind ((h.alloc 8 0 0 φ₁ (by decide) (by decide) h8).frame (R := I.fee φ₂))
    fun o => ?_) fun _ h => sep_assoc' h
  match o with
  | none => exact CTriple.ret' () fun _ _ => trivial
  | some p =>
    let G := FAssn.ex fun bs : Array Byte => ⟪bs.size = (8 : BitVec 64).toNat⟫ ⋆ I.granted p 0 φ₁ bs
    refine CTriple.pre (CTriple.bind ((h.alloc 4096 0 0 φ₂ (by decide) (by decide) h4096).frame (R := G))
      fun v => ?_) fun _ h => ac_cast h (by simp only [FAllocInv.allocPost, G]; ac_rfl)
    refine CTriple.pre (P := FAssn.ex fun bs => ⟪bs.size = 8⟫ ⋆ ((I.own ⋆ I.granted p 0 φ₁ bs) ⋆ Any))
      (CTriple.ex fun bs => CTriple.lift fun hbs =>
        CTriple.post ((h.free ⟨p, 8⟩ 0 0 φ₁ bs (by decide) (by rw [hbs]; rfl) (by rw [hbs]; decide)).frame
          (R := Any)) fun _ _ _ => trivial) ?_
    intro r hr
    -- `alloc`'s result (a grant, or the fee back) joins the rest (`Any`).
    have hr' : ((I.own ⋆ Any) ⋆ G) r := by
      cases v <;> exact sep_mono_left (fun r h => sep_mono_right (fun _ _ => trivial) h) hr
    obtain ⟨bs, hb⟩ := sep_ex.mp (sep_comm hr')
    obtain ⟨hbs, hb⟩ := Full.sep_lift.mp (sep_assoc hb)
    -- `granted ⋆ (own ⋆ Any)` to `(own ⋆ granted) ⋆ Any`.
    exact ⟨bs, Full.sep_lift.mpr ⟨hbs, sep_mono_left (fun _ h => sep_comm h) (sep_assoc' hb)⟩⟩

/-- **O-E, kernel-checked: no `FAllocSpec` of the stock arena holds after `init`.** For every
invariant `I` with `CAllocSpec vt arena I` whose `fits` admits the client's two requests, `I.own`
and two fees (`FAllocInv.fee`; `emp` for an allocator that charges none) do not hold in `mInit`
(the arena over the 256-byte `FixedBufferAllocator` right after `init`), with any frame: the
client's triple (`client_ct`) would rule out its run's `.illegal` (`client_illegal`; `mInit` is a
full-state sequential memory, `mInit_fseq`). -/
theorem not_fallocSpec_arena (I : FAllocInv) (h : CAllocSpec vt arena I) (h8 : I.fits 8 0)
    (h4096 : I.fits 4096 0) : ¬ ∃ φ₁ φ₂ r rF, Holds mInit r rF ∧ (I.own ⋆ (I.fee φ₁ ⋆ I.fee φ₂)) r := by
  rintro ⟨φ₁, φ₂, r, rF, hh, ho⟩
  have ht := client_ct I h h8 h4096 φ₁ φ₂ 1000 mInit r rF hh ho mInit_fseq
  rw [Witness.errOf_eq_some.mp client_illegal] at ht
  cases ht

/-! ## Reset: revoking ghost state cannot withdraw a grant's bytes (`not_reset_own`)

Can `reset` be specified with the arena's state alone as its precondition, so that a client
with outstanding grants calls it without giving anything back and the epoch bump revokes those
grants: `{I.own} reset {I'.own}` (`I'` the next epoch's invariant)? No, for any two invariants.
A grant gives the client its bytes (`FAllocInv.granted`), exclusive cells in the client's part of
the resource; the ledger bump and the revocation of receipts and claims (`Upd.bump`,
`EUpd.revoke`, `EUpd.prevokeC`) withdraw only ghost state. The client below allocates 8 bytes,
resets with `.free_all`, and allocates 8 bytes again. By the frame rule it still holds the first
grant's bytes next to the second grant, so its triple (`reset_client_ct`) ends with two separate
grants, while the kernel computes both to be byte 24 of the `FixedBufferAllocator`'s buffer
(`reset_client_run`: the reset gave the node back, the child rewound and handed it out again).
So a sound `reset` precondition must hand back every outstanding grant's bytes. (Over
`page_allocator` the reset `munmap`s the node and a later store to the old grant is `.illegal`;
the kernel run of that client needs more than the build's memory cap.)
-/

/-- `alloc` of 8 bytes, `reset(.free_all)`, `alloc` of 8 bytes. -/
def resetClient : ConcM Tgt (Option Ptr × Option Ptr) := do
  let p ← vt.alloc arena 8 0 0
  let _ ← heap_ArenaAllocator_reset arena .free_all
  let q ← vt.alloc arena 8 0 0
  pure (p, q)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The client's run: both allocations return byte 24 of the child's buffer. -/
theorem reset_client_run :
    (((Sched.soloRun 1000 resetClient).run mInit).run.map fun r => r.map (·.1)) =
      some (.ok (some ⟨some 0, 24⟩, some ⟨some 0, 24⟩)) := by
  unroll_solo 3

/-- A grant of `I` at `p` of 8 bytes, for the fee `φ`. -/
def G8 (I : FAllocInv) (φ : Frac) (p : Ptr) : FAssn :=
  FAssn.ex fun bs : Array Byte => ⟪bs.size = (8 : BitVec 64).toNat⟫ ⋆ I.granted p 0 φ bs

/-- What the client ends with: both grants, when both allocations succeed. -/
def keeps (I I' : FAllocInv) (φ₁ φ₂ : Frac) : Option Ptr × Option Ptr → FAssn
  | (some p, some q) => G8 I φ₁ p ⋆ (G8 I' φ₂ q ⋆ Any)
  | _ => Any

/-- A grant owns its first byte. -/
theorem g8_owns {I : FAllocInv} {φ : Frac} {p : Ptr} {b : BlockId} (hb : p.block = some b) {r : Res}
    (h : G8 I φ p r) : ∃ fc, r.heap (b, p.off.toNat) = some fc := by
  obtain ⟨bs, h⟩ := h
  obtain ⟨hbs, A, S, K, q, r₁, r₂, -, rfl, h1, -⟩ := Full.sep_lift.mp h
  obtain ⟨fc, hx, -⟩ := Owns.region (i := 0) hb (by rw [hbs]; decide) r₁ h1
  exact ⟨fc, by show (r₁.heap _).or _ = _; rw [← Nat.add_zero p.off.toNat, hx]; rfl⟩

/-- **Two grants at one pointer are not separate.** -/
theorem keeps_same {I I' : FAllocInv} {φ₁ φ₂ : Frac} {p : Ptr} {b : BlockId}
    (hb : p.block = some b) {r : Res} (h : keeps I I' φ₁ φ₂ (some p, some p) r) : False := by
  obtain ⟨r₁, r₂, hd, -, h1, r₃, r₄, -, rfl, h3, -⟩ := h
  obtain ⟨_, e1⟩ := g8_owns hb h1
  obtain ⟨_, e3⟩ := g8_owns hb h3
  rcases hd (b, p.off.toNat) with e | e
  · rw [e1] at e; cases e
  · have e' : (r₃.heap (b, p.off.toNat)).or (r₄.heap (b, p.off.toNat)) = none := e
    rw [e3] at e'; cases e'

set_option maxRecDepth 20000 in
/-- **The client meets its triple** under every two `FAllocSpec`s of the arena whose `fits`
admit 8 bytes, and every `reset` triple from the first one's state to the second one's and a fee
of the second. -/
theorem reset_client_ct (I I' : FAllocInv) (h : CAllocSpec vt arena I)
    (h' : CAllocSpec vt arena I') (h8 : I.fits 8 0) (h8' : I'.fits 8 0) (φ₁ φ₂ : Frac)
    (hres : CTriple I.own (heap_ArenaAllocator_reset arena .free_all) (fun _ => I'.own ⋆ I'.fee φ₂)) :
    CTriple (I.own ⋆ I.fee φ₁) resetClient (keeps I I' φ₁ φ₂) := by
  refine CTriple.bind (h.alloc 8 0 0 φ₁ (by decide) (by decide) h8) fun o => ?_
  -- the rest of the client, with the first grant (or its fee) framed
  have rest : ∀ R : FAssn, (∀ o' r, (I'.allocPost 8 0 φ₂ o' ⋆ R) r → keeps I I' φ₁ φ₂ (o, o') r) →
      CTriple (I.own ⋆ R) (do
        let _ ← heap_ArenaAllocator_reset arena .free_all
        let q ← vt.alloc arena 8 0 0
        pure (o, q)) (keeps I I' φ₁ φ₂) := fun R hk =>
    CTriple.bind (hres.frame (R := R)) fun _ =>
      CTriple.bind ((h'.alloc 8 0 0 φ₂ (by decide) (by decide) h8').frame (R := R)) fun o' =>
        CTriple.ret' _ (hk o')
  cases o with
  | none =>
    refine CTriple.pre (rest Any fun _ _ _ => trivial) fun r hr => ?_
    exact sep_mono_right (fun _ _ => trivial) hr
  | some p =>
    refine CTriple.pre (rest (G8 I φ₁ p) fun o' r hr => ?_) fun r hr => hr
    cases o' with
    | none => trivial
    | some q =>
      exact sep_mono_right (fun _ h => sep_mono_right (fun _ _ => trivial) (sep_comm h))
        (sep_comm hr)

set_option maxRecDepth 100000 in
/-- **Reset, kernel-checked: no `reset` triple with the arena's state as its precondition**
(`{I.own} reset(.free_all) {I'.own ⋆ I'.fee φ₂}`) coexists with `FAllocSpec`s `I`, `I'` of the
arena of which `I` and a fee hold after `init`: the client's triple (`reset_client_ct`) would end
with two separate grants that the run (`reset_client_run`) puts at one byte. Revocation (the
epoch bump) cannot withdraw a grant's bytes, and no fee changes that: a `reset` must take every
outstanding grant back (with the fee of `docs/sep-full-state.md` §The fee of a grant, an arena's
`reset` takes the whole epoch token, which a client with an outstanding grant does not have). -/
theorem not_reset_own (I I' : FAllocInv) (h : CAllocSpec vt arena I)
    (h' : CAllocSpec vt arena I') (h8 : I.fits 8 0) (h8' : I'.fits 8 0) (φ₁ φ₂ : Frac)
    (hres : CTriple I.own (heap_ArenaAllocator_reset arena .free_all) (fun _ => I'.own ⋆ I'.fee φ₂)) :
    ¬ ∃ r rF, Holds mInit r rF ∧ (I.own ⋆ I.fee φ₁) r := by
  rintro ⟨r, rF, hh, ho⟩
  have ht := reset_client_ct I I' h h' h8 h8' φ₁ φ₂ hres 1000 mInit r rF hh ho mInit_fseq
  have hrun := reset_client_run
  revert ht
  cases e : ((Sched.soloRun 1000 resetClient).run mInit).run with
  | none => rw [e] at hrun; cases hrun
  | some x =>
    rcases x with err | ⟨v, m'⟩
    · rw [e] at hrun; cases hrun
    · rw [e] at hrun
      simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq] at hrun
      subst hrun
      rintro ⟨r', -, hk, -⟩
      exact keeps_same rfl hk

-- `check.sh` requires only the standard axioms.
#print axioms foreign_free_panics
#print axioms oob_free_illegal
#print axioms aligned_index_overflows
#print axioms memTop_unbounded
#print axioms node_buf_low
#print axioms aligned_index_ok
#print axioms not_fallocSpec_arena
#print axioms not_reset_own

end AllocArena.ArenaObstruction
