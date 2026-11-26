import ZigLean.Isa.X86

/-!
# A checked block computes the same under every operand placement (A02, ASM-07 item 4)

`ZigLean/Isa/X86.lean` runs a block on a state in which every `r` operand has a location of its
own (`vreg k`) and every location that is not an input holds 0. The compiled block runs on the
machine's registers: the compiler chooses a register for each `r` operand and registers for the
address of each `m` operand, an input may get the register of an output, and the registers that
carry no input hold whatever the caller left there.

This file states that machine (`Placement`, `Placement.run`) and proves, once for all blocks,
that `Block.check` is enough (`Block.check_placement`): for a block that passes the check, every
admissible placement and every machine state that holds the inputs in their places,

* every memory operand is accessed while the registers of its address still hold their entry
  values (`Placement.run` is `some`),
* every output holds the value of `Block.out`, and
* the instructions fault exactly as `Block.fault` says.

So the value of a generated `airIsa_<hash>` does not depend on the placement or on the other
contents of the registers. What stays assumed about the compiler is `Placement.Admissible`, and
nothing else.

The model has no addresses, symbols, branches or instruction pointer (`Instr` has no such
operand, and the decoder rejects a template with one), so a block's value cannot depend on where
its code is loaded: there is nothing to prove about the load address.

Two memory operands are two locations of the machine state here, as in the model. That they do
not overlap is the effect contract's (premise ASM-03), not a fact about placement.
-/

namespace Zig.Isa.X86

/-! ## The writes of an instruction -/

/-- One write of an instruction: the value `v` at width `w` to the location `l`. -/
structure Write where
  w : Width
  l : Loc
  v : BitVec w.bits

def State.write (s : State) (e : Write) : State := s.set e.w e.l e.v

/-- The writes of an instruction on the state it runs in, in order. Their values depend on the
state only through `Instr.reads` (`Instr.effect_place`). -/
def Instr.effect : Instr → State → List Write
  | .bin op w src dst, s => [⟨w, dst, op.eval (src.val s w) (s.get w dst)⟩]
  | .un op w dst, s => [⟨w, dst, op.eval (s.get w dst)⟩]
  | .cnt op w src dst, s => [⟨w, dst, op.eval (s.get w src)⟩]
  | .xchg w a b, s => [⟨w, a, s.get w b⟩, ⟨w, b, s.get w a⟩]
  | .div w src, s =>
    let nd := divOperands s w src
    match w with
    | .w8 => [⟨.w16, rax, BitVec.ofNat _ (nd.1 % nd.2 * 256 + nd.1 / nd.2)⟩]
    | .w16 => [⟨.w16, rax, BitVec.ofNat _ (nd.1 / nd.2)⟩, ⟨.w16, rdx, BitVec.ofNat _ (nd.1 % nd.2)⟩]
    | .w32 => [⟨.w32, rax, BitVec.ofNat _ (nd.1 / nd.2)⟩, ⟨.w32, rdx, BitVec.ofNat _ (nd.1 % nd.2)⟩]
    | .w64 => [⟨.w64, rax, BitVec.ofNat _ (nd.1 / nd.2)⟩, ⟨.w64, rdx, BitVec.ofNat _ (nd.1 % nd.2)⟩]

theorem Instr.step_eq_effect (i : Instr) (s : State) :
    i.step s = (i.effect s).foldl State.write s := by
  cases i with
  | bin op w src dst => rfl
  | un op w dst => rfl
  | cnt op w src dst => rfl
  | xchg w a b => rfl
  | div w src => cases w <;> rfl

theorem Instr.effect_writes (i : Instr) (s : State) :
    (i.effect s).map (fun e => (e.l, e.w)) = i.writes := by
  cases i with
  | bin op w src dst => rfl
  | un op w dst => rfl
  | cnt op w src dst => rfl
  | xchg w a b => rfl
  | div w src => cases w <;> rfl

/-! ## Placements -/

/-- The compiler's choices for one block: the register of each register-class (`r`) operand and
the registers that hold the address of each memory (`m`) operand (a base and an index, the stack
pointer, or none for an absolute address). -/
structure Placement where
  reg : Nat → Fin 16
  addr : Nat → List (Fin 16)

/-- Where a location of the model is on the machine. -/
def Placement.loc (P : Placement) : Loc → Loc
  | .vreg k => .reg (P.reg k)
  | l => l

def Src.place (f : Loc → Loc) : Src → Src
  | .loc l => .loc (f l)
  | .imm v => .imm v

/-- The instruction with its operands placed. -/
def Instr.place (f : Loc → Loc) : Instr → Instr
  | .bin op w src dst => .bin op w (src.place f) (f dst)
  | .un op w dst => .un op w (f dst)
  | .cnt op w src dst => .cnt op w (f src) (f dst)
  | .xchg w a b => .xchg w (f a) (f b)
  | .div w src => .div w (f src)

def Write.place (f : Loc → Loc) (e : Write) : Write := ⟨e.w, f e.l, e.v⟩

def Src.locs : Src → List Loc
  | .loc l => [l]
  | .imm _ => []

/-- The operands that the instruction names. -/
def Instr.locs : Instr → List Loc
  | .bin _ _ src dst => src.locs ++ [dst]
  | .un _ _ dst => [dst]
  | .cnt _ _ src dst => [src, dst]
  | .xchg _ a b => [a, b]
  | .div _ src => [src]

def Block.operandLocs (b : Block) : List Loc := b.inputLocs ++ b.outputLocs

/-- What the compiler guarantees of a placement (the residue of premise ASM-07 item 4):

* no operand is in a clobbered register;
* an output has a register of its own, except that an input which is not an output too may be
  in the register of an output without `&`. (Two such inputs may share a register as well: the
  compiler does that for one value passed twice.);
* a register of a memory operand's address is not clobbered and is not the register of an `&`
  output. -/
structure Placement.Admissible (P : Placement) (b : Block) : Prop where
  clobber : ∀ l ∈ b.operandLocs, ∀ r ∈ b.clobbers, P.loc l ≠ .reg r
  share : ∀ o ∈ b.outputLocs, ∀ l ∈ b.operandLocs, P.loc o = P.loc l → o ≠ l →
    o ∉ b.early ∧ l ∉ b.outputLocs
  addr : ∀ k, Loc.mem k ∈ b.operandLocs → ∀ r ∈ P.addr k,
    r ∉ b.clobbers ∧ ∀ o ∈ b.outputLocs, P.loc o = .reg r → o ∉ b.early

/-- The machine state `p0` holds the inputs `vals` of the block in their places, at the width of
each operand's type. Nothing is said about any other bit of the state. -/
def Placement.Entry (P : Placement) (b : Block) (vals : List (BitVec 64)) (p0 : State) : Prop :=
  ∀ lw ∈ b.inputs, p0.get lw.2 (P.loc lw.1) = (initState b.inputs vals).get lw.2 lw.1

/-- Do the registers of the address of a memory operand hold what they held on entry (`p0`)? -/
def Placement.intact (P : Placement) (p0 p : State) : Loc → Bool
  | .mem k => (P.addr k).all fun r => p (.reg r) == p0 (.reg r)
  | _ => true

/-- The placed instructions on the machine, from the entry state `p0`: `none` when an instruction
names a memory operand after a register of its address changed (it would access other memory). -/
def Placement.run (P : Placement) (p0 : State) : List Instr → State → Option State
  | [], p => some p
  | i :: rest, p => if i.locs.all (P.intact p0 p) then P.run p0 rest (i.step p) else none

/-- The placed block on the machine, from the entry state `p0`. -/
def Placement.exec (P : Placement) (b : Block) (p0 : State) : Option State :=
  P.run p0 (b.instrs.map (Instr.place P.loc)) p0

/-- The first fault of the placed block on the machine, from the entry state `p0`. -/
def Placement.fault (P : Placement) (b : Block) (p0 : State) : Option Fault :=
  faultInstrs (b.instrs.map (Instr.place P.loc)) p0

/-- Output `k` of the block in the machine state `p`. -/
def Placement.out (P : Placement) (b : Block) (p : State) (k : Nat) : BitVec 64 :=
  match b.outputs[k]? with
  | some (l, w) => (p.get w (P.loc l)).setWidth 64
  | none => 0

theorem Placement.loc_reg (P : Placement) (r : Fin 16) : P.loc (.reg r) = .reg r := rfl

theorem Placement.loc_mem (P : Placement) (k : Nat) : P.loc (.mem k) = .mem k := rfl

theorem Placement.loc_isMem (P : Placement) (l : Loc) : (P.loc l).isMem = l.isMem := by
  cases l <;> rfl

theorem Placement.loc_eq_mem {P : Placement} {l : Loc} {k : Nat} (h : P.loc l = .mem k) :
    l = .mem k := by
  cases l <;> simp_all [Placement.loc]

theorem Placement.loc_eq_of_isReg {P : Placement} {l l' : Loc} (h : P.loc l = P.loc l')
    (hl : l.isReg = true) (hl' : l'.isReg = true) : l = l' := by
  cases l <;> cases l' <;> simp_all [Placement.loc, Loc.isReg]

/-! ## Agreement of the model state and the machine state -/

/-- The low `n` bits are equal. -/
def agree (n : Nat) (a b : BitVec 64) : Prop := ∀ i, i < n → a.getLsbD i = b.getLsbD i

theorem agree.get {n : Nat} {a b : BitVec 64} (h : agree n a b) {w : Width} (hw : w.bits ≤ n) :
    a.setWidth w.bits = b.setWidth w.bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, h i (Nat.lt_of_lt_of_le hi hw)]

theorem agree_of_get {a b : BitVec 64} {w : Width} (h : a.setWidth w.bits = b.setWidth w.bits) :
    agree w.bits a b := by
  intro i hi
  have := congrArg (·.getLsbD i) h
  simpa [BitVec.getLsbD_setWidth, hi] using this

theorem State.set_other (s : State) (w : Width) {l l' : Loc} (v : BitVec w.bits) (h : l' ≠ l) :
    s.set w l v l' = s l' := by
  simp [State.set, h]

/-- A write defines the low `w` bits. -/
theorem State.set_agree_low (s p : State) (w : Width) (l l2 : Loc) (v : BitVec w.bits) :
    agree w.bits (s.set w l v l) (p.set w l2 v l2) := by
  intro i hi
  rcases Bool.eq_false_or_eq_true l.isMem with hl | hl <;>
    rcases Bool.eq_false_or_eq_true l2.isMem with hl2 | hl2 <;>
    cases w <;>
    simp_all [State.set, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and]

/-- A write to a register keeps the agreement below it: a 32- or 64-bit write defines the whole
register, a narrower one the bits that were defined or are written. -/
theorem State.set_agree_reg (s p : State) (w : Width) (l l2 : Loc) (v : BitVec w.bits) {n : Nat}
    (hl : l.isMem = false) (hl2 : l2.isMem = false) (h : agree n (s l) (p l2)) :
    agree (if w = .w32 || w = .w64 then 64 else Nat.max n w.bits) (s.set w l v l)
      (p.set w l2 v l2) := by
  intro i hi
  have hcase : (w = .w32 ∨ w = .w64) ∨ i < w.bits ∨ i < n := by
    by_cases hn : i < n
    · exact .inr (.inr hn)
    · cases w <;> simp [Nat.max_def] at hi ⊢
      all_goals (split at hi <;> omega)
  rcases hcase with hfull | hlow | hold
  · rcases hfull with rfl | rfl <;> simp [State.set, hl, hl2]
  · cases w <;>
      simp_all [State.set, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and]
  · have := h i hold
    cases w <;>
      simp_all [State.set, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and]

/-! ## The values of an instruction depend only on its reads -/

theorem divOperands_place {f : Loc → Loc} (hf : ∀ r, f (.reg r) = .reg r) {s p : State}
    {w : Width} {src : Loc}
    (h : ∀ lw ∈ (Instr.div w src).reads, p.get lw.2 (f lw.1) = s.get lw.2 lw.1) :
    divOperands p w (f src) = divOperands s w src := by
  cases w <;> simp [Instr.reads, rax, rdx, hf] at h <;> simp [divOperands, rax, rdx, h]

/-- The placed instruction writes the same values to the placed locations, when the machine
state holds what the model state holds in every location that the instruction reads. -/
theorem Instr.effect_place {f : Loc → Loc} (hf : ∀ r, f (.reg r) = .reg r) {i : Instr}
    {s p : State} (h : ∀ lw ∈ i.reads, p.get lw.2 (f lw.1) = s.get lw.2 lw.1) :
    (i.place f).effect p = (i.effect s).map (Write.place f) := by
  cases i with
  | bin op w src dst =>
    have hsrc : (∀ lw ∈ src.reads w, p.get lw.2 (f lw.1) = s.get lw.2 lw.1) →
        (src.place f).val p w = src.val s w := by
      cases src with
      | loc l => intro h'; simpa [Src.place, Src.val, Src.reads] using h' (l, w) (by simp [Src.reads])
      | imm v => intro _; rfl
    by_cases hz : (op = .xor ∨ op = .sub) ∧ src = .loc dst
    · obtain ⟨hop, rfl⟩ := hz
      rcases hop with rfl | rfl <;>
        simp [Instr.place, Instr.effect, Write.place, Src.place, Src.val, BinOp.eval]
    · have hs := hsrc fun lw hlw => h lw (by cases op <;> simp_all [Instr.reads])
      have hdst : op ≠ .mov → p.get w (f dst) = s.get w dst := fun hop =>
        h (dst, w) (by cases op <;> simp_all [Instr.reads])
      cases op <;>
        simp_all [Instr.place, Instr.effect, Write.place, BinOp.eval]
  | un op w dst =>
    have := h (dst, w) (by simp [Instr.reads])
    simp_all [Instr.place, Instr.effect, Write.place]
  | cnt op w src dst =>
    have := h (src, w) (by simp [Instr.reads])
    simp_all [Instr.place, Instr.effect, Write.place]
  | xchg w a b =>
    have ha := h (a, w) (by simp [Instr.reads])
    have hb := h (b, w) (by simp [Instr.reads])
    simp_all [Instr.place, Instr.effect, Write.place]
  | div w src =>
    have hd := divOperands_place hf h
    cases w <;> simp [Instr.place, Instr.effect, Write.place, hd, rax, rdx, hf]

/-- The placed instruction faults exactly when the model's does. -/
theorem Instr.fault_place {f : Loc → Loc} (hf : ∀ r, f (.reg r) = .reg r) {i : Instr}
    {s p : State} (h : ∀ lw ∈ i.reads, p.get lw.2 (f lw.1) = s.get lw.2 lw.1) :
    (i.place f).fault p = i.fault s := by
  cases i with
  | bin op w src dst => rfl
  | un op w dst => cases op <;> cases w <;> rfl
  | cnt op w src dst =>
    have := h (src, w) (by simp [Instr.reads])
    cases op <;> simp_all [Instr.place, Instr.fault]
  | xchg w a b => rfl
  | div w src =>
    have hd := divOperands_place hf h
    simp [Instr.place, Instr.fault, hd]

theorem Instr.locs_place (f : Loc → Loc) (i : Instr) : (i.place f).locs = i.locs.map f := by
  cases i with
  | bin op w src dst => cases src <;> rfl
  | un op w dst => rfl
  | cnt op w src dst => rfl
  | xchg w a b => rfl
  | div w src => rfl

/-- Every operand that the instruction names is one that the check sees: a read or a write. -/
theorem Instr.mem_locs {i : Instr} {l : Loc} (h : l ∈ i.locs) :
    (∃ w, (l, w) ∈ i.reads) ∨ ∃ w, (l, w) ∈ i.writes := by
  cases i with
  | bin op w src dst =>
    simp only [Instr.locs, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · cases src with
      | imm v => simp [Src.locs] at h
      | loc l' =>
        simp [Src.locs] at h
        subst h
        by_cases hd : l = dst
        · exact .inr ⟨w, by simp [Instr.writes, hd]⟩
        · refine .inl ⟨w, ?_⟩
          cases op <;> simp [Instr.reads, Src.reads, hd]
    · exact .inr ⟨w, by simp [Instr.writes]⟩
  | un op w dst => simp [Instr.locs] at h; exact .inr ⟨w, by simp [Instr.writes, h]⟩
  | cnt op w src dst =>
    simp [Instr.locs] at h
    rcases h with rfl | rfl
    · exact .inl ⟨w, by simp [Instr.reads]⟩
    · exact .inr ⟨w, by simp [Instr.writes]⟩
  | xchg w a b =>
    simp [Instr.locs] at h
    rcases h with rfl | rfl <;> exact .inr ⟨w, by simp [Instr.writes]⟩
  | div w src =>
    simp [Instr.locs] at h
    subst h
    cases w
    · exact .inl ⟨.w8, by simp [Instr.reads]⟩
    · exact .inl ⟨.w16, by simp [Instr.reads]⟩
    · exact .inl ⟨.w32, by simp [Instr.reads]⟩
    · exact .inl ⟨.w64, by simp [Instr.reads]⟩

/-! ## The check's state is a simulation invariant -/

/-- The check's state after one write (`Block.applyWrites`). -/
def Track.write (b : Block) (t : Track) (l : Loc) (w : Width) : Track :=
  { defined := fun l' =>
      if l' = l then
        if l.isMem then w.bits
        else if w = .w32 || w = .w64 then 64
        else Nat.max (t.defined l) w.bits
      else t.defined l'
    stale :=
      if b.outputLocs.contains l && !b.early.contains l then
        t.stale ++ b.inputLocs.filter (fun i => !b.outputLocs.contains i && Block.mayShare i l) ++
          (if l.isMem then [] else (b.inputLocs ++ b.outputLocs).filter (·.isMem))
      else t.stale }

theorem Block.applyWrites_cons (b : Block) (n : Nat) (l : Loc) (w : Width)
    (rest : List (Loc × Width)) (t : Track) :
    b.applyWrites n ((l, w) :: rest) t =
      if !b.memWidthOk l w then .error (.memWidth n l)
      else if !b.writable l then .error (.undeclaredWrite n l)
      else if l.isMem && t.stale.contains l then .error (.staleAddress n l)
      else b.applyWrites n rest (t.write b l w) := rfl

theorem Track.stale_subset_write (b : Block) (t : Track) (l : Loc) (w : Width) {x : Loc}
    (h : x ∈ t.stale) : x ∈ (t.write b l w).stale := by
  unfold Track.write
  dsimp only
  split <;> simp [h]

theorem Block.mem_operandLocs_of_memWidthOk {b : Block} {k : Nat} {w : Width}
    (h : b.memWidthOk (.mem k) w = true) : Loc.mem k ∈ b.operandLocs := by
  simp [Block.memWidthOk, Loc.isMem] at h
  simp only [Block.operandLocs, Block.inputLocs, Block.outputLocs, List.mem_append, List.mem_map]
  rcases h.1 with ⟨w', h'⟩ | ⟨w', h'⟩
  · exact .inl ⟨_, h', rfl⟩
  · exact .inr ⟨_, h', rfl⟩

/-- The model state `s` and the machine state `p` at one point of a checked block. -/
structure Sim (P : Placement) (b : Block) (p0 : State) (t : Track) (s p : State) : Prop where
  /-- The defined bits of a location that no output write may have reused are in its place. -/
  val : ∀ l, l.isMem = true ∨ l ∉ t.stale → agree (t.defined l) (s l) (p (P.loc l))
  /-- The address of a memory operand that the check still lets the block access is intact. -/
  addr : ∀ k, Loc.mem k ∈ b.operandLocs → Loc.mem k ∉ t.stale →
    ∀ r ∈ P.addr k, p (.reg r) = p0 (.reg r)
  /-- Only operands and clobbered registers ever hold defined bits. -/
  known : ∀ l, 0 < t.defined l → l ∈ b.operandLocs ∨ ∃ r, l = .reg r ∧ r ∈ b.clobbers
  /-- A register output is never stale. -/
  stale : ∀ l ∈ t.stale, l.isMem = true ∨ l ∉ b.outputLocs

theorem Block.writable_cases {b : Block} {l : Loc} (h : b.writable l = true) :
    l ∈ b.outputLocs ∨ ∃ r, l = .reg r ∧ r ∈ b.clobbers := by
  simp only [Block.writable, Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.2 with h | h
  · exact .inl (by simpa using h)
  · cases l with
    | reg r => exact .inr ⟨r, rfl, by simpa using h⟩
    | vreg k => simp at h
    | mem k => simp at h

theorem Sim.read {P : Placement} {b : Block} {p0 : State} {t : Track} {s p : State}
    (h : Sim P b p0 t s p) {l : Loc} {w : Width} (hd : w.bits ≤ t.defined l)
    (hs : l ∉ t.stale) : p.get w (P.loc l) = s.get w l :=
  ((h.val l (.inr hs)).get hd).symm

/-- One checked write keeps the invariant. -/
theorem Sim.write {P : Placement} {b : Block} {p0 : State} {t : Track} {s p : State}
    (hP : P.Admissible b) (h : Sim P b p0 t s p) (l : Loc) (w : Width) (v : BitVec w.bits)
    (hw : b.writable l = true) :
    Sim P b p0 (t.write b l w) (s.set w l v) (p.set w (P.loc l) v) := by
  have hwc := Block.writable_cases hw
  have hout_op : ∀ {x}, x ∈ b.outputLocs → x ∈ b.operandLocs := fun hx =>
    List.mem_append.mpr (.inr hx)
  -- The stale set after the write, when `l` is an output without `&`.
  have hstale' : l ∈ b.outputLocs → l ∉ b.early → ∀ x,
      (x ∈ b.inputLocs ∧ x ∉ b.outputLocs ∧ Block.mayShare x l = true) ∨
        (l.isMem = false ∧ x ∈ b.operandLocs ∧ x.isMem = true) → x ∈ (t.write b l w).stale := by
    intro hlo hle x hx
    have hc : (b.outputLocs.contains l && !b.early.contains l) = true := by simp [hlo, hle]
    simp only [Track.write, hc, ite_true, List.mem_append, List.mem_filter]
    rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact .inl (.inr ⟨h1, by simp [h2, h3]⟩)
    · refine .inr ?_
      simp only [h1, Bool.false_eq_true, ite_false, List.mem_filter]
      exact ⟨by simpa [Block.operandLocs] using h2, h3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l' hl'
    by_cases hll : l' = l
    · subst hll
      by_cases hm : l'.isMem = true
      · have hdef : (t.write b l' w).defined l' = w.bits := by simp [Track.write, hm]
        rw [hdef]
        exact State.set_agree_low s p w l' (P.loc l') v
      · have hm' : l'.isMem = false := by simpa using hm
        have hns : l' ∉ t.stale := by
          rcases hl' with hl' | hl'
          · exact absurd hl' hm
          · exact fun hx => hl' (Track.stale_subset_write b t l' w hx)
        have hdef : (t.write b l' w).defined l' =
            if w = .w32 || w = .w64 then 64 else Nat.max (t.defined l') w.bits := by
          simp [Track.write, hm']
        rw [hdef]
        exact State.set_agree_reg s p w l' (P.loc l') v hm'
          (by rw [P.loc_isMem]; exact hm') (h.val l' (.inr hns))
    · have hdef : (t.write b l w).defined l' = t.defined l' := by simp [Track.write, hll]
      rw [hdef, State.set_other s w v hll]
      have hold : l'.isMem = true ∨ l' ∉ t.stale := by
        rcases hl' with hl' | hl'
        · exact .inl hl'
        · exact .inr fun hx => hl' (Track.stale_subset_write b t l w hx)
      by_cases hpl : P.loc l' = P.loc l
      · -- Another location in the written register: it holds no defined bits.
        have hzero : t.defined l' = 0 := by
          apply Classical.byContradiction
          intro hne
          have hpos : 0 < t.defined l' := Nat.pos_of_ne_zero hne
          have hl'm : l'.isMem = false := by
            cases hm : l'.isMem with
            | false => rfl
            | true =>
              cases l' with
              | mem k => exact absurd (Placement.loc_eq_mem (P := P) (l := l) (k := k) hpl.symm).symm hll
              | reg r => simp [Loc.isMem] at hm
              | vreg k => simp [Loc.isMem] at hm
          have hlm : l.isMem = false := by
            rw [← P.loc_isMem, ← hpl, P.loc_isMem]; exact hl'm
          have hl's : l' ∉ (t.write b l w).stale := by
            rcases hl' with hl' | hl'
            · rw [hl'm] at hl'; cases hl'
            · exact hl'
          rcases h.known l' hpos with hop | ⟨r', rfl, hr'⟩
          · rcases hwc with hlo | ⟨r, rfl, hr⟩
            · have hsh := hP.share l hlo l' hop hpl.symm (Ne.symm hll)
              have hin : l' ∈ b.inputLocs := by
                rcases List.mem_append.mp hop with hi | ho
                · exact hi
                · exact absurd ho hsh.2
              refine hl's (hstale' hlo hsh.1 l' (.inl ⟨hin, hsh.2, ?_⟩))
              simp only [Block.mayShare, hl'm, hlm, beq_self_eq_true, Bool.true_and,
                Bool.not_eq_true', Bool.and_eq_false_iff]
              apply Classical.byContradiction
              intro hboth
              simp only [not_or, Bool.not_eq_false] at hboth
              exact hll (Placement.loc_eq_of_isReg hpl hboth.1 hboth.2)
            · exact hP.clobber l' hop r hr hpl
          · rcases hwc with hlo | ⟨r, rfl, hr⟩
            · exact hP.clobber l (hout_op hlo) r' hr' hpl.symm
            · exact hll hpl
        rw [hzero]
        exact fun _ hi => absurd hi (Nat.not_lt_zero _)
      · have : p.set w (P.loc l) v (P.loc l') = p (P.loc l') := State.set_other p w v hpl
        rw [this]
        exact h.val l' hold
  · intro k hk hks r hr
    have hold : Loc.mem k ∉ t.stale := fun hx => hks (Track.stale_subset_write b t l w hx)
    have hne : Loc.reg r ≠ P.loc l := by
      intro heq
      have hadm := hP.addr k hk r hr
      rcases hwc with hlo | ⟨r'', rfl, hr''⟩
      · have hlm : l.isMem = false := by
          rw [← P.loc_isMem, ← heq]; rfl
        exact hks (hstale' hlo (hadm.2 l hlo heq.symm) (.mem k) (.inr ⟨hlm, hk, rfl⟩))
      · have : r = r'' := by simpa [Placement.loc] using heq
        exact hadm.1 (this ▸ hr'')
    rw [State.set_other p w v hne]
    exact h.addr k hk hold r hr
  · intro l' hpos
    by_cases hll : l' = l
    · subst hll
      rcases hwc with hlo | hc
      · exact .inl (hout_op hlo)
      · exact .inr hc
    · have hdef : (t.write b l w).defined l' = t.defined l' := by simp [Track.write, hll]
      exact h.known l' (hdef ▸ hpos)
  · intro x hx
    unfold Track.write at hx
    dsimp only at hx
    split at hx
    · simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with (hx | hx) | hx
      · exact h.stale x hx
      · have hf := hx.2
        simp at hf
        exact .inr hf.1
      · by_cases hm : l.isMem = true
        · simp [hm] at hx
        · simp only [hm, Bool.false_eq_true, ite_false, List.mem_filter] at hx
          exact .inl hx.2
    · exact h.stale x hx

/-- The reads that `checkReads` accepts. -/
theorem Block.checkReads_none {b : Block} {n : Nat} {t : Track} {rs : List (Loc × Width)}
    (h : b.checkReads n t rs = none) :
    ∀ lw ∈ rs, b.memWidthOk lw.1 lw.2 = true ∧ lw.2.bits ≤ t.defined lw.1 ∧ lw.1 ∉ t.stale := by
  induction rs with
  | nil => intro lw hlw; cases hlw
  | cons x rest ih =>
    obtain ⟨l, w⟩ := x
    simp only [Block.checkReads] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i h1 h2 h3
          intro lw hlw
          rcases List.mem_cons.mp hlw with rfl | hlw
          · exact ⟨by simpa using h1, Nat.le_of_not_lt h2, by simpa using h3⟩
          · exact ih h lw hlw

/-- The writes that `applyWrites` accepts: a memory operand is declared and not stale. -/
theorem Block.applyWrites_ok {b : Block} {n : Nat} {ws : List (Loc × Width)} {t t' : Track}
    (h : b.applyWrites n ws t = .ok t') :
    ∀ lw ∈ ws, b.memWidthOk lw.1 lw.2 = true ∧ (lw.1.isMem = true → lw.1 ∉ t.stale) := by
  induction ws generalizing t with
  | nil => intro lw hlw; cases hlw
  | cons x rest ih =>
    obtain ⟨l, w⟩ := x
    rw [Block.applyWrites_cons] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i h1 h2 h3
          intro lw hlw
          rcases List.mem_cons.mp hlw with rfl | hlw
          · refine ⟨by simpa using h1, fun hm hs => h3 ?_⟩
            simp [hm, hs]
          · exact ⟨(ih h lw hlw).1, fun hm hs =>
              (ih h lw hlw).2 hm (Track.stale_subset_write b t l w hs)⟩

/-- The checked writes of one instruction keep the invariant. -/
theorem Sim.writes {P : Placement} {b : Block} {p0 : State} (hP : P.Admissible b) {n : Nat}
    (es : List Write) {t t' : Track} {s p : State} (h : Sim P b p0 t s p)
    (hok : b.applyWrites n (es.map fun e => (e.l, e.w)) t = .ok t') :
    Sim P b p0 t' (es.foldl State.write s) ((es.map (Write.place P.loc)).foldl State.write p) := by
  induction es generalizing t s p with
  | nil =>
    simp only [List.map_nil, Block.applyWrites] at hok
    cases hok
    exact h
  | cons e rest ih =>
    simp only [List.map_cons] at hok
    rw [Block.applyWrites_cons] at hok
    split at hok
    · cases hok
    · split at hok
      · cases hok
      · split at hok
        · cases hok
        · rename_i _ h2 _
          simp only [List.map_cons, List.foldl_cons]
          exact ih (h.write hP e.l e.w e.v (by simpa using h2)) hok

/-- One checked instruction: its memory operands are accessible on the machine, it keeps the
invariant, and it faults on the machine exactly when the model's does. -/
theorem Sim.step {P : Placement} {b : Block} {p0 : State} (hP : P.Admissible b) {n : Nat}
    {i : Instr} {t t' : Track} {s p : State} (h : Sim P b p0 t s p)
    (hr : b.checkReads n t i.reads = none) (hw : b.applyWrites n i.writes t = .ok t') :
    (i.place P.loc).locs.all (P.intact p0 p) = true ∧
      Sim P b p0 t' (i.step s) ((i.place P.loc).step p) ∧
      (i.place P.loc).fault p = i.fault s := by
  have hreads := Block.checkReads_none hr
  have hagree : ∀ lw ∈ i.reads, p.get lw.2 (P.loc lw.1) = s.get lw.2 lw.1 := fun lw hlw =>
    h.read (hreads lw hlw).2.1 (hreads lw hlw).2.2
  refine ⟨?_, ?_, Instr.fault_place P.loc_reg hagree⟩
  · rw [Instr.locs_place, List.all_map, List.all_eq_true]
    intro l hl
    cases l with
    | reg r => rfl
    | vreg k => rfl
    | mem k =>
      have hok : Loc.mem k ∈ b.operandLocs ∧ Loc.mem k ∉ t.stale := by
        rcases Instr.mem_locs hl with ⟨w, hrd⟩ | ⟨w, hwr⟩
        · exact ⟨Block.mem_operandLocs_of_memWidthOk (hreads _ hrd).1, (hreads _ hrd).2.2⟩
        · have := Block.applyWrites_ok hw _ hwr
          exact ⟨Block.mem_operandLocs_of_memWidthOk this.1, this.2 rfl⟩
      simp only [Function.comp, Placement.loc_mem, Placement.intact, List.all_eq_true,
        beq_iff_eq]
      exact fun r hr => h.addr k hok.1 hok.2 r hr
  · rw [Instr.step_eq_effect, Instr.step_eq_effect, Instr.effect_place P.loc_reg hagree]
    exact h.writes hP (i.effect s) (by rw [Instr.effect_writes]; exact hw)

theorem Block.checkOutputs_none {t : Track} {k : Nat} {outs : List (Loc × Width)}
    (h : Block.checkOutputs t k outs = none) : ∀ lw ∈ outs, lw.2.bits ≤ t.defined lw.1 := by
  induction outs generalizing k with
  | nil => intro lw hlw; cases hlw
  | cons x rest ih =>
    obtain ⟨l, w⟩ := x
    simp only [Block.checkOutputs] at h
    split at h
    · cases h
    · rename_i hlt
      intro lw hlw
      rcases List.mem_cons.mp hlw with rfl | hlw
      · exact Nat.le_of_not_lt hlt
      · exact ih h lw hlw

/-- The checked instructions from a point where the invariant holds. -/
theorem Sim.run {P : Placement} {b : Block} {p0 : State} (hP : P.Admissible b)
    (is : List Instr) {n : Nat} {t : Track} {s p : State} (h : Sim P b p0 t s p)
    (hc : b.checkFrom n is t = none) :
    ∃ p', P.run p0 (is.map (Instr.place P.loc)) p = some p' ∧
      (∀ lw ∈ b.outputs, p'.get lw.2 (P.loc lw.1) = (runInstrs is s).get lw.2 lw.1) ∧
      faultInstrs (is.map (Instr.place P.loc)) p = faultInstrs is s := by
  induction is generalizing n t s p with
  | nil =>
    refine ⟨p, rfl, ?_, rfl⟩
    intro lw hlw
    have hdef := Block.checkOutputs_none hc lw hlw
    have hmem : lw.1 ∈ b.outputLocs := List.mem_map.mpr ⟨lw, hlw, rfl⟩
    have hval : lw.1.isMem = true ∨ lw.1 ∉ t.stale := by
      by_cases hs : lw.1 ∈ t.stale
      · rcases h.stale _ hs with hm | ho
        · exact .inl hm
        · exact absurd hmem ho
      · exact .inr hs
    exact ((h.val lw.1 hval).get hdef).symm
  | cons i rest ih =>
    simp only [Block.checkFrom] at hc
    split at hc
    · cases hc
    · split at hc
      · cases hc
      · rename_i hreads
        split at hc
        · cases hc
        · rename_i t' hwrites
          obtain ⟨hint, hsim, hfault⟩ := h.step hP hreads hwrites
          obtain ⟨p', hrun, hout, hf⟩ := ih hsim hc
          refine ⟨p', ?_, hout, ?_⟩
          · simp only [List.map_cons, Placement.run, hint, ite_true]
            exact hrun
          · simp only [List.map_cons, faultInstrs, hfault, hf]

/-! ## The theorem -/

/-- **Placement independence of a checked block.** For a block that passes `Block.check`, every
admissible placement `P` and every machine state `p0` that holds the inputs in their places: the
placed instructions run (each memory operand is accessed while its address is intact), every
output holds the value that the model computes, and the fault is the model's. -/
theorem Block.check_placement {b : Block} (hc : b.check = none) {P : Placement}
    (hP : P.Admissible b) {vals : List (BitVec 64)} {p0 : State} (h0 : P.Entry b vals p0) :
    ∃ p, P.exec b p0 = some p ∧ (∀ k, P.out b p k = b.out vals k) ∧
      P.fault b p0 = b.fault vals := by
  simp only [Block.check] at hc
  split at hc
  · cases hc
  · have hfind : ∀ l lw, b.inputs.find? (·.1 == l) = some lw → lw ∈ b.inputs ∧ lw.1 = l := by
      intro l lw hf
      exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
    have hsim : Sim P b p0
        { defined := fun l => ((b.inputs.find? (·.1 == l)).map (·.2.bits)).getD 0, stale := [] }
        (initState b.inputs vals) p0 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro l _
        dsimp only
        cases hf : b.inputs.find? (·.1 == l) with
        | none => exact fun _ hi => absurd hi (Nat.not_lt_zero _)
        | some lw =>
          obtain ⟨hmem, rfl⟩ := hfind l lw hf
          exact agree_of_get (h0 lw hmem).symm
      · intro k _ _ r _
        rfl
      · intro l hpos
        dsimp only at hpos
        cases hf : b.inputs.find? (·.1 == l) with
        | none => simp [hf] at hpos
        | some lw =>
          obtain ⟨hmem, rfl⟩ := hfind l lw hf
          exact .inl (List.mem_append.mpr (.inl (List.mem_map.mpr ⟨lw, hmem, rfl⟩)))
      · intro l hl
        cases hl
    obtain ⟨p, hrun, hout, hf⟩ := hsim.run hP b.instrs hc
    refine ⟨p, hrun, ?_, hf⟩
    intro k
    simp only [Placement.out, Block.out]
    cases hk : b.outputs[k]? with
    | none => rfl
    | some lw =>
      obtain ⟨l, w⟩ := lw
      have := hout (l, w) (List.mem_of_getElem? hk)
      simp only at this ⊢
      rw [this]

/-- Two admissible placements and two machine states that hold the same inputs give the same
outputs and the same fault: the value of a checked block depends on neither. -/
theorem Block.placement_independent {b : Block} (hc : b.check = none) {P Q : Placement}
    (hP : P.Admissible b) (hQ : Q.Admissible b) {vals : List (BitVec 64)} {p0 q0 : State}
    (hp : P.Entry b vals p0) (hq : Q.Entry b vals q0) :
    ∃ p q, P.exec b p0 = some p ∧ Q.exec b q0 = some q ∧
      (∀ k, P.out b p k = Q.out b q k) ∧ P.fault b p0 = Q.fault b q0 := by
  obtain ⟨p, hpr, hpo, hpf⟩ := Block.check_placement hc hP hp
  obtain ⟨q, hqr, hqo, hqf⟩ := Block.check_placement hc hQ hq
  exact ⟨p, q, hpr, hqr, fun k => (hpo k).trans (hqo k).symm, hpf.trans hqf.symm⟩

end Zig.Isa.X86
