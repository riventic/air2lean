import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AutoAttr
import ZigLean.Mem.Device

/-!
# Device accesses (`docs/sep-full-state.md` §Device state, `docs/volatile-effects.md`)

The full-state rules of the device operations of `ZigLean/Mem/Device.lean` (L13,
`air2lean --device-contract`), stated once for every declared device `d : Device` (its register
map and asm templates) and every device state `D : DevState` (the environment's oracles and the
trace so far). A program's device (`air2lean_device` of a generated module) is an instance.

The device state is the exclusive ghost component `devOwn D` (`ZigLean/Sep/Full/Ghost.lean`):

* `FTotalTriple.vload`, `FTotalTriple.vasm`: a read asks `D`'s oracle with `D`'s trace. The
  oracle's answer is the rule's premise (the environment's side of premise DEV-01: a theorem
  quantifies over the oracle and names the answers it relies on); the read returns it and leaves
  `devOwn` of the trace with one more event.
* `FTotalTriple.vstore`, `FTotalTriple.vasmEffect`: one more event; no oracle is asked.
* `FTotalTriple.ptrProjectDevice`: an offset of a device address inside the declared register
  window that stays inside it is formed; no resource is read.

Fail closed: a read whose answer no premise names, an address, width or direction that `d` does
not declare, a template that `d` does not declare and a pointer into a model block have no rule
(the operations throw there), and without `devOwn` no triple of a read exists
(`tests/roadmap/sep-full/DeviceCX.lean`). The four device steps are instances of one step rule
(`FTotalTriple.devStep`).

The new device state is written as the structure `{ D with trace := D.trace ++ [e] }`, not
through a function of `D`: `fsym` compares two `devOwn` atoms field by field, the traces as lists.
A run gets `devOwn D` from the start memory with the device state `D`
(`FTotalTriple.run_init_dev`, `ZigLean/Sep/Full/Init.lean`).

There is no thread rule: a device access of a spawned thread is not modelled (no locality lemma,
so `fsym` does not derive one).

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig

namespace Full

open FAssn

attribute [fsym_atom] devOwn

/-- **A device step**: a command that, in every memory with the device state `D`, returns `v` and
changes the device state to `D'` and nothing else, takes `devOwn D` to `devOwn D'`. -/
theorem FTotalTriple.devStep {α : Type} {c : MemM α} {D D' : DevState} {v : α}
    (h : ∀ m : Mem, m.dev = D → c.run m = pure (v, { m with dev := D' })) :
    FTotalTriple (devOwn D) c (fun x => ⟪x = v⟫ ⋆ devOwn D') :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    obtain ⟨h0, k0, g0⟩ := hp
    have hr : r = ⟨(⟨FHeap.empty, Know.none, Ghost.unit⟩ : Res).heap,
        (⟨FHeap.empty, Know.none, Ghost.unit⟩ : Res).know,
        (Ghost.devAt D).add (⟨FHeap.empty, Know.none, Ghost.unit⟩ : Res).gh⟩ := by
      rw [res_eta r, h0, k0, g0, Ghost.add_unit]
    rw [hr] at hh
    have hd : m.dev = D := hh.dev (devOwn_sep_intro (R := emp) ⟨rfl, rfl, rfl⟩)
    exact ⟨v, { m with dev := D' }, _, h m hd, hh.setDev D',
      sep_lift.mpr ⟨rfl, rfl, rfl, Ghost.add_unit _⟩, ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩⟩

/-- **A volatile load of a declared register**: one `read` event with the oracle's answer `v`
(`ho`: the environment's answer to this read after the trace so far, premise DEV-01). -/
@[fsym] theorem FTotalTriple.vload {d : Device} {bits align addr : Nat} {p : Ptr} {D : DevState}
    {v : BitVec bits} (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hr : d.readable addr bits = true) (ho : D.oracle D.trace addr bits = some v) :
    FTotalTriple (devOwn D) (Zig.vload d bits align p)
      (fun x => ⟪x = v⟫ ⋆ devOwn { D with trace := D.trace ++ [.read addr bits v.toNat] }) :=
  FTotalTriple.devStep fun _ hd => by subst hd; exact vload_run hp hal hr ho

/-- **A volatile store to a declared register**: one `write` event. -/
@[fsym] theorem FTotalTriple.vstore {d : Device} {bits align addr : Nat} {p : Ptr} {D : DevState}
    {v : BitVec bits} (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hw : d.writable addr bits = true) :
    FTotalTriple (devOwn D) (Zig.vstore d bits align p v)
      (fun _ => devOwn { D with trace := D.trace ++ [.write addr bits v.toNat] }) :=
  (FTotalTriple.devStep (v := ()) fun _ hd => by subst hd; exact vstore_run hp hal hw).post
    fun _ _ h => (sep_lift.mp h).2

/-- **A declared `asm volatile` with an output**: one `asm` event with the asm oracle's answer
`v` (`ho`, premise DEV-01). -/
@[fsym] theorem FTotalTriple.vasm {d : Device} {t : String} {ins : List Nat} {bits : Nat}
    {D : DevState} {v : BitVec bits} (hd : d.asms.contains t = true)
    (ho : D.asmOracle D.trace t ins bits = some v) :
    FTotalTriple (devOwn D) (Zig.vasm d t ins bits)
      (fun x => ⟪x = v⟫ ⋆ devOwn { D with trace := D.trace ++ [.asm t ins bits v.toNat] }) :=
  FTotalTriple.devStep fun _ hm => by subst hm; exact vasm_run hd ho

/-- **A declared `asm volatile` without an output**: one `asm` event. -/
@[fsym] theorem FTotalTriple.vasmEffect {d : Device} {t : String} {ins : List Nat} {D : DevState}
    (hd : d.asms.contains t = true) :
    FTotalTriple (devOwn D) (Zig.vasmEffect d t ins)
      (fun _ => devOwn { D with trace := D.trace ++ [.asm t ins 0 0] }) :=
  (FTotalTriple.devStep (v := ()) fun _ hm => by subst hm; exact vasmEffect_run hd).post
    fun _ _ h => (sep_lift.mp h).2

/-- **A derived pointer inside the declared register window** (`&uart.data`): formed, and nothing
changes. Outside the window the operation is MM-3's `ptrProject`, which has its own rules. -/
@[fsym] theorem FTotalTriple.ptrProjectDevice {P : FAssn} {d : Device} {p : Ptr}
    {project : Ptr → Ptr} {a b : Nat} (hp : devAddr? p = some a)
    (hq : devAddr? (project p) = some b) (ha : d.inWindow a = true) (hb : d.inWindow b = true) :
    FTotalTriple P (Zig.ptrProjectDevice d p project) (fun q => ⟪q = project p⟫ ⋆ P) :=
  FTotalTriple.of_read fun _ _ _ _ _ _ => ptrProjectDevice_run hp hq ha hb

/-! ## The run of a triple over the device state

What a triple over `devOwn` says about a run, for a memory that is `Mem.FSeq` and holds a resource
and a frame without a device fragment (`Holds.addDev` hands `devOwn m.dev` to the program): the
run returns, its final device state is the postcondition's, and the frame is held again. A triple
says nothing about another memory and does not fix the final memory's other fields
(`tests/roadmap/sep-auto/SepAuto/DeviceRunCX.lean`: `not_exact`, `not_every_memory`). The step
count of such a run is `FTotalTriple.run_dev_ticks` (`ZigLean/Sep/Full/Cost.lean`). -/

/-- **The run of a total triple over the device state**: from a memory that holds `P` (no device
fragment in the resource or the frame), the run returns, and the final device state is `D'`. -/
theorem FTotalTriple.run_dev {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {D' : DevState}
    {m : Mem} {r rF : Res} (ht : FTotalTriple (devOwn m.dev ⋆ P) c (fun x => devOwn D' ⋆ Q x))
    (hh : Holds m r rF) (hp : P r) (hs : m.FSeq) (h0 : ∀ X, (r.gh.add rF.gh).dev X = 0) :
    ∃ v m' r', c.run m = pure (v, m') ∧ m'.dev = D' ∧ Holds m' r' rF ∧
      (devOwn D' ⋆ Q v) r' ∧ m'.FSeq := by
  obtain ⟨v, m', r', hr, hh', hq, hs'⟩ := ht.runs (hh.addDev h0) (devOwn_sep_intro hp) hs
  exact ⟨v, m', r', hr, hh'.dev hq, hh', hq, hs'⟩

/-- **The run of a device triple that returns `v`**: the form of the device rules. From every
`Mem.FSeq` memory that holds a resource and a frame without a device fragment, the run returns
`v`, and the final device state is `D'`. -/
theorem FTotalTriple.run_dev_val {α : Type} {c : MemM α} {v : α} {D' : DevState} {m : Mem}
    {r rF : Res} (ht : FTotalTriple (devOwn m.dev) c (fun x => ⟪x = v⟫ ⋆ devOwn D'))
    (hh : Holds m r rF) (hs : m.FSeq) (h0 : ∀ X, (r.gh.add rF.gh).dev X = 0) :
    ∃ m', c.run m = pure (v, m') ∧ m'.dev = D' := by
  obtain ⟨x, m', r', hr, hd, -, hq, -⟩ :=
    FTotalTriple.run_dev (P := fun y => y = r) (Q := fun x => ⟪x = v⟫ ⋆ fun y => y = r)
      ((ht.frame (R := fun y => y = r)).post fun x r' h => by
        rwa [show (devOwn D' ⋆ (⟪x = v⟫ ⋆ fun y => y = r)) =
          ((⟪x = v⟫ ⋆ devOwn D') ⋆ fun y => y = r) by ac_rfl]) hh rfl hs h0
  obtain ⟨-, r₂, -, -, -, h2⟩ := hq
  obtain ⟨rfl, -⟩ := sep_lift.mp h2
  exact ⟨m', hr, hd⟩

end Full
end Zig
