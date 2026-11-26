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
(`tests/roadmap/sep-full/DeviceCX.lean`). All five rules are instances of one step rule
(`FTotalTriple.devStep`, `FTotalTriple.of_read`).

There is no thread rule: a device access of a spawned thread is not modelled (no locality lemma,
so `fsym` does not derive one).

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig

/-- The device state after one more event (`Mem.withEvent`). -/
def DevState.withEvent (D : DevState) (e : DevEvent) : DevState := { D with trace := D.trace ++ [e] }

@[simp] theorem DevState.withEvent_trace (D : DevState) (e : DevEvent) :
    (D.withEvent e).trace = D.trace ++ [e] := rfl

@[simp] theorem DevState.withEvent_oracle (D : DevState) (e : DevEvent) :
    (D.withEvent e).oracle = D.oracle := rfl

@[simp] theorem DevState.withEvent_asmOracle (D : DevState) (e : DevEvent) :
    (D.withEvent e).asmOracle = D.asmOracle := rfl

namespace Full

open FAssn

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
      (fun x => ⟪x = v⟫ ⋆ devOwn (D.withEvent (.read addr bits v.toNat))) :=
  FTotalTriple.devStep fun _ hd => vload_run hp hal hr (hd ▸ ho)

/-- **A volatile store to a declared register**: one `write` event. -/
@[fsym] theorem FTotalTriple.vstore {d : Device} {bits align addr : Nat} {p : Ptr} {D : DevState}
    {v : BitVec bits} (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hw : d.writable addr bits = true) :
    FTotalTriple (devOwn D) (Zig.vstore d bits align p v)
      (fun _ => devOwn (D.withEvent (.write addr bits v.toNat))) :=
  (FTotalTriple.devStep (v := ()) fun _ hd => hd ▸ vstore_run hp hal hw).post
    fun _ _ h => (sep_lift.mp h).2

/-- **A declared `asm volatile` with an output**: one `asm` event with the asm oracle's answer
`v` (`ho`, premise DEV-01). -/
@[fsym] theorem FTotalTriple.vasm {d : Device} {t : String} {ins : List Nat} {bits : Nat}
    {D : DevState} {v : BitVec bits} (hd : d.asms.contains t = true)
    (ho : D.asmOracle D.trace t ins bits = some v) :
    FTotalTriple (devOwn D) (Zig.vasm d t ins bits)
      (fun x => ⟪x = v⟫ ⋆ devOwn (D.withEvent (.asm t ins bits v.toNat))) :=
  FTotalTriple.devStep fun _ hm => vasm_run hd (hm ▸ ho)

/-- **A declared `asm volatile` without an output**: one `asm` event. -/
@[fsym] theorem FTotalTriple.vasmEffect {d : Device} {t : String} {ins : List Nat} {D : DevState}
    (hd : d.asms.contains t = true) :
    FTotalTriple (devOwn D) (Zig.vasmEffect d t ins)
      (fun _ => devOwn (D.withEvent (.asm t ins 0 0))) :=
  (FTotalTriple.devStep (v := ()) fun _ hm => hm ▸ vasmEffect_run hd).post
    fun _ _ h => (sep_lift.mp h).2

/-- **A derived pointer inside the declared register window** (`&uart.data`): formed, and nothing
changes. Outside the window the operation is MM-3's `ptrProject`, which has its own rules. -/
@[fsym] theorem FTotalTriple.ptrProjectDevice {P : FAssn} {d : Device} {p : Ptr}
    {project : Ptr → Ptr} {a b : Nat} (hp : devAddr? p = some a)
    (hq : devAddr? (project p) = some b) (ha : d.inWindow a = true) (hb : d.inWindow b = true) :
    FTotalTriple P (Zig.ptrProjectDevice d p project) (fun q => ⟪q = project p⟫ ⋆ P) :=
  FTotalTriple.of_read fun _ _ _ _ _ _ => ptrProjectDevice_run hp hq ha hb

end Full
end Zig
