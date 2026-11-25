import ZigLean.Sep.Full.Ops
import ZigLean.Mem.Device

/-!
# The device state as a ghost component: regressions (`docs/sep-full-state.md` §Device state)

Until 2026-11-25 `Holds` did not read `Mem.dev`: a memory whose device oracles answer nothing held
the same resources as any other, so every `FTriple` of a device read had a precondition that no
memory satisfies (engine-ledger row `device-read-rules`). Since the maintainer decision of
2026-11-25 the device state is an exclusive ghost component (`devOwn`, `MemAuth.dev`):

1. `vload_no_triple`, `vasm_no_triple`: **a device read has no triple without `devOwn`**. A
   resource and a frame that hold no device fragment are held as well by the memory whose oracles
   answer nothing (`holds_silent`), where the read throws `.unspecified` or `.illegal`, which a
   triple forbids. So the device state must be owned, exactly as before; what changed is that it
   now can be.
2. `vload_run_of_devOwn`: **`devOwn D` fixes the read**: the memory's device state is `D`
   (`Holds.dev`), so the read answers what `D`'s oracle answers for `D`'s trace.
3. `vload_step_holds`: **the read's step keeps `Holds`**: the memory after the read (one more
   event) holds the resource with `devOwn` of the longer trace (`Holds.setDev`), with the same
   frame. Together with 2 this is the memory side of the `vload` rule.
4. `devOwn_twice`: two `devOwn` are never held together (`Holds.devOwn_excl`).

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zig.Full.DeviceCX

open Zig Zig.Full Zig.Full.FAssn

/-- The device state of `m` with oracles that answer nothing (same trace). -/
def silentDev (m : Mem) : DevState :=
  { m.dev with oracle := fun _ _ _ => none, asmOracle := fun _ _ _ _ => none }

/-- `m` with a device whose oracles answer nothing. -/
def silent (m : Mem) : Mem := { m with dev := silentDev m }

/-- **Without device fragments `Holds` does not read the device state.** -/
theorem holds_silent {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (h0 : ∀ D, (r.gh.add rF.gh).dev D = 0) : Holds (silent m) r rF := by
  exact hh.devChange (g' := r.gh) (silentDev m) rfl
    (hh.ghost.2.2.2.withDevState (silentDev m) fun D hD =>
      absurd hD (by rw [h0 D]; exact Nat.lt_irrefl 0))

theorem fseq_silent {m : Mem} (hs : m.FSeq) : (silent m).FSeq := ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩

theorem vload_silent (d : Device) (bits align : Nat) (p : Ptr) (m : Mem) :
    ∃ e, e ≠ Error.stackOverflow ∧
      ((vload d bits align p).run (silent m)).run = some (.error e) := by
  unfold vload
  simp only [StateT.run]
  split
  · exact ⟨_, by decide, rfl⟩
  · split
    · exact ⟨_, by decide, rfl⟩
    · split
      · exact ⟨_, by decide, rfl⟩
      · exact ⟨_, by decide, rfl⟩

theorem vasm_silent (d : Device) (t : String) (ins : List Nat) (bits : Nat) (m : Mem) :
    ∃ e, e ≠ Error.stackOverflow ∧ ((vasm d t ins bits).run (silent m)).run = some (.error e) := by
  unfold vasm
  simp only [StateT.run]
  split
  · exact ⟨_, by decide, rfl⟩
  · exact ⟨_, by decide, rfl⟩

/-- **No triple of a device read from a resource without `devOwn`.** -/
theorem vload_no_triple {d : Device} {bits align : Nat} {p : Ptr} {P : FAssn}
    {Q : BitVec bits → FAssn} (ht : FTriple P (vload d bits align p) Q)
    {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq)
    (h0 : ∀ D, (r.gh.add rF.gh).dev D = 0) : False := by
  have h := ht (silent m) r rF (holds_silent hh h0) hp (fseq_silent hs)
  obtain ⟨e, he, hr⟩ := vload_silent d bits align p m
  rw [hr] at h
  exact he h

theorem vasm_no_triple {d : Device} {t : String} {ins : List Nat} {bits : Nat} {P : FAssn}
    {Q : BitVec bits → FAssn} (ht : FTriple P (vasm d t ins bits) Q)
    {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq)
    (h0 : ∀ D, (r.gh.add rF.gh).dev D = 0) : False := by
  have h := ht (silent m) r rF (holds_silent hh h0) hp (fseq_silent hs)
  obtain ⟨e, he, hr⟩ := vasm_silent d t ins bits m
  rw [hr] at h
  exact he h

/-- **`devOwn D` fixes the read**: it answers what `D`'s oracle answers for `D`'s trace. -/
theorem vload_run_of_devOwn {d : Device} {bits align addr : Nat} {p : Ptr} {D : DevState}
    {R : FAssn} {v : BitVec bits} {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hr : (devOwn D ⋆ R) r) (hp : devAddr? p = some addr) (hal : addr % align = 0)
    (hrd : d.readable addr bits = true) (ho : D.oracle D.trace addr bits = some v) :
    (vload d bits align p).run m = pure (v, m.withEvent (.read addr bits v.toNat)) := by
  obtain rfl := hh.dev hr
  exact vload_run hp hal hrd ho

/-- **The read's step keeps `Holds`**, with `devOwn` of the longer trace and the same frame. -/
theorem vload_step_holds {D : DevState} {addr bits : Nat} {v : BitVec bits} {m : Mem}
    {r rF : Res} (hh : Holds m ⟨r.heap, r.know, (Ghost.devAt D).add r.gh⟩ rF) :
    Holds (m.withEvent (.read addr bits v.toNat))
      ⟨r.heap, r.know, (Ghost.devAt { D with trace := D.trace ++ [.read addr bits v.toNat] }).add r.gh⟩
      rF := by
  obtain rfl := hh.dev (devOwn_sep_intro (R := fun x => x = r) rfl)
  exact hh.setDev _

/-- **Two `devOwn` are never held together.** -/
theorem devOwn_twice {m : Mem} {r rF : Res} {D D' : DevState} (hh : Holds m r rF)
    (h : (devOwn D ⋆ devOwn D' ⋆ emp) r) : False :=
  hh.devOwn_excl h

end Zig.Full.DeviceCX

#print axioms Zig.Full.DeviceCX.vload_no_triple
#print axioms Zig.Full.DeviceCX.vasm_no_triple
#print axioms Zig.Full.DeviceCX.vload_run_of_devOwn
#print axioms Zig.Full.DeviceCX.vload_step_holds
#print axioms Zig.Full.DeviceCX.devOwn_twice
