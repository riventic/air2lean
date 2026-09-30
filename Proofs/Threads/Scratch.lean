import Proofs.Threads.Gen
import ZigLean.Conc.Csl
import ZigLean.Simp

open Zig Threads Assn

theorem writeFlag_eq (c : Ptr) : writeFlag c = (Zig.load Ptr 8 (c.add 0) >>= fun xp =>
    Zig.load (BitVec 32) 4 (c.add 8) >>= fun v => Zig.store (α := BitVec 32) 4 xp v) := by
  unfold writeFlag
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

namespace Zig.TTriple
variable {α β : Type} {P Q R : Assn} {c : MemM α}

theorem frameL {Q : α → Assn} (ht : TTriple P c Q) : TTriple (R ∗ P) c (fun v => R ∗ Q v) :=
  ht.frame.conseq (fun _ h => sep_comm h) (fun _ _ h => sep_comm h)

/-- A step whose post names its result, then the rest. -/
theorem bind_eq {v : α} {P' : Assn} {f : α → MemM β} {Q : β → Assn}
    (hc : TTriple P c (fun r => ⌜r = v⌝ ∗ P')) (hf : TTriple P' (f v) Q) :
    TTriple P (c >>= f) Q :=
  hc.bind fun _ => TTriple.lift fun hr => hr ▸ hf
end Zig.TTriple

theorem writeFlag_spec {c x : Ptr} {Ac Ax : Nat} {cb xb : Array Byte} {v : BitVec 32}
    (hc0 : c.off = 0) (hAc : Ac % 8 = 0) (hx0 : x.off = 0) (hAx : Ax % 4 = 0)
    (hcs : cb.size = 16) (hxs : xb.size = 4)
    (hcx : Enc.decode (cb.extract 0 8) = pure x) (hcv : Enc.decode (cb.extract 8 12) = pure v) :
    TTriple (bytesAt c Ac 16 .stack cb ∗ bytesAt x Ax 4 .stack xb) (writeFlag c)
      (fun _ => bytesAt c Ac 16 .stack cb ∗ bytesAt x Ax 4 .stack (Enc.encode v)) := by
  rw [writeFlag_eq]
  refine TTriple.bind_eq (v := x) (P' := bytesAt c Ac 16 .stack cb ∗ bytesAt x Ax 4 .stack xb) ?_
    (TTriple.bind_eq (v := v) (P' := bytesAt c Ac 16 .stack cb ∗ bytesAt x Ax 4 .stack xb) ?_ ?_)
  · refine (TTriple.loadAt (k := 0) (a := 8) rfl (by decide) (by rw [hcs]; decide)
      (by simp [hc0, hAc]) hcx).frame.conseq (fun _ h => h) fun _ _ h => sep_assoc h
  · refine (TTriple.loadAt (k := 8) (a := 4) rfl (by decide) (by rw [hcs]; decide)
      (by simp [hc0]; omega) hcv).frame.conseq (fun _ h => h) fun _ _ h => sep_assoc h
  · refine (TTriple.storeAt (k := 0) (a := 4) v (by simp [Ptr.add]) (by decide)
      (by rw [hxs]; decide) (by simp [hx0, hAx]) (by decide)).frameL.conseq (fun _ h => h)
      fun _ _ h => ?_
    rwa [writeBytes_all (by rw [hxs, LawfulEnc.size_encode]; rfl)] at h
