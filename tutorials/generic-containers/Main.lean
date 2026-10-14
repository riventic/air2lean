import Proofs.Lists.Append

/-!
Generic containers: `std.ArrayListUnmanaged(u32).append`, the `u32` instance of Zig's generic
array list, translated from the std source. A successful append leaves the list `xs ++ [v]`,
for every allocator that meets the allocator contract; the rest of the memory is untouched.

From the repository root:
  lake build Proofs.Lists.Append
  lake env lean tutorials/generic-containers/Main.lean

See tutorials/generic-containers/README.md for the source, the exercise and the negative control.
-/

namespace GenericContainers

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc Lists.Append

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

/-- A successful `append` gives the list with `v` at the end (possibly in a new buffer); the
fee `I.fee φ` it may spend on a new buffer comes back. -/
theorem append_success (p : Ptr) (xs : List (BitVec 32)) (v : BitVec 32)
    (room : I.fits (4 * growTo (xs.length + 1)) 2)
    (contract : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ (alist I φ p xs ⋆ vtR vtp fns.toList)))
      (array_list_Aligned_u32_null_append p ⟨ctx, vtp⟩ v)
      (fun r => I.own ⋆ (I.fee φ ⋆ ((FAssn.ex fun ys => ⟪r = .ok () → ys = xs ++ [v]⟫ ⋆
        alist I φ p ys) ⋆ vtR vtp fns.toList))) :=
  (append_spec ctx vtp fns I e φ p xs v room contract).post fun r _ h =>
    sep_mono_right (fun _ h => sep_mono_right (fun _ h => sep_mono_left (fun _ h => by
      cases r with
      | ok => exact ⟨xs ++ [v], sep_lift.mpr ⟨fun _ => rfl, h⟩⟩
      | error =>
        obtain ⟨-, h⟩ := sep_lift.mp h
        exact ⟨xs, sep_lift.mpr ⟨nofun, h⟩⟩) h) h) h

end GenericContainers
