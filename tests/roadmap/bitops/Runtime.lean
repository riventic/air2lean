import ZigLean

/-! Kernel-evaluated edge cases: deliberately distinguish leading/trailing counts and
signed/unsigned overflow. These assertions also kill the designated semantic mutations. -/
private def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption
private def isIllegal {α : Type} (r : Zig.Result α) : Bool :=
  match r.run with
  | some (.error .illegal) => true
  | _ => false
example : Zig.clz 4 (1 : BitVec 8) = 7 := by decide
example : Zig.ctz 4 (1 : BitVec 8) = 0 := by decide
example : Zig.ctz 4 (128 : BitVec 8) = 7 := by decide
example : Zig.popcount 4 (129 : BitVec 8) = 2 := by decide
example : Zig.popcount 4 (-1 : BitVec 8) = 8 := by decide
example : Zig.clz 2 (0 : BitVec 3) = 3 := by decide
example : Zig.ctz 2 (0 : BitVec 3) = 3 := by decide
example : Zig.popcount 1 (1 : BitVec 1) = 1 := by decide
example : successful (Zig.shlWithOverflow false (1 : BitVec 8) (7 : BitVec 3)) = some (128, 0) := by decide
example : successful (Zig.shlWithOverflow true (1 : BitVec 8) (7 : BitVec 3)) = some (128, 1) := by decide
example : successful (Zig.shlWithOverflow true (-1 : BitVec 8) (7 : BitVec 3)) = some (128, 0) := by decide
example : isIllegal (Zig.shlWithOverflow false (0 : BitVec 3) (3 : BitVec 2)) = true := by decide
example : isIllegal (Zig.shlWithOverflow false (1 : BitVec 3) (3 : BitVec 2)) = true := by decide
example : isIllegal (Zig.shlWithOverflow true (-1 : BitVec 3) (3 : BitVec 2)) = true := by decide
example : successful (Zig.shlWithOverflow false (0 : BitVec 0) (0 : BitVec 0)) = some (0, 0) := by decide
