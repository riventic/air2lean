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
/-! Wider and non-power-of-two representations: u16/u32/u64/u128, i128, u24/u40 and i7.
Each count result width is the checker's `log2 n + 1`. Wide `decide` unfolds deeper. -/
set_option maxRecDepth 20000
example : Zig.clz 5 (0 : BitVec 16) = 16 ∧ Zig.ctz 5 (0 : BitVec 16) = 16 ∧ Zig.popcount 5 (-1 : BitVec 16) = 16 := by decide
example : Zig.clz 5 (1 : BitVec 16) = 15 ∧ Zig.ctz 5 (32768 : BitVec 16) = 15 ∧ Zig.clz 5 (32768 : BitVec 16) = 0 := by decide
example : Zig.clz 6 (0 : BitVec 32) = 32 ∧ Zig.ctz 6 (0 : BitVec 32) = 32 ∧ Zig.popcount 6 (-1 : BitVec 32) = 32 := by decide
example : Zig.clz 6 (1 : BitVec 32) = 31 ∧ Zig.ctz 6 (2147483648 : BitVec 32) = 31 := by decide
example : Zig.clz 7 (0 : BitVec 64) = 64 ∧ Zig.ctz 7 (0 : BitVec 64) = 64 ∧ Zig.popcount 7 (-1 : BitVec 64) = 64 := by decide
example : Zig.clz 7 (1 : BitVec 64) = 63 ∧ Zig.ctz 7 (9223372036854775808 : BitVec 64) = 63 ∧
    Zig.clz 7 (9223372036854775808 : BitVec 64) = 0 ∧ Zig.popcount 7 (9223372036854775809 : BitVec 64) = 2 := by decide
example : Zig.clz 8 (0 : BitVec 128) = 128 ∧ Zig.ctz 8 (0 : BitVec 128) = 128 ∧ Zig.popcount 8 (-1 : BitVec 128) = 128 := by decide
example : Zig.clz 8 (1 : BitVec 128) = 127 ∧ Zig.ctz 8 (1 : BitVec 128) = 0 ∧ Zig.ctz 8 (-170141183460469231731687303715884105728 : BitVec 128) = 127 := by decide
example : Zig.clz 8 (-170141183460469231731687303715884105728 : BitVec 128) = 0 ∧
    Zig.clz 8 (170141183460469231731687303715884105727 : BitVec 128) = 1 ∧
    Zig.popcount 8 (170141183460469231731687303715884105727 : BitVec 128) = 127 := by decide
example : Zig.clz 5 (0 : BitVec 24) = 24 ∧ Zig.ctz 5 (0 : BitVec 24) = 24 ∧ Zig.popcount 5 (16777215 : BitVec 24) = 24 ∧
    Zig.clz 5 (1 : BitVec 24) = 23 ∧ Zig.ctz 5 (8388608 : BitVec 24) = 23 := by decide
example : Zig.clz 6 (0 : BitVec 40) = 40 ∧ Zig.ctz 6 (0 : BitVec 40) = 40 ∧ Zig.popcount 6 (1099511627775 : BitVec 40) = 40 ∧
    Zig.clz 6 (1 : BitVec 40) = 39 ∧ Zig.ctz 6 (549755813888 : BitVec 40) = 39 := by decide
example : Zig.clz 3 (0 : BitVec 7) = 7 ∧ Zig.ctz 3 (0 : BitVec 7) = 7 ∧ Zig.popcount 3 (-1 : BitVec 7) = 7 ∧
    Zig.clz 3 (-64 : BitVec 7) = 0 ∧ Zig.ctz 3 (-64 : BitVec 7) = 6 ∧ Zig.clz 3 (63 : BitVec 7) = 1 := by decide
example : successful (Zig.shlWithOverflow false (1 : BitVec 64) (63 : BitVec 6)) = some (9223372036854775808, 0) := by decide
example : successful (Zig.shlWithOverflow true (1 : BitVec 64) (63 : BitVec 6)) = some (9223372036854775808, 1) := by decide
example : successful (Zig.shlWithOverflow true (-1 : BitVec 64) (63 : BitVec 6)) = some (9223372036854775808, 0) := by decide
example : successful (Zig.shlWithOverflow false (3 : BitVec 64) (63 : BitVec 6)) = some (9223372036854775808, 1) := by decide
example : successful (Zig.shlWithOverflow false (-1 : BitVec 64) (0 : BitVec 6)) = some (-1, 0) := by decide
example : successful (Zig.shlWithOverflow false (1 : BitVec 128) (127 : BitVec 7)) = some (170141183460469231731687303715884105728, 0) := by decide
example : successful (Zig.shlWithOverflow true (1 : BitVec 128) (127 : BitVec 7)) = some (170141183460469231731687303715884105728, 1) := by decide
example : successful (Zig.shlWithOverflow true (-1 : BitVec 128) (127 : BitVec 7)) = some (170141183460469231731687303715884105728, 0) := by decide
example : successful (Zig.shlWithOverflow false (1 : BitVec 24) (23 : BitVec 5)) = some (8388608, 0) := by decide
example : isIllegal (Zig.shlWithOverflow false (1 : BitVec 24) (24 : BitVec 5)) = true := by decide
example : isIllegal (Zig.shlWithOverflow false (0 : BitVec 24) (31 : BitVec 5)) = true := by decide
example : successful (Zig.shlWithOverflow false (1 : BitVec 40) (39 : BitVec 6)) = some (549755813888, 0) := by decide
example : isIllegal (Zig.shlWithOverflow false (1 : BitVec 40) (40 : BitVec 6)) = true := by decide
example : isIllegal (Zig.shlWithOverflow false (0 : BitVec 40) (63 : BitVec 6)) = true := by decide
example : successful (Zig.shlWithOverflow true (1 : BitVec 7) (6 : BitVec 3)) = some (64, 1) := by decide
example : successful (Zig.shlWithOverflow true (-1 : BitVec 7) (6 : BitVec 3)) = some (64, 0) := by decide
example : successful (Zig.shlWithOverflow false (1 : BitVec 7) (6 : BitVec 3)) = some (64, 0) := by decide
example : isIllegal (Zig.shlWithOverflow true (-1 : BitVec 7) (7 : BitVec 3)) = true := by decide
