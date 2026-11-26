import Air2Lean.CanonCertificate
import Air2Lean.Air.Normalize

/-!
The boundaries of the drop theorems of `Air2Lean/SemDrop.lean` (V02) and the causal controls of
their native binding (`CanonCertificate.dropBound`).

Kernel-checked, for every program, call oracle and memory:

* `placeholder_not_equal`: dropping Sema's dead address-0 placeholder
  (`Raw.dropDeadAllocPlaceholders`) is no equality of `Sem.execFunc`. `Sem` gives the placeholder
  no meaning, so the function before the drop is stuck and the function after returns. The
  theorem for this rewrite is therefore the refinement `Drop.execFunc_drop_le`.
* `lanePtr_not_refined`: dropping a dead runtime lane pointer (`Raw.dropDeadRuntimeLanePtrs`) is
  not even that refinement. `Sem` checks the index of an item pointer against the vector's
  count where the pointer is formed, so the function before the drop is `.illegal` for an index
  past the count, and the function after returns. No drop theorem covers this rewrite.

These are statements about `Sem`, not native miscompilations: the compiler generates no code
for either dropped instruction.

`main` (`lean --run`) binds the actual output of `Raw.dropDeadAllocPlaceholders` to the
refinement and checks that everything else stays unbound.
-/

namespace CanonDrop

open Air2Lean Air2Lean.Sem

def types : Array Ty := #[
  .void, .noreturn, .int false 8, .ptr "one" false 2, .int false 64, .bool, .vector 4 5,
  .ptr "one" false 6, .ptr "one" false 5, .array 4 2 false, .ptr "one" false 9]

def ptrLayout : Layout := { size := some 8, align := some 8, ptrAlign := some 1 }

def layouts : Array Layout := #[
  { size := some 0, align := some 1 }, {}, { size := some 1, align := some 1 }, ptrLayout,
  { size := some 8, align := some 8 }, { size := some 1, align := some 1 },
  { size := some 1, align := some 1 }, ptrLayout, { ptrLayout with runtimeLane := true },
  { size := some 4, align := some 1 }, ptrLayout]

def fn (params : Array TyId) (body : Array Inst) : Func :=
  { dialect := .ofVersion .v0_15_2, name := "canon.f", params, ret := 0, body, types, layouts,
    globals := #[] }

/-- `%0 = bitcast(*u8, @as(usize, 0))`, the placeholder, then `ret void`. -/
def placeholder : Func := fn #[] #[⟨0, 3, .bitcast false (.int 4 0)⟩, ⟨1, 1, .ret .void⟩]

def dropZero : InstId → Bool := (· == 0)

def dropTwo : InstId → Bool := (· == 2)

theorem placeholder_ok : Drop.dropOk false dropZero placeholder = true := by
  simp only [Drop.dropOk, Drop.okBody, Drop.okInst, Drop.stuckIn, Drop.isDebug, placeholder, fn,
    dropZero] <;> rfl

theorem placeholder_before (prog : Prog) (o : Oracle) (m : Zig.Mem) :
    ((execFunc prog o placeholder []).run m).run = none := by
  have hst : evalMem placeholder (fun _ => none) ⟨0, 3, .bitcast false (.int 4 0)⟩ =
      StateT.lift stuck :=
    Drop.evalMem_stuck (D := dropZero) (fun _ _ => rfl) 0 rfl
  cases ht : prog.entryTicked "canon.f" <;>
    simp only [execFunc, placeholder, fn, argsOk, ht, execBody, execInst] <;>
    simp only [placeholder, fn] at hst <;> simp only [hst] <;> rfl

theorem placeholder_after (prog : Prog) (o : Oracle) (m : Zig.Mem) :
    ((execFunc prog o (Drop.dropFunc dropZero placeholder) []).run m).run ≠ none := by
  cases ht : prog.entryTicked "canon.f" <;>
    simp only [execFunc, Drop.dropFunc, Func.withBody, Drop.dropBody, Drop.dropInst, placeholder,
      fn, dropZero, argsOk, ht, air_sem] <;> simp <;> rfl

/-- Dropping the placeholder is no equality: before the drop the function is stuck. -/
theorem placeholder_not_equal (prog : Prog) (o : Oracle) (m : Zig.Mem) :
    (execFunc prog o placeholder []).run m ≠
      (execFunc prog o (Drop.dropFunc dropZero placeholder) []).run m := by
  intro h
  exact placeholder_after prog o m (h ▸ placeholder_before prog o m)

/-- `%2 = ptr_elem_ptr(%0, %1)` of a `*@Vector(4, bool)` and a runtime index, typed as the runtime
lane pointer and never read, then `ret void`. -/
def lanePtr : Func :=
  fn #[7, 4] #[⟨0, 7, .arg 0⟩, ⟨1, 4, .arg 1⟩, ⟨2, 8, .elemPtr (.inst 0) (.inst 1)⟩, ⟨3, 1, .ret .void⟩]

def lanePtrArgs (p : Zig.Ptr) : List Value := [.ptr p, .int false 64 9]

theorem lanePtr_before (prog : Prog) (o : Oracle) (m : Zig.Mem) (p : Zig.Ptr) :
    ((execFunc prog o lanePtr (lanePtrArgs p)).run m).run = some (.error .illegal) := by
  cases ht : prog.entryTicked "canon.f" <;>
    simp only [execFunc, lanePtr, lanePtrArgs, fn, argsOk, ht, air_sem] <;> simp <;> rfl

theorem lanePtr_after (prog : Prog) (o : Oracle) (m : Zig.Mem) (p : Zig.Ptr) :
    ∃ m', ((execFunc prog o (Drop.dropFunc dropTwo lanePtr) (lanePtrArgs p)).run m).run =
      some (.ok (.void, m')) := by
  cases ht : prog.entryTicked "canon.f" <;>
    simp only [execFunc, Drop.dropFunc, Func.withBody, Drop.dropBody, Drop.dropInst, lanePtr,
      lanePtrArgs, fn, dropTwo, argsOk, ht, air_sem] <;> simp <;> exact ⟨_, rfl⟩

open Lean.Order in
/-- Dropping the dead lane pointer is no refinement: before the drop an index past the count is
illegal behaviour in `Sem`, after it the function returns. -/
theorem lanePtr_not_refined (prog : Prog) (o : Oracle) (m : Zig.Mem) (p : Zig.Ptr) :
    ¬ (execFunc prog o lanePtr (lanePtrArgs p) ⊑
      execFunc prog o (Drop.dropFunc dropTwo lanePtr) (lanePtrArgs p)) := by
  intro h
  obtain ⟨m', hm'⟩ := lanePtr_after prog o m p
  have hb := lanePtr_before prog o m p
  have hle : (execFunc prog o lanePtr (lanePtrArgs p)).run m ⊑
      (execFunc prog o (Drop.dropFunc dropTwo lanePtr) (lanePtrArgs p)).run m := h m
  have heq := Result.eq_of_le hle fun hs => by rw [hs] at hb; cases hb
  rw [heq, hm'] at hb
  cases hb

/-! ## `itemReads` moves an item pointer's check (open finding)

`Raw.itemReads` folds `ptr_elem_ptr` and the `load` that is its only reader into one
`ptr_elem_val` at the load, wherever the load is. `Sem` checks the index where the pointer is
formed, so with the load in a branch that does not run, the function before the rewrite is
`.illegal` for an index past the count and the function after it returns
(docs/architecture-audit/canon-drop-rewrites.md). -/

/-- `%3 = ptr_elem_ptr(%0, %1)` of a `*[4]u8`, read only in the `then` branch of `%2`. -/
def itemBefore : Func :=
  fn #[10, 4, 5] #[⟨0, 10, .arg 0⟩, ⟨1, 4, .arg 1⟩, ⟨2, 5, .arg 2⟩, ⟨3, 3, .elemPtr (.inst 0) (.inst 1)⟩,
    ⟨4, 1, .condBr (.inst 2) #[⟨5, 2, .load (.inst 3)⟩, ⟨6, 1, .ret (.inst 5)⟩]
      #[⟨7, 1, .ret (.int 2 0)⟩]⟩]

/-- `itemBefore` after `Raw.itemReads` (`main` checks that it is). -/
def itemAfter : Func :=
  fn #[10, 4, 5] #[⟨0, 10, .arg 0⟩, ⟨1, 4, .arg 1⟩, ⟨2, 5, .arg 2⟩,
    ⟨4, 1, .condBr (.inst 2) #[⟨5, 2, .ptrElemVal (.inst 0) (.inst 1)⟩, ⟨6, 1, .ret (.inst 5)⟩]
      #[⟨7, 1, .ret (.int 2 0)⟩]⟩]

def itemArgs (p : Zig.Ptr) : List Value := [.ptr p, .int false 64 9, .bool false]

theorem itemReads_before (prog : Prog) (o : Oracle) (m : Zig.Mem) (p : Zig.Ptr) :
    ((execFunc prog o itemBefore (itemArgs p)).run m).run = some (.error .illegal) := by
  cases ht : prog.entryTicked "canon.f" <;>
    simp only [execFunc, itemBefore, itemArgs, fn, argsOk, ht, air_sem] <;> simp <;> rfl

theorem itemReads_after (prog : Prog) (o : Oracle) (m : Zig.Mem) (p : Zig.Ptr) :
    ∃ m', ((execFunc prog o itemAfter (itemArgs p)).run m).run =
      some (.ok (.int false 8 0, m')) := by
  cases ht : prog.entryTicked "canon.f" <;>
    simp only [execFunc, itemAfter, itemArgs, fn, argsOk, ht, air_sem] <;> simp <;> exact ⟨_, rfl⟩

/-- `itemReads` does not preserve `Sem.execFunc` on this function. -/
theorem itemReads_not_preserved (prog : Prog) (o : Oracle) (m : Zig.Mem) (p : Zig.Ptr) :
    (execFunc prog o itemBefore (itemArgs p)).run m ≠ (execFunc prog o itemAfter (itemArgs p)).run m := by
  intro h
  obtain ⟨m', hm'⟩ := itemReads_after prog o m p
  rw [← h, itemReads_before prog o m p] at hm'
  cases hm'

/-! ## The native binding -/

open Air2Lean.Raw

def inst (id : InstId) (tag : String) (ty : TyId) (args : Array Val := #[]) : RawInst :=
  { id, tag, ty := some ty, args, body := #[], thenBody := #[], elseBody := #[], cases := #[],
    target := none, param := none, callee := none, index := none, name := none, line := none,
    order := none, rmwOp := none, successOrder := none, failureOrder := none, op := none,
    mask := #[], asm := none, unsupported := false }

def rawFn (params : Array TyId) (body : Array RawInst) : RawFunc :=
  { schema := 12, version? := some .v0_15_2,
    profile := { name := "abi64-le-v1", schema := 12, zigVersion := ZigVersion.v0_15_2.toString },
    name := "canon.f", params, ret := 0, body, types, layouts, globals := #[] }

/-- The placeholder, a pointer `bitcast` of it, a debug instruction that names that, a line, and
`ret void`. -/
def rawPlaceholder : RawFunc :=
  rawFn #[] #[inst 0 "bitcast" 3 #[.int 4 0], inst 1 "bitcast" 3 #[.inst 0],
    { inst 2 "dbg_var_ptr" 0 #[.inst 1] with name := some "x" },
    { inst 3 "dbg_stmt" 0 with line := some 7 }, inst 4 "ret" 1 #[.void]]

/-- The dead runtime lane pointer of `lanePtr`. -/
def rawLanePtr : RawFunc :=
  rawFn #[7, 4] #[{ inst 0 "arg" 7 with param := some 0 }, { inst 1 "arg" 4 with param := some 1 },
    inst 2 "ptr_elem_ptr" 8 #[.inst 0, .inst 1], inst 3 "ret" 1 #[.void]]

/-- `itemBefore` as raw AIR. -/
def rawItem : RawFunc :=
  rawFn #[10, 4, 5] #[{ inst 0 "arg" 10 with param := some 0 }, { inst 1 "arg" 4 with param := some 1 },
    { inst 2 "arg" 5 with param := some 2 }, inst 3 "ptr_elem_ptr" 3 #[.inst 0, .inst 1],
    { inst 4 "cond_br" 1 #[.inst 2] with
      thenBody := #[inst 5 "load" 2 #[.inst 3], inst 6 "ret" 1 #[.inst 5]],
      elseBody := #[inst 7 "ret" 1 #[.int 2 0]] }]

def decoded (rewrite : RawFunc → RawFunc) (raw : RawFunc) : Except String (Func × Func) := do
  let pre ← normalizeCanonical raw
  let post ← normalizeCanonical (rewrite raw)
  if CanonCertificate.sameFunction pre post then throw s!"{raw.name}: the rewrite did not fire"
  pure (pre, post)

end CanonDrop

open Air2Lean CanonDrop

def main : IO Unit := do
  let expect (label : String) (want got : Bool) : IO Unit :=
    if want == got then IO.println s!"native-drop-binding: {label}"
    else throw (IO.userError s!"native drop binding: {label}: expected {want}")
  let (pre, post) ← IO.ofExcept (decoded Raw.dropDeadAllocPlaceholders rawPlaceholder)
  expect "dead placeholder bound to the refinement" true (CanonCertificate.dropBound false pre post)
  expect "dead placeholder not bound to the equality" false (CanonCertificate.dropBound true pre post)
  -- Debug information alone binds to the equality.
  let lineOnly : Func := { post with body := post.body.filter (·.id != 3) }
  expect "debug line bound to the equality" true (CanonCertificate.dropBound true post lineOnly)
  expect "changed operand rejected" false (CanonCertificate.dropBound false pre
    { post with body := post.body.modify 1 fun i => { i with op := .ret (.bool true) } })
  expect "changed function metadata rejected" false
    (CanonCertificate.dropBound false pre { post with ret := 1 })
  expect "dropped live instruction rejected" false
    (CanonCertificate.dropBound false pre { post with body := post.body.filter (·.id != 4) })
  -- A kept `alloc` whose only address-taking use is dropped changes from a block to a register
  -- local, so the drop is rejected.
  let escaping : Func := fn #[] #[⟨0, 3, .alloc⟩, ⟨1, 3, .bitcast false (.int 4 0)⟩,
    ⟨2, 3, .elemPtr (.inst 1) (.inst 0)⟩, ⟨3, 1, .ret .void⟩]
  expect "changed register classification rejected" false
    (CanonCertificate.dropBound false escaping
      { escaping with body := escaping.body.filter fun i => i.id == 0 || i.id == 3 })
  let (pre, post) ← IO.ofExcept (decoded Raw.dropDeadRuntimeLanePtrs rawLanePtr)
  expect "dead runtime lane pointer stays unbound" false (CanonCertificate.dropBound false pre post)
  -- The open `itemReads` finding is about the actual rewrite: the kernel-checked pair
  -- (`itemReads_not_preserved`) is its input and its output.
  let (pre, post) ← IO.ofExcept (decoded Raw.itemReads rawItem)
  expect "itemReads counterexample is the rewrite's input and output" true
    (CanonCertificate.sameFunction pre itemBefore && CanonCertificate.sameFunction post itemAfter)
