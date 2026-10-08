import Calls

/-! Theorems about the fresh emitted `Calls.callOnce` (one call through a parameter): it is
`dispatchIn` over `resolve` of the program's callable-address table, for every pointer. The
dispatch is then complete for the declared targets of its signature and rejects the
target of another signature and every unknown executable address. -/
namespace IndirectCallsBridge
open Calls Zig Zig.External

def unary : String := "fn (u32) u32"
def binary : String := "fn (u32, u32) u32"

/-- The program's table (`fnRefs`): each address-taken function's block (`mem0` order)
and its signature. -/
def table : List (String × Ptr) :=
  [(unary, ⟨some 0, 0⟩), (unary, ⟨some 1, 0⟩), (unary, ⟨some 2, 0⟩), (binary, ⟨some 3, 0⟩)]

/-- The translated implementation of each `fn (u32) u32` target, by address. -/
def impl (x : BitVec 32) (q : Ptr) : MemM (BitVec 32) :=
  StateT.lift (if q = ⟨some 0, 0⟩ then double x else if q = ⟨some 1, 0⟩ then succ x
    else square x)

theorem table_nodup : (table.map (·.2)).Nodup := by decide

/-- The emitted indirect call is the table dispatch, for every pointer. -/
theorem callOnce_resolve (p : Ptr) (x : BitVec 32) (m : Mem) :
    (callOnce p x).run m = (dispatchIn (resolve table unary (impl x)) p).run m := by
  by_cases h0 : p = ⟨some 0, 0⟩
  · subst h0; rfl
  by_cases h1 : p = ⟨some 1, 0⟩
  · subst h1; rfl
  by_cases h2 : p = ⟨some 2, 0⟩
  · subst h2; rfl
  have lhs : (callOnce p x).run m = (throw .illegal : MemM (BitVec 32)).run m := by
    simp [callOnce, h0, h1, h2]
    rfl
  rw [lhs]
  by_cases h3 : p = ⟨some 3, 0⟩
  · subst h3
    rw [resolve_incompatible (t := binary) (by simp [table]) (by decide) table_nodup]
  · rw [resolve_unknown (by simp [table, h0, h1, h2, h3])]

/-- Completeness: every declared target of the signature is reachable and runs itself. -/
theorem callOnce_complete {q : Ptr} (mem : (unary, q) ∈ table) (x : BitVec 32) (m : Mem) :
    (callOnce q x).run m = (impl x q).run m := by
  rw [callOnce_resolve, resolve_complete mem table_nodup]

/-- The declared target of another signature is never called through this pointer type. -/
theorem callOnce_incompatible (x : BitVec 32) (m : Mem) :
    (callOnce ⟨some 3, 0⟩ x).run m = (throw .illegal : MemM (BitVec 32)).run m := by
  rw [callOnce_resolve, resolve_incompatible (t := binary) (by simp [table]) (by decide)
    table_nodup]

/-- Any address outside the table, an unknown executable address, is rejected. -/
theorem callOnce_unknown {p : Ptr} (h : p ∉ table.map (·.2)) (x : BitVec 32) (m : Mem) :
    (callOnce p x).run m = (throw .illegal : MemM (BitVec 32)).run m := by
  rw [callOnce_resolve, resolve_unknown h]

/-- A successful call ran a declared target of its signature. -/
theorem callOnce_ok {p : Ptr} {x r : BitVec 32} {m m' : Mem}
    (run : (callOnce p x).run m = some (.ok (r, m'))) :
    (unary, p) ∈ table ∧ (impl x p).run m = some (.ok (r, m')) := by
  rw [callOnce_resolve] at run
  by_cases hm : (unary, p) ∈ table
  · rw [resolve_complete hm table_nodup] at run
    exact ⟨hm, run⟩
  · rw [dispatchIn_not_mem (fun h => hm (mem_resolve_addresses.mp h))] at run
    cases run

end IndirectCallsBridge
