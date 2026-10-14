namespace AssuranceFixture

/-- Named like engine code, but logical: a theorem states something about it, so the kernel sees
an arbitrary inhabitant of an opaque handle and the audit needs a premise. -/
partial def wpWalk (n : Nat) : Nat :=
  if n = 0 then 0 else wpWalk (n - 1)

theorem partialWrapper : wpWalk 3 = wpWalk 3 := rfl

end AssuranceFixture
