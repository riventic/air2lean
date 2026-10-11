import LangLongTail.ErrorParams

/-!
# L10: error values as runtime parameters, on the retained translation

`LangLongTail.ErrorParams` is the translation of `air/error_params/0.16.0`; the 0.17.0, 0.15.2
and 0.14.1 exports translate to the same text apart from the profile header (`check.sh`). A
one-name error set (`error{Boom}`) is a runtime parameter like any other: the error passed in is
the error returned, whatever its name, and the generic `fail(tag, err: anytype)` instances keep
the error of their caller.
-/

open ErrorParams Zig

namespace ErrorParamsClients

/-- The error parameter is returned as given, for every name: the translation does not replace
the one-name error set's value by a constant. -/
theorem orBoom_spec (x : BitVec 32) (e : ErrName) :
    orBoom x e = pure (if x = 0#32 then .error e else .ok x) := by
  by_cases h : x = 0#32
  · subst h; simp [orBoom]
  · simp [orBoom, h]

/-- `forward` passes `error.Boom` on to `orBoom`. -/
theorem forward_spec (x : BitVec 32) :
    forward x = pure (if x = 0#32 then .error "Boom" else .ok x) := by
  simp [forward, Zig.call, orBoom_spec]

/-- The unused error parameter keeps its slot: `skipFirst`'s result is its second argument. -/
theorem skipFirst_spec (e : ErrName) (x : BitVec 32) : skipFirst e x = pure (Zig.mulWrap x 3) := by
  simp [skipFirst]

/-- The two `fail` instances: the one-name instance returns `error.Boom` at 0, the two-name one
`error.Right` (`viaFail` maps it to 201). An overflowing `tag + 1` is the safety panic. -/
theorem viaFail_values :
    (viaFail 0).run = some (.ok 100) ∧ (viaFail 1).run = some (.ok 201) ∧
      (viaFail 2).run = some (.ok 5) ∧ (viaFail 0xffffffff).run = some (.error .overflow) := by
  decide +kernel

theorem unwrapEmpty_spec (x : BitVec 32) : unwrapEmpty (.ok x) = pure x := by
  simp [unwrapEmpty, Zig.call, Zig.unwrapPayload]

end ErrorParamsClients
