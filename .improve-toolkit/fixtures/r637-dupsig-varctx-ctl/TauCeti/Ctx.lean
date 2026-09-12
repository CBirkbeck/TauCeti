namespace TauCeti

section Special
variable {V : Type*} [NormedAddCommGroup V] [FiniteDimensional ℝ V]

/-- Proved under the finite-dimensional instance. -/
private theorem tp_result_of_finiteDimensional (hc : 0 ≤ c) : SomePred V c := by
  trivial

end Special

section General
variable {V : Type*} [NormedAddCommGroup V]

/-- The same signature TEXT, but without the `FiniteDimensional` instance: a different theorem. -/
theorem tp_result (hc : 0 ≤ c) : SomePred V c := by
  trivial

end General

section Same
variable {W : Type*}

/-- Two declarations in ONE `variable` context with identical signatures ARE a duplicate. -/
theorem tp_dup_one (hw : 0 ≤ d) : OtherPred W d := by
  trivial

/-- Same context, same signature. -/
theorem tp_dup_two (hw : 0 ≤ d) : OtherPred W d := by
  trivial

end Same

end TauCeti
