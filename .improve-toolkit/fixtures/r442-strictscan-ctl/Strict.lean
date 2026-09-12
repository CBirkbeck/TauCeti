import TauCeti.Basic

namespace TauCeti

/-- Every use is `.le`, so the strict hypothesis can be weakened to `≤`. -/
theorem tp_onlyLe (a b : ℝ) (hgap : a < b) : a ≤ b := by
  refine le_trans hgap.le ?_
  exact le_of_eq (by ring)

/-- The bare mention of `hsharp` below is a genuine STRICT use, so this must not be reported. -/
theorem tn_realStrict (a b : ℝ) (hsharp : a < b) : a ≤ b := by
  have hstep := hsharp.le
  exact le_of_lt hsharp

/-- `linarith` reads the context without naming hypotheses, so a text scan cannot see how
`hquiet` is used. The declaration must be SKIPPED, not reported, even though `.le` appears. -/
theorem tn_opaqueTactic (a b : ℝ) (hquiet : a < b) : a ≤ b := by
  have hstep := hquiet.le
  linarith

/-- Comments are masked before matching (r171): the bare `hmasked` in this very docstring, and in
the line comment below, are prose and must not count as strict uses. -/
theorem tp_proseMasked (a b : ℝ) (hmasked : a < b) : a ≤ b := by
  -- hmasked would be usable strictly here, but we only need hmasked in its weak form
  refine le_trans hmasked.le ?_
  exact le_of_eq (by ring)

end TauCeti
