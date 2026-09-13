module
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.PrimePowerIndex
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt

/-! # probe: summability of the von Mangoldt weighted ideal terms -/

@[expose] public section
open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField
namespace TauCeti
namespace MultiplicativeIdealWeight
variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

theorem summable_idealTerm_vonMangoldtTransform {s : ℂ}
    (hs : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    Summable (idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s) := by
  obtain ⟨y, hy, hys⟩ : ∃ y : ℝ, Summable (idealTerm K χ.toIdealArithmeticFunction y)
      ∧ y < s.re := by simpa [idealAbscissaOfAbsConv_def, sInf_lt_iff] using hs
  have hlog := summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re
    (f := χ.toIdealArithmeticFunction) (s := (y : ℂ)) (s' := s)
    (h := by simpa using hys) (hs := hy)
  refine hlog.of_norm_bounded fun A ↦ ?_
  have hfac : ‖idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s A‖
      = ‖(IdealArithmeticFunction.vonMangoldt : IdealArithmeticFunction K) A‖
        * ‖idealTerm K χ.toIdealArithmeticFunction s A‖ := by
    rw [idealTerm_def, idealTerm_def, IdealArithmeticFunction.vonMangoldtTransform_apply,
      norm_div, norm_div, norm_mul]
    ring
  rw [hfac]
  exact mul_le_mul_of_nonneg_right
    (IdealArithmeticFunction.norm_vonMangoldt_le_log A) (norm_nonneg _)

end MultiplicativeIdealWeight
end TauCeti
