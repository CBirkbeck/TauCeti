module
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.PrimePowerIndex
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup

/-! # probe: the summand of the von Mangoldt identity -/

@[expose] public section
open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField
namespace TauCeti
variable {K : Type*} [Field K] [NumberField K]

example (χ : MultiplicativeIdealWeight K) (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s
        (idealPrimePowerOf P k : (Ideal (𝓞 K))⁰)
      = Complex.log (Ideal.absNorm P.asIdeal : ℂ)
          * (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ (k + 1) := by
  have hmem : P.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have hP : Prime (((⟨P.asIdeal, hmem⟩ : (Ideal (𝓞 K))⁰)) : Ideal (𝓞 K)) :=
    Ideal.prime_of_isPrime P.ne_bot P.isPrime
  have hpow : (idealPrimePowerOf P k : (Ideal (𝓞 K))⁰)
      = (⟨P.asIdeal, hmem⟩ : (Ideal (𝓞 K))⁰) ^ (k + 1) := Subtype.ext (by simp)
  rw [idealTerm_def, hpow,
    MultiplicativeIdealWeight.vonMangoldtTransform_apply_prime_pow _ hP k.succ_pos,
    SubmonoidClass.coe_pow, map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow]
  have hlog : Complex.log (Ideal.absNorm P.asIdeal : ℂ)
      = ((Real.log (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
  rw [hlog, Nat.succ_eq_add_one]
  ring

end TauCeti
