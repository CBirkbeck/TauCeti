/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Norm.Reduction
public import TauCeti.NumberTheory.ModularForms.QExpansion.BigO
public import TauCeti.Analysis.Asymptotics.Punctured

/-!
# Vanishing `q`-coefficients transfer to the level-one norm

The finite-dimensionality of `M_k(Γ)` at general level is proved by showing that the map
"first `N` `q`-expansion coefficients" is eventually injective, and the step that makes that
work is the **norm step** recorded here: if the first `N` coefficients of `f` vanish, so do the
first `N` coefficients of its level-one norm `ModularForm.norm 𝒮ℒ f`.

The mechanism is `Norm/Reduction.lean`'s factorisation `norm f = f * restProd f`. Passing to
cusp functions turns it into a product near the puncture `q = 0`, where `restProd f` is bounded;
so an `O(‖q‖ ^ N)` bound on the cusp function of `f` transfers to the norm. The bound holds only
on the *punctured* neighbourhood, because `restProd` is only controlled there — extending it
across `0` is `TauCeti.isBigO_nhds_of_isBigO_punctured`, a general fact about punctured
`O`-bounds kept in `TauCeti/Analysis/Asymptotics/Punctured.lean`, applied using that the cusp
function of the norm vanishes at `0`.

## Main results

* `ModularForm.NormReduction.τfun`: the inverse `q`-parameter, as a map to `ℍ`.
* `ModularForm.NormReduction.qExpansion_coeff_eq_zero_norm_of_qExpansion_coeff_eq_zero`:
  the norm step.

## References

Ported from AINTLIB's `LeanModularForms` project
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit `6d87d596a537`,
Apache 2.0),
`projects/LeanModularForms/LeanModularForms/Modularforms/DimGenCongLevels/NormTransfer.lean`,
whose `qExpansion_coeff_eq_zero_norm_of_qExpansion_coeff_eq_zero` is the main result here. That
file's `norm_apply_eq_mul_restProd` and `valueAtInfty_norm_eq_zero_of_valueAtInfty_eq_zero`
already live in `Norm/Reduction.lean`, so only the analytic half is ported. The cusp width is
this repository's `(G Γ).strictWidthInfty` in place of that project's `cuspWidth`.
-/

open scoped MatrixGroups Topology
open Filter UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass

public section

namespace ModularForm.NormReduction

open TauCeti TauCeti.ModularForm.NormReduction

noncomputable section
variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- **The inverse `q`-parameter, landing in `ℍ`**: `q ↦ ofComplex (invQParam h q)`. It is the
change of variables under which a cusp function is evaluated, and it carries the punctured
neighbourhood of `0` to `Im τ → ∞` (`tendsto_τfun_atImInfty`). -/
def τfun (h : ℝ) : ℂ → ℍ :=
  fun q : ℂ ↦ UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q)

/-- **Unfolding `τfun` pointwise**: it is `ofComplex` of the inverse `q`-parameter. -/
@[simp]
theorem τfun_apply (h : ℝ) (q : ℂ) :
    τfun h q = UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) := by
  unfold τfun
  rfl

/-- **Unfolding `τfun` as a function**, for rewriting under a `Tendsto` or a composition. -/
theorem τfun_def (h : ℝ) :
    τfun h = fun q : ℂ ↦ UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) := by
  unfold τfun
  rfl

/-- **`τfun` carries the puncture to the cusp**: `q → 0` with `q ≠ 0` sends `τfun h q` to
`Im τ → ∞`. -/
theorem tendsto_τfun_atImInfty {h : ℝ} (hh : 0 < h) :
    Tendsto (τfun h) (𝓝[≠] (0 : ℂ)) UpperHalfPlane.atImInfty := by
  rw [τfun_def]
  simpa [Function.comp_def] using
    UpperHalfPlane.tendsto_comap_im_ofComplex.comp
      (Function.Periodic.invQParam_tendsto (h := h) hh)

/-- **The cusp function is the form evaluated at `τfun`**, away from the puncture. -/
theorem cuspFunction_eq_eval_τfun_of_ne_zero {Γ' : Subgroup (GL (Fin 2) ℝ)} {k' : ℤ} {h : ℝ}
    (f : ModularForm Γ' k') {q : ℂ} (hq : q ≠ 0) : cuspFunction h f q = f (τfun h q) := by
  simp [cuspFunction, Function.Periodic.cuspFunction, τfun_apply, hq]

section FiniteIndex

variable [Γ.FiniteIndex]

/-- **The cusp function of the norm factors**, away from the puncture: the cusp function of `f`
times `restProd f` evaluated at `τfun`. This is `norm_apply_eq_mul_restProd` transported through
`cuspFunction_eq_eval_τfun_of_ne_zero`. -/
theorem cuspFunction_norm_eq_mul_restProd_of_ne_zero (f : ModularForm (G Γ) k) {h : ℝ} {q : ℂ}
    (hq : q ≠ 0) :
    cuspFunction h (_root_.ModularForm.norm 𝒮ℒ f) q =
      cuspFunction h f q * restProd f (τfun h q) := by
  rw [cuspFunction_eq_eval_τfun_of_ne_zero (f := _root_.ModularForm.norm 𝒮ℒ f) hq,
    cuspFunction_eq_eval_τfun_of_ne_zero (f := f) hq]
  simpa using norm_apply_eq_mul_restProd f (τfun h q)

/-- **`restProd` is bounded near the puncture**, being bounded at `Im τ → ∞` and precomposed
with `τfun`, which carries the puncture there. -/
theorem isBigO_one_restProd_τfun (f : ModularForm (G Γ) k) {h : ℝ} (hh : 0 < h) :
    (fun q : ℂ ↦ restProd f (τfun h q)) =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℝ) := by
  have hb : restProd f =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := isBoundedAtImInfty_restProd f
  exact hb.comp_tendsto (tendsto_τfun_atImInfty (h := h) hh)

/-- **Near the puncture the cusp function of the norm factors**, as an eventual equality on
`𝓝[≠] 0`. -/
theorem cuspFunction_norm_eventuallyEq_mul (f : ModularForm (G Γ) k) {h : ℝ} :
    (fun q : ℂ ↦ cuspFunction h (_root_.ModularForm.norm 𝒮ℒ f) q) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q : ℂ ↦ cuspFunction h f q * restProd f (τfun h q) := by
  filter_upwards [self_mem_nhdsWithin (s := ({0}ᶜ : Set ℂ))] with q hq
  exact cuspFunction_norm_eq_mul_restProd_of_ne_zero f (by simpa using hq)

/-- **The punctured `O(‖q‖ ^ N)` bound for the norm's cusp function**, when the first `N`
`q`-coefficients of `f` vanish: the bound for `f` holds on a full neighbourhood, and the extra
factor is bounded near the puncture. -/
theorem isBigO_pow_cuspFunction_norm_punctured (f : ModularForm (G Γ) k)
    (hh : 0 < (G Γ).strictWidthInfty)
    (hper : (G Γ).strictWidthInfty ∈ (G Γ).strictPeriods) (N : ℕ)
    (hcoeff : ∀ m < N, (qExpansion (G Γ).strictWidthInfty f).coeff m = 0) :
    cuspFunction (G Γ).strictWidthInfty (_root_.ModularForm.norm 𝒮ℒ f) =O[𝓝[≠] (0 : ℂ)]
      fun q : ℂ ↦ ‖q‖ ^ N := by
  have hO_f := _root_.TauCeti.ModularFormClass.cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero
    f hh hper N hcoeff
  have hprod := (hO_f.mono nhdsWithin_le_nhds).mul (isBigO_one_restProd_τfun f hh)
  refine (hprod.congr' ?_ ?_).congr' (cuspFunction_norm_eventuallyEq_mul f).symm EventuallyEq.rfl
  · exact EventuallyEq.rfl
  · filter_upwards with q using by simp

/-- **The norm's cusp function vanishes at the puncture** when the first `N ≥ 1` coefficients
of `f` do: the `0`th coefficient is the value at `∞`, which transfers to the norm. -/
theorem norm_cuspFunction_apply_zero_eq_zero (f : ModularForm (G Γ) k)
    (hh : 0 < (G Γ).strictWidthInfty)
    (hper : (G Γ).strictWidthInfty ∈ (G Γ).strictPeriods)
    (hperSL : (G Γ).strictWidthInfty ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    {N : ℕ} (hNpos : 0 < N)
    (hcoeff : ∀ m < N, (qExpansion (G Γ).strictWidthInfty f).coeff m = 0) :
    cuspFunction (G Γ).strictWidthInfty (_root_.ModularForm.norm 𝒮ℒ f) 0 = 0 := by
  have hval0 : valueAtInfty (f : ℍ → ℂ) = 0 := by
    have h0 := UpperHalfPlane.qExpansion_coeff_zero hh
      (_root_.ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hper)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hper)
    simpa [h0] using hcoeff 0 hNpos
  have hnorm0 := valueAtInfty_norm_eq_zero_of_valueAtInfty_eq_zero f hval0
  have h0 := UpperHalfPlane.cuspFunction_apply_zero hh
    (_root_.ModularFormClass.analyticAt_cuspFunction_zero
      (f := _root_.ModularForm.norm 𝒮ℒ f) hh hperSL)
    (SlashInvariantFormClass.periodic_comp_ofComplex (_root_.ModularForm.norm 𝒮ℒ f) hperSL)
  rw [h0, hnorm0]

/-- **Vanishing of the first `N` `q`-coefficients passes to the level-one norm.** This is the
step that makes the eventual injectivity of "the first `N` coefficients" — and with it the
finite-dimensionality of `M_k(Γ)` at general level — reduce to level one. -/
theorem qExpansion_coeff_eq_zero_norm_of_qExpansion_coeff_eq_zero (f : ModularForm (G Γ) k)
    (hh : 0 < (G Γ).strictWidthInfty)
    (hper : (G Γ).strictWidthInfty ∈ (G Γ).strictPeriods)
    (hperSL : (G Γ).strictWidthInfty ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    {N n : ℕ} (hn : n < N)
    (hcoeff : ∀ m < N, (qExpansion (G Γ).strictWidthInfty f).coeff m = 0) :
    (qExpansion (G Γ).strictWidthInfty (_root_.ModularForm.norm 𝒮ℒ f)).coeff n = 0 :=
  _root_.TauCeti.ModularFormClass.qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow
    (_root_.ModularForm.norm 𝒮ℒ f) hh hperSL hn
    (isBigO_nhds_of_isBigO_punctured
      (isBigO_pow_cuspFunction_norm_punctured f hh hper N hcoeff)
      (norm_cuspFunction_apply_zero_eq_zero f hh hper hperSL (Nat.zero_lt_of_lt hn) hcoeff))

end FiniteIndex

end

end ModularForm.NormReduction
