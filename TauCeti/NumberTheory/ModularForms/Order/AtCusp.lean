/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ENat.BigOperators
public import TauCeti.NumberTheory.ModularForms.QExpansion.Order

/-!
# The vanishing order at the cusp

The vanishing order of a modular form at the cusp is the order of its `q`-expansion, as an
integer with junk value `0` at the identically vanishing expansion — the convention of the
interior dictionary `orderOfVanishingAt`. It is computed by the analytic order of the cusp
function at `0`, vanishes when the constant term is nonzero, and rescales linearly in the
width — the cusp term of the level-one valence formula. The lemmas take the raw analytic,
periodicity, and boundedness hypotheses of the underlying `q`-expansion theorems; for a
modular form all of them are supplied by the `ModularFormClass` machinery.

This is the integral exponent of the width-`h` expansion, the correct primitive at every
cusp: at an irregular cusp of odd weight the conventionally normalized order is the
half-integer obtained by reading this exponent at the doubled width, a `ℚ`-valued
convention layer that belongs with the cusp classification machinery and is deliberately
not defined here.

## Main declarations

* `TauCeti.orderAtCusp`.
* `TauCeti.orderAtCusp_eq_analyticOrderAt`: the analytic-order dictionary.
* `TauCeti.orderAtCusp_nat_mul`: linear rescaling in the width.
* `TauCeti.orderAtCuspQ`: the `ℚ`-valued cusp order — the doubled-width exponent halved,
  the conventional half-integral order at irregular cusps.
* `TauCeti.ModularForm.orderAtCusp_eq_zero_iff`: for a nonzero modular form, order zero
  is a nonzero constant term (the class-level interface lives in `TauCeti.ModularForm`).
* `TauCeti.orderAtCusp_mul`: additivity on products (with `orderAtCusp_pow` and
  `orderAtCusp_prod`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex Filter Function Metric Set SlashInvariantForm Periodic

open scoped ModularForm Topology Filter Manifold

namespace TauCeti

variable {h : ℝ} {g : ℍ → ℂ}

/-- The vanishing order at the cusp: the order of the `q`-expansion at width `h`, as an
integer, with junk value `0` when the expansion vanishes identically — the `untop₀`
convention of `orderOfVanishingAt`. This is the exponent of the width-`h` uniformizer;
normalized orders at other widths (half-integral at irregular cusps) are conversion
layers over this primitive. -/
def orderAtCusp (h : ℝ) (f : ℍ → ℂ) : ℤ := ((qExpansion h f).order.toNat : ℤ)

/-- `orderAtCusp` unfolded to the `q`-expansion order. The definition is sealed by the
module system; this equation is the supported cross-module rewrite. -/
lemma orderAtCusp_def (h : ℝ) (f : ℍ → ℂ) :
    orderAtCusp h f = ((qExpansion h f).order.toNat : ℤ) := by
  unfold orderAtCusp
  rfl

/-- The cusp order is nonnegative. -/
lemma orderAtCusp_nonneg (h : ℝ) (f : ℍ → ℂ) : 0 ≤ orderAtCusp h f := by
  rw [orderAtCusp_def]
  exact Int.natCast_nonneg _

/-- The cusp order is the analytic order of the cusp function at `0`. For a modular form
the analyticity is `ModularFormClass.analyticAt_cuspFunction_zero`. -/
lemma orderAtCusp_eq_analyticOrderAt (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    orderAtCusp h g = ((analyticOrderAt (cuspFunction h g) 0).toNat : ℤ) := by
  rw [orderAtCusp_def, qExpansion_order_eq_analyticOrderAt_cuspFunction hg]

/-- A nonzero constant term at the cusp forces cusp order zero, with no analyticity
hypothesis: the constant coefficient of the `q`-expansion is the value at `0`. -/
lemma orderAtCusp_eq_zero_of_cuspFunction_ne_zero (h0 : cuspFunction h g 0 ≠ 0) :
    orderAtCusp h g = 0 := by
  rw [orderAtCusp_def, Int.natCast_eq_zero, ENat.toNat_eq_zero]
  left
  by_contra hne
  exact h0 (by
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff, qExpansion_coeff, iteratedDeriv_zero]
      using PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp hne)

/-- The cusp order rescales linearly in the width. For a modular form the periodicity,
boundedness, and holomorphy are `SlashInvariantFormClass.periodic_comp_ofComplex`,
`ModularFormClass.bdd_at_infty`, and `ModularFormClass.holo`. -/
lemma orderAtCusp_nat_mul {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg_bdd : IsBoundedAtImInfty g)
    (hg_mdiff : MDiff g) : orderAtCusp (m * h) g = m * orderAtCusp h g := by
  rw [orderAtCusp_def, orderAtCusp_def,
    qExpansion_nat_mul_order hh hm hg_per hg_bdd hg_mdiff, ENat.toNat_mul]
  simp [mul_comm]

private lemma cuspFunction_mul_eventuallyEq (h : ℝ) (f g : ℍ → ℂ) :
    cuspFunction h (f * g) =ᶠ[𝓝[≠] (0 : ℂ)] cuspFunction h f * cuspFunction h g := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [UpperHalfPlane.cuspFunction, Pi.mul_apply, Function.comp_apply,
    Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq]

private lemma cuspFunction_mul_nhds {f g : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    cuspFunction h (f * g) =ᶠ[𝓝 (0 : ℂ)] cuspFunction h f * cuspFunction h g := by
  have h_lim : Filter.Tendsto (cuspFunction h (f * g)) (𝓝[≠] 0)
      (𝓝 (cuspFunction h f 0 * cuspFunction h g 0)) :=
    (((hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))).congr'
      (cuspFunction_mul_eventuallyEq h f g).symm
  have h_at : cuspFunction h (f * g) 0 = cuspFunction h f 0 * cuspFunction h g 0 := by
    rw [UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    exact h_lim.limUnder_eq
  rw [← nhdsNE_sup_pure (0 : ℂ)]
  exact Filter.eventually_sup.mpr
    ⟨cuspFunction_mul_eventuallyEq h f g, Filter.eventually_pure.mpr h_at⟩

/-- The cusp order is additive on products. The finiteness hypotheses exclude an
identically vanishing factor, where the junk value `0` would break additivity. -/
lemma orderAtCusp_mul {f g : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hf' : analyticOrderAt (cuspFunction h f) 0 ≠ ⊤)
    (hg' : analyticOrderAt (cuspFunction h g) 0 ≠ ⊤) :
    orderAtCusp h (f * g) = orderAtCusp h f + orderAtCusp h g := by
  have h_full := cuspFunction_mul_nhds hf hg
  rw [orderAtCusp_eq_analyticOrderAt ((hf.mul hg).congr h_full.symm),
    orderAtCusp_eq_analyticOrderAt hf, orderAtCusp_eq_analyticOrderAt hg,
    analyticOrderAt_congr h_full, analyticOrderAt_mul hf hg, ENat.toNat_add hf' hg']
  push_cast
  ring

private lemma cuspFunction_const (h : ℝ) (c : ℂ) :
    UpperHalfPlane.cuspFunction h (fun _ ↦ c) = fun _ ↦ c := by
  have h_lim : Filter.limUnder (𝓝[≠] (0 : ℂ))
      (((fun _ ↦ c : ℍ → ℂ) ∘ ofComplex) ∘ Function.Periodic.invQParam h) = c :=
    Filter.Tendsto.limUnder_eq tendsto_const_nhds
  rw [UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction, h_lim]
  exact Function.update_eq_self 0 (fun _ ↦ c)

private lemma cuspFunction_one (h : ℝ) : cuspFunction h (1 : ℍ → ℂ) = 1 :=
  cuspFunction_const h 1

/-- Every constant function has cusp order zero: a nonzero constant by the nonvanishing
constant term, the zero function by the junk value. -/
@[simp]
lemma orderAtCusp_const (h : ℝ) (c : ℂ) : orderAtCusp h (fun _ ↦ c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : qExpansion h (fun _ ↦ (0 : ℂ)) = 0 := by
      ext m
      rw [qExpansion_coeff, cuspFunction_const]
      simp
    rw [orderAtCusp_def, h0, PowerSeries.order_zero]
    rfl
  · exact orderAtCusp_eq_zero_of_cuspFunction_ne_zero (by
      rw [cuspFunction_const]
      exact hc)

/-- The constant-one function has cusp order zero. -/
@[simp]
lemma orderAtCusp_one (h : ℝ) : orderAtCusp h (1 : ℍ → ℂ) = 0 :=
  orderAtCusp_const h 1

private lemma cuspFunction_pow_nhds {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    ∀ n : ℕ, cuspFunction h (f ^ n) =ᶠ[𝓝 (0 : ℂ)] cuspFunction h f ^ n
  | 0 => by simp [pow_zero, cuspFunction_one]
  | n + 1 => by
    have h_prev := cuspFunction_pow_nhds hf n
    calc cuspFunction h (f ^ (n + 1))
        =ᶠ[𝓝 (0 : ℂ)] cuspFunction h (f ^ n) * cuspFunction h f := by
          rw [pow_succ]
          exact cuspFunction_mul_nhds ((hf.pow n).congr h_prev.symm) hf
      _ =ᶠ[𝓝 (0 : ℂ)] cuspFunction h f ^ n * cuspFunction h f :=
          h_prev.mul Filter.EventuallyEq.rfl
      _ = cuspFunction h f ^ (n + 1) := (pow_succ _ _).symm

/-- The cusp order multiplies under powers, with no finiteness hypothesis: at the
identically vanishing expansion both sides take the junk value. -/
lemma orderAtCusp_pow {f : ℍ → ℂ} (n : ℕ) (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    orderAtCusp h (f ^ n) = n * orderAtCusp h f := by
  have h_ev := cuspFunction_pow_nhds hf n
  rw [orderAtCusp_eq_analyticOrderAt ((hf.pow n).congr h_ev.symm),
    orderAtCusp_eq_analyticOrderAt hf, analyticOrderAt_congr h_ev, analyticOrderAt_pow hf,
    nsmul_eq_mul, ENat.toNat_mul]
  simp

private lemma cuspFunction_prod_nhds {ι : Type*} {f : ι → ℍ → ℂ} (s : Finset ι)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (f i)) 0) :
    cuspFunction h (∏ i ∈ s, f i) =ᶠ[𝓝 (0 : ℂ)] ∏ i ∈ s, cuspFunction h (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [cuspFunction_one]
  | cons a s ha ih =>
    have h_prev := ih fun i hi ↦ hf i (Finset.mem_cons_of_mem hi)
    calc cuspFunction h (∏ i ∈ Finset.cons a s ha, f i)
        =ᶠ[𝓝 (0 : ℂ)] cuspFunction h (f a) * cuspFunction h (∏ i ∈ s, f i) := by
          rw [Finset.prod_cons]
          exact cuspFunction_mul_nhds (hf a (Finset.mem_cons_self a s))
            ((Finset.analyticAt_prod _ fun i hi ↦
              hf i (Finset.mem_cons_of_mem hi)).congr h_prev.symm)
      _ =ᶠ[𝓝 (0 : ℂ)] cuspFunction h (f a) * ∏ i ∈ s, cuspFunction h (f i) :=
          Filter.EventuallyEq.rfl.mul h_prev
      _ = ∏ i ∈ Finset.cons a s ha, cuspFunction h (f i) := by rw [Finset.prod_cons]

/-- The cusp order is additive on finite products. The finiteness hypotheses exclude an
identically vanishing factor, where the junk value `0` would break additivity. -/
lemma orderAtCusp_prod {ι : Type*} {f : ι → ℍ → ℂ} (s : Finset ι)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (f i)) 0)
    (hf' : ∀ i ∈ s, analyticOrderAt (cuspFunction h (f i)) 0 ≠ ⊤) :
    orderAtCusp h (∏ i ∈ s, f i) = ∑ i ∈ s, orderAtCusp h (f i) := by
  have h_ev := cuspFunction_prod_nhds s hf
  rw [orderAtCusp_eq_analyticOrderAt ((Finset.analyticAt_prod _ hf).congr h_ev.symm),
    analyticOrderAt_congr h_ev, TauCeti.analyticOrderAt_prod hf, ENat.toNat_sum hf',
    Nat.cast_sum]
  exact Finset.sum_congr rfl fun i hi ↦ (orderAtCusp_eq_analyticOrderAt (hf i hi)).symm

/-- The `ℚ`-valued cusp order: the width-`2h` exponent, halved. For an `h`-periodic
function this is the integral order `orderAtCusp h` (`orderAtCuspQ_eq_orderAtCusp`);
at an irregular cusp of odd weight, where the form is only `2h`-periodic, it is the
conventional half-integral order. -/
def orderAtCuspQ (h : ℝ) (f : ℍ → ℂ) : ℚ := (orderAtCusp (2 * h) f : ℚ) / 2

/-- `orderAtCuspQ` unfolded to the halved doubled-width exponent. -/
lemma orderAtCuspQ_def (h : ℝ) (f : ℍ → ℂ) :
    orderAtCuspQ h f = (orderAtCusp (2 * h) f : ℚ) / 2 := by
  unfold orderAtCuspQ
  rfl

/-- For an `h`-periodic bounded holomorphic function the `ℚ`-valued cusp order is the
integral one: the doubled-width exponent doubles. -/
lemma orderAtCuspQ_eq_orderAtCusp (hh : 0 < h) (hg_per : Periodic (g ∘ ofComplex) h)
    (hg_bdd : IsBoundedAtImInfty g) (hg_mdiff : MDiff g) :
    orderAtCuspQ h g = (orderAtCusp h g : ℚ) := by
  have h2 := orderAtCusp_nat_mul (g := g) (m := 2) hh (by norm_num) hg_per hg_bdd hg_mdiff
  rw [orderAtCuspQ_def, show ((2 : ℕ) : ℝ) * h = 2 * h by norm_num] at *
  rw [h2]
  push_cast
  ring

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {f : F}

private lemma cuspFunction_not_eventually_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ¬∀ᶠ q in 𝓝 (0 : ℂ), cuspFunction h f q = 0 := by
  intro h_ev
  have h_diff : DifferentiableOn ℂ (cuspFunction h f) (ball 0 1) :=
    have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
    differentiableOn_cuspFunction_ball hh (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  have h_eqOn : EqOn (cuspFunction h f) 0 (ball 0 1) :=
    (h_diff.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball 0 1).isPreconnected (mem_ball_self one_pos) h_ev
  refine hf (funext fun τ ↦ ?_)
  rw [Pi.zero_apply, ← SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne']
  exact h_eqOn (by
    rw [mem_ball, dist_zero_right]
    exact_mod_cast Function.Periodic.norm_qParam_lt_one hh τ.im_pos)

/-- The cusp function of a nonzero modular form is nonvanishing on a punctured
neighborhood of `0`. -/
lemma cuspFunction_eventually_ne_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), cuspFunction h f q ≠ 0 :=
  (ModularFormClass.analyticAt_cuspFunction_zero f hh
    hΓ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (cuspFunction_not_eventually_zero hh hΓ hf)

/-- The width rescaling for a modular form, with the periodicity, boundedness, and
holomorphy supplied by the class machinery. -/
lemma orderAtCusp_nat_mul_of_mem_strictPeriods [ModularFormClass F Γ k] {m : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hΓ : h ∈ Γ.strictPeriods) :
    orderAtCusp (m * h) ⇑f = m * orderAtCusp h ⇑f :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  orderAtCusp_nat_mul hh hm (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.bdd_at_infty f) (ModularFormClass.holo f)

/-- For a nonzero modular form the cusp function does not vanish identically near `0`,
so its analytic order there is finite. -/
lemma analyticOrderAt_cuspFunction_ne_top [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    analyticOrderAt (cuspFunction h ⇑f) 0 ≠ ⊤ := by
  simp only [ne_eq, analyticOrderAt_eq_top]
  exact cuspFunction_not_eventually_zero hh hΓ hf

/-- For a nonzero modular form the cusp order vanishes iff the constant term — the value
of the cusp function at `0` — is nonzero. -/
@[simp]
lemma orderAtCusp_eq_zero_iff [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    orderAtCusp h ⇑f = 0 ↔ cuspFunction h ⇑f 0 ≠ 0 := by
  have h_an := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  rw [orderAtCusp_eq_analyticOrderAt h_an, Int.natCast_eq_zero, ENat.toNat_eq_zero,
    or_iff_left (analyticOrderAt_cuspFunction_ne_top hh hΓ hf),
    h_an.analyticOrderAt_eq_zero]

/-- For a nonzero modular form the cusp order is positive iff the form vanishes at the
cusp. -/
@[simp]
lemma orderAtCusp_pos_iff [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    0 < orderAtCusp h ⇑f ↔ cuspFunction h ⇑f 0 = 0 := by
  rw [(orderAtCusp_nonneg h ⇑f).lt_iff_ne, ne_comm,
    ← not_not (a := cuspFunction h ⇑f 0 = 0)]
  exact not_congr (orderAtCusp_eq_zero_iff hh hΓ hf)

end ModularForm

end TauCeti

end
