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

`orderAtCusp` is the integral exponent of the width-`h` expansion, the correct primitive
at every cusp; `rationalOrderAtCusp` supplies the width-normalized `ℚ`-valued convention
on top of it — the doubled-width exponent halved, which is the integral order for an
`h`-periodic function and the conventional half-integer at an irregular cusp of odd
weight.

## Main declarations

* `TauCeti.orderAtCusp`.
* `TauCeti.orderAtCusp_eq_analyticOrderAt`: the analytic-order dictionary.
* `TauCeti.orderAtCusp_nat_mul`: linear rescaling in the width.
* `TauCeti.rationalOrderAtCusp`: the `ℚ`-valued cusp order — the doubled-width exponent halved,
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

/-- The cusp order is additive on products. The finiteness hypotheses exclude an
identically vanishing factor, where the junk value `0` would break additivity. -/
lemma orderAtCusp_mul {f g : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hf' : analyticOrderAt (cuspFunction h f) 0 ≠ ⊤)
    (hg' : analyticOrderAt (cuspFunction h g) 0 ≠ ⊤) :
    orderAtCusp h (f * g) = orderAtCusp h f + orderAtCusp h g := by
  have hf'' : (qExpansion h f).order ≠ ⊤ := by
    rwa [qExpansion_order_eq_analyticOrderAt_cuspFunction hf]
  have hg'' : (qExpansion h g).order ≠ ⊤ := by
    rwa [qExpansion_order_eq_analyticOrderAt_cuspFunction hg]
  rw [orderAtCusp_def, orderAtCusp_def, orderAtCusp_def, qExpansion_mul hf hg,
    PowerSeries.order_mul, ENat.toNat_add hf'' hg'']
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
  · have h0 : qExpansion h (fun _ ↦ (0 : ℂ)) = 0 := qExpansion_zero h
    rw [orderAtCusp_def, h0, PowerSeries.order_zero]
    rfl
  · exact orderAtCusp_eq_zero_of_cuspFunction_ne_zero (by
      rw [cuspFunction_const]
      exact hc)

/-- The constant-one function has cusp order zero. -/
@[simp]
lemma orderAtCusp_one (h : ℝ) : orderAtCusp h (1 : ℍ → ℂ) = 0 :=
  orderAtCusp_const h 1

private lemma cuspFunction_pow {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    ∀ n : ℕ, cuspFunction h (f ^ n) = cuspFunction h f ^ n
  | 0 => by rw [pow_zero, pow_zero]; exact cuspFunction_one h
  | n + 1 => by
    rw [pow_succ, pow_succ, ← cuspFunction_pow hf n,
      cuspFunction_mul (by rw [cuspFunction_pow hf n]; exact (hf.continuousAt.pow n))
        hf.continuousAt]

/-- The cusp order multiplies under powers, with no finiteness hypothesis: at the
identically vanishing expansion both sides take the junk value. -/
lemma orderAtCusp_pow {f : ℍ → ℂ} (n : ℕ) (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    orderAtCusp h (f ^ n) = n * orderAtCusp h f := by
  have h_an : AnalyticAt ℂ (cuspFunction h (f ^ n)) 0 := by
    rw [cuspFunction_pow hf n]
    exact hf.pow n
  rw [orderAtCusp_eq_analyticOrderAt h_an, orderAtCusp_eq_analyticOrderAt hf,
    cuspFunction_pow hf n, analyticOrderAt_pow hf, nsmul_eq_mul, ENat.toNat_mul]
  simp

private lemma cuspFunction_prod {ι : Type*} {f : ι → ℍ → ℂ} (s : Finset ι)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (f i)) 0) :
    cuspFunction h (∏ i ∈ s, f i) = ∏ i ∈ s, cuspFunction h (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using cuspFunction_one h
  | cons a s ha ih =>
    have h_prev := ih fun i hi ↦ hf i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.prod_cons, ← h_prev,
      cuspFunction_mul (hf a (Finset.mem_cons_self a s)).continuousAt
        (by rw [h_prev]; exact (Finset.analyticAt_prod _ fun i hi ↦
          hf i (Finset.mem_cons_of_mem hi)).continuousAt)]

/-- The cusp order is additive on finite products. The finiteness hypotheses exclude an
identically vanishing factor, where the junk value `0` would break additivity. -/
lemma orderAtCusp_prod {ι : Type*} {f : ι → ℍ → ℂ} (s : Finset ι)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (f i)) 0)
    (hf' : ∀ i ∈ s, analyticOrderAt (cuspFunction h (f i)) 0 ≠ ⊤) :
    orderAtCusp h (∏ i ∈ s, f i) = ∑ i ∈ s, orderAtCusp h (f i) := by
  have h_an : AnalyticAt ℂ (cuspFunction h (∏ i ∈ s, f i)) 0 := by
    rw [cuspFunction_prod s hf]
    exact Finset.analyticAt_prod _ hf
  rw [orderAtCusp_eq_analyticOrderAt h_an, cuspFunction_prod s hf,
    TauCeti.analyticOrderAt_prod hf, ENat.toNat_sum hf', Nat.cast_sum]
  exact Finset.sum_congr rfl fun i hi ↦ (orderAtCusp_eq_analyticOrderAt (hf i hi)).symm

/-- The `ℚ`-valued cusp order: the width-`2h` exponent, halved. For an `h`-periodic
function this is the integral order `orderAtCusp h` (`rationalOrderAtCusp_eq_orderAtCusp`);
at an irregular cusp of odd weight, where the form is only `2h`-periodic, it is the
conventional half-integral order. -/
def rationalOrderAtCusp (h : ℝ) (f : ℍ → ℂ) : ℚ := (orderAtCusp (2 * h) f : ℚ) / 2

/-- `rationalOrderAtCusp` unfolded to the halved doubled-width exponent. -/
lemma rationalOrderAtCusp_def (h : ℝ) (f : ℍ → ℂ) :
    rationalOrderAtCusp h f = (orderAtCusp (2 * h) f : ℚ) / 2 := by
  unfold rationalOrderAtCusp
  rfl

/-- For an `h`-periodic bounded holomorphic function the `ℚ`-valued cusp order is the
integral one: the doubled-width exponent doubles. -/
lemma rationalOrderAtCusp_eq_orderAtCusp (hh : 0 < h) (hg_per : Periodic (g ∘ ofComplex) h)
    (hg_bdd : IsBoundedAtImInfty g) (hg_mdiff : MDiff g) :
    rationalOrderAtCusp h g = (orderAtCusp h g : ℚ) := by
  have h2 := orderAtCusp_nat_mul (g := g) (m := 2) hh (by norm_num) hg_per hg_bdd hg_mdiff
  norm_num at h2
  rw [rationalOrderAtCusp_def, h2]
  push_cast
  ring

/-- The rational cusp order is nonnegative. -/
lemma rationalOrderAtCusp_nonneg (h : ℝ) (f : ℍ → ℂ) : 0 ≤ rationalOrderAtCusp h f := by
  rw [rationalOrderAtCusp_def]
  exact div_nonneg (by exact_mod_cast orderAtCusp_nonneg (2 * h) f) (by norm_num)

/-- Every constant function has rational cusp order zero. -/
@[simp]
lemma rationalOrderAtCusp_const (h : ℝ) (c : ℂ) : rationalOrderAtCusp h (fun _ ↦ c) = 0 := by
  rw [rationalOrderAtCusp_def, orderAtCusp_const]
  norm_num

/-- The constant-one function has rational cusp order zero. -/
@[simp]
lemma rationalOrderAtCusp_one (h : ℝ) : rationalOrderAtCusp h (1 : ℍ → ℂ) = 0 := by
  rw [rationalOrderAtCusp_def, orderAtCusp_one]
  norm_num

/-- The rational cusp order is additive on products. -/
lemma rationalOrderAtCusp_mul {f g : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction (2 * h) f) 0)
    (hg : AnalyticAt ℂ (cuspFunction (2 * h) g) 0)
    (hf' : analyticOrderAt (cuspFunction (2 * h) f) 0 ≠ ⊤)
    (hg' : analyticOrderAt (cuspFunction (2 * h) g) 0 ≠ ⊤) :
    rationalOrderAtCusp h (f * g) = rationalOrderAtCusp h f + rationalOrderAtCusp h g := by
  simp only [rationalOrderAtCusp_def]
  rw [orderAtCusp_mul hf hg hf' hg']
  push_cast
  ring

/-- The rational cusp order multiplies under powers. -/
lemma rationalOrderAtCusp_pow {f : ℍ → ℂ} (n : ℕ)
    (hf : AnalyticAt ℂ (cuspFunction (2 * h) f) 0) :
    rationalOrderAtCusp h (f ^ n) = n * rationalOrderAtCusp h f := by
  rw [rationalOrderAtCusp_def, rationalOrderAtCusp_def, orderAtCusp_pow n hf]
  push_cast
  ring

/-- The rational cusp order is additive on finite products. -/
lemma rationalOrderAtCusp_prod {ι : Type*} {f : ι → ℍ → ℂ} (s : Finset ι)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction (2 * h) (f i)) 0)
    (hf' : ∀ i ∈ s, analyticOrderAt (cuspFunction (2 * h) (f i)) 0 ≠ ⊤) :
    rationalOrderAtCusp h (∏ i ∈ s, f i) = ∑ i ∈ s, rationalOrderAtCusp h (f i) := by
  rw [rationalOrderAtCusp_def, orderAtCusp_prod s hf hf']
  push_cast
  simp [rationalOrderAtCusp_def, Finset.sum_div]

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
