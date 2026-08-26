/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Evaluating a real étale algebra at its real and complex places

For a real polynomial `f`, the quotient `ℝ[X]/f` maps to a product of copies of `ℝ`, one for each
real root of `f`, and copies of `ℂ`, one for each irreducible quadratic factor — the archimedean
places of the algebra. This file builds that evaluation map and shows it is injective when `f` is
nonzero and squarefree, which is the point: an element of `ℝ[X]/f` is determined by its values at
the real roots together with its values at the upper-half-plane roots of the quadratic factors.

Over `ℝ` an irreducible polynomial has degree `1` or `2` (`Irreducible.natDegree_le_two`), so those
two families exhaust the factors, and a degree-2 factor `p` has two conjugate non-real roots. One
is singled out by its sign: `Polynomial.upperRoot` is the root in the open upper half-plane, and
evaluation there identifies `ℝ[X]/p` with `ℂ` (`Polynomial.evalUpperEquiv`).

## Main definitions

* `Polynomial.upperRoot` : the root of an irreducible real quadratic with positive imaginary part.
* `Polynomial.evalUpperHom`, `Polynomial.evalUpperEquiv` : evaluation at that root, as an
  `ℝ`-algebra hom `ℝ[X]/p → ℂ` and, for a quadratic `p`, an isomorphism.
* `Polynomial.etaleEvalHom` : the evaluation map
  `ℝ[X]/f → ({x // f.eval x = 0} → ℝ) × ({p ∈ normalizedFactors f // deg p = 2} → ℂ)`.

## Main results

* `Polynomial.upperRoot_im_pos` : the chosen root really does lie in the upper half-plane.
* `Polynomial.etaleEvalHom_injective` : for `f ≠ 0` squarefree, the evaluation map is injective.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` (`github.com/MichaelStollBayreuth/EllipticCurves`,
Apache-2.0) at commit `66889eada51ac1eb2a1c98b3c1ba5b0bbe64a8d0`, file
`EllipticCurves/Mathlib/RealEtale.lean`, the section preceding the square-class decomposition.

Two things are spelled differently here, in both cases because Mathlib already has what the
source provides for itself.

* The source indexes the quadratic factors by its own `Polynomial.Factors` wrapper — a subtype of
  monic irreducible divisors, introduced there to avoid the `DecidableEq` that `normalizedFactors`
  carries. Over `ℝ` that motivation does not apply, since `Real.decidableEq` is an instance, so the
  factors are indexed by membership in `normalizedFactors` directly and the wrapper is not needed.
  `Polynomial.mem_normalizedFactors_iff` is Mathlib's, and supplies monic, irreducible and divides
  in one step.
* The source proves `Module.finrank ℝ (AdjoinRoot p) = p.natDegree` for itself. That is Mathlib's
  `finrank_quotient_span_eq_natDegree`, which is stronger — it needs no `p ≠ 0` — so it is used
  instead. It has to be ascribed at the `AdjoinRoot` spelling before rewriting, since `rw` does not
  see through the definitional unfolding to `ℝ[X] ⧸ Ideal.span {p}`.
-/

public section

open Complex UniqueFactorizationMonoid

namespace Polynomial

variable {p : ℝ[X]} (hp : Irreducible p) (hd : p.natDegree = 2)

/-- A complex root of an irreducible real quadratic in the open upper half-plane: of the two
conjugate roots, the one with positive imaginary part. -/
noncomputable def upperRoot : ℂ :=
  let z := (IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hp).ne').choose
  if 0 < z.im then z else starRingEnd ℂ z

include hp in
/-- The chosen root is a root: conjugation preserves vanishing of a real polynomial. -/
theorem aeval_upperRoot : aeval (upperRoot hp) p = 0 := by
  have hz := (IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hp).ne').choose_spec
  rw [upperRoot]
  split_ifs with h
  · exact hz
  · rw [aeval_conj, hz, map_zero]

include hp hd in
/-- An irreducible real quadratic has no real root, so each of its complex roots is non-real. -/
theorem im_ne_zero_of_aeval_eq_zero {z : ℂ} (hz : aeval z p = 0) : z.im ≠ 0 := by
  intro him
  have hz' : z = algebraMap ℝ ℂ z.re := Complex.ext (by simp) (by simp [him])
  rw [hz', aeval_algebraMap_apply, map_eq_zero] at hz
  exact hp.not_isRoot_of_natDegree_ne_one (by omega) hz

include hp hd in
/-- The chosen root lies in the open upper half-plane. -/
theorem upperRoot_im_pos : 0 < (upperRoot hp).im := by
  have hz := (IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hp).ne').choose_spec
  have hne := im_ne_zero_of_aeval_eq_zero hp hd hz
  rw [upperRoot]
  split_ifs with h
  · exact h
  · rw [Complex.conj_im]
    exact neg_pos.mpr ((not_lt.mp h).lt_of_ne hne)

/-- Evaluation at the upper-half-plane root, as an `ℝ`-algebra hom `ℝ[X]/p → ℂ`. -/
noncomputable def evalUpperHom : AdjoinRoot p →ₐ[ℝ] ℂ :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId ℝ ℂ) (upperRoot hp)
    (by have := aeval_upperRoot hp; simpa [aeval_def] using this)

include hp in
theorem evalUpperHom_injective : Function.Injective (evalUpperHom hp) :=
  have : Fact (Irreducible p) := ⟨hp⟩
  (evalUpperHom hp).toRingHom.injective

/-- **`ℝ[X]/p ≃ ℂ` for an irreducible real quadratic `p`.** The evaluation hom is injective, and
a dimension count over `ℝ` makes it surjective. -/
noncomputable def evalUpperEquiv : AdjoinRoot p ≃ₐ[ℝ] ℂ :=
  have : Fact (Irreducible p) := ⟨hp⟩
  AlgEquiv.ofBijective (evalUpperHom hp) ⟨evalUpperHom_injective hp, by
    have hsurj : Function.Surjective ⇑(evalUpperHom hp).toLinearMap := by
      -- `AdjoinRoot p` is by definition `ℝ[X] ⧸ span {p}`, but `rw` does not see through that,
      -- so Mathlib's dimension count is ascribed at the `AdjoinRoot` spelling first.
      have hfr : Module.finrank ℝ (AdjoinRoot p) = p.natDegree :=
        finrank_quotient_span_eq_natDegree
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj (evalUpperHom_injective hp), hfr, hd,
        Complex.finrank_real_complex]
    exact hsurj⟩

/-! ### The evaluation map at all archimedean places -/

variable {f : ℝ[X]}

/-- The tuple of evaluation points: each real root of `f`, and the upper root of each
degree-2 factor. -/
noncomputable def etaleTuple (f : ℝ[X]) :
    ({x : ℝ // f.eval x = 0} → ℝ) ×
      ({p : ℝ[X] // p ∈ normalizedFactors f ∧ p.natDegree = 2} → ℂ) :=
  (fun x ↦ (x : ℝ), fun p ↦ upperRoot (irreducible_of_normalized_factor _ p.2.1))

/-- The real-root component of `aeval (etaleTuple f) q` is `q.eval x`. -/
theorem aeval_etaleTuple_fst (q : ℝ[X]) (x : {x : ℝ // f.eval x = 0}) :
    (aeval (etaleTuple f) q).1 x = q.eval (x : ℝ) := by
  have h := aeval_algHom_apply
    ((Pi.evalAlgHom ℝ (fun _ : {x : ℝ // f.eval x = 0} ↦ ℝ) x).comp (AlgHom.fst ℝ _ _))
    (etaleTuple f) q
  simp only [AlgHom.comp_apply, AlgHom.fst_apply, Pi.evalAlgHom_apply] at h
  rw [← h]
  -- `(etaleTuple f).1 x` is by definition the real number `x`, so this is ordinary evaluation.
  change aeval ((etaleTuple f).1 x) q = q.eval (x : ℝ)
  simp [etaleTuple, aeval_def, eval₂_id]

/-- The degree-2-factor component of `aeval (etaleTuple f) q` is the value at the upper root. -/
theorem aeval_etaleTuple_snd (q : ℝ[X])
    (p : {p : ℝ[X] // p ∈ normalizedFactors f ∧ p.natDegree = 2}) :
    (aeval (etaleTuple f) q).2 p
      = aeval (upperRoot (irreducible_of_normalized_factor _ p.2.1)) q := by
  have h := aeval_algHom_apply
    ((Pi.evalAlgHom ℝ
      (fun _ : {p : ℝ[X] // p ∈ normalizedFactors f ∧ p.natDegree = 2} ↦ ℂ) p).comp
      (AlgHom.snd ℝ _ _)) (etaleTuple f) q
  simp only [AlgHom.comp_apply, AlgHom.snd_apply, Pi.evalAlgHom_apply] at h
  rw [← h]
  rfl

/-- `f` itself vanishes at every evaluation point. -/
theorem aeval_etaleTuple : aeval (etaleTuple f) f = 0 := by
  have h1 : (aeval (etaleTuple f) f).1 = 0 := by
    funext x; rw [Pi.zero_apply, aeval_etaleTuple_fst]; exact x.2
  have h2 : (aeval (etaleTuple f) f).2 = 0 := by
    funext p
    rw [Pi.zero_apply, aeval_etaleTuple_snd]
    have hirr := irreducible_of_normalized_factor _ p.2.1
    have hd : aeval (upperRoot hirr) (p : ℝ[X]) ∣ aeval (upperRoot hirr) f :=
      _root_.map_dvd _ (dvd_of_mem_normalizedFactors p.2.1)
    rw [aeval_upperRoot] at hd
    exact zero_dvd_iff.mp hd
  exact Prod.ext h1 h2

/-- **Evaluation at the archimedean places of `ℝ[X]/f`**, as an `ℝ`-algebra hom into the product
of the residue fields: `ℝ` at each real root, `ℂ` at each irreducible quadratic factor. -/
noncomputable def etaleEvalHom (f : ℝ[X]) :
    AdjoinRoot f →ₐ[ℝ]
      ({x : ℝ // f.eval x = 0} → ℝ) ×
        ({p : ℝ[X] // p ∈ normalizedFactors f ∧ p.natDegree = 2} → ℂ) :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId ℝ _) (etaleTuple f) (by
    have := aeval_etaleTuple (f := f); rwa [aeval_def] at this)

/-- Definitional: `AdjoinRoot.liftAlgHom_mk` and `Algebra.toRingHom_ofId` are both `rfl`, so
evaluating a representative is evaluating the polynomial. Parenthesised so that it elaborates
against the sealed body across the module boundary. -/
theorem etaleEvalHom_mk (q : ℝ[X]) :
    etaleEvalHom f (AdjoinRoot.mk f q) = aeval (etaleTuple f) q := (rfl)

@[simp]
theorem etaleEvalHom_mk_fst (q : ℝ[X]) (x : {x : ℝ // f.eval x = 0}) :
    (etaleEvalHom f (AdjoinRoot.mk f q)).1 x = q.eval (x : ℝ) := by
  rw [etaleEvalHom_mk, aeval_etaleTuple_fst]

@[simp]
theorem etaleEvalHom_mk_snd (q : ℝ[X])
    (p : {p : ℝ[X] // p ∈ normalizedFactors f ∧ p.natDegree = 2}) :
    (etaleEvalHom f (AdjoinRoot.mk f q)).2 p
      = aeval (upperRoot (irreducible_of_normalized_factor _ p.2.1)) q := by
  rw [etaleEvalHom_mk, aeval_etaleTuple_snd]

/-- **The evaluation map is injective for `f` nonzero and squarefree.** A class killed at every
place is divisible by every irreducible factor of `f`; the factors are pairwise coprime, so their
product — which is `f` up to a unit — divides it. -/
theorem etaleEvalHom_injective (hf : f ≠ 0) (hsq : Squarefree f) :
    Function.Injective (etaleEvalHom f) := by
  classical
  have : Finite {p : ℝ[X] // p ∈ normalizedFactors f} :=
    (normalizedFactors f).finite_toSet.to_subtype
  have : Fintype {p : ℝ[X] // p ∈ normalizedFactors f} := Fintype.ofFinite _
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [AdjoinRoot.mk_eq_zero]
  -- Every irreducible factor divides `q`: a linear one because `q` vanishes at its root, a
  -- quadratic one because `q` vanishes at its upper root, which has it as minimal polynomial.
  have hfac (p : {p : ℝ[X] // p ∈ normalizedFactors f}) : (p : ℝ[X]) ∣ q := by
    obtain ⟨hirr, hmon, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hf).mp p.2
    rcases eq_or_ne (p : ℝ[X]).natDegree 1 with h1 | h1
    · set x₀ := -(p : ℝ[X]).coeff 0 with hx0
      have hpx : (p : ℝ[X]) = X - C x₀ := by
        conv_lhs => rw [hmon.eq_X_add_C h1]
        rw [hx0, map_neg, sub_neg_eq_add]
      have hroot : f.eval x₀ = 0 :=
        eval_eq_zero_of_dvd_of_eval_eq_zero hdvd (by rw [hpx]; simp)
      have hq : q.eval x₀ = 0 := by
        have h := congrArg (·.1 ⟨x₀, hroot⟩) ha
        simpa using h
      rw [hpx]
      exact dvd_iff_isRoot.mpr hq
    · have hd2 : (p : ℝ[X]).natDegree = 2 := by
        have h0 := hirr.natDegree_pos
        have h2 := hirr.natDegree_le_two
        omega
      have hq : aeval (upperRoot hirr) q = 0 := by
        have h := congrArg (·.2 ⟨(p : ℝ[X]), p.2, hd2⟩) ha
        simpa using h
      rw [minpoly.eq_of_irreducible_of_monic hirr (aeval_upperRoot hirr) hmon]
      exact minpoly.dvd ℝ _ hq
  -- The distinct factors are pairwise coprime, so their product divides `q`; and that product is
  -- `f` up to a unit, because squarefreeness makes `normalizedFactors f` duplicate-free.
  have hcop : ∀ p₁ p₂ : {p : ℝ[X] // p ∈ normalizedFactors f}, p₁ ≠ p₂ →
      IsCoprime (p₁ : ℝ[X]) (p₂ : ℝ[X]) := by
    intro p₁ p₂ hne
    obtain ⟨h₁, hm₁, -⟩ := (Polynomial.mem_normalizedFactors_iff hf).mp p₁.2
    obtain ⟨h₂, hm₂, -⟩ := (Polynomial.mem_normalizedFactors_iff hf).mp p₂.2
    refine (Ideal.isCoprime_span_singleton_iff _ _).mp <| Ideal.isCoprime_iff_sup_eq.mpr <|
      Ideal.IsMaximal.coprime_of_ne (PrincipalIdealRing.isMaximal_of_irreducible h₁)
        (PrincipalIdealRing.isMaximal_of_irreducible h₂) fun h ↦ hne <| Subtype.ext <|
      eq_of_monic_of_associated hm₁ hm₂ <| Ideal.span_singleton_eq_span_singleton.mp h
  have hprod : Associated (∏ p : {p : ℝ[X] // p ∈ normalizedFactors f}, (p : ℝ[X])) f := by
    have hcoe : ∏ p : {p : ℝ[X] // p ∈ normalizedFactors f}, (p : ℝ[X]) =
        ∏ p ∈ (normalizedFactors f).toFinset, p := by
      refine (Fintype.prod_equiv (Equiv.subtypeEquivRight fun p ↦ ?_) _ _ fun x ↦ ?_).trans
        (Finset.prod_coe_sort _ fun x ↦ x)
      · exact (Multiset.mem_toFinset).symm
      · rw [Equiv.subtypeEquivRight_apply]
    rw [hcoe, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hf).mp hsq),
      Multiset.map_id']
    exact prod_normalizedFactors hf
  exact hprod.symm.dvd.trans (Fintype.prod_dvd_of_coprime (fun _ _ hab ↦ hcop _ _ hab) hfac)

end Polynomial
