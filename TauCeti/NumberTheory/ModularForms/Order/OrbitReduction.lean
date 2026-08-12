/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.NumberTheory.Modular
public import TauCeti.NumberTheory.ModularForms.Order.AtCusp
public import TauCeti.NumberTheory.ModularForms.Order.Orbits

import TauCeti.Analysis.Complex.UpperHalfPlane.Rho
import TauCeti.NumberTheory.Modular.Orbits
import TauCeti.NumberTheory.ModularForms.FiniteZeros

/-!
# Reduction of the valence formula to the non-elliptic orbit space

The valence formula is proved as an identity over an arbitrary complete divisor set: for every
finite `S ⊆ 𝒟` catching all nonzero-order points, three sums — over the strict interior, the
left vertical edge, and the left half-arc minus `ρ` — together with the weighted elliptic and
cusp terms equal `k/12`. This file reduces that hypothesis-shaped identity (`h_core`) to the
headline form, a `∑ᶠ` over the non-elliptic orbit space.

The reduction picks one representative per non-elliptic orbit of nonzero order inside the
canonical set `canonicalReps`: interior points represent themselves; a right-vertical-edge point
is moved to the left edge by `z ↦ z - 1`; a right-half-arc point is moved to the left half-arc
by `z ↦ -1/z`. Faithfulness is the injectivity of the orbit map on the left part of `𝒟`
(`TauCeti.ModularGroup.orbit_mk_injOn_fd_left`), and the elliptic orbits are excluded by their
closed-domain descriptions (`orbit_mk_eq_I_iff`, `orbit_mk_eq_ρ_iff`).

## Main declarations

* `TauCeti.ModularForm.fdZeros`: the canonical complete divisor set — the nonzero-order points
  of the closed fundamental domain of a nonzero level-one form.
* `TauCeti.ModularForm.canonicalReps`: one representative per non-elliptic orbit of nonzero
  order — the strict-interior, left-vertical and left-half-arc points of `fdZeros`.
* `TauCeti.ModularForm.exists_mem_canonicalReps_orbit_mk_eq`: every non-elliptic orbit of
  nonzero order has a representative in `canonicalReps`.
* `TauCeti.ModularForm.finsum_orderOfVanishingOnOrbit_eq_sum_canonicalReps`: the `∑ᶠ` over the
  non-elliptic orbit space equals the `canonicalReps` sum.
* `TauCeti.ModularForm.sum_canonicalReps_split`: the `canonicalReps` sum splits into the three
  family sums of the core identity.
* `TauCeti.ModularForm.finsum_orderOfVanishingOnOrbit_add_elliptic_add_qExpansionOrderAtCusp_eq`:
  **the valence formula in orbit-space form**, conditional on the core identity `h_core`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/Orbits.lean`, `ForMathlib/CanonicalReps.lean` and
  `ForMathlib/ValenceFormula.lean`), ported onto the current Mathlib pin. The denominator
  analysis behind AINTLIB's representative selection is replaced here by Mathlib's
  classification `ModularGroup.cases_of_mem_fd_smul_mem_fd`, through the orbit lemmas of
  `TauCeti.NumberTheory.Modular.Orbits`.
-/

public noncomputable section

open UpperHalfPlane

open scoped ModularForm MatrixGroups Modular

namespace TauCeti

namespace ModularForm

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- The canonical complete divisor set of a nonzero level-one form: the finitely many points
of the closed fundamental domain `𝒟` carrying nonzero vanishing order, as a `Finset`. -/
def fdZeros [ModularFormClass F 𝒮ℒ k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) : Finset ℍ :=
  (finite_zeros_in_fd hf).toFinset

/-- Membership in the canonical divisor set: a point of `𝒟` of nonzero order. -/
@[simp]
lemma mem_fdZeros [ModularFormClass F 𝒮ℒ k] {f : F} {hf : (⇑f : ℍ → ℂ) ≠ 0} {p : ℍ} :
    p ∈ fdZeros hf ↔ p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0 :=
  (finite_zeros_in_fd hf).mem_toFinset

/-- One representative per non-elliptic orbit of nonzero order: the points of `fdZeros` in the
strict interior, on the left vertical edge, or on the left half-arc minus `ρ`. The right
vertical edge and right half-arc are omitted — `z ↦ z - 1` and `z ↦ -1/z` move them onto the
left representatives — and the elliptic points are excluded by all three filters. -/
def canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) : Finset ℍ :=
  (fdZeros hf).filter fun p : ℍ ↦
    ((p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧ 1 < ‖(p : ℂ)‖ ∧
        |(p : ℂ).re| < 1 / 2) ∨
      ((p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∨
      ((p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)

private lemma coe_re_ρ : (ρ : ℂ).re = -(1 / 2) := by
  norm_num [UpperHalfPlane.ρ]

private lemma coe_vadd_one_ρ : (((1 : ℝ) +ᵥ ρ : ℍ) : ℂ) = (ρ : ℂ) + 1 := by
  rw [coe_vadd, Complex.ofReal_one, add_comm]

private lemma norm_eq_one_of_mem_corners {z : ℂ}
    (hz : z ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)) : ‖z‖ = 1 := by
  rcases Finset.mem_insert.mp hz with rfl | hz'
  · exact Complex.norm_I
  rcases Finset.mem_insert.mp hz' with rfl | hz''
  · exact norm_ρ
  · rw [Finset.mem_singleton.mp hz'']
    exact norm_ρ_add_one

private lemma ne_elliptic_of_mem_canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F}
    {hf : (⇑f : ℍ → ℂ) ≠ 0} {p : ℍ} (hp : p ∈ canonicalReps hf) :
    p ≠ I ∧ p ≠ ρ ∧ p ≠ (1 : ℝ) +ᵥ ρ := by
  have hcond := (Finset.mem_filter.mp hp).2
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩ <;> subst h <;>
    rcases hcond with ⟨hno, hgt, -⟩ | ⟨hre, hgt⟩ | ⟨hne, hnorm, hre⟩
  · exact hno (by rw [coe_I]; exact Finset.mem_insert_self _ _)
  · rw [coe_I, Complex.I_re] at hre; norm_num at hre
  · rw [coe_I, Complex.I_re] at hre; norm_num at hre
  · exact hno (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  · rw [norm_ρ] at hgt; norm_num at hgt
  · exact hne rfl
  · rw [coe_vadd_one_ρ] at hno
    exact hno (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  · rw [coe_vadd_one_ρ, Complex.add_re, coe_re_ρ, Complex.one_re] at hre; norm_num at hre
  · rw [coe_vadd_one_ρ, Complex.add_re, coe_re_ρ, Complex.one_re] at hre; norm_num at hre

/-- The canonical representatives lie in the non-elliptic orbits. -/
theorem orbit_mk_ne_of_mem_canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F}
    {hf : (⇑f : ℍ → ℂ) ≠ 0} {p : ℍ} (hp : p ∈ canonicalReps hf) :
    (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' I ∧
      (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' ρ := by
  obtain ⟨hne_I, hne_ρ, hne_vadd⟩ := ne_elliptic_of_mem_canonicalReps hp
  have hfd : p ∈ 𝒟 := (mem_fdZeros.mp (Finset.mem_filter.mp hp).1).1
  exact ⟨fun h ↦ hne_I ((ModularGroup.orbit_mk_eq_I_iff hfd).mp h),
    fun h ↦ ((ModularGroup.orbit_mk_eq_ρ_iff hfd).mp h).elim hne_ρ hne_vadd⟩

/-- The orbit map is injective on the canonical representatives, which lie left of the
boundary identifications of `𝒟`. -/
theorem orbit_mk_injOn_canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    Set.InjOn (fun p : ℍ ↦ (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ))
      ↑(canonicalReps hf) := by
  refine ModularGroup.orbit_mk_injOn_fd_left.mono fun p hp ↦ ?_
  obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hp
  refine ⟨(mem_fdZeros.mp hmem).1, ?_, ?_⟩
  · rcases hcond with ⟨-, -, habs⟩ | ⟨hre, -⟩ | ⟨-, -, hre⟩
    · exact lt_of_abs_lt (coe_re p ▸ habs)
    · rw [← coe_re, hre]; norm_num
    · exact (coe_re p ▸ hre).trans (by norm_num)
  · intro hnorm
    rcases hcond with ⟨-, hgt, -⟩ | ⟨-, hgt⟩ | ⟨-, -, hre⟩
    · rw [hnorm] at hgt; norm_num at hgt
    · rw [hnorm] at hgt; norm_num at hgt
    · exact coe_re p ▸ hre

private lemma one_le_norm_of_mem_fd {p : ℍ} (hp : p ∈ 𝒟) : 1 ≤ ‖(p : ℂ)‖ := by
  have h := hp.1
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (p : ℂ)]

private lemma coe_S_smul (p : ℍ) : ((ModularGroup.S • p : ℍ) : ℂ) = (-(p : ℂ))⁻¹ := by
  rw [modular_S_smul, coe_mk]

private lemma norm_coe_S_smul {p : ℍ} (hp : ‖(p : ℂ)‖ = 1) :
    ‖((ModularGroup.S • p : ℍ) : ℂ)‖ = 1 := by
  rw [coe_S_smul, norm_inv, norm_neg, hp, inv_one]

private lemma re_coe_S_smul {p : ℍ} (hp : ‖(p : ℂ)‖ = 1) :
    ((ModularGroup.S • p : ℍ) : ℂ).re = -(p : ℂ).re := by
  rw [coe_S_smul, Complex.inv_re, Complex.neg_re, Complex.normSq_neg,
    Complex.normSq_eq_norm_sq, hp, one_pow, div_one]

private lemma S_smul_mem_fd {p : ℍ} (hp : p ∈ 𝒟) (hnorm : ‖(p : ℂ)‖ = 1) :
    ModularGroup.S • p ∈ 𝒟 := by
  refine ⟨?_, ?_⟩
  · rw [Complex.normSq_eq_norm_sq, norm_coe_S_smul hnorm]
    norm_num
  · have h := re_coe_S_smul hnorm
    rw [coe_re, coe_re] at h
    rw [h, abs_neg]
    exact hp.2

private lemma eq_I_of_norm_eq_one_of_re_eq_zero {p : ℍ} (hnorm : ‖(p : ℂ)‖ = 1)
    (hre : (p : ℂ).re = 0) : p = I := by
  have him_pos : (0 : ℝ) < (p : ℂ).im := p.im_pos
  have h1 : (p : ℂ).re * (p : ℂ).re + (p : ℂ).im * (p : ℂ).im = 1 := by
    have h := Complex.normSq_eq_norm_sq (p : ℂ)
    rw [hnorm, one_pow] at h
    simpa [Complex.normSq_apply] using h
  rw [hre, zero_mul, zero_add] at h1
  have hprod : ((p : ℂ).im - 1) * ((p : ℂ).im + 1) = 0 := by nlinarith
  have him : (p : ℂ).im = 1 := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  exact UpperHalfPlane.ext (Complex.ext (by rw [hre, coe_I, Complex.I_re])
    (by rw [him, coe_I, Complex.I_im]))

private lemma normSq_coe_vadd_neg_one {p : ℍ} (hre : (p : ℂ).re = 1 / 2) :
    Complex.normSq (((-1 : ℝ) +ᵥ p : ℍ) : ℂ) = Complex.normSq (p : ℂ) := by
  rw [coe_vadd, Complex.normSq_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, hre, zero_add]
  norm_num

private lemma norm_coe_vadd_neg_one {p : ℍ} (hre : (p : ℂ).re = 1 / 2) :
    ‖(((-1 : ℝ) +ᵥ p : ℍ) : ℂ)‖ = ‖(p : ℂ)‖ := by
  rw [Complex.norm_def, Complex.norm_def, normSq_coe_vadd_neg_one hre]

private lemma vadd_neg_one_mem_fd {p : ℍ} (hp : p ∈ 𝒟) (hre : (p : ℂ).re = 1 / 2) :
    (-1 : ℝ) +ᵥ p ∈ 𝒟 := by
  refine ⟨?_, ?_⟩
  · rw [normSq_coe_vadd_neg_one hre]
    exact hp.1
  · have hre' : p.re = 1 / 2 := coe_re p ▸ hre
    rw [vadd_re, hre']
    norm_num

private lemma exists_of_re_eq_half [ModularFormClass F 𝒮ℒ k] {f : F}
    {hf : (⇑f : ℍ → ℂ) ≠ 0} {p₀ : ℍ} (hfd : p₀ ∈ 𝒟) (hord : orderOfVanishingAt f p₀ ≠ 0)
    (hre : (p₀ : ℂ).re = 1 / 2) (hlt : 1 < ‖(p₀ : ℂ)‖) :
    ∃ p ∈ canonicalReps hf,
      (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' p₀ := by
  have horb : (Quotient.mk'' ((-1 : ℝ) +ᵥ p₀) : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) =
      Quotient.mk'' p₀ := by
    simpa using ModularGroup.orbit_mk_int_vadd (-1) p₀
  have hord' : orderOfVanishingAt f ((-1 : ℝ) +ᵥ p₀) ≠ 0 := by
    rw [← orderOfVanishingOnOrbit_mk (k := k) f, horb, orderOfVanishingOnOrbit_mk]
    exact hord
  refine ⟨(-1 : ℝ) +ᵥ p₀, Finset.mem_filter.mpr ⟨mem_fdZeros.mpr
    ⟨vadd_neg_one_mem_fd hfd hre, hord'⟩, Or.inr (Or.inl ⟨?_, ?_⟩)⟩, horb⟩
  · rw [coe_vadd, Complex.add_re, Complex.ofReal_re, hre]
    norm_num
  · rw [norm_coe_vadd_neg_one hre]
    exact hlt

private lemma exists_of_norm_eq_one_of_re_pos [ModularFormClass F 𝒮ℒ k] {f : F}
    {hf : (⇑f : ℍ → ℂ) ≠ 0} {p₀ : ℍ} (hfd : p₀ ∈ 𝒟) (hord : orderOfVanishingAt f p₀ ≠ 0)
    (hnorm : ‖(p₀ : ℂ)‖ = 1) (hpos : 0 < (p₀ : ℂ).re)
    (hqρ : (Quotient.mk'' p₀ : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' ρ) :
    ∃ p ∈ canonicalReps hf,
      (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' p₀ := by
  have horb : (Quotient.mk'' (ModularGroup.S • p₀) : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) =
      Quotient.mk'' p₀ := Quotient.sound' ⟨ModularGroup.S, rfl⟩
  have hord' : orderOfVanishingAt f (ModularGroup.S • p₀) ≠ 0 := by
    rw [← orderOfVanishingOnOrbit_mk (k := k) f, horb, orderOfVanishingOnOrbit_mk]
    exact hord
  have hne : ((ModularGroup.S • p₀ : ℍ) : ℂ) ≠ (ρ : ℂ) := fun h ↦
    hqρ (horb ▸ congrArg Quotient.mk'' (UpperHalfPlane.coe_injective h))
  refine ⟨ModularGroup.S • p₀, Finset.mem_filter.mpr ⟨mem_fdZeros.mpr
    ⟨S_smul_mem_fd hfd hnorm, hord'⟩, Or.inr (Or.inr ⟨hne, norm_coe_S_smul hnorm, ?_⟩)⟩, horb⟩
  rw [re_coe_S_smul hnorm]
  linarith

/-- Every non-elliptic orbit of nonzero order has a representative among the canonical ones:
a fundamental-domain representative exists, and the boundary identifications move it into
`canonicalReps` when it falls on the omitted right vertical edge or right half-arc. -/
theorem exists_mem_canonicalReps_orbit_mk_eq [ModularFormClass F 𝒮ℒ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) {q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ}
    (hqI : q ≠ Quotient.mk'' I) (hqρ : q ≠ Quotient.mk'' ρ)
    (hq : orderOfVanishingOnOrbit f q ≠ 0) :
    ∃ p ∈ canonicalReps hf, Quotient.mk'' p = q := by
  obtain ⟨p₀, rfl, hfd⟩ := ModularGroup.exists_rep_mem_fd q
  rw [orderOfVanishingOnOrbit_mk] at hq
  rcases (one_le_norm_of_mem_fd hfd).lt_or_eq with hlt | heq
  · rcases lt_or_eq_of_le hfd.2 with hre_lt | hre_eq
    · refine ⟨p₀, Finset.mem_filter.mpr ⟨mem_fdZeros.mpr ⟨hfd, hq⟩,
        Or.inl ⟨fun hc ↦ hlt.ne' (norm_eq_one_of_mem_corners hc), hlt, ?_⟩⟩, rfl⟩
      rwa [coe_re]
    · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hre_eq with h | h
      · exact exists_of_re_eq_half hfd hq ((coe_re p₀).trans h) hlt
      · exact ⟨p₀, Finset.mem_filter.mpr ⟨mem_fdZeros.mpr ⟨hfd, hq⟩,
          Or.inr (Or.inl ⟨(coe_re p₀).trans h, hlt⟩)⟩, rfl⟩
  · rcases lt_trichotomy ((p₀ : ℂ).re) 0 with hneg | hzero | hpos
    · have hne : (p₀ : ℂ) ≠ (ρ : ℂ) := fun h ↦
        hqρ (congrArg Quotient.mk'' (UpperHalfPlane.coe_injective h))
      exact ⟨p₀, Finset.mem_filter.mpr ⟨mem_fdZeros.mpr ⟨hfd, hq⟩,
        Or.inr (Or.inr ⟨hne, heq.symm, hneg⟩)⟩, rfl⟩
    · exact absurd (congrArg Quotient.mk''
        (eq_I_of_norm_eq_one_of_re_eq_zero heq.symm hzero)) hqI
    · exact exists_of_norm_eq_one_of_re_pos hfd hq heq.symm hpos hqρ

/-- The `∑ᶠ` over the non-elliptic orbit space equals the sum over the canonical
representatives: the orbit map matches `canonicalReps` bijectively with the non-elliptic
orbits of nonzero order, and the order is orbit-constant. -/
theorem finsum_orderOfVanishingOnOrbit_eq_sum_canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ∑ᶠ q : NonEllipticOrbit, orderOfVanishingOnOrbit f q.val =
      ∑ p ∈ canonicalReps hf, orderOfVanishingAt f p := by
  rw [finsum_eq_sum _ (hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic hf)]
  refine (Finset.sum_bij
    (fun p hp ↦ (⟨Quotient.mk'' p, orbit_mk_ne_of_mem_canonicalReps hp⟩ : NonEllipticOrbit))
    ?_ ?_ ?_ ?_).symm
  · intro p hp
    refine (hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic hf).mem_toFinset.mpr ?_
    simpa using (mem_fdZeros.mp (Finset.mem_filter.mp hp).1).2
  · intro p₁ h₁ p₂ h₂ h
    exact orbit_mk_injOn_canonicalReps hf h₁ h₂ (congrArg Subtype.val h)
  · intro q hq
    obtain ⟨p, hp, hporb⟩ := exists_mem_canonicalReps_orbit_mk_eq hf q.2.1 q.2.2
      ((hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic hf).mem_toFinset.mp hq)
    exact ⟨p, hp, Subtype.ext hporb⟩
  · intro p hp
    exact (orderOfVanishingOnOrbit_mk f p).symm

/-- The canonical-representative sum splits into the three family sums of the core identity:
strict interior, left vertical edge, and left half-arc minus `ρ`. -/
theorem sum_canonicalReps_split [ModularFormClass F 𝒮ℒ k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ∑ p ∈ canonicalReps hf, orderOfVanishingAt f p =
      ∑ p ∈ (fdZeros hf).filter (fun p : ℍ ↦
          (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧ 1 < ‖(p : ℂ)‖ ∧
            |(p : ℂ).re| < 1 / 2),
          orderOfVanishingAt f p +
        ∑ p ∈ (fdZeros hf).filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          orderOfVanishingAt f p +
        ∑ p ∈ (fdZeros hf).filter (fun p : ℍ ↦
          (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          orderOfVanishingAt f p := by
  classical
  have hd₂ : Disjoint
      ((fdZeros hf).filter fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖)
      ((fdZeros hf).filter fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) := by
    refine Finset.disjoint_left.mpr fun p hp hq ↦ ?_
    have h1 := (Finset.mem_filter.mp hp).2.2
    rw [(Finset.mem_filter.mp hq).2.2.1] at h1
    exact lt_irrefl 1 h1
  have hd₁ : Disjoint
      ((fdZeros hf).filter fun p : ℍ ↦
        (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧ 1 < ‖(p : ℂ)‖ ∧
          |(p : ℂ).re| < 1 / 2)
      (((fdZeros hf).filter fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∪
        (fdZeros hf).filter fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) := by
    refine Finset.disjoint_left.mpr fun p hp hq ↦ ?_
    obtain ⟨-, hgt, habs⟩ := (Finset.mem_filter.mp hp).2
    rcases Finset.mem_union.mp hq with hq | hq
    · rw [(Finset.mem_filter.mp hq).2.1] at habs
      norm_num at habs
    · rw [(Finset.mem_filter.mp hq).2.2.1] at hgt
      norm_num at hgt
  unfold canonicalReps
  rw [Finset.filter_or, Finset.filter_or, Finset.sum_union hd₁, Finset.sum_union hd₂,
    ← add_assoc]

/-- **The valence formula in orbit-space form**, conditional on the core identity.

The hypothesis `h_core` is the valence formula over an arbitrary complete divisor set
`S ⊆ 𝒟`, its interior and boundary contributions grouped into the three families produced by
the contour argument: the strict interior, the left vertical edge, and the left half-arc
minus `ρ`. It is proved separately, by contour integration of the logarithmic derivative
along the boundary of the fundamental domain.

The conclusion re-indexes the three families by the non-elliptic orbits they represent:

`∑ᶠ_{q non-elliptic} ord_q f + (1/2)·ord_i f + (1/3)·ord_ρ f + ord_∞ f = k/12`. -/
theorem finsum_orderOfVanishingOnOrbit_add_elliptic_add_qExpansionOrderAtCusp_eq
    [ModularFormClass F 𝒮ℒ k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (h_core : ∀ S : Finset ℍ, (∀ p ∈ S, p ∈ 𝒟) →
      (∀ p, p ∈ 𝒟 → orderOfVanishingAt f p ≠ 0 → p ∈ S) →
      ((∑ p ∈ S.filter (fun p : ℍ ↦
          (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧ 1 < ‖(p : ℂ)‖ ∧
            |(p : ℂ).re| < 1 / 2),
          orderOfVanishingAt f p : ℤ) : ℂ) +
        ((∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          orderOfVanishingAt f p : ℤ) : ℂ) +
        ((∑ p ∈ S.filter (fun p : ℍ ↦
          (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          orderOfVanishingAt f p : ℤ) : ℂ) +
        1 / 2 * (orderOfVanishingAt f I : ℂ) + 1 / 3 * (orderOfVanishingAt f ρ : ℂ) +
        qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 12) :
    ((∑ᶠ q : NonEllipticOrbit, orderOfVanishingOnOrbit f q.val : ℤ) : ℂ) +
      1 / 2 * (orderOfVanishingAt f I : ℂ) + 1 / 3 * (orderOfVanishingAt f ρ : ℂ) +
      qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 12 := by
  have h := h_core (fdZeros hf) (fun p hp ↦ (mem_fdZeros.mp hp).1)
    fun p hp hord ↦ mem_fdZeros.mpr ⟨hp, hord⟩
  rw [finsum_orderOfVanishingOnOrbit_eq_sum_canonicalReps hf, sum_canonicalReps_split hf]
  push_cast
  push_cast at h
  linear_combination h

end ModularForm

end TauCeti

end
