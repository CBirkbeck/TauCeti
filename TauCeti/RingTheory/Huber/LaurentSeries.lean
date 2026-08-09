/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.Huber.Basic

/-!
# The formal Laurent series field is a Tate ring

For a field `K` the formal Laurent series `K⸨X⸩`, with the `X`-adic topology of Mathlib's
`LaurentSeries.valued` instance, are a Tate ring: the power series are an open subring, the
ideal `(X)` is a finitely generated ideal of definition, and `X` itself is a pseudouniformiser.

Together with `TauCeti.Huber.PadicInt.not_isTateRing` and `TauCeti.Huber.Padic.isTateRing` this
is the equal-characteristic half of the roadmap's Layer-0 examples separating Huber from Tate.

## Main definitions

* `TauCeti.Huber.LaurentSeries.idealOfDefinition`: the ideal `(X)` of `K⟦X⟧ ⊆ K⸨X⸩`.
* `TauCeti.Huber.LaurentSeries.pairOfDefinition`: the pair of definition `(K⟦X⟧, (X))`.

## Main results

* `TauCeti.Huber.LaurentSeries.mem_idealOfDefinition_pow_iff`: membership of `(X)ⁿ` is the
  valuation bound `v f ≤ exp (-n)`. Every topological statement here is read off this.
* `TauCeti.Huber.LaurentSeries.isPseudoUniformizer_X`: `X` is a pseudouniformiser.
* `TauCeti.Huber.LaurentSeries.isHuberRing` and `TauCeti.Huber.LaurentSeries.isTateRing`.

## Implementation notes

The ring of definition is not built by hand: `LaurentSeries.val_le_one_iff_eq_coe` says that a
Laurent series has valuation at most one exactly when it is a power series, so Mathlib's
`LaurentSeries.powerSeries_as_subring` *is* the valuation subring and is open by
`Valued.isOpen_integer`.

The neighbourhood API of a `Valued` ring is phrased in the value group `ValueGroup₀ v` rather
than in `Γ₀`, so the two `private` lemmas below convert once, in each direction, between that
form and the `ℤᵐ⁰` bounds the rest of the file uses.

## Provenance

New work; the roadmap names no source for this row. The file's shape follows
`TauCeti/RingTheory/Huber/Padic.lean`, the `ℤ_[p]` example, so that the two Layer-0 examples
present the same interface.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §6, where Huber and Tate rings are introduced
  (Proposition and Definition 6.1) and `F⸨t⸩` is the standard equal-characteristic example of a
  Tate ring.
-/

public section

open Filter Topology WithZero PowerSeries
open scoped LaurentSeries

namespace TauCeti.Huber

namespace LaurentSeries

open _root_.LaurentSeries (powerSeries_as_subring powerSeriesEquivSubring val_le_one_iff_eq_coe
  valuation_X_pow)

variable (K : Type*) [Field K]

/-- The power series inside `K⸨X⸩` are exactly the elements of valuation at most one. -/
theorem coe_powerSeries_as_subring :
    ((powerSeries_as_subring K : Subring K⸨X⸩) : Set K⸨X⸩) = (Valued.v (R := K⸨X⸩)).integer := by
  ext f
  simp only [Valuation.mem_integer_iff, SetLike.mem_coe]
  rw [val_le_one_iff_eq_coe]
  exact ⟨by rintro ⟨g, -, rfl⟩; exact ⟨g, rfl⟩, by rintro ⟨g, rfl⟩; exact ⟨g, trivial, rfl⟩⟩

/-- The ring of definition is open, being the valuation subring. -/
theorem isOpen_powerSeries_as_subring :
    IsOpen ((powerSeries_as_subring K : Subring K⸨X⸩) : Set K⸨X⸩) :=
  (coe_powerSeries_as_subring K) ▸ Valued.isOpen_integer K⸨X⸩

/-- The variable `X`, viewed inside the ring of definition `K⟦X⟧ ⊆ K⸨X⸩`. -/
noncomputable def subringX : powerSeries_as_subring K := powerSeriesEquivSubring K PowerSeries.X

@[simp]
theorem coe_subringX : (subringX K : K⸨X⸩) = ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := (rfl)

/-- The ideal of definition `(X)` of `K⟦X⟧ ⊆ K⸨X⸩`. -/
noncomputable def idealOfDefinition : Ideal (powerSeries_as_subring K) := Ideal.span {subringX K}

/-- Unfolding lemma for `TauCeti.Huber.LaurentSeries.idealOfDefinition`. -/
theorem idealOfDefinition_def : idealOfDefinition K = Ideal.span {subringX K} := (rfl)

/-- `X` is nonzero in `K⸨X⸩`, so, `K⸨X⸩` being a field, all its powers are invertible. -/
theorem coe_X_ne_zero : ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ≠ 0 := by
  simp only [HahnSeries.ofPowerSeries_X, ne_eq, HahnSeries.single_eq_zero_iff, one_ne_zero,
    not_false_eq_true]

variable {K}

/-- **The bridge to the valuation**: a power series lies in `(X)ⁿ` exactly when its valuation is
at most `exp (-n)`. -/
theorem mem_idealOfDefinition_pow_iff (n : ℕ) (f : powerSeries_as_subring K) :
    f ∈ idealOfDefinition K ^ n ↔ Valued.v (f : K⸨X⸩) ≤ exp (-(n : ℤ)) := by
  rw [idealOfDefinition_def, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨g, rfl⟩
    have hg : Valued.v (g : K⸨X⸩) ≤ 1 := by
      have hmem := g.2
      rwa [← SetLike.mem_coe, coe_powerSeries_as_subring, SetLike.mem_coe,
        Valuation.mem_integer_iff] at hmem
    have hcoe : ((g * subringX K ^ n : powerSeries_as_subring K) : K⸨X⸩)
        = (g : K⸨X⸩) * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n := by
      push_cast [coe_subringX]
      rfl
    rw [hcoe, map_mul, valuation_X_pow]
    calc Valued.v (g : K⸨X⸩) * exp (-(n : ℤ)) ≤ 1 * exp (-(n : ℤ)) := by gcongr
      _ = exp (-(n : ℤ)) := one_mul _
  · intro hf
    have hu : Valued.v ((f : K⸨X⸩) * (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n)⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀, valuation_X_pow, ← le_div_iff₀ (by simp), div_eq_mul_inv, one_mul,
        inv_inv]
      exact hf
    obtain ⟨F, hF⟩ := (val_le_one_iff_eq_coe K _).mp hu
    refine ⟨powerSeriesEquivSubring K F, Subtype.ext ?_⟩
    have hcoe : ((powerSeriesEquivSubring K F * subringX K ^ n : powerSeries_as_subring K) : K⸨X⸩)
        = (F : K⸨X⸩) * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n := by
      push_cast [coe_subringX]
      rfl
    rw [hcoe, hF, inv_mul_cancel_right₀ (pow_ne_zero n (coe_X_ne_zero K))]

variable (K)

/-- The valuation ball cut out by `v (Xⁿ)` is a neighbourhood of zero. The bound is phrased with
`v (Xⁿ)` rather than `exp (-n)` so that it is visibly in the value group. -/
private theorem ball_mem_nhds (n : ℕ) :
    {x : K⸨X⸩ | Valued.v x < Valued.v (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n)} ∈ 𝓝 (0 : K⸨X⸩) := by
  refine Valued.mem_nhds_zero.mpr
    ⟨Units.mk0 (Valued.v.restrict (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n)) (by simp), ?_⟩
  exact fun _ hx ↦ Valued.v.restrict_lt_iff.mp hx

/-- Conversely every neighbourhood of zero contains a valuation ball with a bound in `ℤᵐ⁰`. -/
private theorem exists_ball_subset {s : Set K⸨X⸩} (hs : s ∈ 𝓝 (0 : K⸨X⸩)) :
    ∃ c : ℤᵐ⁰, c ≠ 0 ∧ {x : K⸨X⸩ | Valued.v x < c} ⊆ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  exact ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1, by simp,
    fun x hx ↦ hγ (Valued.v.restrict_lt_iff_lt_embedding.mpr hx)⟩

/-- The subspace topology on `K⟦X⟧ ⊆ K⸨X⸩` is the `X`-adic topology. -/
theorem isAdic_idealOfDefinition : IsAdic (idealOfDefinition K) := by
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · have hmem : (((idealOfDefinition K ^ n).toAddSubgroup :
        AddSubgroup (powerSeries_as_subring K)) : Set (powerSeries_as_subring K))
        ∈ 𝓝 (0 : powerSeries_as_subring K) := by
      rw [IsInducing.subtypeVal.nhds_eq_comap, ZeroMemClass.coe_zero, Filter.mem_comap]
      refine ⟨_, ball_mem_nhds K n, fun f hf ↦ (mem_idealOfDefinition_pow_iff n f).mpr ?_⟩
      have hf' : Valued.v (f : K⸨X⸩)
          < Valued.v (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n) := hf
      rw [valuation_X_pow] at hf'
      exact hf'.le
    exact AddSubgroup.isOpen_of_mem_nhds _ hmem
  · rw [IsInducing.subtypeVal.nhds_eq_comap, ZeroMemClass.coe_zero, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨c, hc, hct⟩ := exists_ball_subset K ht
    refine ⟨(1 - log c).toNat, fun f hf ↦ hts (hct ?_)⟩
    refine lt_of_le_of_lt ((mem_idealOfDefinition_pow_iff _ f).mp hf) ?_
    rw [← lt_log_iff_exp_lt hc]
    omega

/-- **The pair of definition** `(K⟦X⟧, (X))` of `K⸨X⸩`. -/
noncomputable def pairOfDefinition : PairOfDefinition K⸨X⸩ where
  ringOfDefinition := powerSeries_as_subring K
  isOpen_ringOfDefinition := isOpen_powerSeries_as_subring K
  idealOfDefinition := idealOfDefinition K
  fg_idealOfDefinition := ⟨{subringX K}, by simp [idealOfDefinition_def]⟩
  isAdic_idealOfDefinition := isAdic_idealOfDefinition K

/-- The ring of definition of `TauCeti.Huber.LaurentSeries.pairOfDefinition` is the power series.

There is deliberately no companion lemma for the ideal: `PairOfDefinition.idealOfDefinition` is
dependent on `ringOfDefinition`, so with the body hidden by the module system an equation between
the two ideals does not typecheck. The bridge
`TauCeti.Huber.LaurentSeries.mem_idealOfDefinition_pow_iff` is what consumers use instead. -/
@[simp]
theorem pairOfDefinition_ringOfDefinition :
    (pairOfDefinition K).ringOfDefinition = powerSeries_as_subring K := (rfl)

/-- **`X` is a pseudouniformiser of `K⸨X⸩`**: it is a unit, since `K⸨X⸩` is a field, and
`v (Xⁿ) = exp (-n)` tends to zero. -/
theorem isPseudoUniformizer_X : IsPseudoUniformizer ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := by
  refine isPseudoUniformizer_iff.mpr ⟨isUnit_iff_ne_zero.mpr (coe_X_ne_zero K), ?_⟩
  refine Filter.tendsto_def.mpr fun s hs ↦ ?_
  obtain ⟨c, hc, hcs⟩ := exists_ball_subset K hs
  filter_upwards [eventually_ge_atTop (1 - log c).toNat] with n hn
  refine hcs (show Valued.v (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ n) < c from ?_)
  rw [valuation_X_pow, ← lt_log_iff_exp_lt hc]
  omega

instance isHuberRing : IsHuberRing K⸨X⸩ := ⟨⟨pairOfDefinition K⟩⟩

instance isTateRing : IsTateRing K⸨X⸩ where
  exists_isPseudoUniformizer := ⟨_, isPseudoUniformizer_X K⟩

end LaurentSeries

end TauCeti.Huber
