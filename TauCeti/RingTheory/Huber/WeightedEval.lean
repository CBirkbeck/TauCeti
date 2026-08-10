/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.Bounded
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Evaluating a weighted restricted power series

Wedhorn's universal property of `A⟨X₁, …, Xₖ⟩_T` (Proposition 5.50) sends a `T`-restricted series
to the sum of its terms at a chosen tuple `b`. Before there is a map to speak of, that sum has to
exist, and this file supplies exactly that: the family of terms is summable.

Summability is where the defining condition earns its keep. `T`-restrictedness says that for each
open subgroup `U` of `A`, all but finitely many coefficients lie in `Tν · U`; so all but finitely
many terms lie in `(φ(Tν) · bν) · φ(U)`. If the weighted monomials `φ(Tν) · bν` stay inside one
bounded set — `TauCeti.Huber.IsWeightBounded` below, which is Wedhorn's hypothesis that the
variables are power-bounded *relative to the weights* — then shrinking `U` shrinks every one of
those terms at once, so the terms tend to zero along the cofinite filter. In a complete
nonarchimedean group that is already summability.

## Main definitions

* `TauCeti.Huber.weightedEvalTerm`: the term `φ(coeff ν f) · bν` of the evaluation.
* `TauCeti.Huber.IsWeightBounded`: the weighted monomials `φ(Tν) · bν` form a bounded set. This is
  the hypothesis on `b`; taking `T` the one-weight family recovers "each `bᵢ` is power-bounded".

## Main results

* `TauCeti.Huber.tendsto_cofinite_weightedEvalTerm`: the terms tend to zero along `cofinite`. This
  is the content, and it needs no completeness.
* `TauCeti.Huber.summable_weightedEvalTerm`: hence they are summable, once `B` is complete.

The evaluation map itself, its continuity, and the uniqueness that makes Proposition 5.50 a
universal property are not proved here.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50, whose analytic core this is.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

section Terms

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]

/-- The `ν`-th term of the evaluation of `f` at `b` along `φ`, namely `φ(coeff ν f) · bν`. -/
def weightedEvalTerm (φ : A →+* B) (b : Fin k → B) (f : MvPowerSeries (Fin k) A)
    (ν : Fin k →₀ ℕ) : B :=
  φ (MvPowerSeries.coeff ν f) * ∏ i, b i ^ ν i

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- Unfolding lemma for `TauCeti.Huber.weightedEvalTerm`. -/
theorem weightedEvalTerm_def (φ : A →+* B) (b : Fin k → B) (f : MvPowerSeries (Fin k) A)
    (ν : Fin k →₀ ℕ) :
    weightedEvalTerm φ b f ν = φ (MvPowerSeries.coeff ν f) * ∏ i, b i ^ ν i := (rfl)

/-- **The hypothesis on the tuple `b`**: the weighted monomials `φ(Tν) · bν`, over all
multi-indices at once, form a bounded subset of `B`.

This is Wedhorn's requirement that the variables be power-bounded *relative to the weights*, in
the form the summability argument uses. It is a condition on the whole family rather than on each
`bᵢ` separately, because the bound has to be uniform in `ν`; for the one-weight family `T ≡ {1}`
it says exactly that the set of monomials `bν` is bounded, i.e. that each `bᵢ` is power-bounded
and the bounds combine. -/
def IsWeightBounded (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) : Prop :=
  IsBounded (⋃ ν : Fin k →₀ ℕ, (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν)

omit [TopologicalSpace A] in
/-- Unfolding lemma for `TauCeti.Huber.IsWeightBounded`. The body is not exported, so this is how
a consumer supplies one or takes one apart. -/
theorem isWeightBounded_iff (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) :
    IsWeightBounded φ T b ↔
      IsBounded (⋃ ν : Fin k →₀ ℕ, (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν) := (Iff.rfl)

variable [NonarchimedeanRing A] [NonarchimedeanRing B]

/-- **The terms of the evaluation tend to zero along the cofinite filter.** This is the whole
content of summability, and it needs no completeness.

The three hypotheses each do one thing: `T`-restrictedness puts all but finitely many coefficients
into `Tν · U`, continuity of `φ` makes `U` small enough that `φ(U)` shrinks the bounded family,
and `IsWeightBounded` is what makes one `U` work for every `ν` at once. -/
theorem tendsto_cofinite_weightedEvalTerm {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {b : Fin k → B} (hb : IsWeightBounded φ T b) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) :
    Filter.Tendsto (weightedEvalTerm φ b f) Filter.cofinite (𝓝 0) := by
  refine Filter.tendsto_def.mpr fun W hW ↦ ?_
  obtain ⟨G, hGW⟩ := NonarchimedeanAddGroup.is_nonarchimedean W hW
  -- Shrink `G` by the bounded family of weighted monomials, then pull the result back along `φ`.
  obtain ⟨V, hV, hVG⟩ := isBounded_iff.mp ((isWeightBounded_iff φ T b).mp hb) (G : Set B)
    (G.isOpen.mem_nhds G.zero_mem)
  obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ (hφ.continuousAt.preimage_mem_nhds
    (by simpa only [map_zero] using hV))
  -- All but finitely many coefficients lie in `Tν · U`, and every such term lands in `G`.
  filter_upwards [isWeightedRestricted_iff.mp hf U] with ν hν
  refine hGW ?_
  -- Multiplying by `bν` is additive, so `Tν · U` lands in `G` as soon as its generators do.
  let ψ : A →+ B := (AddMonoidHom.mulRight (∏ i, b i ^ ν i)).comp (φ : A →+ B)
  refine weightMul_le (V := G.toAddSubgroup.comap ψ) |>.mpr (fun t ht u hu ↦ ?_) hν
  -- On a generator the term is `φ u * (φ t * bν)`: a small element times a bounded one.
  have hgen : ψ (t * u) = φ u * (φ t * ∏ i, b i ^ ν i) := by
    simp only [ψ, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight,
      AddMonoidHom.coe_coe, map_mul]
    ring
  simp only [AddSubgroup.mem_comap, hgen]
  exact hVG (Set.mul_mem_mul (hUV hu) (Set.mem_iUnion.mpr ⟨ν, ⟨t, ht, rfl⟩⟩))

end Terms

section Summable

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]

/-- **The evaluation of a `T`-restricted series is summable.** Its terms tend to zero along the
cofinite filter, which in a complete nonarchimedean group is summability. -/
theorem summable_weightedEvalTerm {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {b : Fin k → B} (hb : IsWeightBounded φ T b) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) :
    Summable (weightedEvalTerm φ b f) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_cofinite_weightedEvalTerm hφ hb hf)

end Summable

end TauCeti.Huber

end
