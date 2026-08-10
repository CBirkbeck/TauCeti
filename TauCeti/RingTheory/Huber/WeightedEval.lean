/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.Bounded
public import TauCeti.RingTheory.Huber.PowerBounded
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
those terms at once, so the terms tend to zero along the cofinite filter. That convergence is the
*necessary* condition, not yet the sufficient one: it is completeness of the target that upgrades
it to summability, through Mathlib's
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`.

## Main definitions

* `TauCeti.Huber.weightedEvalTerm`: the term `φ(coeff ν f) · bν` of the evaluation.
* `TauCeti.Huber.IsWeightBounded`: the weighted monomials `φ(Tν) · bν` form a bounded set. This is
  the hypothesis on `b`. At the one-weight family it is boundedness of the set of monomials `bν`
  (`TauCeti.Huber.isWeightBounded_one_weight_iff`), which implies that each `bᵢ` is power-bounded;
  the converse needs a finite pointwise product of bounded sets to be bounded, so it is not stated
  here.

## Main results

* `TauCeti.Huber.tendsto_weightedEvalTerm_cofinite_zero`: the terms tend to zero along the
  cofinite filter. This is the analytic input, and it needs no completeness.
* `TauCeti.Huber.summable_weightedEvalTerm`: completeness upgrades that convergence to
  summability.

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
`bᵢ` separately, because the bound has to be uniform in `ν`. For the one-weight family `T ≡ {1}`
it says exactly that the set of monomials `bν` is bounded, which is strictly a statement about the
family: it gives that each `bᵢ` is power-bounded, but recovering it from the individual bounds
needs those bounds to combine multiplicatively. -/
def IsWeightBounded (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) : Prop :=
  IsBounded (⋃ ν : Fin k →₀ ℕ, (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν)

omit [TopologicalSpace A] in
/-- Unfolding lemma for `TauCeti.Huber.IsWeightBounded`. The body is not exported, so this is how
a consumer supplies one or takes one apart. -/
theorem isWeightBounded_iff (φ : A →+* B) (T : Fin k → Set A) (b : Fin k → B) :
    IsWeightBounded φ T b ↔
      IsBounded (⋃ ν : Fin k →₀ ℕ, (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow T ν) := (Iff.rfl)

omit [TopologicalSpace A] in
/-- **At the one-weight family the hypothesis is boundedness of the monomials.** With every weight
equal to `{1}` the weighted monomials are just the `bν`, so `IsWeightBounded` says exactly that
they form a bounded set — the condition a reader expects to see, and the bridge from the roadmap's
power-bounded-variable hypothesis. -/
theorem isWeightBounded_one_weight_iff (φ : A →+* B) (b : Fin k → B) :
    IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b ↔
      IsBounded (Set.range fun ν : Fin k →₀ ℕ ↦ ∏ i, b i ^ ν i) := by
  have hset : (⋃ ν : Fin k →₀ ℕ,
      (fun t ↦ φ t * ∏ i, b i ^ ν i) '' weightPow (fun _ : Fin k ↦ ({1} : Set A)) ν)
      = Set.range fun ν : Fin k →₀ ℕ ↦ ∏ i, b i ^ ν i := by
    ext x
    simp [weightPow_one_weight]
  rw [isWeightBounded_iff, hset]

omit [TopologicalSpace A] in
/-- **Each variable is power-bounded.** The monomial at `ν = single i n` is `bᵢ ^ n`, so the
one-weight hypothesis contains every power of every `bᵢ` in one bounded set. The converse — that
individually power-bounded variables satisfy the hypothesis — needs a finite pointwise product of
bounded sets to be bounded, which the repo does not yet have, and is not claimed here. -/
theorem IsWeightBounded.isPowerBounded {φ : A →+* B} {b : Fin k → B}
    (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b) (i : Fin k) :
    IsPowerBounded (b i) := by
  refine isPowerBounded_iff.mpr (((isWeightBounded_one_weight_iff φ b).mp hb).subset ?_)
  rintro _ ⟨n, rfl⟩
  refine ⟨Finsupp.single i n, ?_⟩
  simp [Finsupp.single_apply, Finset.prod_ite_eq]


variable [NonarchimedeanAddGroup A] [NonarchimedeanAddGroup B]

/-- **The terms of the evaluation tend to zero along the cofinite filter.** This is the whole
analytic input to summability — the convergence a summable family must have. It needs no
completeness; completeness is what makes it *sufficient*, in
`TauCeti.Huber.summable_weightedEvalTerm`.

The three hypotheses each do one thing: `T`-restrictedness puts all but finitely many coefficients
into `Tν · U`, continuity of `φ` makes `U` small enough that `φ(U)` shrinks the bounded family,
and `IsWeightBounded` is what makes one `U` work for every `ν` at once. -/
theorem tendsto_weightedEvalTerm_cofinite_zero {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
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
  -- Multiplying by `bν` is additive, so `Tν · U` lands in `G` as soon as its generators do.
  let ψ : A →+ B := (AddMonoidHom.mulRight (∏ i, b i ^ ν i)).comp (φ : A →+ B)
  have hgen : ∀ t ∈ weightPow T ν, ∀ u ∈ U.toAddSubgroup, t * u ∈ G.toAddSubgroup.comap ψ := by
    intro t ht u hu
    -- On a generator the term is `φ u * (φ t * bν)`: a small element times a bounded one.
    have hval : ψ (t * u) = φ u * (φ t * ∏ i, b i ^ ν i) := by
      simp only [ψ, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight,
        AddMonoidHom.coe_coe, map_mul]
      ring
    simp only [AddSubgroup.mem_comap, hval]
    exact hVG (Set.mul_mem_mul (hUV hu) (Set.mem_iUnion.mpr ⟨ν, ⟨t, ht, rfl⟩⟩))
  have hcomap : MvPowerSeries.coeff ν f ∈ G.toAddSubgroup.comap ψ := weightMul_le.mpr hgen hν
  -- `ψ` applied to the coefficient is the term `φ (coeff ν f) * bν`, which is `weightedEvalTerm`
  -- by definition. Stated here rather than left to close the goal by unfolding.
  have hterm : weightedEvalTerm φ b f ν ∈ (G : Set B) := hcomap
  exact hGW hterm


end Terms

section Summable

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanAddGroup B] [CompleteSpace B]

/-- **The evaluation of a `T`-restricted series is summable.** Its terms tend to zero along the
cofinite filter, which in a complete nonarchimedean group is summability. -/
theorem summable_weightedEvalTerm {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {b : Fin k → B} (hb : IsWeightBounded φ T b) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) :
    Summable (weightedEvalTerm φ b f) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_weightedEvalTerm_cofinite_zero hφ hb hf)

end Summable

end TauCeti.Huber

end
