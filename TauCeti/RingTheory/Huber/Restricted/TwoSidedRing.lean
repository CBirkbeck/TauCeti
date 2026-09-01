/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries

/-!
# The ring of two-sided restricted series `A⟨X, X⁻¹⟩`

`TauCeti.Huber.twoSidedRestrictedSubmodule` is only the `A`-*module* of coefficient families
underlying Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39). This module supplies the multiplication, which
that file deliberately left out, and makes the coefficient object a ring — a commutative
`A`-algebra when `A` is commutative, as the source states.

## Why this is not the one-sided argument

For the one-sided `A⟨X₁, …, Xₖ⟩` the coefficient convolution `(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ` is a
**finite** sum, because `MvPowerSeries.coeff_mul` runs over the antidiagonal of `Fin k →₀ ℕ`, which
is a `Finset`; that is what `TauCeti.Huber.IsRestricted.mul` rearranges. Over `ℤ` the antidiagonal
`{(i, j) | i + j = n}` is **infinite**, so the coefficient is a genuine infinite sum and there is
no rearrangement to perform. Concretely `ℤ` carries no `Finset.HasAntidiagonal` instance and can
carry none, so the `Finset`-indexed Cauchy-product lemmas do not apply here at all.

## The facts that replace it

* *Restrictedness is summability.* In a **complete** nonarchimedean group, a family is summable
  exactly when it tends to `0` along the cofinite filter
  (`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`), which is precisely the
  restrictedness condition: `mem_twoSidedRestrictedSubmodule_iff_summable`.
* *Existence.* Hence `Summable.mul_of_nonarchimedean` makes `(i, j) ↦ aᵢbⱼ` summable on `ℤ × ℤ`,
  and each antidiagonal, being a subfamily, is summable too — this is the source's "convergent
  series `∑_{k + l = n} aₖ bₗ`".
* *Closure.* That the product is again restricted needs neither completeness nor summability. It is
  `NonarchimedeanAddGroup.zeroAtFilter_cofinite_tsum_fiber` applied to addition `ℤ × ℤ → ℤ`: an
  open subgroup omits only finitely many `aᵢbⱼ`, hence meets only finitely many antidiagonals, and
  an antidiagonal all of whose terms lie in an open — hence closed — subgroup sums back into it.
* *Associativity.* Both `((fg)h)ₙ` and `(f(gh))ₙ` are the sum of `aᵢ bⱼ cₗ` over
  `{i + j + l = n}`, an infinite family summable by two applications of
  `Summable.mul_of_nonarchimedean`; summing it fibrewise in the degree of the partial product
  (`HasSum.prod_fiberwise`) gives the two bracketings, and uniqueness of limits identifies them.
  Nothing of the sort is in Mathlib's `DiscreteConvolution`, which has the unit, distributivity
  and commutativity but no associativity.

## Main definitions

* `TauCeti.Huber.twoSidedRestrictedSubmodule.instMul`: the product on `A⟨X, X⁻¹⟩`, Mathlib's
  `DiscreteConvolution.addConvolution` along the bilinear map `LinearMap.mul ℤ A`.
* `TauCeti.Huber.twoSidedRestrictedSubmodule.instRing`, `instCommRing`, `instAlgebra`: **the ring
  structure**, and the `A`-algebra structure of Example 6.39 when `A` is commutative.

## Main results

* `TauCeti.Huber.addConvolution_mul_apply`: the coefficient formula `(fg)ₙ = ∑' k, aₖ b_{n-k}`.
* `TauCeti.Huber.addConvolution_mem_twoSidedRestrictedSubmodule`: **the closure result** — a
  convolution of restricted families is restricted.
* `TauCeti.Huber.mem_twoSidedRestrictedSubmodule_iff_summable`: over a complete group,
  restrictedness is summability.
* `TauCeti.Huber.summable_mul_sub_of_mem_twoSidedRestrictedSubmodule` and
  `TauCeti.Huber.addConvolutionExists_of_mem_twoSidedRestrictedSubmodule`: over a complete ring the
  coefficient series of a product converge.

## Implementation notes

The product is *not* the pointwise product of `ℤ → A`, so `A⟨X, X⁻¹⟩` is not a subring of `ℤ → A`
and there is no ambient convolution ring to take a subring of — unlike the one-sided case, where
`MvPowerSeries` already supplies one and `TauCeti.Huber.restrictedMvPowerSeriesSubring` is a genuine
`Subring`. The multiplication is therefore installed directly on the submodule's coercion to a type,
where nothing else claims a `Mul`.

We reuse Mathlib's `DiscreteConvolution.addConvolution` rather than defining a `ℤ`-indexed
convolution: it is the same sum over the same fibre, `addFiber n = {(i, j) | i + j = n}`.

The multiplication and the closure result need only a nonarchimedean ring topology. The ring
axioms need the coefficient ring to be complete **and** Hausdorff (`[CompleteSpace A] [T0Space A]`):
completeness so that the coefficient series converge at all, and Hausdorffness so that `tsum` is a
limit rather than a choice among limits — without it neither distributivity nor associativity is
provable. This is exactly Wedhorn's convention, whose "complete" means "Hausdorff and every Cauchy
filter basis converges" (Definition 5.31(4)–(5)), and it is the hypothesis list the consumer
`TauCeti.RingTheory.Huber.Restricted.Laurent` already carries.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39.
-/

public section

open Filter Topology DiscreteConvolution

namespace TauCeti.Huber

section Convolution

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The antidiagonal `{(i, j) | i + j = n}` in `ℤ × ℤ`, parametrised by its first coordinate.

This is where the `ℤ`-indexed picture and Mathlib's fibre picture meet, and it is an `Equiv` rather
than a `Finset` precisely because the antidiagonal is infinite. -/
private def addFiberEquivInt (n : ℤ) : ℤ ≃ (addFiber n : Set (ℤ × ℤ)) where
  toFun k := ⟨(k, n - k), by simp [mem_addFiber]⟩
  invFun ab := ab.1.1
  left_inv _ := rfl
  right_inv ab := Subtype.ext (Prod.ext rfl (by have := mem_addFiber.mp ab.2; dsimp only; omega))

omit [NonarchimedeanRing A] in
/-- **The coefficient formula for the two-sided product**: `(fg)ₙ = ∑' k, aₖ b_{n-k}`, the familiar
Laurent convolution. Reindexing Mathlib's sum over `addFiber n` by the first coordinate is exactly
`addFiberEquivInt`. -/
theorem addConvolution_mul_apply (f g : ℤ → A) (n : ℤ) :
    addConvolution (LinearMap.mul ℤ A) f g n = ∑' k : ℤ, f k * g (n - k) :=
  ((addFiberEquivInt n).tsum_eq fun ab ↦ f ab.1.1 * g ab.1.2).symm

/-- **The product of two restricted families is restricted**, so `A⟨X, X⁻¹⟩` is closed under the
convolution. This is what makes it a ring rather than merely a module, and it needs neither
completeness nor summability:
`NonarchimedeanAddGroup.zeroAtFilter_cofinite_tsum_fiber` sums along the fibres of addition
`ℤ × ℤ → ℤ`, and `tendsto_mul_cofinite_nhds_zero` supplies its hypothesis on `(i, j) ↦ aᵢbⱼ`. Where
a coefficient sum fails to converge it is `0` by the `tsum` convention, and `0` lies in every
subgroup, so the degenerate case costs nothing and no completeness hypothesis is needed to state
closure. -/
theorem addConvolution_mem_twoSidedRestrictedSubmodule {f g : ℤ → A}
    (hf : f ∈ twoSidedRestrictedSubmodule A A) (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    addConvolution (LinearMap.mul ℤ A) f g ∈ twoSidedRestrictedSubmodule A A := by
  rw [mem_twoSidedRestrictedSubmodule] at hf hg ⊢
  have key : addConvolution (LinearMap.mul ℤ A) f g
      = fun n ↦ ∑' i : {i : ℤ × ℤ // i.1 + i.2 = n}, f i.1.1 * g i.1.2 :=
    funext fun _ ↦ tsum_congr_set_coe (fun ab : ℤ × ℤ ↦ f ab.1 * g ab.2)
      (Set.ext fun (_ : ℤ × ℤ) ↦ mem_addFiber)
  rw [key]
  exact NonarchimedeanAddGroup.zeroAtFilter_cofinite_tsum_fiber
    (F := fun ab : ℤ × ℤ ↦ f ab.1 * g ab.2) (tendsto_mul_cofinite_nhds_zero hf hg)
    (fun ab ↦ ab.1 + ab.2)

/-- **The product on `A⟨X, X⁻¹⟩`**: the coefficient convolution `(fg)ₙ = ∑' k, aₖ b_{n-k}`, which
lands back in the submodule by `addConvolution_mem_twoSidedRestrictedSubmodule`. Only a
nonarchimedean ring topology is needed to *define* it; the ring axioms are
`twoSidedRestrictedSubmodule.instRing`. -/
noncomputable instance twoSidedRestrictedSubmodule.instMul :
    Mul (twoSidedRestrictedSubmodule A A) where
  mul f g := ⟨addConvolution (LinearMap.mul ℤ A) f g,
    addConvolution_mem_twoSidedRestrictedSubmodule f.2 g.2⟩

/-- **The unit of `A⟨X, X⁻¹⟩`** is the constant series `1 = 1 · X⁰`, i.e. the family supported at
degree `0`. -/
instance twoSidedRestrictedSubmodule.instOne : One (twoSidedRestrictedSubmodule A A) where
  one := ⟨Pi.single 0 1, single_mem_twoSidedRestrictedSubmodule 0 1⟩

/-- The product is the convolution of the coefficient families. Its body is not exposed, so this
is how it is computed outside this module. -/
@[simp]
theorem coe_mul_twoSidedRestrictedSubmodule (f g : twoSidedRestrictedSubmodule A A) :
    ((f * g : twoSidedRestrictedSubmodule A A) : ℤ → A) =
      addConvolution (LinearMap.mul ℤ A) f g := (rfl)

/-- The unit is the family supported at degree `0` with value `1`. -/
@[simp]
theorem coe_one_twoSidedRestrictedSubmodule :
    ((1 : twoSidedRestrictedSubmodule A A) : ℤ → A) = Pi.single 0 1 := (rfl)

end Convolution

section Summable

variable {A M : Type*} [Semiring A] [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [Module A M] [ContinuousConstSMul A M]

/-- **Restrictedness is summability** over a complete nonarchimedean group: a family lies in the
submodule exactly when it is summable. This is
`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` read through the membership criterion,
and it is what turns Wedhorn's "the product of two such series is well defined" into a theorem. -/
theorem mem_twoSidedRestrictedSubmodule_iff_summable {f : ℤ → M} :
    f ∈ twoSidedRestrictedSubmodule A M ↔ Summable f := by
  rw [mem_twoSidedRestrictedSubmodule]
  exact (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f).symm

end Summable

section Ring

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A]

/-- **Each coefficient of a product is a convergent series** (Wedhorn's "the convergent series
`∑_{k + l = n} aₖ bₗ`"): restrictedness *is* summability over a complete nonarchimedean ring, so
`Summable.mul_of_nonarchimedean` makes `(i, j) ↦ aᵢbⱼ` summable on all of `ℤ × ℤ`, and the
antidiagonal `k ↦ (k, n - k)` is a subfamily. -/
theorem summable_mul_sub_of_mem_twoSidedRestrictedSubmodule {f g : ℤ → A}
    (hf : f ∈ twoSidedRestrictedSubmodule A A) (hg : g ∈ twoSidedRestrictedSubmodule A A)
    (n : ℤ) : Summable fun k ↦ f k * g (n - k) :=
  ((mem_twoSidedRestrictedSubmodule_iff_summable.mp hf).mul_of_nonarchimedean
    (mem_twoSidedRestrictedSubmodule_iff_summable.mp hg)).comp_injective
    (i := fun k ↦ (k, n - k)) fun _ _ hab ↦ (Prod.mk.inj hab).1

/-- **The convolution of two restricted families exists**, in the form Mathlib's distributivity
lemmas for `DiscreteConvolution.addConvolution` consume: the same subfamily argument as
`summable_mul_sub_of_mem_twoSidedRestrictedSubmodule`, on Mathlib's fibre `addFiber n`. -/
theorem addConvolutionExists_of_mem_twoSidedRestrictedSubmodule {f g : ℤ → A}
    (hf : f ∈ twoSidedRestrictedSubmodule A A) (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    AddConvolutionExists (LinearMap.mul ℤ A) f g :=
  fun _ ↦ ((mem_twoSidedRestrictedSubmodule_iff_summable.mp hf).mul_of_nonarchimedean
    (mem_twoSidedRestrictedSubmodule_iff_summable.mp hg)).subtype _

variable [T0Space A]

namespace twoSidedRestrictedSubmodule

/-- Both bracketings of a triple product are the sum of `aᵢ bⱼ cₗ` over `{i + j + l = n}`. That
fibre is indexed by `(m, k) ↦ (k, m - k, n - m)`, with `m` the degree of the partial product `fg`;
summing first over `k` gives `((fg)h)ₙ`, while after the reindexing `(m, k) ↦ (k, m - k)` summing
first over the second coordinate gives `(f(gh))ₙ`. -/
protected theorem mul_assoc (f g h : twoSidedRestrictedSubmodule A A) :
    f * g * h = f * (g * h) := by
  ext n
  simp only [coe_mul_twoSidedRestrictedSubmodule, addConvolution_mul_apply]
  have hF : Summable fun p : ℤ × ℤ ↦
      (f : ℤ → A) p.2 * (g : ℤ → A) (p.1 - p.2) * (h : ℤ → A) (n - p.1) :=
    (((mem_twoSidedRestrictedSubmodule_iff_summable.mp f.2).mul_of_nonarchimedean
      (mem_twoSidedRestrictedSubmodule_iff_summable.mp g.2)).mul_of_nonarchimedean
      (mem_twoSidedRestrictedSubmodule_iff_summable.mp h.2)).comp_injective
      (i := fun p : ℤ × ℤ ↦ ((p.2, p.1 - p.2), n - p.1)) fun p q hpq ↦ by
        simp only [Prod.mk.injEq] at hpq
        exact Prod.ext (by omega) hpq.1.1
  refine (hF.hasSum.prod_fiberwise fun m ↦ ?_).tsum_eq.trans
    (HasSum.prod_fiberwise
      (f := fun q : ℤ × ℤ ↦ (f : ℤ → A) q.1 * ((g : ℤ → A) q.2 * (h : ℤ → A) (n - q.1 - q.2)))
      ?_ fun k ↦ ?_).tsum_eq.symm
  · exact (summable_mul_sub_of_mem_twoSidedRestrictedSubmodule f.2 g.2 m).hasSum.mul_right _
  · refine ((Equiv.prodComm ℤ ℤ).trans
      (Equiv.prodShear (Equiv.refl ℤ) Equiv.subRight)).hasSum_iff.mp ?_
    convert hF.hasSum using 1
    funext ⟨m, k⟩
    simp [mul_assoc]
  · exact (summable_mul_sub_of_mem_twoSidedRestrictedSubmodule g.2 h.2 (n - k)).hasSum.mul_left _

/-- **`A⟨X, X⁻¹⟩` is a ring** (Wedhorn, Example 6.39). The unit, the two annihilation laws and
distributivity are Mathlib's `DiscreteConvolution` lemmas, the latter fed by
`addConvolutionExists_of_mem_twoSidedRestrictedSubmodule`; associativity is proved here. -/
noncomputable instance instRing : Ring (twoSidedRestrictedSubmodule A A) where
  __ := Submodule.addCommGroup _
  __ := instMul
  __ := instOne
  mul_assoc := twoSidedRestrictedSubmodule.mul_assoc
  one_mul _ := Subtype.ext <| by simp
  mul_one _ := Subtype.ext <| by simp
  left_distrib f g h := Subtype.ext <|
    (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2).distrib_add _
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 h.2)
  right_distrib f g h := Subtype.ext <|
    (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 h.2).add_distrib _
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule g.2 h.2)
  zero_mul f := Subtype.ext (zero_addConvolution _ _)
  mul_zero f := Subtype.ext (addConvolution_zero _ _)

end twoSidedRestrictedSubmodule

end Ring

section CommRing

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A]

namespace twoSidedRestrictedSubmodule

/-- **`A⟨X, X⁻¹⟩` is commutative when `A` is**: swapping the two coordinates of each antidiagonal
is `DiscreteConvolution.addConvolution_comm`. -/
noncomputable instance instCommRing : CommRing (twoSidedRestrictedSubmodule A A) where
  __ := instRing
  mul_comm f g := Subtype.ext (addConvolution_comm (LinearMap.mul ℤ A) (f : ℤ → A) g mul_comm)

/-- **`A⟨X, X⁻¹⟩` is an `A`-algebra** (Wedhorn, Example 6.39), with the scalar action it already
carries as a submodule of `ℤ → A`: scalars pass through each coefficient series by
`Summable.tsum_mul_left`. -/
noncomputable instance instAlgebra : Algebra A (twoSidedRestrictedSubmodule A A) :=
  have h : ∀ (r : A) (f g : twoSidedRestrictedSubmodule A A), r • f * g = r • (f * g) :=
    fun r f g ↦ by
      ext n
      simp only [coe_mul_twoSidedRestrictedSubmodule, addConvolution_mul_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul]
      rw [← (summable_mul_sub_of_mem_twoSidedRestrictedSubmodule f.2 g.2 n).tsum_mul_left r]
      exact tsum_congr fun k ↦ mul_assoc _ _ _
  Algebra.ofModule h fun r f g ↦ by rw [mul_comm, h, mul_comm]

end twoSidedRestrictedSubmodule

/-- The structure map sends `a` to the constant series `a = a · X⁰`. It characterises
`twoSidedRestrictedSubmodule.instAlgebra`, whose body is not exposed. -/
@[simp]
theorem coe_algebraMap_twoSidedRestrictedSubmodule (a : A) :
    ((algebraMap A (twoSidedRestrictedSubmodule A A) a : twoSidedRestrictedSubmodule A A) :
        ℤ → A) = Pi.single 0 a := by
  -- `Algebra.ofModule` sends `a` to `a • 1`, with the submodule's own scalar action, by definition.
  change ((a • (1 : twoSidedRestrictedSubmodule A A) : twoSidedRestrictedSubmodule A A) : ℤ → A) = _
  rw [Submodule.coe_smul, coe_one_twoSidedRestrictedSubmodule, ← Pi.single_smul, smul_eq_mul,
    mul_one]

end CommRing

end TauCeti.Huber
