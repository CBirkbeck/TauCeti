/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Bounding a product of ideals by a span over a subring

Let `S` be a subring of `R`, let `G ⊆ R`, and let `J` be an ideal of `R` that lies inside `S`.
Then

```text
J * Ideal.span G ≤ Submodule.span S G,
```

the containment being of `S`-submodules of `R`. Taking `J = Ideal.span G`, which is legitimate
whenever the ideal itself lies inside `S`, bounds the *square* of that ideal.

The conclusion is a containment, not an equality: `Ideal.span G` generally is **not** spanned by
`G` over `S`, and the product need not be a finitely generated `S`-submodule either. What the
containment does give, for finite `G`, is a finitely generated `S`-submodule sandwiching the
product from above.

## Why the coefficients can be moved

An element `Σ bᵢ gᵢ` of `Ideal.span G` has its coefficients `bᵢ` in `R`, and nothing puts them in
`S`. Multiplying by `x ∈ J` rescues this, because the coefficients can be moved onto the other
factor:

```text
x * (Σ bᵢ gᵢ) = Σ (x * bᵢ) gᵢ,
```

and each `x * bᵢ` lies in `J`, hence in `S`. The new coefficients are in `S` even though the old
ones were not. This is the same absorption used in
`Valuation.map_le_pow_of_mem_span_pow_succ` to bound a valuation on a power of an ideal.

The intended application is the intersection of two rings of definition, where the ideal has to
descend to a *smaller* subring and `Ideal.map` is therefore unavailable: `Submodule.span S G` is
an ideal of `S`, is finitely generated when `G` is, and is sandwiched as
`I * I ≤ Submodule.span S G ≤ I`.

## Main results

* `Ideal.mul_mem_span_of_mem`
* `Ideal.restrictScalars_mul_le_span`
* `Ideal.restrictScalars_mul_self_le_span`

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Corollary 6.4.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R] (S : Subring R) {G : Set R} {J : Ideal R}

/-- For `x` in an ideal `J` contained in `S` and `y` in `Ideal.span G`, the product `x * y` lies
in the `S`-span of `G`. -/
theorem mul_mem_span_of_mem (hJS : ∀ x ∈ J, x ∈ S) :
    ∀ y ∈ Ideal.span G, ∀ x ∈ J, x * y ∈ Submodule.span S G := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem g hg =>
    intro x hx
    exact Submodule.smul_mem _ (⟨x, hJS x hx⟩ : S) (Submodule.subset_span hg)
  | zero => intro x _; simp
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    intro x hx
    rw [mul_add]
    exact Submodule.add_mem _ (ih₁ x hx) (ih₂ x hx)
  | smul c y _ ih =>
    intro x hx
    rw [smul_eq_mul, ← mul_assoc]
    exact ih _ (J.mul_mem_right c hx)

/-- **An ideal inside a subring, times a span, is bounded by the span over that subring.** If `J`
is an ideal of `R` lying inside a subring `S`, then `J * Ideal.span G` is contained in the
`S`-span of `G`. -/
theorem restrictScalars_mul_le_span (hJS : ∀ x ∈ J, x ∈ S) :
    Submodule.restrictScalars S (J * Ideal.span G) ≤ Submodule.span S G := by
  intro a ha
  rw [Submodule.restrictScalars_mem] at ha
  refine Submodule.mul_induction_on ha (fun x hx y hy ↦ ?_) fun x y hx hy ↦ ?_
  · exact mul_mem_span_of_mem S hJS y hy x hx
  · exact Submodule.add_mem _ hx hy

/-- **The square of an ideal contained in a subring is bounded by the span of its generators over
that subring.** The case `J = Ideal.span G` of `restrictScalars_mul_le_span`. -/
theorem restrictScalars_mul_self_le_span (hIS : ∀ x ∈ Ideal.span G, x ∈ S) :
    Submodule.restrictScalars S (Ideal.span G * Ideal.span G) ≤ Submodule.span S G :=
  restrictScalars_mul_le_span S hIS

end Ideal
