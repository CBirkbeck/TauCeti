/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic

/-!
# Rational subsets of the adic spectrum

**The set-level constructions beneath Wedhorn, *Adic Spaces* (arXiv:1910.05934v1),
Definition 7.29 and Remark 7.30.**

For a finite numerator set `T` and a denominator `s`, the rational subset is the trace on
`spa A⁺` of the basic open `Spv(A)(T/s)`:

```text
R(T/s) = {v ∈ spa A⁺ ; v(t) ≤ v(s) ≠ 0 for every t ∈ T} = spa A⁺ ∩ Spv(A)(T/s).
```

As with `spa` itself, the definition is stated for arbitrary data: no hypothesis relates the
topology of `A` to its ring operations, the subring is arbitrary, and Wedhorn's standing
condition that the ideal `T · A` be open is not assumed. It is Wedhorn's rational subset of
`Spa (A, A⁺)` under his hypotheses (a Huber ring, a ring of integral elements, `T · A` open);
the open-ideal condition enters only in the results that need it — the basis claims of
Definition 7.29 and the quasi-compactness of Theorem 7.35 — none of which is in this file.

What is here is the part of Remark 7.30 that holds with no hypotheses at all, inherited from
the corresponding facts about `Spv(A)(T/s)`:

* inserting the denominator among the numerators changes nothing (Wedhorn's "one may replace
  `T` by `T ∪ {s}`"), and
* rational subsets are stable under finite intersection — Remark 7.30(5), the part Theorem
  7.35's own proof consumes — with the same product presentation as at the `Spv A` level.

## Main definitions

* `TauCeti.ValuationSpectrum.rationalSubset` : the rational subset `R(T/s)` of `spa A⁺`, as a
  `Set (Spv A)`.

## Main results

* `TauCeti.ValuationSpectrum.isOpen_val_preimage_rationalSubset` : a rational subset is open
  in the subspace `spa A⁺`.
* `TauCeti.ValuationSpectrum.rationalSubset_insert_self` : the denominator may be inserted
  among the numerators.
* `TauCeti.ValuationSpectrum.rationalSubset_inter` : **Remark 7.30(5)** — the intersection of
  two rational subsets is the rational subset of the numerator products over the denominator
  product.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.29 and Remark 7.30.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The rational subset `R(T/s)` of the adic spectrum: the trace on `spa A⁺` of the basic open
`Spv(A)(T/s)`. Under Wedhorn's hypotheses — a Huber ring, a ring of integral elements, and the
ideal `T · A` open — this is his Definition 7.29; the definition itself asks for none of them,
and the open-ideal condition first matters for the basis claims, which are not in this file. -/
def rationalSubset (Aplus : Subring A) (T : Finset A) (s : A) : Set (Spv A) :=
  spa Aplus ∩ basicOpenFinset T s

/-- The set-level characterization of a rational subset, mirroring `spa_def`. -/
theorem rationalSubset_def (Aplus : Subring A) (T : Finset A) (s : A) :
    rationalSubset Aplus T s = spa Aplus ∩ basicOpenFinset T s := (rfl)

/-- Membership in `R(T/s)`: a point of the adic spectrum where every numerator is dominated by
the denominator and the denominator is not in the support. -/
@[simp]
theorem mem_rationalSubset_iff (Aplus : Subring A) (T : Finset A) (s : A) (v : Spv A) :
    v ∈ rationalSubset Aplus T s ↔
      v ∈ spa Aplus ∧ (∀ t ∈ T, v.toValuativeRel.vle t s) ∧ ¬ v.toValuativeRel.vle s 0 := by
  rw [rationalSubset_def, Set.mem_inter_iff, mem_basicOpenFinset_iff]

open scoped Classical in
/-- Inserting the denominator among the numerators changes nothing — Wedhorn's "one may
replace `T` by `T ∪ {s}`" (Definition 7.29). -/
@[simp]
theorem rationalSubset_insert_self (Aplus : Subring A) (T : Finset A) (s : A) :
    rationalSubset Aplus (insert s T) s = rationalSubset Aplus T s := by
  rw [rationalSubset_def, rationalSubset_def, basicOpenFinset_insert_self]

/-- The preimage of `R(T/s)` under the coercion of the subtype `spa A⁺` is open: a rational
subset is relatively open in the adic spectrum. -/
theorem isOpen_val_preimage_rationalSubset (Aplus : Subring A) (T : Finset A) (s : A) :
    IsOpen (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) := by
  have h : (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus))
      = Subtype.val ⁻¹' basicOpenFinset T s := by
    ext v
    simp only [rationalSubset_def, Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact and_iff_right v.2
  rw [h]
  exact (isOpen_basicOpenFinset T s).preimage continuous_subtype_val

open scoped Classical Pointwise in
/-- **Wedhorn Remark 7.30(5)**: rational subsets are stable under finite intersection, with
the numerator products over the denominator product presenting the intersection. This is the
form Theorem 7.35's own proof consumes. -/
@[simp]
theorem rationalSubset_inter (Aplus : Subring A) (T₁ T₂ : Finset A) (s₁ s₂ : A) :
    rationalSubset Aplus T₁ s₁ ∩ rationalSubset Aplus T₂ s₂
      = rationalSubset Aplus (insert s₁ T₁ * insert s₂ T₂) (s₁ * s₂) := by
  rw [rationalSubset_def, rationalSubset_def, rationalSubset_def, ← basicOpenFinset_inter]
  ext v
  simp only [Set.mem_inter_iff]
  tauto

end TauCeti.ValuationSpectrum

end
