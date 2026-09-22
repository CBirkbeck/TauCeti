/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# The long exact sequence of Tate cohomology

Mathlib's Tate cohomology of a finite group comes with the connecting homomorphism
`TateCohomology.δ` of a short exact sequence of representations and the exactness of the long
exact sequence it lies in. This file records the consequence used for dimension shifting: the
connecting homomorphism is an isomorphism as soon as the middle term of the short exact sequence
has vanishing Tate cohomology in the two adjacent degrees. It is the Tate counterpart of Mathlib's
`groupCohomology.isIso_δ_of_isZero`.

## Main statements

* `TauCeti.TateCohomology.isIso_δ_of_isZero`: the connecting homomorphism
  `Ĥⁿ(G, X₃) ⟶ Ĥⁿ⁺¹(G, X₁)` is an isomorphism when `Ĥⁿ(G, X₂)` and `Ĥⁿ⁺¹(G, X₂)` vanish.
* `TauCeti.TateCohomology.δIso`: the same connecting homomorphism, bundled as an isomorphism.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- A connecting homomorphism of Tate cohomology is an isomorphism when the middle term of the
short exact sequence has vanishing Tate cohomology in the two relevant degrees. -/
theorem isIso_δ_of_isZero {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℤ)
    (h₀ : IsZero (tateCohomology X.X₂ n)) (h₁ : IsZero (tateCohomology X.X₂ (n + 1))) :
    IsIso (_root_.TateCohomology.δ hX n) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact hX).isIso_δ n (n + 1) rfl h₀ h₁

/-- The connecting homomorphism `Ĥⁿ(G, X₃) ≅ Ĥⁿ⁺¹(G, X₁)` of a short exact sequence whose middle
term has vanishing Tate cohomology in degrees `n` and `n + 1`, as an isomorphism. -/
def δIso {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℤ)
    (h₀ : IsZero (tateCohomology X.X₂ n)) (h₁ : IsZero (tateCohomology X.X₂ (n + 1))) :
    tateCohomology X.X₃ n ≅ tateCohomology X.X₁ (n + 1) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact hX).δIso n (n + 1) rfl h₀ h₁

/-- The bundled connecting isomorphism is the connecting homomorphism. -/
@[simp]
theorem δIso_hom {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℤ)
    (h₀ : IsZero (tateCohomology X.X₂ n)) (h₁ : IsZero (tateCohomology X.X₂ (n + 1))) :
    (δIso hX n h₀ h₁).hom = _root_.TateCohomology.δ hX n := by
  rfl

end TauCeti.TateCohomology
