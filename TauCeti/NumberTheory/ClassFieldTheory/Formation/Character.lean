/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic
public import TauCeti.RepresentationTheory.Rep.Trivial

/-!
# The connecting class of a character of a finite normal layer

Let `Γ = U ⧸ V` be the Galois group of a finite normal layer. A character `χ : Γ^ab → ℚ/ℤ` is a
homomorphism `Γ → ℚ/ℤ`, which is a class in `H¹(Γ, ℚ/ℤ)` for the trivial action. The connecting
map of the sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial `Γ`-modules sends it to a class
`δχ ∈ H²(Γ, ℤ)`, which is read in the Tate group of degree `2`. This is the class through which
Artin and Tate characterize the Artin map: `χ(artinMap a)` is the invariant of the cup product of
the degree-zero class of `a` with `δχ`.

As elsewhere in this development, `ℚ/ℤ` is the rational circle `AddCircle (1 : ℚ)`.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass`: the connecting class
  `δχ ∈ H²(Γ, ℤ)` of a character `χ : Γ^ab → ℚ/ℤ`, in the Tate group of degree `2`.

## Main results

* `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_def`: `δχ` is the connecting map
  of `Rep.ratAddCircleShortComplex` applied to the class of `χ` in `H¹(Γ, ℚ/ℤ)`, read in Tate
  cohomology.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §3.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory.NormalLayer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (L : NormalLayer G)

/-- The **connecting class** `δχ ∈ H²(Γ, ℤ)` of a character `χ : Γ^ab → ℚ/ℤ` of the Galois group
`Γ` of a finite normal layer, in the Tate group of degree `2`: the image of `χ`, as a class in
`H¹(Γ, ℚ/ℤ)` for the trivial action, under the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`. The
character is read on `Γ` through the abelianization map `Γ → Γ^ab`. -/
def characterConnectingClass (χ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    L.TrivialTateH 2 :=
  (TateCohomology.isoGroupCohomology 2).inv.app (Rep.trivial ℤ L.Gal ℤ) <|
    groupCohomology.δ (Rep.ratAddCircleShortComplex_shortExact L.Gal) 1 2 rfl <|
      (groupCohomology.H1IsoOfIsTrivial (Rep.trivial ℤ L.Gal (AddCircle (1 : ℚ)))).inv <|
        χ.comp Abelianization.of.toAdditive

/-- The connecting class of `χ` is the connecting map applied to the class of `Γ → Γ^ab → ℚ/ℤ`
in `H¹(Γ, ℚ/ℤ)`, carried to Tate cohomology by the comparison of positive degrees. -/
theorem characterConnectingClass_def (χ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    L.characterConnectingClass χ =
      (TateCohomology.isoGroupCohomology 2).inv.app (Rep.trivial ℤ L.Gal ℤ)
        (groupCohomology.δ (Rep.ratAddCircleShortComplex_shortExact L.Gal) 1 2 rfl
          ((groupCohomology.H1IsoOfIsTrivial (Rep.trivial ℤ L.Gal (AddCircle (1 : ℚ)))).inv
            (χ.comp Abelianization.of.toAdditive))) :=
  (rfl)

end TauCeti.ClassFieldTheory.NormalLayer
