/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Norm.Reduction
public import TauCeti.NumberTheory.ModularForms.Norm.Trace
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing

/-!
# Orders along the norm map

The general-level valence formula reads the level-one formula off the norm
`ModularForm.norm 𝒮ℒ f`, so it needs the orders of `f` to distribute over the norm's coset
product. This file records that distribution at interior points: each coset factor is
nonzero when `f` is, and the vanishing order of the norm is the sum of the orders of the
factors.

## Main declarations

* `TauCeti.ModularForm.NormReduction.quotientFunc_ne_zero`: a coset factor of the norm of a
  nonzero form is nonzero.
* `TauCeti.ModularForm.NormReduction.orderOfVanishingAt_norm`: the vanishing order of the
  norm at a point is the sum of the vanishing orders of the coset factors.
-/

open UpperHalfPlane

open scoped MatrixGroups

namespace TauCeti.ModularForm.NormReduction

noncomputable section
variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- A coset factor of the norm of a nonzero form is nonzero: the factor is a slash translate
of `f`, and the slash action of a group element kills only `0`. -/
public lemma quotientFunc_ne_zero {f : ModularForm (G Γ) k} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (q : Q Γ) : SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q ≠ 0 := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [SlashInvariantForm.quotientFunc_mk]
    exact fun h ↦ hf ((SlashAction.slash_eq_zero_iff k (g.val⁻¹) (⇑f : ℍ → ℂ)).1 h)

/-- The vanishing order of the norm at an interior point is the sum of the vanishing orders
of its coset factors. -/
public lemma orderOfVanishingAt_norm [Γ.FiniteIndex] [Fintype (Q Γ)]
    (f : ModularForm (G Γ) k) (hf : (⇑f : ℍ → ℂ) ≠ 0) (p : ℍ) :
    orderOfVanishingAt (⇑(_root_.ModularForm.norm 𝒮ℒ f)) p =
      ∑ q : Q Γ, orderOfVanishingAt
        (SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q) p := by
  rw [show (⇑(_root_.ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) =
      ∏ q : Q Γ, SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q by
    simp only [_root_.ModularForm.coe_norm]
    congr!]
  exact orderOfVanishingAt_prod
    (fun q _ ↦ _root_.TauCeti.SlashInvariantForm.mdifferentiable_quotientFunc f q)
    (fun q _ ↦ quotientFunc_ne_zero hf q) p

end

end TauCeti.ModularForm.NormReduction
