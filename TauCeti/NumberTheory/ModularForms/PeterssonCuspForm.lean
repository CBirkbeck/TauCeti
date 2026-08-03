/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.PeterssonInner

/-!
# The `Inner` structure on cusp forms

The level-one-domain Petersson pairing `CuspForm.peterssonInnerFd` packaged as an
`Inner ℂ (CuspForm Γ k)` structure, with its defining equation. The pairing's
Hermitian-sesquilinear laws and positive definiteness live with the pairing itself in
`TauCeti.NumberTheory.ModularForms.PeterssonInner`.

We do **not** register an `InnerProductSpace ℂ (CuspForm Γ k)` instance: that structure
requires a compatible `Norm`, which `CuspForm Γ k` does not carry.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/PeterssonInner.lean`).

## References

* Diamond–Shurman, *A first course in modular forms*, §5.4
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/PeterssonInner.lean`)
-/

public section

noncomputable section

namespace CuspForm

open UpperHalfPlane ModularGroup MeasureTheory

open scoped ComplexConjugate ComplexInnerProductSpace MatrixGroups

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The level-one-domain Petersson pairing as an `Inner ℂ` structure on cusp forms. -/
instance : Inner ℂ (CuspForm Γ k) where
  inner := peterssonInnerFd

@[simp]
theorem inner_def (f g : CuspForm Γ k) : ⟪f, g⟫ = peterssonInnerFd f g := rfl

end CuspForm
