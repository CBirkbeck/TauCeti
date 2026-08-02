/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie

/-!
# The differential is a Lie algebra morphism

Precomposition of counit-valued derivations along a bialgebra morphism
(`TauCeti.derivationComp`) preserves the convolution commutator: the differential of a
morphism of affine monoid schemes is a morphism of Lie algebras (ReductiveGroups
roadmap, Layer 2, "the differential of a homomorphism"). The bracket identity uses
only the coalgebra half of the morphism — it intertwines the convolution products
termwise; the algebra half already entered in `derivationComp`, which needs
`d (φ (x * y)) = d (φ x * φ y)` to produce a derivation at all.

## Main declarations

* `TauCeti.derivationComp_bracket`: the differential preserves the bracket.
* `TauCeti.derivationCompLieHom`: the differential as a morphism of Lie algebras.
-/

public section

namespace TauCeti

open Coalgebra TensorProduct WithConv

section LieMap

variable {R A A' B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing A'] [Bialgebra R A'] [CommRing B] [Algebra R B]

/-- The differential preserves the convolution commutator: a bialgebra morphism
intertwines comultiplications, hence convolution products of derivations termwise. -/
theorem derivationComp_bracket (φ : A' →ₐc[R] A)
    (d₁ d₂ : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    derivationComp (B := B) φ ⁅d₁, d₂⁆ =
      ⁅derivationComp (B := B) φ d₁, derivationComp (B := B) φ d₂⁆ := by
  ext a
  rw [derivationComp_apply, Derivation.bracket_apply, Derivation.bracket_apply]
  have hΔ : comul (R := R) ((φ : A' →ₐ[R] A) a) =
      TensorProduct.map (φ : A' →ₐ[R] A).toLinearMap (φ : A' →ₐ[R] A).toLinearMap
        (comul a) :=
    (DFunLike.congr_fun (CoalgHomClass.map_comp_comul (φ : A' →ₐc[R] A)) a).symm
  have hmap : ∀ e₁ e₂ : Derivation R A (Bialgebra.CounitAlgebra R A B),
      TensorProduct.map (↑e₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ↑e₂
          (TensorProduct.map (φ : A' →ₐ[R] A).toLinearMap
            (φ : A' →ₐ[R] A).toLinearMap (comul a)) =
        TensorProduct.map
          ((↑e₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ∘ₗ (φ : A' →ₐ[R] A).toLinearMap)
          ((↑e₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ∘ₗ (φ : A' →ₐ[R] A).toLinearMap)
          (comul a) := fun e₁ e₂ =>
    (DFunLike.congr_fun (TensorProduct.map_comp _ _ _ _).symm (comul a))
  have hslot : ∀ (e₁ e₂ : Derivation R A (Bialgebra.CounitAlgebra R A B))
      (z : A' ⊗[R] A'),
      LinearMap.mul' R (Bialgebra.CounitAlgebra R A B)
          (TensorProduct.map
            ((↑e₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ∘ₗ
              (φ : A' →ₐ[R] A).toLinearMap)
            ((↑e₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ∘ₗ
              (φ : A' →ₐ[R] A).toLinearMap) z) =
        LinearMap.mul' R (Bialgebra.CounitAlgebra R A' B)
          (TensorProduct.map
            (↑(derivationComp (B := B) φ e₁) : A' →ₗ[R] Bialgebra.CounitAlgebra R A' B)
            ↑(derivationComp (B := B) φ e₂) z) := by
    intro e₁ e₂ z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans ((map_zero _).symm.trans rfl)
    | tmul x y =>
      simp only [TensorProduct.map_tmul, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mul'_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply]
      rw [derivationComp_apply, derivationComp_apply]
      -- The residual is print-identical across the two coefficient synonyms; the
      -- multiplications are definitionally `B`'s.
      rfl
    | add u w hu hw =>
      rw [map_add, map_add, map_add, map_add, hu, hw]
      -- Addition on both sides is definitionally `B`'s.
      rfl
  rw [hΔ, hmap, hmap, hslot, hslot]
  rfl

/-- The differential on derivations, as a morphism of Lie algebras. -/
noncomputable def derivationCompLieHom (φ : A' →ₐc[R] A) :
    Derivation R A (Bialgebra.CounitAlgebra R A B) →ₗ⁅R⁆
      Derivation R A' (Bialgebra.CounitAlgebra R A' B) :=
  { derivationComp (B := B) φ with
    map_lie' := derivationComp_bracket φ _ _ }

@[simp]
lemma derivationCompLieHom_apply (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    derivationCompLieHom (B := B) φ d = derivationComp φ d := by
  -- `derivationCompLieHom` has no equation lemma to rewrite with; `change` spells out
  -- its definitional unfolding once, explicitly.
  change derivationComp (B := B) φ d = _
  rfl

end LieMap

end TauCeti
