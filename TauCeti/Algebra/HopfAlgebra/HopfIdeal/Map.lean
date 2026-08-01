/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Comap

/-!
# Images of Hopf ideals under morphisms into commutative Hopf algebras

This file records the pushforward of a Hopf ideal along a bialgebra morphism
`f : H →ₐc[R] K` with commutative codomain: the ordinary ideal-theoretic image
`Ideal.map f I` of a Hopf ideal `I` is again a Hopf ideal. Commutativity of the codomain
makes the generated ideal two-sided and the antipode an algebra endomorphism; the coideal
and counit conditions transport along `f` because `f` intertwines the comultiplications
and counits.

Together with `TauCeti.HopfIdeal.comap`, this gives both variance directions for Hopf
ideals. The two are adjoint along surjective morphisms
(`TauCeti.HopfIdeal.map_le_iff_le_comap`).

This is a Layer 3 prerequisite for the reductive-groups roadmap target "Hopf ideals ↔
closed subgroup schemes", specifically the "kernels" part of the dictionary: the kernel of
the affine group-scheme morphism induced by `f` is cut out by the image of the
augmentation ideal under `f`.

## Main declarations

* `TauCeti.HopfIdeal.map`: the image of a Hopf ideal under a bialgebra morphism with
  commutative codomain.
* `TauCeti.HopfIdeal.map_toIdeal` and `TauCeti.HopfIdeal.mem_map_of_mem`: characteristic
  API.
* `TauCeti.HopfIdeal.map_id` and `TauCeti.HopfIdeal.map_map`: identity and composition
  laws.
* `TauCeti.HopfIdeal.map_le_iff_le_comap`: the image is left adjoint to the inverse image
  along a surjective morphism.

## References

The construction is the standard image of a Hopf ideal; see for instance
[Milne, *Algebraic Groups*][milne2017] around Definition 3.10, where quotients by such
images cut out closed subgroup schemes.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace HopfIdeal

section Semiring

variable {R : Type u} [CommSemiring R]
variable {H : Type v} {K : Type w} [Semiring H] [CommSemiring K]
variable [HopfAlgebra R H] [HopfAlgebra R K]

private theorem map_tensor_leftTensorIdeal (f : H →ₐc[R] K) (I : Ideal H) :
    Ideal.map (Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K)).toRingHom
      (leftTensorIdeal (R := R) (H := H) I) =
      leftTensorIdeal (R := R) (H := K) (Ideal.map (f : H →+* K) I) := by
  rw [leftTensorIdeal, leftTensorIdeal, Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  simp

private theorem map_tensor_rightTensorIdeal (f : H →ₐc[R] K) (I : Ideal H) :
    Ideal.map (Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K)).toRingHom
      (rightTensorIdeal (R := R) (H := H) I) =
      rightTensorIdeal (R := R) (H := K) (Ideal.map (f : H →+* K) I) := by
  rw [rightTensorIdeal, rightTensorIdeal, Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  simp

private theorem tensorProduct_map_coe (f : H →ₐc[R] K) (y : H ⊗[R] H) :
    TensorProduct.map (f : H →ₗ[R] K) (f : H →ₗ[R] K) y =
      Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp [ha, hb]

private theorem comul_mem_map (I : HopfIdeal R H) (f : H →ₐc[R] K) ⦃x : K⦄
    (hx : x ∈ Ideal.map (f : H →+* K) I.toIdeal) :
    Coalgebra.comul (R := R) x ∈
      leftTensorIdeal (R := R) (H := K) (Ideal.map (f : H →+* K) I.toIdeal) ⊔
        rightTensorIdeal (R := R) (H := K) (Ideal.map (f : H →+* K) I.toIdeal) := by
  have h : Ideal.map (f : H →+* K) I.toIdeal ≤
      Ideal.comap (Bialgebra.comulAlgHom R K).toRingHom
        (leftTensorIdeal (R := R) (H := K) (Ideal.map (f : H →+* K) I.toIdeal) ⊔
          rightTensorIdeal (R := R) (H := K) (Ideal.map (f : H →+* K) I.toIdeal)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    simp only [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Bialgebra.comulAlgHom_apply]
    rw [(CoalgHomClass.map_comp_comul_apply f i).symm.trans (tensorProduct_map_coe f _),
      ← map_tensor_leftTensorIdeal, ← map_tensor_rightTensorIdeal, ← Ideal.map_sup]
    exact Ideal.mem_map_of_mem _ (I.comul_mem hi)
  simpa using Ideal.mem_comap.mp (h hx)

private theorem counit_eq_zero_map (I : HopfIdeal R H) (f : H →ₐc[R] K) ⦃x : K⦄
    (hx : x ∈ Ideal.map (f : H →+* K) I.toIdeal) : Coalgebra.counit (R := R) x = 0 := by
  have h : Ideal.map (f : H →+* K) I.toIdeal ≤
      Ideal.comap (Bialgebra.counitAlgHom R K).toRingHom ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    simp only [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Bialgebra.counitAlgHom_apply, Ideal.mem_bot, CoalgHomClass.counit_comp_apply]
    exact I.counit_eq_zero hi
  simpa using Ideal.mem_comap.mp (h hx)

private theorem antipode_mem_map (I : HopfIdeal R H) (f : H →ₐc[R] K) ⦃x : K⦄
    (hx : x ∈ Ideal.map (f : H →+* K) I.toIdeal) :
    HopfAlgebra.antipode R x ∈ Ideal.map (f : H →+* K) I.toIdeal := by
  have h : Ideal.map (f : H →+* K) I.toIdeal ≤
      Ideal.comap (HopfAlgebra.antipodeAlgHom R K).toRingHom
        (Ideal.map (f : H →+* K) I.toIdeal) := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    simp only [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      HopfAlgebra.antipodeAlgHom_apply]
    rw [← BialgHom.map_antipode]
    exact Ideal.mem_map_of_mem _ (I.antipode_mem hi)
  simpa using Ideal.mem_comap.mp (h hx)

/-- The image of a Hopf ideal under a bialgebra morphism into a commutative Hopf algebra.

Its underlying ideal is the ordinary ideal-theoretic image `Ideal.map`. -/
def map (I : HopfIdeal R H) (f : H →ₐc[R] K) : HopfIdeal R K :=
  ofIdeal (Ideal.map (f : H →+* K) I.toIdeal) (comul_mem_map I f)
    (counit_eq_zero_map I f) (antipode_mem_map I f)

/-- The underlying ideal of `I.map f` is the ordinary ideal-theoretic image. -/
@[simp]
theorem map_toIdeal (I : HopfIdeal R H) (f : H →ₐc[R] K) :
    (I.map f).toIdeal = Ideal.map (f : H →+* K) I.toIdeal := by
  -- `map` has no equation lemma to rewrite with; `change` spells out its definitional
  -- unfolding to an `ofIdeal` application, whose underlying ideal is definitionally the
  -- ideal it was built from.
  change (ofIdeal (Ideal.map (f : H →+* K) I.toIdeal) _ _ _).toIdeal = _
  rfl

/-- The image of a Hopf ideal contains the image of each of its elements. -/
theorem mem_map_of_mem (f : H →ₐc[R] K) {I : HopfIdeal R H} {x : H} (hx : x ∈ I) :
    f x ∈ I.map f :=
  Ideal.mem_map_of_mem _ hx

/-- Image of Hopf ideals is monotone. -/
theorem map_mono (f : H →ₐc[R] K) {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    I.map f ≤ J.map f :=
  Ideal.map_mono (toIdeal_le_toIdeal.mpr hIJ)

end Semiring

section Id

variable {R : Type u} [CommSemiring R]
variable {H : Type v} [CommSemiring H] [HopfAlgebra R H]

/-- The image of a Hopf ideal under the identity morphism. -/
@[simp]
theorem map_id (I : HopfIdeal R H) : I.map (BialgHom.id R H) = I :=
  ext fun _ => by
    rw [← mem_toIdeal, map_toIdeal,
      show ((BialgHom.id R H : H →ₐc[R] H) : H →+* H) = RingHom.id H from
        RingHom.ext fun _ => rfl,
      Ideal.map_id, mem_toIdeal]

end Id

section Comp

variable {R : Type u} [CommSemiring R]
variable {H : Type v} {K : Type w} {L : Type x}
variable [Semiring H] [CommSemiring K] [CommSemiring L]
variable [HopfAlgebra R H] [HopfAlgebra R K] [HopfAlgebra R L]

/-- Image of Hopf ideals is functorial. -/
theorem map_map (I : HopfIdeal R H) (f : H →ₐc[R] K) (g : K →ₐc[R] L) :
    (I.map f).map g = I.map (g.comp f) :=
  ext fun _ => by
    rw [← mem_toIdeal, map_toIdeal, map_toIdeal, Ideal.map_map, ← mem_toIdeal, map_toIdeal,
      show ((g.comp f : H →ₐc[R] L) : H →+* L) = (g : K →+* L).comp (f : H →+* K) from
        RingHom.ext fun _ => rfl]

end Comp

section Adjunction

variable {R : Type u} [CommRing R]
variable {H : Type v} {K : Type w} [Ring H] [CommRing K]
variable [HopfAlgebra R H] [HopfAlgebra R K]

/-- Along a surjective morphism, the image of Hopf ideals is left adjoint to the inverse
image. -/
theorem map_le_iff_le_comap {f : H →ₐc[R] K} (hf : Function.Surjective f)
    {I : HopfIdeal R H} {J : HopfIdeal R K} : I.map f ≤ J ↔ I ≤ J.comap f hf := by
  rw [le_def, le_def]
  constructor
  · exact fun h x hx => mem_comap.mpr (h (mem_map_of_mem f hx))
  · intro h x hx
    rw [← mem_toIdeal] at hx
    refine Ideal.map_le_iff_le_comap.mpr (fun i hi => ?_) hx
    exact Ideal.mem_comap.mpr (mem_toIdeal.mpr (mem_comap.mp (h hi)))

end Adjunction

end HopfIdeal

end TauCeti
