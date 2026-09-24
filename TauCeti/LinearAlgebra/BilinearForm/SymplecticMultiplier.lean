/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.LinearAlgebra.Matrix.SymplecticMultiplier

/-!
# The multiplier of an alternating form on a rank-two module

Let `B` be an alternating bilinear form on a free module `V` of rank two over a commutative ring
`R`. The alternating forms on `V` make up a free module of rank one, on which an endomorphism `f`
acts by its determinant:

    B (f x) (f y) = det f * B x y.

So when `f` scales a nonzero `B` by some `d` over an integral domain, `d` is `det f`, and the
matrix `A` of `f` in a basis indexed by `l ⊕ l` satisfies `Aᵀ * J * A = d • J`.

This is the module-level form of `Matrix.det_eq_of_transpose_mul_J_mul_eq_smul`, and its last
statement produces the hypothesis of
`TauCeti.Matrix.sq_le_four_mul_of_exists_nonneg_symplectic_multiplier` from a pairing: the
additive Weil pairing on the `ℓ`-torsion of an elliptic curve is an alternating form of this kind,
which an isogeny scales by its degree.

## Main results

* `LinearMap.IsAlt.compl₁₂_self_eq_det_smul`: `B (f x) (f y) = det f * B x y` in rank two.
* `LinearMap.IsAlt.det_eq_of_compl₁₂_self_eq_smul`: the multiplier of a nonzero alternating form is
  the determinant.
* `LinearMap.IsAlt.transpose_toMatrix_mul_J_mul_toMatrix_eq_smul`: the matrix of such an `f` has
  symplectic multiplier `d`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB` @
`f622f4aa0bd7b9d8b8cb931b5f8cb709f1d179e2`, Apache-2.0), file
`projects/HasseWeil/HasseWeil/HasseBound/WeilPairing/PairingDet.lean`, theorems
`alternating_comp_eq_det_smul` and `det_eq_of_alternating_scaling`. The source states them over a
field for a basis indexed by `Fin 2`, for the value at `(b 0, b 1)` alone, and with nondegeneracy as
`ω (b 0) (b 1) ≠ 0`. Here the identity is the equality of forms, over any commutative ring and with
no basis in the statement, and the determinant statement asks only that `B ≠ 0` over a domain. The
source's `linearMap_det_eq_of_symplectic_scaling` and `frob_det_data_of_pairing_form` are not
reproduced: the first is `LinearMap.det_toMatrix` composed with
`Matrix.det_eq_of_transpose_mul_J_mul_eq_smul`, and the second is three applications of the matrix
statement here.
-/

public section

open scoped Matrix

namespace LinearMap.IsAlt

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {B : LinearMap.BilinForm R V}

-- The identity at the basis pair, by expanding `f (b 0)` and `f (b 1)` in the basis.
private theorem apply_map_zero_map_one (hB : B.IsAlt) (b : Module.Basis (Fin 2) R V)
    (f : V →ₗ[R] V) : B (f (b 0)) (f (b 1)) = LinearMap.det f * B (b 0) (b 1) := by
  have hrepr (j : Fin 2) : f (b j) = toMatrix b b f 0 j • b 0 + toMatrix b b f 1 j • b 1 := by
    rw [toMatrix_apply, toMatrix_apply,
      ← Fin.sum_univ_two (fun i ↦ b.repr (f (b j)) i • b i), b.sum_repr]
  rw [hrepr 0, hrepr 1, ← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hB.self_eq_zero, ← hB.neg (b 0) (b 1)]
  ring

/-- **An endomorphism of a rank-two module scales an alternating form by its determinant**:
`B (f x) (f y) = det f * B x y`. -/
theorem compl₁₂_self_eq_det_smul [Module.Free R V] [Module.Finite R V] (hB : B.IsAlt)
    (hV : Module.finrank R V = 2) (f : V →ₗ[R] V) : B.compl₁₂ f f = LinearMap.det f • B := by
  -- over the zero ring every module has rank one
  have : Nontrivial R := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    rw [Module.finrank_subsingleton] at hV
    omega
  let b := Module.finBasisOfFinrankEq R V hV
  have h01 := hB.apply_map_zero_map_one b f
  rw [LinearMap.ext_iff_basis b b]
  simp only [Fin.forall_fin_two, compl₁₂_apply, smul_apply, smul_eq_mul, hB.self_eq_zero,
    mul_zero, h01, true_and, and_true]
  rw [← hB.neg, h01, ← hB.neg (b 0), mul_neg]

/-- **The multiplier of a nonzero alternating form on a rank-two module is the determinant**: over
an integral domain, if `f` scales `B ≠ 0` by `d`, then `det f = d`. -/
theorem det_eq_of_compl₁₂_self_eq_smul [IsDomain R] [Module.Free R V] [Module.Finite R V]
    (hB : B.IsAlt) (hB0 : B ≠ 0) (hV : Module.finrank R V = 2) {f : V →ₗ[R] V} {d : R}
    (h : B.compl₁₂ f f = d • B) : LinearMap.det f = d := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, B x y ≠ 0 := by
    by_contra! h0
    exact hB0 (LinearMap.ext₂ h0)
  have := LinearMap.congr_fun₂ (h.symm.trans (hB.compl₁₂_self_eq_det_smul hV f)) x y
  simp only [smul_apply, smul_eq_mul] at this
  exact (mul_right_cancel₀ hxy this).symm

/-- **The matrix of an endomorphism scaling an alternating form has that symplectic multiplier.**
Over an integral domain, if `f` scales `B ≠ 0` by `d`, then in any basis of `V` indexed by `l ⊕ l`,
for a singleton `l`, the matrix `A` of `f` satisfies `Aᵀ * J * A = d • J`. -/
theorem transpose_toMatrix_mul_J_mul_toMatrix_eq_smul [IsDomain R] {l : Type*} [DecidableEq l]
    [Fintype l] [Unique l] (hB : B.IsAlt) (hB0 : B ≠ 0) (b : Module.Basis (l ⊕ l) R V)
    {f : V →ₗ[R] V} {d : R} (h : B.compl₁₂ f f = d • B) :
    (toMatrix b b f)ᵀ * Matrix.J l R * toMatrix b b f = d • Matrix.J l R := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  rw [Matrix.transpose_mul_J_mul_eq_det_smul, LinearMap.det_toMatrix,
    hB.det_eq_of_compl₁₂_self_eq_smul hB0
      (by simp only [Module.finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_unique]) h]

end LinearMap.IsAlt
