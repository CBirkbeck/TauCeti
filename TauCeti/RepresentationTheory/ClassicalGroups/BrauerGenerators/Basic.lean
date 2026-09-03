/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Bookkeeping for the Brauer generators on two strands

A Brauer diagram on two strands acts on a tensor square, so the calculations in
`TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal` and in
`TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic` both expand pure
tensors indexed by `Fin 2`. That expansion needs the same two pieces of glue in either file: a sum
over the functions `Fin 2 → ι` is a double sum, and a pure tensor indexed by `Fin 2` may be
rewritten in `![·, ·]` form. Neither says anything about an invariant form, so both live here
rather than being repeated in the two files that use them.

## Main results

* `TauCeti.sum_pi_fin_two`: a sum over `Fin 2 → ι` is a double sum over `ι`.
* `TauCeti.tprod_fin_two`: a pure tensor on two strands is `⨂ₜ ![v 0, v 1]`.
* `Matrix.piTensorProductMap_tprod_single`: applying a matrix in both strands re-expands a basis
  pure tensor in the standard basis. Use it whenever a two-strand pure tensor of standard basis
  vectors is pushed through `PiTensorProduct.map` and the result is wanted coefficientwise.
-/

public section

namespace TauCeti

/-- A sum over the functions `Fin 2 → ι` is a double sum. -/
theorem sum_pi_fin_two {ι M : Type*} [Fintype ι] [AddCommMonoid M] (f : ι → ι → M) :
    ∑ r : Fin 2 → ι, f (r 0) (r 1) = ∑ p : ι, ∑ q : ι, f p q :=
  Eq.trans
    (Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => ι) _
      (fun pq : ι × ι => f pq.1 pq.2) fun _ => rfl)
    (Fintype.sum_prod_type' f)

/-- A pure tensor on two strands, written in `![·, ·]` form. -/
theorem tprod_fin_two {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (v : Fin 2 → M) :
    PiTensorProduct.tprod R v = PiTensorProduct.tprod R ![v 0, v 1] := by
  congr 1
  funext i
  fin_cases i <;> simp

end TauCeti

namespace Matrix

/-- Applying a matrix `A` in both strands re-expands a pure tensor of standard basis vectors back
in the standard basis: the coefficient of `Pi.single p 1 ⊗ Pi.single q 1` is `A p x * A q y`. -/
theorem piTensorProductMap_tprod_single {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [CommSemiring R] (A : Matrix κ ι R) (x y : ι) :
    PiTensorProduct.map (fun _ : Fin 2 => Matrix.mulVecLin A)
        (PiTensorProduct.tprod R ![Pi.single x (1 : R), Pi.single y (1 : R)]) =
      ∑ p : κ, ∑ q : κ, (A p x * A q y) •
        PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)] := by
  have hcol : ∀ z : ι, A *ᵥ Pi.single z (1 : R) = ∑ p : κ, A p z • Pi.single p (1 : R) := by
    intro z
    rw [Matrix.mulVec_single_one, ← (Pi.basisFun R κ).sum_repr (A.col z)]
    simp [Matrix.col_apply]
  have hfun : (fun i : Fin 2 =>
      Matrix.mulVecLin A (![Pi.single x (1 : R), Pi.single y (1 : R)] i)) =
      fun i : Fin 2 => ∑ p : κ, A p (![x, y] i) • Pi.single p (1 : R) := by
    funext i
    fin_cases i <;> simp [hcol]
  rw [PiTensorProduct.map_tprod, hfun,
    MultilinearMap.map_sum (PiTensorProduct.tprod R)
      (g := fun i : Fin 2 => fun p : κ => A p (![x, y] i) • Pi.single p (1 : R)),
    ← TauCeti.sum_pi_fin_two fun p q => (A p x * A q y) •
      PiTensorProduct.tprod R ![Pi.single p (1 : R), Pi.single q (1 : R)]]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : PiTensorProduct.tprod R (fun i : Fin 2 => Pi.single (r i) (1 : R))
      = PiTensorProduct.tprod R ![Pi.single (r 0) (1 : R), Pi.single (r 1) (1 : R)] :=
    TauCeti.tprod_fin_two _
  rw [MultilinearMap.map_smul_univ, hr, Fin.prod_univ_two]
  simp

end Matrix
