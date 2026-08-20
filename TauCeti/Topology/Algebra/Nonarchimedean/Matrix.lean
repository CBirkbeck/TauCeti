/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Nakayama for a matrix with topologically nilpotent entries

Over a complete nonarchimedean ring, `1 - B` is invertible as soon as every entry of `B` is
topologically nilpotent, and consequently a family satisfying `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` vanishes.

The module the family lives in carries **no topology**: the whole topological input is the
invertibility of `1 - B`, after which the conclusion is linear algebra. That is what makes this
usable where the module is an abstract subquotient.

## Main results

* `TauCeti.Huber.isTopologicallyNilpotent_one_sub_det_one_sub`: `1 - det (1 - B)` is topologically
  nilpotent.
* `TauCeti.Huber.isUnit_one_sub_of_isTopologicallyNilpotent_entries`: hence `1 - B` is a unit.
* `TauCeti.Huber.eq_zero_of_forall_eq_sum_smul`: a family fixed by such a `B` is zero.

## References

* [S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*][bosch_guntzer_remmert],
  §3.7.2/1, where this is the algebraic engine behind closedness of finitely generated submodules.
-/

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsUniformAddGroup A] [NonarchimedeanRing A]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The entries of `B`, viewed in `A°`. Topologically nilpotent elements are power-bounded, so
this is well defined, and it is what puts `B` inside the ideal `A°°` where the determinant
computation happens. -/
private def toPowerBoundedMatrix (B : Matrix n n A)
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) : Matrix n n (powerBoundedSubring A) :=
  Matrix.of fun i j ↦ ⟨B i j, mem_powerBoundedSubring.mpr
    (IsPowerBounded.of_isTopologicallyNilpotent (hB i j))⟩

omit [T2Space A] [CompleteSpace A] [IsUniformAddGroup A] in
/-- **The determinant of `1 - B` is `1` up to a topologically nilpotent error.** Every entry of
`B` lies in the ideal `A°°` of `A°`, so `1 - B` reduces to the identity modulo that ideal and its
determinant reduces to `1`. -/
theorem isTopologicallyNilpotent_one_sub_det_one_sub {B : Matrix n n A}
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) :
    IsTopologicallyNilpotent (1 - (1 - B).det) := by
  set I := topologicallyNilpotentIdeal A with hI
  set B' := toPowerBoundedMatrix B hB with hB'
  -- Modulo `A°°` the matrix `1 - B'` is the identity, so its determinant is `1`.
  have hmap : (Ideal.Quotient.mk I).mapMatrix (1 - B') = 1 := by
    ext i j
    have hzero : Ideal.Quotient.mk I (B' i j) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (mem_topologicallyNilpotentIdeal.mpr (hB i j))
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, hzero,
      Matrix.one_apply, apply_ite (Ideal.Quotient.mk I)]
  have hmod : Ideal.Quotient.mk I (1 - B').det = 1 := by
    rw [RingHom.map_det, hmap, Matrix.det_one]
  -- So `1 - det (1 - B')` lies in `A°°`, and `A°°` is topological nilpotence.
  have hmem : (1 : powerBoundedSubring A) - (1 - B').det ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hmod, map_one, sub_self]
  have hcoemap : (powerBoundedSubring A).subtype.mapMatrix (1 - B') = 1 - B := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
      hB', toPowerBoundedMatrix, apply_ite ((↑) : powerBoundedSubring A → A)]
  have hcoe : ((1 - B').det : A) = (1 - B).det := by
    rw [show (((1 - B').det : powerBoundedSubring A) : A)
      = (powerBoundedSubring A).subtype (1 - B').det from rfl,
      RingHom.map_det, hcoemap]
  simpa [hcoe] using (mem_topologicallyNilpotentIdeal.mp hmem)

/-- **`1 - B` is invertible when every entry of `B` is topologically nilpotent.** The determinant
is `1` minus a topologically nilpotent element, hence a unit by the geometric series, and a square
matrix over a commutative ring is a unit exactly when its determinant is. -/
theorem isUnit_one_sub_of_isTopologicallyNilpotent_entries {B : Matrix n n A}
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) : IsUnit (1 - B) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simpa using (isTopologicallyNilpotent_one_sub_det_one_sub hB).isUnit_one_sub

omit [DecidableEq n] in
/-- **Nakayama for topologically nilpotent entries.** If every entry of `B` is topologically
nilpotent and `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` for every `i`, then every `yᵢ` vanishes.

`P` carries no topology: `1 - B` is a unit by the statement above, and applying its inverse to the
relation `∑ⱼ (1 - B)ᵢⱼ • yⱼ = 0` is pure linear algebra. -/
theorem eq_zero_of_forall_eq_sum_smul {P : Type*} [AddCommGroup P] [Module A P]
    {B : Matrix n n A} (hB : ∀ i j, IsTopologicallyNilpotent (B i j))
    {y : n → P} (hy : ∀ i, y i = ∑ j, B i j • y j) (k : n) : y k = 0 := by
  classical
  obtain ⟨U, hU⟩ := isUnit_one_sub_of_isTopologicallyNilpotent_entries hB
  -- The relation says `(1 - B)` kills `y` in the sense of the matrix action on `n → P`.
  have hrel : ∀ i, ∑ j, (1 - B) i j • y j = 0 := by
    intro i
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.one_apply,
      ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, one_smul]
    rw [← hy i, sub_self]
  -- Apply the inverse: `y k = ∑ⱼ (U⁻¹ (1 - B))ₖⱼ • yⱼ`, and the inner sums all vanish.
  have hinv : (↑U⁻¹ : Matrix n n A) * (1 - B) = 1 := by rw [← hU]; exact U.inv_mul
  calc y k = ∑ j, (1 : Matrix n n A) k j • y j := by
        simp [Matrix.one_apply, ite_smul]
    _ = ∑ j, ((↑U⁻¹ : Matrix n n A) * (1 - B)) k j • y j := by rw [hinv]
    _ = ∑ i, (↑U⁻¹ : Matrix n n A) k i • ∑ j, (1 - B) i j • y j := by
        simp_rw [Matrix.mul_apply, Finset.sum_smul, ← smul_smul, Finset.smul_sum]
        exact Finset.sum_comm
    _ = 0 := by simp only [hrel, smul_zero, Finset.sum_const_zero]

end TauCeti.Huber
