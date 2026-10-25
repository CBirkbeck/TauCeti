/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.TensorProduct.Symmetric
public import TauCeti.Algebra.Lie.Weights.Basis
public import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
public import TauCeti.Algebra.Lie.GeneralLinear.Finrank
public import TauCeti.LinearAlgebra.SymmetricPower.Basis
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Four weight diagrams for sl₃

The diagonal trace-zero subalgebra is proved to be a Cartan subalgebra. Its coordinate weights
`εᵢ` give explicit formal characters and their supports for the standard module, its dual,
the adjoint module, and the native symmetric-square quotient. The adjoint zero coefficient is two;
the dimensions are three, three, eight, and six.

Coordinates are evaluations on the two simple coroots. The weights `ε₀` and `−ε₂` have
coordinates
`(1, 0)` and `(0, 1)`, the usual fundamental weights for upper-triangular positive roots.
The coordinate map is injective. The displayed adjoint roots form the usual hexagon, and the
six symmetric-square weights are the unordered pairwise sums of the standard weights.

Characters are computed from actual eigenvector bases. The adjoint calculation uses the exact
trace sequence of matrix modules. The symmetric-square calculation uses the canonical Lie-module
comparison with symmetric tensors, whose basis comes from the symmetric-power quotient.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 12.
-/

public section

open scoped TensorProduct

open LieAlgebra LieModule Matrix

private theorem support_sum_single_one {ι α : Type*} [Fintype ι] (f : ι → α) :
    ((∑ i, AddMonoidAlgebra.single (f i) (1 : ℤ)).coeff.support : Set α) =
      Set.range f := by
  classical
  ext a
  simp [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, Finset.sum_boole]

namespace TauCeti.Sl3

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type) [Field K]

/-- The diagonal trace-zero matrices in the standard matrix Lie algebra `sl₃`. -/
abbrev cartan := (diagonalCartan K (Fin 3)).comap (SpecialLinear.sl (Fin 3) K).incl

/-- A trace-zero matrix belongs to the diagonal subalgebra exactly when it is diagonal. -/
@[simp]
theorem mem_cartan_iff_isDiag (A : SpecialLinear.sl (Fin 3) K) :
    A ∈ cartan K ↔ A.val.IsDiag := by
  simp only [cartan, LieSubalgebra.mem_comap, LieSubalgebra.coe_incl,
    mem_diagonalCartan_iff_isDiag]

private theorem isDiag (A : cartan K) : A.val.val.IsDiag :=
  mem_diagonalCartan_iff_isDiag.mp A.property

instance : IsLieAbelian (cartan K) where
  trivial A B := Subtype.ext (Subtype.ext (lie_eq_zero_of_isDiag (isDiag K A) (isDiag K B)))

/-- The diagonal difference `Eᵢᵢ − Eⱼⱼ` in the diagonal trace-zero subalgebra. -/
def diagonalElement (i j : Fin 3) : cartan K :=
  ⟨SpecialLinear.singleSubSingle i j (1 : K), by
    simp only [cartan, LieSubalgebra.mem_comap, LieSubalgebra.coe_incl,
      mem_diagonalCartan_iff_isDiag]
    rw [SpecialLinear.val_singleSubSingle]
    exact mem_diagonalCartan_iff_isDiag.mp ((diagonalCartan K (Fin 3)).sub_mem
      (single_self_mem_diagonalCartan i 1) (single_self_mem_diagonalCartan j 1))⟩

/-- The underlying matrix of a diagonal difference is `Eᵢᵢ − Eⱼⱼ`. -/
@[simp]
theorem diagonalElement_val (i j : Fin 3) :
    (diagonalElement K i j).val.val = Matrix.single i i (1 : K) - Matrix.single j j 1 := by
  simp only [diagonalElement, SpecialLinear.val_singleSubSingle]

private theorem diagonal_normalizer [CharZero K] : (cartan K).normalizer = cartan K := by
  refine le_antisymm (fun X hX => ?_) (cartan K).le_normalizer
  simp only [cartan, LieSubalgebra.mem_comap, LieSubalgebra.coe_incl,
    mem_diagonalCartan_iff_isDiag]
  intro i j hij
  have h := (LieSubalgebra.mem_normalizer_iff _ X).mp hX (diagonalElement K i j).val
    (diagonalElement K i j).property
  have he := (isDiag K ⟨_, h⟩) hij
  -- Unwrap the nested subalgebra brackets to read their matrix coefficient.
  change ⁅X.val, (diagonalElement K i j).val.val⁆ i j = 0 at he
  have heq : ⁅X.val, (diagonalElement K i j).val.val⁆ i j = -(2 : K) * X.val i j := by
    simp [diagonalElement, SpecialLinear.val_singleSubSingle, LieRing.of_associative_ring_bracket,
      Matrix.mul_sub, Matrix.sub_mul, hij, Ne.symm hij]
    ring
  rw [heq, mul_eq_zero] at he
  exact he.resolve_left (neg_ne_zero.mpr (by norm_num))

instance [CharZero K] : (cartan K).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := diagonal_normalizer K

/-- The coordinate weight that reads the ith diagonal entry. -/
def epsilon (i : Fin 3) : Module.Dual K (cartan K) where
  toFun A := A.val.val i i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A coordinate weight evaluates to the corresponding diagonal entry. -/
@[simp] theorem epsilon_apply (i : Fin 3) (A : cartan K) : epsilon K i A = A.val.val i i := by
  unfold epsilon
  rfl

private theorem weight_basis (i : Fin 3) (A : cartan K) :
    ⁅A, Pi.basisFun K (Fin 3) i⁆ = epsilon K i A • Pi.basisFun K (Fin 3) i := by
  simp only [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply, Pi.basisFun_apply,
    epsilon_apply]
  ext j
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst j
    simp only [ite_true]
  · rw [ite_eq_right h]
    exact isDiag K A h

/-- The standard three-dimensional module has weights `ε₀`, `ε₁`, and `ε₂`. -/
theorem formalCharacter_standard : formalCharacter K (cartan K) (Fin 3 → K) =
    ∑ i, AddMonoidAlgebra.single (epsilon K i) (1 : ℤ) :=
  (Pi.basisFun K (Fin 3)).formalCharacter_eq_sum_single_of_weight_basis (weight_basis K)

private theorem dual_weight_basis (i : Fin 3) (A : cartan K) :
    ⁅A, (Pi.basisFun K (Fin 3)).dualBasis i⁆ =
      (-epsilon K i) A • (Pi.basisFun K (Fin 3)).dualBasis i := by
  apply (Pi.basisFun K (Fin 3)).ext
  intro j
  simp only [Module.Dual.lie_apply, weight_basis, map_smul, LinearMap.smul_apply,
    Module.Basis.dualBasis_apply_self, LinearMap.neg_apply]
  by_cases h : i = j
  · subst j
    simp only [ite_true, smul_eq_mul, mul_one]
  · simp only [Ne.symm h, ite_false, smul_zero, neg_zero]

/-- The dual standard module has the negatives of the three coordinate weights. -/
theorem formalCharacter_dual : formalCharacter K (cartan K) (Module.Dual K (Fin 3 → K)) =
    ∑ i, AddMonoidAlgebra.single (-epsilon K i) (1 : ℤ) :=
  (Pi.basisFun K (Fin 3)).dualBasis.formalCharacter_eq_sum_single_of_weight_basis
    (dual_weight_basis K)

private theorem matrix_weight_basis (ij : Fin 3 × Fin 3) (A : cartan K) :
    ⁅A, Matrix.stdBasis K (Fin 3) (Fin 3) ij⁆ =
      (epsilon K ij.1 - epsilon K ij.2) A • Matrix.stdBasis K (Fin 3) (Fin 3) ij := by
  rcases ij with ⟨i, j⟩
  simp only [Matrix.stdBasis_eq_single, LieSubalgebra.coe_bracket_of_module,
    LinearMap.sub_apply, epsilon_apply]
  exact lie_single_of_mem_diagonalCartan A.property i j 1

private theorem matrix_character : formalCharacter K (cartan K) (Matrix (Fin 3) (Fin 3) K) =
    ∑ ij : Fin 3 × Fin 3, AddMonoidAlgebra.single (epsilon K ij.1 - epsilon K ij.2) (1 : ℤ) :=
  (Matrix.stdBasis K (Fin 3) (Fin 3)).formalCharacter_eq_sum_single_of_weight_basis
    (matrix_weight_basis K)

private abbrev scalar := TrivialLieModule K (cartan K) K

private instance : FiniteDimensional K (scalar K) :=
  Module.Finite.of_injective (TrivialLieModule.equiv K (cartan K) K).toLinearMap
    (TrivialLieModule.equiv K (cartan K) K).injective

private def traceHom : Matrix (Fin 3) (Fin 3) K →ₗ⁅K, cartan K⁆ scalar K where
  toLinearMap := (TrivialLieModule.equiv K (cartan K) K).symm.toLinearMap.comp
    (Matrix.traceLinearMap (Fin 3) K K)
  map_lie' {A B} := by
    -- The trace target carries the zero Lie action.
    change (TrivialLieModule.equiv K (cartan K) K).symm (Matrix.trace ⁅A.val.val, B⁆) = _
    rw [matrix_trace_commutator_zero, map_zero, trivial_lie_zero]

private def inclusion :
    SpecialLinear.sl (Fin 3) K →ₗ⁅K, cartan K⁆ Matrix (Fin 3) (Fin 3) K where
  toLinearMap := (SpecialLinear.sl (Fin 3) K).incl.toLinearMap
  map_lie' := rfl

private theorem matrix_character_eq_sl_add [IsAlgClosed K] :
    formalCharacter K (cartan K) (Matrix (Fin 3) (Fin 3) K) =
      formalCharacter K (cartan K) (SpecialLinear.sl (Fin 3) K) +
        formalCharacter K (cartan K) (scalar K) := by
  apply formalCharacter_eq_add_of_exact (inclusion K) (traceHom K)
  · intro B
    -- The trace target carries the zero Lie action.
    change (TrivialLieModule.equiv K (cartan K) K).symm B.trace = 0 ↔
      ∃ A : SpecialLinear.sl (Fin 3) K, A.val = B
    rw [LinearEquiv.map_eq_zero_iff]
    exact ⟨fun h => ⟨⟨B, SpecialLinear.mem_sl_iff.mpr h⟩, rfl⟩,
      fun ⟨A, h⟩ => h ▸ SpecialLinear.mem_sl_iff.mp A.property⟩
  · exact Subtype.val_injective
  · intro a
    refine ⟨Matrix.single 0 0 ((TrivialLieModule.equiv K (cartan K) K) a), ?_⟩
    apply (TrivialLieModule.equiv K (cartan K) K).injective
    simp [traceHom]

private noncomputable def scalarBasis : Module.Basis (Fin 1) K (scalar K) :=
  (Module.Basis.singleton (Fin 1) K).map (TrivialLieModule.equiv K (cartan K) K).symm

private theorem scalar_weight_basis (i : Fin 1) (A : cartan K) :
    ⁅A, scalarBasis K i⁆ = (0 : Module.Dual K (cartan K)) A • scalarBasis K i := by
  simp only [trivial_lie_zero, LinearMap.zero_apply, zero_smul]

private theorem scalar_character : formalCharacter K (cartan K) (scalar K) =
    AddMonoidAlgebra.single 0 (1 : ℤ) := by
  have h := (scalarBasis K).formalCharacter_eq_sum_single_of_weight_basis (scalar_weight_basis K)
  simpa using h

private theorem adjoint_character [IsAlgClosed K] :
    formalCharacter K (cartan K) (SpecialLinear.sl (Fin 3) K) =
      (∑ ij : Fin 3 × Fin 3,
        AddMonoidAlgebra.single (epsilon K ij.1 - epsilon K ij.2) (1 : ℤ)) -
        AddMonoidAlgebra.single 0 (1 : ℤ) := by
  have h := matrix_character K
  rw [matrix_character_eq_sl_add, scalar_character] at h
  exact eq_sub_iff_add_eq.mpr h

/-- The eight adjoint weights, with zero repeated twice and each of the six roots once. -/
def adjointWeight : Fin 8 → Module.Dual K (cartan K) :=
  ![0, 0, epsilon K 0 - epsilon K 1, epsilon K 0 - epsilon K 2,
    epsilon K 1 - epsilon K 0, epsilon K 1 - epsilon K 2,
    epsilon K 2 - epsilon K 0, epsilon K 2 - epsilon K 1]

/-- The adjoint character has its six root weights and the zero weight twice. -/
theorem formalCharacter_adjoint [IsAlgClosed K] :
    formalCharacter K (cartan K) (SpecialLinear.sl (Fin 3) K) =
      ∑ i, AddMonoidAlgebra.single (adjointWeight K i) (1 : ℤ) := by
  rw [adjoint_character]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, sub_self]
  simp [adjointWeight, Fin.sum_univ_succ]
  abel

/-- The support of the adjoint character is the six roots together with zero. -/
theorem support_formalCharacter_adjoint [IsAlgClosed K] :
    ((formalCharacter K (cartan K) (SpecialLinear.sl (Fin 3) K)).coeff.support :
      Set (Module.Dual K (cartan K))) = Set.range (adjointWeight K) := by
  rw [formalCharacter_adjoint, support_sum_single_one]

/-- Coordinate weights on a diagonal difference are the differences of Kronecker deltas. -/
theorem epsilon_diagonalElement (i j k : Fin 3) :
    epsilon K i (diagonalElement K j k) =
      (if i = j then 1 else 0) - (if i = k then 1 else 0) := by
  simp [epsilon_apply, diagonalElement, SpecialLinear.val_singleSubSingle, Matrix.single_apply,
    eq_comm]

/-- The zero-weight coefficient of the actual adjoint representation is two. -/
theorem formalCharacter_adjoint_zero [IsAlgClosed K] [CharZero K] :
    (formalCharacter K (cartan K) (SpecialLinear.sl (Fin 3) K)).coeff 0 = 2 := by
  have hne (i j : Fin 3) (hij : i ≠ j) : epsilon K i - epsilon K j ≠ 0 := by
    intro h
    have he := congrArg (fun f : Module.Dual K (cartan K) => f (diagonalElement K i j)) h
    simp only [LinearMap.sub_apply, epsilon_diagonalElement, LinearMap.zero_apply,
      ite_eq_right hij, ite_eq_right (Ne.symm hij)] at he
    norm_num at he
  rw [formalCharacter_adjoint]
  simp [adjointWeight, Fin.sum_univ_succ, AddMonoidAlgebra.coeff_single, hne]

private def symmetricIndex : Fin 6 → Sym (Fin 3) 2 :=
  ![TauCeti.Sym.ofFn ![0, 0], TauCeti.Sym.ofFn ![0, 1], TauCeti.Sym.ofFn ![0, 2],
    TauCeti.Sym.ofFn ![1, 1], TauCeti.Sym.ofFn ![1, 2], TauCeti.Sym.ofFn ![2, 2]]

private theorem symmetricIndex_counts (i : Fin 6) :
    ((symmetricIndex i : Multiset (Fin 3)).count 0,
      (symmetricIndex i : Multiset (Fin 3)).count 1) =
      (![(2, 0), (1, 1), (1, 0), (0, 2), (0, 1), (0, 0)] : Fin 6 → ℕ × ℕ) i := by
  fin_cases i <;> simp [symmetricIndex, TauCeti.Sym.coe_ofFn, List.ofFn_succ]

private theorem symmetricIndex_bijective : Function.Bijective symmetricIndex := by
  apply (Fintype.bijective_iff_injective_and_card symmetricIndex).mpr
  constructor
  · intro i j hij
    have h : Function.Injective
        (![(2, 0), (1, 1), (1, 0), (0, 2), (0, 1), (0, 0)] : Fin 6 → ℕ × ℕ) := by decide
    apply h
    rw [← symmetricIndex_counts, ← symmetricIndex_counts, hij]
  · norm_num [Sym.card_sym_eq_multichoose, Nat.multichoose]

/-- The six weights of the symmetric square of the standard module. -/
def symmetricWeight : Fin 6 → Module.Dual K (cartan K) :=
  ![epsilon K 0 + epsilon K 0, epsilon K 0 + epsilon K 1,
    epsilon K 0 + epsilon K 2, epsilon K 1 + epsilon K 1,
    epsilon K 1 + epsilon K 2, epsilon K 2 + epsilon K 2]

private theorem symmetricIndex_weight (i : Fin 6) :
    (((symmetricIndex i : Multiset (Fin 3)).map (epsilon K)).sum) =
      symmetricWeight K i := by
  fin_cases i <;> simp [symmetricIndex, symmetricWeight, TauCeti.Sym.coe_ofFn,
    List.ofFn_succ]

/-- Coordinates of a weight on the two simple coroots. -/
def weightCoordinates (μ : Module.Dual K (cartan K)) : K × K :=
  (μ (diagonalElement K 0 1), μ (diagonalElement K 1 2))

/-- Weight coordinates are evaluations on the two simple coroots. -/
theorem weightCoordinates_def (μ : Module.Dual K (cartan K)) :
    weightCoordinates K μ = (μ (diagonalElement K 0 1), μ (diagonalElement K 1 2)) := by
  unfold weightCoordinates
  rfl

/-- Every trace-zero diagonal matrix is a linear combination of the two simple coroots. -/
theorem diagonal_decomposition (A : cartan K) :
    A = A.val.val 0 0 • diagonalElement K 0 1 -
      A.val.val 2 2 • diagonalElement K 1 2 := by
  have hoff (i j : Fin 3) (hij : i ≠ j) : A.val.val i j = 0 := isDiag K A hij
  have ht := SpecialLinear.mem_sl_iff.mp A.val.property
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three] at ht
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalElement, SpecialLinear.val_singleSubSingle, hoff]
  linear_combination ht

/-- The simple-coroot coordinates determine a weight on the diagonal Cartan. -/
theorem weightCoordinates_injective : Function.Injective (weightCoordinates K) := by
  intro f g h
  have h0 : f (diagonalElement K 0 1) = g (diagonalElement K 0 1) := congrArg Prod.fst h
  have h1 : f (diagonalElement K 1 2) = g (diagonalElement K 1 2) := congrArg Prod.snd h
  ext A
  calc
    f A = f (A.val.val 0 0 • diagonalElement K 0 1 -
        A.val.val 2 2 • diagonalElement K 1 2) := congrArg f (diagonal_decomposition K A)
    _ = g (A.val.val 0 0 • diagonalElement K 0 1 -
        A.val.val 2 2 • diagonalElement K 1 2) := by simp only [map_sub, map_smul, h0, h1]
    _ = g A := congrArg g (diagonal_decomposition K A).symm

/-- The standard weight diagram in fundamental-weight coordinates. -/
theorem standard_weightCoordinates (i : Fin 3) :
    weightCoordinates K (epsilon K i) = (![(1, 0), (-1, 1), (0, -1)] : Fin 3 → K × K) i := by
  fin_cases i <;> simp only [weightCoordinates, epsilon_diagonalElement] <;> norm_num

/-- The dual standard weight diagram in fundamental-weight coordinates. -/
theorem dual_weightCoordinates (i : Fin 3) :
    weightCoordinates K (-epsilon K i) = (![(-1, 0), (1, -1), (0, 1)] : Fin 3 → K × K) i := by
  fin_cases i <;> simp only [weightCoordinates, LinearMap.neg_apply,
    epsilon_diagonalElement] <;> norm_num

/-- The adjoint diagram is a hexagon with its central weight repeated twice. -/
theorem adjoint_weightCoordinates (i : Fin 8) :
    weightCoordinates K (adjointWeight K i) =
      (![(0, 0), (0, 0), (2, -1), (1, 1), (-2, 1), (-1, 2), (-1, -1), (1, -2)] :
        Fin 8 → K × K) i := by
  fin_cases i <;> norm_num [adjointWeight, weightCoordinates, diagonalElement,
    SpecialLinear.val_singleSubSingle, Matrix.single_apply]

/-- The symmetric-square diagram has the six displayed fundamental-weight coordinates. -/
theorem symmetric_weightCoordinates (i : Fin 6) :
    weightCoordinates K (symmetricWeight K i) =
      (![(2, 0), (0, 1), (1, -1), (-2, 2), (-1, 0), (0, -2)] : Fin 6 → K × K) i := by
  fin_cases i <;> norm_num [symmetricWeight, weightCoordinates, diagonalElement,
    SpecialLinear.val_singleSubSingle, Matrix.single_apply]

/-- The standard module has dimension three. -/
example : Module.finrank K (Fin 3 → K) = 3 := by simp

/-- The dual standard module has dimension three. -/
example : Module.finrank K (Module.Dual K (Fin 3 → K)) = 3 := by simp

/-- The adjoint module has dimension eight. -/
example : Module.finrank K (SpecialLinear.sl (Fin 3) K) = 8 := by
  norm_num [TauCeti.finrank_sl]

section SymmetricSquare
variable [Invertible (2 : K)]

/- The direct tensor action is definitionally the restricted matrix action. Selecting it here
keeps the weight-basis computation on the tensor-product API. -/
local instance (priority := 2000) :
    LieRingModule (cartan K) ((Fin 3 → K) ⊗[K] (Fin 3 → K)) :=
  TensorProduct.LieModule.lieRingModule

local instance (priority := 2000) :
    LieModule K (cartan K) ((Fin 3 → K) ⊗[K] (Fin 3 → K)) :=
  TensorProduct.LieModule.lieModule

local instance (priority := 2000) :
    LieRingModule (cartan K) (symmetricTensors K (Fin 3 → K)) :=
  symmetricTensorsLieRingModule

local instance (priority := 2000) :
    LieModule K (cartan K) (symmetricTensors K (Fin 3 → K)) :=
  symmetricTensorsLieModule

private noncomputable def symmetricBasis :
    Module.Basis (Sym (Fin 3) 2) K (symmetricTensors K (Fin 3 → K)) :=
  ((Pi.basisFun K (Fin 3)).symmetricPower 2).map
    (symmetricTensorsEquivSymmetricPower K (Fin 3 → K)).symm

private theorem symmetric_weight_basis (s : Sym (Fin 3) 2) (A : cartan K) :
    ⁅A, symmetricBasis K s⁆ =
      (((s : Multiset (Fin 3)).map (epsilon K)).sum) A • symmetricBasis K s := by
  obtain ⟨p, rfl⟩ := TauCeti.Sym.ofFn_surjective s
  apply Subtype.ext
  -- The subtype action is the restriction of the tensor-product action.
  change ⁅A, (symmetricBasis K (TauCeti.Sym.ofFn p)).val⁆ =
    (((TauCeti.Sym.ofFn p : Multiset (Fin 3)).map (epsilon K)).sum) A •
      (symmetricBasis K (TauCeti.Sym.ofFn p)).val
  have hs : (symmetricBasis K (TauCeti.Sym.ofFn p)).val =
      ⅟(2 : K) • (Pi.basisFun K (Fin 3) (p 0) ⊗ₜ[K] Pi.basisFun K (Fin 3) (p 1) +
        Pi.basisFun K (Fin 3) (p 1) ⊗ₜ[K] Pi.basisFun K (Fin 3) (p 0)) := by
    rw [symmetricBasis, Module.Basis.map_apply, Module.Basis.symmetricPower_apply,
      SymmetricPower.tprodOfSym_ofFn]
    have hp : (fun i => Pi.basisFun K (Fin 3) (p i)) =
        ![Pi.basisFun K (Fin 3) (p 0), Pi.basisFun K (Fin 3) (p 1)] := by
      ext i
      fin_cases i <;> rfl
    rw [hp]
    exact coe_symmetricTensorsEquivSymmetricPower_symm_tprod K (Fin 3 → K) _ _
  rw [hs]
  -- Identify the restricted and directly constructed tensor Lie actions.
  erw [LieModule.lie_smul (R := K) (L := cartan K)
    (M := (Fin 3 → K) ⊗[K] (Fin 3 → K)), lie_add]
  simp only [TensorProduct.LieModule.lie_tmul_right, weight_basis,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, TauCeti.Sym.coe_ofFn,
    Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn,
    Fin.sum_univ_two, LinearMap.add_apply, Function.comp_apply]
  module

private theorem symmetric_character :
    formalCharacter K (cartan K) (symmetricTensors K (Fin 3 → K)) =
      ∑ s : Sym (Fin 3) 2,
        AddMonoidAlgebra.single (((s : Multiset (Fin 3)).map (epsilon K)).sum) (1 : ℤ) :=
  (symmetricBasis K).formalCharacter_eq_sum_single_of_weight_basis (symmetric_weight_basis K)

private theorem symmetric_character_six :
    formalCharacter K (cartan K) (symmetricTensors K (Fin 3 → K)) =
      ∑ i, AddMonoidAlgebra.single (symmetricWeight K i) (1 : ℤ) := by
  rw [symmetric_character]
  symm
  apply Fintype.sum_bijective symmetricIndex symmetricIndex_bijective
  intro i
  rw [symmetricIndex_weight]

/-- The symmetric square has dimension six. -/
example : Module.finrank K (symmetricTensors K (Fin 3 → K)) = 6 := by
  rw [(symmetricTensorsEquivSymmetricPower K (Fin 3 → K)).finrank_eq,
    SymmetricPower.finrank_eq]
  norm_num [Nat.multichoose]

/-- The actual symmetric-power quotient has the six pairwise sums of standard weights. -/
theorem formalCharacter_symmetricPower :
    formalCharacter K (cartan K) (Sym[K]^2 (Fin 3 → K)) =
      ∑ i, AddMonoidAlgebra.single (symmetricWeight K i) (1 : ℤ) :=
  (formalCharacter_congr (symmetricTensorsLieEquivSymmetricPower
    (R := K) (L := cartan K) (M := Fin 3 → K))).symm.trans (symmetric_character_six K)

/-- The support of the actual symmetric-square character is its six weights. -/
theorem support_formalCharacter_symmetricPower :
    ((formalCharacter K (cartan K) (Sym[K]^2 (Fin 3 → K))).coeff.support :
      Set (Module.Dual K (cartan K))) = Set.range (symmetricWeight K) := by
  rw [formalCharacter_symmetricPower, support_sum_single_one]

end SymmetricSquare

/-- The standard character has exactly the three coordinate weights in its support. -/
theorem support_formalCharacter_standard :
    ((formalCharacter K (cartan K) (Fin 3 → K)).coeff.support :
      Set (Module.Dual K (cartan K))) = Set.range (epsilon K) := by
  rw [formalCharacter_standard, support_sum_single_one]

/-- The dual standard character is supported on the negatives of the coordinate weights. -/
theorem support_formalCharacter_dual :
    ((formalCharacter K (cartan K) (Module.Dual K (Fin 3 → K))).coeff.support :
      Set (Module.Dual K (cartan K))) = Set.range (fun i => -epsilon K i) := by
  rw [formalCharacter_dual, support_sum_single_one]

end TauCeti.Sl3
