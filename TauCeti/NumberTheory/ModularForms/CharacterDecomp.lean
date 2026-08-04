/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.MulChar.Duality
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector
public import TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# Character decomposition of modular forms for `Γ₁(N)`

For each character `χ : (ZMod N)ˣ →* ℂˣ`, the nebentypus character space
`modFormCharSpace k χ` and its cusp-form analogue `cuspFormCharSpace k χ` are cut out in
`TauCeti/NumberTheory/ModularForms/DiamondOperators.lean` as simultaneous
diamond-eigenspaces. This file proves the internal direct sum decomposition

  `M_k(Γ₁(N)) = ⨁_{χ} M_k(Γ₁(N), χ)`

together with its cusp-form analogues and the refinement to diamond-invariant
submodules, by simultaneous diagonalization of the commuting finite-order diamond
operators (`TauCeti/LinearAlgebra/Eigenspace/JointEigenvector.lean`).

Finite-dimensionality of `M_k(Γ₁(N))` is **not** proved here: the results that need it
take it as an instance hypothesis, to be discharged once the roadmap's dimension-formula
milestones land. Cusp-form finite-dimensionality follows from the modular-form one
(`CuspForm.finiteDimensional_of_modularForm`).

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CharacterDecomp.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), realizing
Layer 0 of the ModularForms roadmap.

## Main results

* `iSup_modFormCharSpace_eq_top`: the character spaces span `M_k(Γ₁(N))`.
* `iSupIndep_modFormCharSpace`, `iSupIndep_cuspFormCharSpace`: the families are
  supremum-independent.
* `isInternal_modFormCharSpace`: the `DirectSum.IsInternal` statement.
* `iSup_inf_modFormCharSpace_of_invariant`, `iSup_inf_cuspFormCharSpace_of_invariant`:
  any diamond-invariant submodule is the supremum of its intersections with the
  character spaces, with finsupp-indexed corollaries
  `exists_finsupp_of_diamondOp_invariant`/`exists_finsupp_of_diamondOpCusp_invariant`.
* `endo_ext_of_mem_modFormCharSpace`: two endomorphisms agreeing on every character
  space are equal — the gluing principle for extending Hecke-operator identities proven
  per character space to the whole space.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.2
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups DirectSum

noncomputable section

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- Each diamond operator has finite order. -/
lemma diamondOpHom_isOfFinOrder (d : (ZMod N)ˣ) : IsOfFinOrder (diamondOpHom k d) :=
  (diamondOpHom k).isOfFinOrder (isOfFinOrder_of_finite d)

/-- Each diamond operator is a semisimple endomorphism. -/
lemma diamondOp_isSemisimple (d : (ZMod N)ˣ) : (diamondOpHom k d).IsSemisimple :=
  Module.End.isSemisimple_of_isOfFinOrder (diamondOpHom_isOfFinOrder d)

/-- The diamond operators pairwise commute. -/
lemma diamondOpHom_pairwise_commute :
    Pairwise fun d₁ d₂ : (ZMod N)ˣ ↦ Commute (diamondOpHom k d₁) (diamondOpHom k d₂) :=
  fun _ _ _ ↦ (Commute.all _ _).map (diamondOpHom k)

/-- The joint eigenspace indexed by a function `χ : (ZMod N)ˣ → ℂ`. When `χ` is
not the underlying function of a character `(ZMod N)ˣ →* ℂˣ`, this space is
`⊥`; otherwise it coincides with `modFormCharSpace k χ₀` for that character. -/
def jointDiamondEigenspace (k : ℤ) (χ : (ZMod N)ˣ → ℂ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, (diamondOpHom k d).eigenspace (χ d)

/-- `jointDiamondEigenspace` at the underlying function of a character agrees
with `modFormCharSpace`. -/
lemma jointDiamondEigenspace_eq_modFormCharSpace (χ₀ : (ZMod N)ˣ →* ℂˣ) :
    jointDiamondEigenspace k (fun d ↦ (χ₀ d : ℂ)) = modFormCharSpace k χ₀ := by
  ext f
  simp [jointDiamondEigenspace, Submodule.mem_iInf]

/-- If `jointDiamondEigenspace k χ ≠ ⊥`, then `χ` comes from a character, i.e.,
equals `(d ↦ (χ₀ d : ℂ))` for some `χ₀ : (ZMod N)ˣ →* ℂˣ`. -/
lemma exists_charHom_of_jointDiamondEigenspace_ne_bot {χ : (ZMod N)ˣ → ℂ}
    (hχ : jointDiamondEigenspace k χ ≠ ⊥) :
    ∃ χ₀ : (ZMod N)ˣ →* ℂˣ, (fun d ↦ ((χ₀ d) : ℂ)) = χ :=
  exists_charHom_of_iInf_eigenspace_ne_bot (ρ := diamondOpHom k) hχ

/-- **The character subspaces `modFormCharSpace k χ` span the whole space**:
modular forms for `Γ₁(N)` decompose into the span of nebentypus character
spaces, one for each character `(ZMod N)ˣ →* ℂˣ`. -/
theorem iSup_modFormCharSpace_eq_top (k : ℤ)
    [FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)] :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, modFormCharSpace k χ) =
    (⊤ : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have h_top_fun : (⨆ χ : (ZMod N)ˣ → ℂ, jointDiamondEigenspace k χ) = ⊤ :=
    iSup_iInf_eigenspace_eq_top_of_isSemisimple (diamondOpHom k) diamondOpHom_pairwise_commute
      diamondOp_isSemisimple
  refine le_antisymm le_top (h_top_fun ▸ iSup_le fun χ ↦ ?_)
  by_cases hχ : jointDiamondEigenspace k χ = ⊥
  · simp only [hχ, bot_le]
  · obtain ⟨χ₀, rfl⟩ := exists_charHom_of_jointDiamondEigenspace_ne_bot hχ
    rw [jointDiamondEigenspace_eq_modFormCharSpace]
    exact le_iSup (modFormCharSpace k) χ₀

/-- **The character subspaces form an independent family.** -/
theorem iSupIndep_modFormCharSpace (k : ℤ) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ ↦ modFormCharSpace (N := N) k χ) := by
  have h_indep_fun : iSupIndep (fun χ : (ZMod N)ˣ → ℂ ↦ jointDiamondEigenspace k χ) :=
    iSupIndep_iInf_eigenspace_of_isSemisimple (diamondOpHom k) diamondOpHom_pairwise_commute
      diamondOp_isSemisimple
  have h : iSupIndep (fun χ₀ : (ZMod N)ˣ →* ℂˣ ↦ jointDiamondEigenspace k
      fun d ↦ (χ₀ d : ℂ)) :=
    h_indep_fun.comp fun _ _ h ↦ MonoidHom.ext fun d ↦ Units.ext (congr_fun h d)
  simpa only [jointDiamondEigenspace_eq_modFormCharSpace] using h

/-- **Internal direct sum decomposition**: `M_k(Γ₁(N))` decomposes as the direct
sum of the nebentypus character spaces `modFormCharSpace k χ`. -/
theorem isInternal_modFormCharSpace (k : ℤ) [DecidableEq ((ZMod N)ˣ →* ℂˣ)]
    [FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)] :
    DirectSum.IsInternal (fun χ : (ZMod N)ˣ →* ℂˣ ↦ modFormCharSpace k χ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_modFormCharSpace k) (iSup_modFormCharSpace_eq_top k)

/-- The character group `(ZMod N)ˣ →* ℂˣ` is finite. -/
instance instFiniteCharHom : Finite ((ZMod N)ˣ →* ℂˣ) :=
  .of_equiv (MulChar (ZMod N) ℂ) MulChar.equivToUnitHom

/-- `Fintype` version of `instFiniteCharHom`, needed to state sums over the
character group at the statement level (`∑ χ : …`). -/
noncomputable instance instFintypeCharHom : Fintype ((ZMod N)ˣ →* ℂˣ) :=
  Fintype.ofFinite _

-- The forgetful linear injection of cusp forms into modular forms, used to transfer
-- finite-dimensionality; not public API.
private def cuspFormToModularForm : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm := f.toSlashInvariantForm
      holo' := f.holo'
      bdd_at_cusps' := fun hc g hg ↦ (f.zero_at_cusps' hc g hg).boundedAtFilter }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero N] in
private lemma cuspFormToModularForm_injective :
    Function.Injective (cuspFormToModularForm (N := N) (k := k)) :=
  fun _ _ hfg ↦ DFunLike.ext' (congr_arg (⇑) hfg)

/-- Finite-dimensionality of `S_k(Γ₁(N))` follows from finite-dimensionality of
`M_k(Γ₁(N))`, along the forgetful injection. -/
instance CuspForm.finiteDimensional_of_modularForm
    [FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)] :
    FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  FiniteDimensional.of_injective (cuspFormToModularForm (N := N) (k := k))
    cuspFormToModularForm_injective

/-- Each cusp-form diamond operator has finite order. -/
lemma diamondOpCuspHom_isOfFinOrder (d : (ZMod N)ˣ) : IsOfFinOrder (diamondOpCuspHom k d) :=
  (diamondOpCuspHom k).isOfFinOrder (isOfFinOrder_of_finite d)

/-- Each cusp-form diamond operator is semisimple. -/
lemma diamondOpCusp_isSemisimple (d : (ZMod N)ˣ) : (diamondOpCuspHom k d).IsSemisimple :=
  Module.End.isSemisimple_of_isOfFinOrder (diamondOpCuspHom_isOfFinOrder d)

/-- The cusp-form diamond operators pairwise commute. -/
lemma diamondOpCuspHom_pairwise_commute :
    Pairwise fun d₁ d₂ : (ZMod N)ˣ ↦
      Commute (diamondOpCuspHom k d₁) (diamondOpCuspHom k d₂) :=
  fun _ _ _ ↦ (Commute.all _ _).map (diamondOpCuspHom k)

/-- For each cusp-form diamond operator, the supremum of its eigenspaces is
the whole space. -/
lemma diamondOpCusp_iSup_eigenspace_eq_top
    [FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)] (d : (ZMod N)ˣ) :
    ⨆ μ : ℂ, (diamondOpCuspHom k d).eigenspace μ =
    (⊤ : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) :=
  (diamondOpCusp_isSemisimple d).iSup_eigenspace_eq_top

/-- For each diamond operator, the supremum of its eigenspaces is the whole
space. -/
lemma diamondOp_iSup_eigenspace_eq_top
    [FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)] (d : (ZMod N)ˣ) :
    ⨆ μ : ℂ, (diamondOpHom k d).eigenspace μ =
    (⊤ : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) :=
  (diamondOp_isSemisimple d).iSup_eigenspace_eq_top

/-- The joint cusp-form eigenspace indexed by an arbitrary function
`χ : (ZMod N)ˣ → ℂ`. For characters this coincides with
`cuspFormCharSpace`; for non-characters it is `⊥`. -/
def jointDiamondCuspEigenspace (k : ℤ) (χ : (ZMod N)ˣ → ℂ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, (diamondOpCuspHom k d).eigenspace (χ d)

/-- `jointDiamondCuspEigenspace` at the underlying function of a character
agrees with `cuspFormCharSpace`. -/
lemma jointDiamondCuspEigenspace_eq_cuspFormCharSpace (χ₀ : (ZMod N)ˣ →* ℂˣ) :
    jointDiamondCuspEigenspace k (fun d ↦ (χ₀ d : ℂ)) = cuspFormCharSpace k χ₀ := by
  ext f
  simp [jointDiamondCuspEigenspace, Submodule.mem_iInf]

/-- If `jointDiamondCuspEigenspace k χ ≠ ⊥`, then `χ` comes from a character. -/
lemma exists_charHom_of_jointDiamondCuspEigenspace_ne_bot {χ : (ZMod N)ˣ → ℂ}
    (hχ : jointDiamondCuspEigenspace k χ ≠ ⊥) :
    ∃ χ₀ : (ZMod N)ˣ →* ℂˣ, (fun d ↦ ((χ₀ d) : ℂ)) = χ :=
  exists_charHom_of_iInf_eigenspace_ne_bot (ρ := diamondOpCuspHom k) hχ

/-- **The cusp-form character subspaces form an independent family.** -/
theorem iSupIndep_cuspFormCharSpace (k : ℤ) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ ↦ cuspFormCharSpace (N := N) k χ) := by
  have h_indep_fun : iSupIndep (fun χ : (ZMod N)ˣ → ℂ ↦ jointDiamondCuspEigenspace k χ) :=
    iSupIndep_iInf_eigenspace_of_isSemisimple (diamondOpCuspHom k)
      diamondOpCuspHom_pairwise_commute diamondOpCusp_isSemisimple
  have h : iSupIndep (fun χ₀ : (ZMod N)ˣ →* ℂˣ ↦ jointDiamondCuspEigenspace k
      fun d ↦ (χ₀ d : ℂ)) :=
    h_indep_fun.comp fun _ _ h ↦ MonoidHom.ext fun d ↦ Units.ext (congr_fun h d)
  simpa only [jointDiamondCuspEigenspace_eq_cuspFormCharSpace] using h

section InvariantSubmodule

/-- **Character decomposition of a diamond-invariant submodule of `M_k(Γ₁(N))`.**
If `p ⊆ M_k(Γ₁(N))` is stable under every diamond operator `⟨d⟩` for
`d ∈ (ZMod N)ˣ`, then `p` equals the supremum of its intersections with the
nebentypus character subspaces `modFormCharSpace k χ`. Specializing `p = ⊤`
recovers `iSup_modFormCharSpace_eq_top`. -/
theorem iSup_inf_modFormCharSpace_of_invariant
    (k : ℤ) [FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)]
    (p : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ modFormCharSpace k χ) = p := by
  have h_fun_top : (⨆ χ : (ZMod N)ˣ → ℂ, p ⊓ jointDiamondEigenspace k χ) = p :=
    iSup_inf_iInf_eigenspace_of_invariant (diamondOpHom k) diamondOpHom_pairwise_commute
      diamondOp_isSemisimple diamondOp_iSup_eigenspace_eq_top p hp
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) ?_
  conv_lhs => rw [← h_fun_top]
  refine iSup_le fun χ ↦ ?_
  by_cases hχ : p ⊓ jointDiamondEigenspace k χ = ⊥
  · simp only [hχ, bot_le]
  · obtain ⟨χ₀, rfl⟩ := exists_charHom_of_jointDiamondEigenspace_ne_bot
      (fun h_bot ↦ hχ (by rw [h_bot, inf_bot_eq]))
    rw [jointDiamondEigenspace_eq_modFormCharSpace]
    exact le_iSup (fun ψ : (ZMod N)ˣ →* ℂˣ ↦ p ⊓ modFormCharSpace k ψ) χ₀

/-- **Character decomposition of a diamond-invariant submodule of `S_k(Γ₁(N))`.**
The cusp-form analogue of `iSup_inf_modFormCharSpace_of_invariant`. -/
theorem iSup_inf_cuspFormCharSpace_of_invariant
    (k : ℤ) [FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)]
    (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ cuspFormCharSpace k χ) = p := by
  have h_fun_top : (⨆ χ : (ZMod N)ˣ → ℂ, p ⊓ jointDiamondCuspEigenspace k χ) = p :=
    iSup_inf_iInf_eigenspace_of_invariant (diamondOpCuspHom k)
      diamondOpCuspHom_pairwise_commute diamondOpCusp_isSemisimple
      diamondOpCusp_iSup_eigenspace_eq_top p hp
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) ?_
  conv_lhs => rw [← h_fun_top]
  refine iSup_le fun χ ↦ ?_
  by_cases hχ : p ⊓ jointDiamondCuspEigenspace k χ = ⊥
  · simp only [hχ, bot_le]
  · obtain ⟨χ₀, rfl⟩ := exists_charHom_of_jointDiamondCuspEigenspace_ne_bot
      (fun h_bot ↦ hχ (by rw [h_bot, inf_bot_eq]))
    rw [jointDiamondCuspEigenspace_eq_cuspFormCharSpace]
    exact le_iSup (fun ψ : (ZMod N)ˣ →* ℂˣ ↦ p ⊓ cuspFormCharSpace k ψ) χ₀

/-- **Finsupp-indexed character decomposition of a modular form in a
diamond-invariant submodule.** Consumer-facing corollary of
`iSup_inf_modFormCharSpace_of_invariant`: any element of a diamond-invariant
submodule `p ⊆ M_k(Γ₁(N))` is a finitely-supported sum of nebentypus-character
components, each landing simultaneously in `p` and in its character subspace. -/
theorem exists_finsupp_of_diamondOp_invariant
    (k : ℤ) [FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)]
    (p : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpHom k d f ∈ p)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ p) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ ModularForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ p ⊓ modFormCharSpace k χ) ∧
        (g.sum fun _ y ↦ y) = f :=
  (Submodule.mem_iSup_iff_exists_finsupp _ _).mp <|
    (iSup_inf_modFormCharSpace_of_invariant k p hp).symm ▸ hf

/-- **Finsupp-indexed character decomposition of a cusp form in a
diamond-invariant submodule.** Cusp-form analogue of
`exists_finsupp_of_diamondOp_invariant`. -/
theorem exists_finsupp_of_diamondOpCusp_invariant
    (k : ℤ) [FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)]
    (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ p) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ p ⊓ cuspFormCharSpace k χ) ∧
        (g.sum fun _ y ↦ y) = f :=
  (Submodule.mem_iSup_iff_exists_finsupp _ _).mp <|
    (iSup_inf_cuspFormCharSpace_of_invariant k p hp).symm ▸ hf

end InvariantSubmodule

/-- **Extensionality along the character decomposition**: two `ℂ`-linear endomorphisms of
`M_k(Γ₁(N))` that agree on every nebentypus subspace `modFormCharSpace k χ` are equal.
This is the gluing principle by which identities of Hecke operators proven per character
space extend to the whole space of modular forms. -/
theorem endo_ext_of_mem_modFormCharSpace
    [FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)]
    {S T : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (h : ∀ (χ : (ZMod N)ˣ →* ℂˣ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      f ∈ modFormCharSpace k χ → S f = T f) : S = T := by
  refine LinearMap.ext fun f ↦ ?_
  have hf : f ∈ ⨆ χ : (ZMod N)ˣ →* ℂˣ, modFormCharSpace k χ :=
    iSup_modFormCharSpace_eq_top (N := N) k ▸ Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun g ↦ S g = T g) hf h (by simp only [map_zero])
    fun x y hx hy ↦ by simp only [map_add, hx, hy]

end
