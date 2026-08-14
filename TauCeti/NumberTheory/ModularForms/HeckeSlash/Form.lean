/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Invariance

/-!
# The slash sum as an operator on slash-invariant forms

`Invariance.lean` proves that `heckeSlashSum k D f` is `SL₂(ℤ)`-invariant when `f` is. This file
packages that into a map `SlashInvariantForm 𝒮ℒ k → SlashInvariantForm 𝒮ℒ k`, which is the point
at which the double coset finally acts on *forms* rather than on raw functions `ℍ → ℂ`.

## Crossing from `ℚ` to `ℝ`

The two sides speak different languages, and reconciling them is most of this file.
`SlashInvariantForm Γ k` is indexed by a subgroup of `GL(2, ℝ)`, and `𝒮ℒ` is the range of
`mapGL ℝ`; the invariance theorem is stated at `SLnZ 2`, the range of `mapGL ℚ`, under the
rational slash action. Both are ranges of `mapGL` out of the *same* `SL₂(ℤ)`, so a single lemma
relates them: `map (algebraMap ℚ ℝ)` sends `mapGL ℚ s` to `mapGL ℝ s`. Both directions of the
bridge follow, and `ModularForm.rat_slash` turns each rational slash into the real one.

## Main definitions

* `HeckeRing.GL2.heckeSlashInvariant`: the double coset acting on `SlashInvariantForm 𝒮ℒ k`.

## Main results

* `HeckeRing.GL2.map_ratCast_mem_SL` and `HeckeRing.GL2.exists_mem_SLnZ_of_mem_SL`: the two
  directions of the `SLnZ 2` ↔ `𝒮ℒ` correspondence.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck): `glMap_mapGL_eq`,
`glMap_mem_SL`, `mem_SL_exists_H` and `heckeSlashInvariant`.

These are the bridging helpers that earlier files in this chain deliberately avoided: carrying
slash-invariance rationally kept `Reindex.lean` and `Invariance.lean` free of them, and this is
the file that pays for that choice, once, where the `ℝ`-indexed `SlashInvariantForm` makes it
unavoidable.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, Proposition 3.37.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- Entrywise `ℚ → ℝ` turns the rational image of `s : SL₂(ℤ)` into its real image. This is the
single fact behind both directions of the `SLnZ 2` ↔ `𝒮ℒ` correspondence. -/
lemma map_ratCast_mapGL (s : SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (mapGL ℚ s) = mapGL ℝ s := by
  ext i j
  simp

/-- An element of `SL₂(ℤ) ≤ GL(2, ℚ)` maps into `𝒮ℒ`. -/
lemma map_ratCast_mem_SL {δ : GL (Fin 2) ℚ} (hδ : δ ∈ SLnZ 2) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) δ ∈ 𝒮ℒ := by
  obtain ⟨s, rfl⟩ := (mem_SLnZ_iff 2).mp hδ
  exact ⟨s, (map_ratCast_mapGL s).symm⟩

/-- Every element of `𝒮ℒ` is the image of one of `SLnZ 2`. -/
lemma exists_mem_SLnZ_of_mem_SL {γ : GL (Fin 2) ℝ} (hγ : γ ∈ 𝒮ℒ) :
    ∃ δ ∈ SLnZ 2, Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) δ = γ := by
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hγ
  exact ⟨mapGL ℚ s, (mem_SLnZ_iff 2).mpr ⟨s, rfl⟩, map_ratCast_mapGL s⟩

/-- Real slash-invariance under `𝒮ℒ` gives rational slash-invariance under `SLnZ 2`. -/
lemma slash_eq_of_mem_SLnZ {f : ℍ → ℂ} (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) {δ : GL (Fin 2) ℚ}
    (hδ : δ ∈ SLnZ 2) : f ∣[k] δ = f := by
  rw [ModularForm.rat_slash]
  exact hf _ (map_ratCast_mem_SL hδ)

/-- **The double coset acting on slash-invariant forms.** The underlying function is
`heckeSlashSum`, and its invariance is `heckeSlashSum_slash_invariant_of_mem_SLnZ` transported
across the `SLnZ 2` ↔ `𝒮ℒ` correspondence.

⚠ As in `Invariance.lean`, this is the sum over the representatives `heckeSlashSum` fixes; no
claim is made that different choices of representatives give the same form. -/
noncomputable def heckeSlashInvariant (f : SlashInvariantForm 𝒮ℒ k) : SlashInvariantForm 𝒮ℒ k where
  toFun := heckeSlashSum k D f
  slash_action_eq' γ hγ := by
    obtain ⟨δ, hδ, rfl⟩ := exists_mem_SLnZ_of_mem_SL hγ
    rw [← ModularForm.rat_slash]
    exact heckeSlashSum_slash_invariant_of_mem_SLnZ k D f
      (fun _ h ↦ slash_eq_of_mem_SLnZ k f.slash_action_eq' h) hδ

end HeckeRing.GL2
