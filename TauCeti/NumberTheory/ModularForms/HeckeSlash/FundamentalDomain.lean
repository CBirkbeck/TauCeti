/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic

/-!
# The Hecke coset representatives tile a fundamental domain

`HeckeRing.GL2.heckeSlashSum` sums `f ∣[k] aᵥ` over `v : DecompQuotient Γ₂ Γ₁ δ⁻¹`, with
`aᵥ = rightCosetRep D v = δ τᵥ⁻¹`. Everything there lives in `GL (Fin 2) ℚ`, which does **not**
act on `ℍ`, so the statement is made along a homomorphism `φ` into a group that does.

This file shows that the images `φ aᵥ` of those representatives translate a fundamental domain
for `φ(Γ₂)` into one for `φ(Γ₁) ⊓ φ(δ) φ(Γ₂) φ(δ)⁻¹`.

**`φ` is a parameter, and is not assumed injective.** The group acting faithfully on `ℍ` is a
quotient of a matrix group by its scalars, so any faithful `φ` collapses `±1` — and it must, since
a non-identity element acting trivially makes `MeasureTheory.IsFundamentalDomain` unsatisfiable for
every set of positive measure. Injectivity is replaced by an ambient subgroup `H` containing both
groups, stable under conjugation by `δ`, with `ker φ ⊓ H ≤ Γ₁`; at `H` the determinant-one subgroup
this reads `{±1} ≤ Γ₁`, true of every `Γ₀(N)`.

This is what turns a sum of slashes into a single integral: because the translates tile, an
integral of `heckeSlashSum` over a fundamental domain for the smaller group may be read termwise
over one for `Γ₂`, which is how the Petersson pairing of a Hecke operator against a form is
computed and hence how its adjoint is identified.

## Main results

* `HeckeRing.GL2.isFundamentalDomain_iUnion_rightCosetRep_smul`: the tiling.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/AdjointTheory/FDTransport.lean`,
<https://github.com/CBirkbeck/AINTLIB>, commit `6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`,
Apache-2.0, Chris Birkbeck), where the same transport is carried out at `PSL` level.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.5.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open MeasureTheory ConjAct Matrix TauCeti UpperHalfPlane DoubleCoset

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂)

open scoped Classical in
/-- **The images of the Hecke coset representatives tile a fundamental domain.**

`heckeSlashSum` sums over `v : DecompQuotient Γ₂ Γ₁ δ⁻¹` with `aᵥ = rightCosetRep D v = δ τᵥ⁻¹`,
all in `GL (Fin 2) ℚ`. Their images under a homomorphism `φ` into a group acting on `ℍ` translate
a fundamental domain `S` for `φ(Γ₂)` into one for `φ(Γ₁) ⊓ φ(δ) φ(Γ₂) φ(δ)⁻¹`.

`φ` is a parameter rather than a fixed map, and it is **not** assumed injective: the group that
acts faithfully on `ℍ` is a quotient of a matrix group by its scalars, so a faithful `φ`
necessarily collapses `±1`. What replaces injectivity is the ambient subgroup `H` — containing
`Γ₁` and `Γ₂`, stable under conjugation by `δ`, and meeting `ker φ` inside `Γ₁`. Taking `H` to be
the determinant-one subgroup makes `ker φ ⊓ H = {±1}`, which lies in every `Γ₀(N)`.

Injectivity would not do instead: for `-I ∈ Γ₂` the hypothesis `hS` is unsatisfiable, since `-I`
is then a non-identity element of `φ(Γ₂)` acting trivially and
`MeasureTheory.IsFundamentalDomain` demands a.e.-disjointness over distinct *group elements*. -/
theorem isFundamentalDomain_iUnion_rightCosetRep_smul
    {P : Type*} [Group P] [MulAction P ℍ] (φ : GL (Fin 2) ℚ →* P)
    {H : Subgroup (GL (Fin 2) ℚ)}
    [Countable (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]
    {S : Set ℍ} {μ : Measure ℍ}
    (h₁ : Γ₂ ≤ H) (h₂ : Γ₁ ≤ H)
    (hconj : ∀ y ∈ H, (D.out : GL (Fin 2) ℚ) * y * (D.out : GL (Fin 2) ℚ)⁻¹ ∈ H)
    (hker : φ.ker ⊓ H ≤ Γ₁)
    (hS : IsFundamentalDomain (Γ₂.map φ : Subgroup P) S μ)
    (hδ : Measure.QuasiMeasurePreserving
      (fun x : ℍ ↦ (φ (D.out : GL (Fin 2) ℚ))⁻¹ • x) μ μ)
    (hnull : ∀ v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹,
      NullMeasurableSet ((φ (((v.out : Γ₂) : GL (Fin 2) ℚ)))⁻¹ • S) μ) :
    IsFundamentalDomain
      ((Γ₁.map φ ⊓ toConjAct (φ (D.out : GL (Fin 2) ℚ)) • Γ₂.map φ : Subgroup P))
      (⋃ v, φ (rightCosetRep D v) • S) μ := by
  have hconj' : ∀ y ∈ H, ((D.out : GL (Fin 2) ℚ)⁻¹)⁻¹ * y * (D.out : GL (Fin 2) ℚ)⁻¹ ∈ H := by
    simpa [mul_assoc] using hconj
  set e := decompQuotientEquivMapOfKerInfLe' φ Γ₂ Γ₁ H (D.out : GL (Fin 2) ℚ)⁻¹
    (φ (D.out : GL (Fin 2) ℚ))⁻¹ (map_inv φ _) h₁ h₂ hconj' hker with he_def
  set r : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹ → (Γ₂.map φ : Subgroup P) := fun v ↦
    (φ.subgroupMap Γ₂ v.out)⁻¹ with hr_def
  have hset : ∀ v, (φ (D.out : GL (Fin 2) ℚ)) * ((r v : P)) = φ (rightCosetRep D v) := fun v ↦ by
    rw [rightCosetRep_def, map_mul, map_inv]
    rfl
  have hbij : Function.Bijective fun v ↦
      (QuotientGroup.mk (r v)⁻¹ :
        (Γ₂.map φ : Subgroup P) ⧸
          (toConjAct (φ (D.out : GL (Fin 2) ℚ))⁻¹ • (Γ₁.map φ : Subgroup P)).subgroupOf
            (Γ₂.map φ : Subgroup P)) := by
    have heq : ∀ v, (QuotientGroup.mk (r v)⁻¹ : _) = e v := by
      intro v
      conv_rhs => rw [← v.out_eq]
      rw [he_def, decompQuotientEquivMapOfKerInfLe'_mk]
      simp [hr_def]
    exact funext heq ▸ e.bijective
  have := hS.iUnion_mul_smul_of_transversal (φ (D.out : GL (Fin 2) ℚ)) hδ
    (fun v ↦ hnull v) hbij
  simpa only [hset] using this

end HeckeRing.GL2
