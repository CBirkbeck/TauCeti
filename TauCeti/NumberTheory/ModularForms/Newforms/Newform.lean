/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action
public import TauCeti.NumberTheory.ModularForms.Newforms.Basic

/-!
# Good Hecke eigenforms and newforms, as bundled forms

A **good Hecke eigenform** of level `Γ₁(N)` and weight `k` is a nonzero cusp form with a
nebentypus `χ` that is a simultaneous eigenvector of the `Γ₀(N)` Hecke ring acting on
`cuspFormCharSpace k χ` (`heckeRingHomCuspCharSpace`), at every index coprime to the level.
A **newform** is a good Hecke eigenform lying in the new subspace and normalised by `a₁ = 1`:
Miyake's *primitive form* (§4.6). Both are bundled here as structures extending `CuspForm`, so
that the character, the eigenvalue system and the analytic invariants travel with the form.

## Design

* Eigen-ness is demanded only at indices coprime to `N`: the ring element at a bad index lies in
  another double coset and is not packaged. The eigenvalue slot at a bad index carries no
  arithmetic and is normalised to `0`, which is what makes an eigenform determined by its
  underlying cusp form and character (`EigenformAwayFromLevel.ext_of_toCuspForm`). It is not a
  claim about `U_p`.
* The public eigenvalue interface is `EigenformAwayFromLevel.eigenvalue`, guarded by
  `Nat.Coprime n N`; the total `ringEigenvalue` is a representation detail.
* That a newform is an eigenvector of every `T_n` is a theorem (Atkin–Lehner–Li; Miyake
  Theorem 4.6.13), not a field. The comparison of the ring eigenvalue with the classical
  operator `heckeTCuspNat` is likewise a theorem, and is not proved here.

## Main definitions

* `HeckeRing.GL2.EigenformAwayFromLevel`: the bundled good Hecke eigenform.
* `HeckeRing.GL2.Newform`: the bundled newform.
* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue`: the eigenvalue at an index coprime to the
  level.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.ext_of_toCuspForm`,
  `HeckeRing.GL2.Newform.ext_of_toCuspForm`: the bundled data is determined by the underlying
  cusp form and the character.

## Provenance

Follows the shapes of `structure Eigenform` and `structure Newform` of the AINTLIB
`LeanModularForms` project (`LeanModularForms/HeckeRIngs/GL2/Newforms/{Basic,MainLemma}.lean`,
Chris Birkbeck, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), with the porting
decisions the roadmap pins: the structure is named for the qualified notion, the nonzeroness
field is added, the character space is the cusp-form one, and the bad-index slots are
normalised to `0`. The source's `Eigenform.eigenvalue`/`isEigen` (the classical eigenvalue,
which in its convention carries a diamond factor `χ(n)`) rest on its
`heckeT_n_cusp_eq_heckeRingHom`, which has no counterpart here yet.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn

open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **A good Hecke eigenform, bundled.** A nonzero cusp form of level `Γ₁(N)` with a nebentypus
`χ`, together with an eigenvalue system for the `Γ₀(N)` Hecke ring acting on
`cuspFormCharSpace k χ`: at every index `n` coprime to `N`, the ring element
`heckeTCompositeGamma0 N n` acts by the scalar `ringEigenvalue n`. Eigen-ness is demanded only
away from the level; the slots at indices not coprime to `N` carry no arithmetic and are
normalised to `0`, so that an eigenform is determined by its underlying cusp form and character.
-/
structure EigenformAwayFromLevel (N : ℕ) [NeZero N] (k : ℤ)
    extends CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  /-- The nebentypus character. -/
  χ : (ZMod N)ˣ →* ℂˣ
  /-- The form transforms under the diamond operators by `χ`. -/
  mem_charSpace : toCuspForm ∈ cuspFormCharSpace k χ
  /-- The eigenvalue system for the `Γ₀(N)` Hecke ring; only the values at indices coprime to
  `N` carry meaning. -/
  ringEigenvalue : ℕ+ → ℂ
  /-- At an index coprime to `N`, the Hecke ring element `heckeTCompositeGamma0 N n` acts on the
  form by `ringEigenvalue n`. -/
  isRingEigen : ∀ n : ℕ+, Nat.Coprime n.val N →
    heckeRingHomCuspCharSpace (k := k) (χ := χ) (heckeTCompositeGamma0 N n.val)
        ⟨toCuspForm, mem_charSpace⟩
      = ringEigenvalue n • (⟨toCuspForm, mem_charSpace⟩ : cuspFormCharSpace k χ)
  /-- The slots at indices not coprime to `N` are normalised to `0`. -/
  ringEigen_bad : ∀ n : ℕ+, ¬ Nat.Coprime n.val N → ringEigenvalue n = 0
  /-- An eigenform is nonzero. -/
  ne_zero : toCuspForm ≠ 0

/-- **A newform**: a good Hecke eigenform lying in the new subspace and normalised by `a₁ = 1`
(Miyake's *primitive form*). That a newform is an eigenform for every `T_n` is a theorem, not
part of the definition. -/
structure Newform (N : ℕ) [NeZero N] (k : ℤ) extends EigenformAwayFromLevel N k where
  /-- The form lies in the new subspace `S_k(Γ₁(N))ⁿᵉʷ`. -/
  isNew : toCuspForm ∈ TauCeti.cuspFormsNew N k
  /-- The form is normalised: its first Fourier coefficient is `1`. -/
  isNorm : (qExpansion 1 toCuspForm).coeff 1 = 1

namespace EigenformAwayFromLevel

variable (f : EigenformAwayFromLevel N k)

/-- The eigenvalue at an index coprime to the level: the public face of `ringEigenvalue`. -/
def eigenvalue (n : ℕ+) (_hn : Nat.Coprime n.val N) : ℂ := f.ringEigenvalue n

/-- Two good Hecke eigenforms with the same underlying cusp form and character are equal: the
eigenvalues at good indices are determined by the form, and the bad slots are normalised. -/
theorem ext_of_toCuspForm {f g : EigenformAwayFromLevel N k} (hχ : f.χ = g.χ)
    (h : f.toCuspForm = g.toCuspForm) : f = g := by
  obtain ⟨F, χf, memf, af, eigf, badf, nzf⟩ := f
  obtain ⟨G, χg, memg, ag, eigg, badg, nzg⟩ := g
  simp only at hχ h
  subst hχ h
  have hx : (⟨F, memf⟩ : cuspFormCharSpace k χf) ≠ 0 := fun hx ↦ nzf (congrArg Subtype.val hx)
  have hae : af = ag := funext fun n ↦ by
    by_cases hn : Nat.Coprime n.val N
    · exact smul_left_injective ℂ hx ((eigf n hn).symm.trans (eigg n hn))
    · rw [badf n hn, badg n hn]
  subst hae
  rfl

end EigenformAwayFromLevel

namespace Newform

/-- Two newforms with the same underlying cusp form and character are equal. -/
theorem ext_of_toCuspForm {f g : Newform N k} (hχ : f.χ = g.χ)
    (h : f.toCuspForm = g.toCuspForm) : f = g := by
  obtain ⟨f, hfn, hf1⟩ := f
  obtain ⟨g, hgn, hg1⟩ := g
  have : f = g := EigenformAwayFromLevel.ext_of_toCuspForm hχ h
  subst this
  rfl

end Newform

end HeckeRing.GL2
