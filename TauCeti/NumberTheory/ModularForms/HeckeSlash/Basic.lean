/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The slash sum over a double-coset decomposition

A Hecke operator acts on a modular form by slashing it against representatives of the double
coset and summing. This file defines that sum. It is unconditionally *additive* in `f` and kills
`0`; homogeneity — and so `ℂ`-linearity — additionally needs the representatives to have positive
determinant, because the scalar passes through the slash only on that branch.

⚠ **It is not yet an action, and on a general `f : ℍ → ℂ` it is not even well defined.**
`heckeSlashSum` is a sum over *chosen* representatives — `D.out` for the double coset and
`i.out` for each of its left cosets — and on an arbitrary function the choice changes the
answer: replacing `σᵢ` by `hσᵢ` for `h ∈ Γ₁` multiplies the representative `(σᵢδ)ᵀ` by
`hᵀ` on the right, and `f ∣[k] (Xhᵀ) = (f ∣[k] X) ∣[k] hᵀ` differs from `f ∣[k] X` unless the
slash by `hᵀ` is trivial on that function. Even the identity double coset can therefore send a
raw `f` to `f ∣[k] h` rather than to `f`.

What repairs it is slash-invariance of `f`, and that is the proof of Shimura's Proposition
3.37: right multiplication permutes the representatives, so the sum is again invariant once `f`
is invariant under the group they are right cosets of. ⚠ **That group is `Γ₂ᵀ`, not `Γ₁`** —
see "Which group the representatives are cosets of" below; the two agree exactly when the
triple is transpose-stable, as the level-one pair is. That theorem, and the descent of this sum
to a genuine operator on
`SlashInvariantForm` and `ModularForm`, are deliberately **not** in this file — the reindexing
argument is substantial and is a different claim. Until then this is an auxiliary sum, named to
say so, and every consumer must supply the invariance hypothesis itself.

## The transpose, and why it is here

The Hecke ring is built from the decomposition of `HδH` into **left** cosets `σᵢδH`
(`DoubleCoset.DecompQuotient`, and `LeftCosetModule/Basic.lean` in this repository). But the
slash action is a *right* action, so invariance of `∑ᵢ f ∣[k] Xᵢ` under `f ↦ f ∣[k] γ` needs
right multiplication by `γ` to permute the `Xᵢ` up to multiplication by `H` **on the left** —
that is, the `Xᵢ` must represent **right** cosets `HXᵢ`.

Transposition exchanges the two: if `HδH = ⊔ᵢ (σᵢδ)H` then `HδH = ⊔ᵢ H(δᵀσᵢᵀ)`, because
transposition is an anti-automorphism preserving `SL₂(ℤ)` and fixing every double coset. So the
representative used here is `(σᵢδ)ᵀ`, which is `transposeRep`.

## Which group the representatives are cosets of

The display above is the level-one case, where a single `H = SL₂(ℤ)` sits on both sides. In
general transposition is an *anti*-homomorphism, so it reverses the two flanks:
`(Γ₁ δ Γ₂)ᵀ = Γ₂ᵀ δᵀ Γ₁ᵀ`, and the left-coset decomposition `Γ₁ δ Γ₂ = ⊔ᵢ (σᵢ δ) Γ₂` transposes
to `⊔ᵢ Γ₂ᵀ (σᵢ δ)ᵀ`. So `transposeRep` enumerates right cosets of **`Γ₂ᵀ`**, and the invariance
that makes the sum well defined is invariance under `Γ₂ᵀ`.

⚠ **This is why the level-one pair is special, and why the generality here stops short of a
level-`N` operator.** `SLnZ 2` is transpose-stable (`transposeGLEquiv_mem_SLnZ`, which is just
`det` and integrality surviving transposition) and sits on both flanks, so `Γ₂ᵀ = Γ₁` and the
sum is Shimura's operator for `Γ₁ δ Γ₂` acting on `Γ₁`-invariant functions. A congruence
subgroup is **not** transpose-stable: transposition swaps the off-diagonal entries, so
`!![1, 1; 0, 1] ∈ Γ₁(N)` for every `N` while its transpose lies in `Γ₁(N)` only when `N = 1`,
and `Γ₁(N)ᵀ = Γ¹(N)`. At such a triple the expression below is still defined — it is a finite sum
over chosen representatives, nothing more — but the cosets it runs over belong to `Γ₂ᵀ δᵀ Γ₁ᵀ`,
so it is in no sense an operator on `Γ₁(N)`-invariant forms. Anything
that wants the latter must first reconcile that orientation — either by carrying the correctly
transposed source and target subgroups, or by a device that avoids the transpose altogether
(upper-triangular representatives, as in `HeckeSlash/UpperTri/`).

The transpose is an artefact of which handedness Mathlib's `DecompQuotient` supplies, not of the
mathematics. Shimura decomposes `Γ₁αΓ₂ = ⊔ᵥ Γ₁aᵥ` — the group on the **left** — so his slash,
being a right action, permutes those representatives directly and no transpose ever appears.

⚠ Conventions: `gH` is a left coset and `Hg` a right one, as in Mathlib and in
`LeftCosetModule/Basic.lean`. AINTLIB's `HeckeAction.lean` uses the opposite labels for the
same objects; the mathematics is identical, the words are not.

Transposition is available as the anti-involution of `GLn/TransposeAntiInvolution.lean`, the
same one that proves the Hecke ring commutative; this file only needs that it preserves
`posDetInt 2`, and only for the three declarations that mention determinants at all.

## An arbitrary triple, and what each declaration actually needs

The declarations are stated over an arbitrary triple `HeckeCoset Δ Γ₁ Γ₂` rather than the
level-one pair `(posDetInt 2, SLnZ 2, SLnZ 2)`, and each carries only what it uses. Nothing is
asked of `Δ` at all beyond containing the chosen `δ`.

* `transposeRep` and its characteristic equation need only the group law.
* The **sum** and its additivity and vanishing on `0` need only that the index type is finite,
  so they take `[Fintype (DecompQuotient Γ₁ Γ₂ δ)]` directly. A Hecke triple supplies that
  instance (`HeckeRing/Basic.lean`) and is strictly stronger — it also demands commensurability
  and that `Δ` commensurate `Γ₂`, none of which the sum uses.
* Positivity of the determinant enters exactly once, in **homogeneity**: on the positive branch
  the slash action's conjugation `σ` is trivial and scalars commute past it
  (`ModularForm.rat_smul_slash_of_det_pos`), whereas over a general `GL(2, ℚ)`-element the twist
  is complex conjugation and linearity would fail. So `transposeRep_mem_posDetInt`,
  `det_transposeRep_pos` and `heckeSlashSum_smul` — and only those — ask for positivity, and only
  of the two factors of `σᵢ δ` that actually appear: `Γ₁ ≤ posDetInt 2` and `δ ∈ posDetInt 2`.
  Neither `Γ₂` nor the rest of `Δ` is constrained. At the level-one pair these are
  `SLnZ_le_posDetInt 2` and `D.out.2`.

⚠ Positivity being available at level `N` is *not* enough to read the sum there as a Hecke
operator: what fails at a congruence subgroup is the transpose orientation, not the determinant.
See "Which group the representatives are cosets of" above.

## Main definitions

* `HeckeRing.GL2.transposeRep`: the transposed representative `(σᵢ δ)ᵀ`.
* `HeckeRing.GL2.heckeSlashSum`: the choice-dependent sum `∑ᵢ f ∣[k] (σᵢ δ)ᵀ`.

## Main results

* `HeckeRing.GL2.transposeRep_def`, `HeckeRing.GL2.heckeSlashSum_def` and
  `HeckeRing.GL2.heckeSlashSum_apply`: the characteristic equations, which are the interface
  since neither definition is `@[expose]`. The last two are the function-level and pointwise
  forms of the same equation.
* `HeckeRing.GL2.det_transposeRep_pos`: the representatives have positive determinant, given
  `Γ₁ ≤ posDetInt 2` and `δ ∈ posDetInt 2`.
* `HeckeRing.GL2.heckeSlashSum_add` and `heckeSlashSum_zero`: additivity and vanishing on `0`,
  with no hypothesis beyond finiteness of the index type.
* `HeckeRing.GL2.heckeSlashSum_smul`: homogeneity, which additionally needs the two positivity
  hypotheses above. Together with `heckeSlashSum_add` it gives `ℂ`-linearity.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck): `transposeRep`,
its `heckeSlash` (renamed `heckeSlashSum` here, since it is not yet an action) and that
definition's additivity, zero and scalar lemmas. Restated
against TauCeti's `HeckeCoset`/`posDetInt` vocabulary and `transposeGLEquiv` rather than
AINTLIB's `GL_pair`/`GL_transposeEquiv`, and over an arbitrary triple rather than the fixed
level-one pair both projects start from.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 *Action of double cosets on automorphic forms*: equation (3.4.1) defines the operator
  `f ∣[Γ₁ α Γ₂]ₖ` as the sum below, and Proposition 3.37 is the statement that it maps
  automorphic forms to automorphic forms — the invariance this file stops short of.
-/

public section

open Matrix UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂)

/-- The transposed left-coset representative `(σᵢ δ)ᵀ = δᵀ σᵢᵀ`, where `δ` is the chosen
representative of the double coset `D` and `σᵢ` runs over its left-coset decomposition of
`Γ₁ δ Γ₂`. The transpose turns it into a representative of the right coset `Γ₂ᵀ(σᵢ δ)ᵀ`, which
is the handedness a right action needs — the enclosing double coset being the transposed
`Γ₂ᵀ δᵀ Γ₁ᵀ`, since transposition reverses the flanks. ⚠ The group on the left is `Γ₂ᵀ`, not
`Γ₁`; see "Which group the representatives are cosets of" in the module docstring. -/
noncomputable def transposeRep (i : DecompQuotient Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ)) :
    GL (Fin 2) ℚ :=
  (transposeGLEquiv 2 ((i.out : GL (Fin 2) ℚ) * (D.out : GL (Fin 2) ℚ))).unop

-- `transposeRep` and `heckeSlashSum` are not `@[expose]`, so a module downstream of this one cannot
-- unfold either body. Their characteristic equations below are therefore the interface, not a
-- restatement of something already visible; `transposeRep_def` is written `(rfl)` in the style of
-- `ModularForms/Basic.lean`, which opts out of exporting the definitional equality itself.

/-- Defining equation for `transposeRep`: the transpose of `σᵢ δ`. Since `transposeRep` is not
`@[expose]`, a downstream module rewrites with this instead of unfolding the body. -/
lemma transposeRep_def (i : DecompQuotient Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ)) :
    transposeRep D i =
      (transposeGLEquiv 2 ((i.out : GL (Fin 2) ℚ) * (D.out : GL (Fin 2) ℚ))).unop := (rfl)

/-- Each representative lies in `posDetInt 2` when the two factors of `σᵢ δ` do. Only `Γ₁` and the
chosen `δ` are constrained: nothing is asked of `Γ₂`, and nothing of `Δ` beyond containing `δ`. -/
lemma transposeRep_mem_posDetInt (hΓ₁ : Γ₁.toSubmonoid ≤ posDetInt 2)
    (hD : (D.out : GL (Fin 2) ℚ) ∈ posDetInt 2)
    (i : DecompQuotient Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ)) : transposeRep D i ∈ posDetInt 2 :=
  transposeRep_def D i ▸
    transposeGLEquiv_mem_posDetInt 2 (mul_mem (hΓ₁ i.out.2) hD)

/-- The representatives have positive determinant — the `0 < det` half of
`transposeRep_mem_posDetInt`, in the shape `ModularForm.rat_smul_slash_of_det_pos` consumes. -/
lemma det_transposeRep_pos (hΓ₁ : Γ₁.toSubmonoid ≤ posDetInt 2)
    (hD : (D.out : GL (Fin 2) ℚ) ∈ posDetInt 2)
    (i : DecompQuotient Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ)) :
    0 < (transposeRep D i : Matrix (Fin 2) (Fin 2) ℚ).det :=
  ((mem_posDetInt_iff 2).mp (transposeRep_mem_posDetInt D hΓ₁ hD i)).2

-- From here on the sum needs its index type to be finite, and that is *all* it needs: a Hecke
-- triple supplies this `Fintype` (`HeckeRing/Basic.lean`) but is strictly stronger, so the
-- instance is stated directly. It is introduced here rather than `omit`ted from the four
-- declarations above, which do without it.
variable [Fintype (DecompQuotient Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ))]

/-- **The slash sum over a chosen decomposition of a double coset**:
`∑ᵢ f ∣[k] (σᵢ δ)ᵀ`, over the transposed representatives of the left-coset decomposition of
`Γ₁ δ Γ₂`.

⚠ The transposed representatives enumerate right cosets of `Γ₂ᵀ` inside `Γ₂ᵀ δᵀ Γ₁ᵀ`. Reading
this as Shimura's `f ∣[Γ₁ α Γ₂]ₖ` (§3.4 (3.4.1), up to the `det` normalising factor) therefore
needs **two** things, not one: the flanks must match, `Γ₂ᵀ = Γ₁` (equivalently `Γ₁ᵀ = Γ₂`), *and*
the double coset itself must be transpose-stable, `Γ₁ δᵀ Γ₂ = Γ₁ δ Γ₂` — matching the flanks alone
leaves `δᵀ` where `δ` should be. Both hold at the level-one pair, where transposition preserves
`SL₂(ℤ)` and fixes every double coset; the identification is asserted here only for that case.
See "Which group the representatives are cosets of" in the module docstring.

⚠ This depends on the chosen representatives `D.out` and `i.out`, and on a general
`f : ℍ → ℂ` the value changes with them — see the module docstring. Slash-invariance of `f` is
*sufficient* to make it independent of the choices, and so an action; that is a separate
theorem. Whether it is also necessary is not claimed here — a particular `f` and `D` could be
independent by cancellation. Do not read this definition as "the Hecke operator" until the
sufficiency theorem is available. -/
noncomputable def heckeSlashSum (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : DecompQuotient Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ), f ∣[k] transposeRep D i

/-- Defining equation for `heckeSlashSum` at the level of functions. Since `heckeSlashSum` is
not `@[expose]`, a downstream module rewrites with this instead of unfolding the body; the
pointwise `heckeSlashSum_apply` below is the companion for arguments that work at a point. -/
lemma heckeSlashSum_def (f : ℍ → ℂ) : heckeSlashSum k D f =
    ∑ i : DecompQuotient Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ), f ∣[k] transposeRep D i := (rfl)

/-- The pointwise value of the slash sum: the sum of the slashed values. This is the equation
the reindexing proof of Prop 3.37 works from. -/
lemma heckeSlashSum_apply (f : ℍ → ℂ) (τ : ℍ) : heckeSlashSum k D f τ =
    ∑ i : DecompQuotient Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ), (f ∣[k] transposeRep D i) τ :=
  Finset.sum_apply ..

/-- The slash sum is additive in `f`. -/
@[simp]
lemma heckeSlashSum_add (f g : ℍ → ℂ) : heckeSlashSum k D (f + g) =
    heckeSlashSum k D f + heckeSlashSum k D g := by
  simp [heckeSlashSum, Finset.sum_add_distrib]

/-- The slash sum kills the zero function. -/
@[simp]
lemma heckeSlashSum_zero : heckeSlashSum k D 0 = 0 := by
  rw [heckeSlashSum]
  exact Finset.sum_eq_zero fun i _ ↦ SlashAction.zero_slash k (transposeRep D i)

/-- **The slash sum is homogeneous in `f`**: a scalar acting on `ℂ` through the scalar tower
passes out of the sum. With `heckeSlashSum_add`, at `α := ℂ`, this gives `ℂ`-linearity.

Unlike additivity, this needs the two factors of `σᵢ δ` to have positive determinant — exactly
`Γ₁ ≤ posDetInt 2` and `δ ∈ posDetInt 2`, with `Γ₂` and the rest of `Δ` unconstrained — because
the scalar passes through the slash only on that branch. -/
@[simp]
lemma heckeSlashSum_smul (hΓ₁ : Γ₁.toSubmonoid ≤ posDetInt 2)
    (hD : (D.out : GL (Fin 2) ℚ) ∈ posDetInt 2)
    {α : Type*} [DistribSMul α ℂ] [IsScalarTower α ℂ ℂ] (c : α) (f : ℍ → ℂ) :
    heckeSlashSum k D (c • f) = c • heckeSlashSum k D f := by
  rw [heckeSlashSum, heckeSlashSum]
  -- each representative has positive determinant, so the slash carries no `σ` twist: the
  -- scalar leaves the summands one at a time, and only then comes out of the sum as a whole
  exact (Finset.sum_congr rfl fun i _ ↦ ModularForm.rat_smul_slash_of_det_pos k
    (det_transposeRep_pos D hΓ₁ hD i) f c).trans Finset.smul_sum.symm

end HeckeRing.GL2
