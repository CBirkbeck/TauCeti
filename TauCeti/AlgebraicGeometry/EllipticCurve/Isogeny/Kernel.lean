/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.FixedField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability

/-!
# The kernel of an isogeny

An isogeny is a map of function fields, so it has no point map to take a fibre of. Its kernel is
read off the translation action instead: a point `P` of `W₁` lies in the kernel exactly when
translating by `P` moves no function pulled back from `W₂`. On the points where the two notions
can be compared this is the usual kernel, since `φ(X + P) = φ(X) + φ(P)`, and it is stated here
for every isogeny over every field, with no separability or rationality hypothesis.

The degree bounds the kernel: a pulled-back field of degree `d` is fixed by at most `d`
translations. The bound is often strict, because these are the `F`-rational points only: a
separable isogeny whose geometric kernel is not rational has fewer of them than its degree.
Equality needs separability *and* rationality of the whole geometric kernel. For `1 − π_q` over a
finite field both hold, its geometric kernel being the `𝔽_q`-rational points, and the point count
`deg (1 − π_q) = #E(𝔽_q)` is what they then yield; neither that identity nor the general equality
is proved here.

## Main definitions

* `TauCeti.Isogeny.ker`: the subgroup of points whose translation fixes the pulled-back field.

## Main results

* `TauCeti.Isogeny.card_ker_le_degree`: the kernel has at most `deg φ` elements.
* `TauCeti.Isogeny.ker_le_ker_comp`: postcomposition can only enlarge the kernel.
* `TauCeti.Isogeny.ker_eq_bot_of_separableDegree_eq_one`: separable degree one forces this kernel
  to be trivial, as for Frobenius.
* `TauCeti.Isogeny.card_ker_eq_degree_iff`: the cardinality statement is *equivalent* to the
  reverse fixed-field inclusion.
* `TauCeti.Isogeny.card_ker_dvd_separableDegree` and `card_ker_le_separableDegree`: the kernel
  order divides, so is bounded by, the separable degree.
* `TauCeti.Isogeny.fieldPullback_fieldRange_le_translationFixedField_ker`: the pulled-back field is
  fixed by the kernel.

## Provenance

The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache 2.0, commit
`513e83879e2f8cbc626eb9e04d660e92be16ccba`) proves the corresponding cardinality statement in
`EC/SeparableKernelTorsor.lean` as `card_kernel_eq_degree_of_separable_isogeny`, parametric on two
witnesses. The second exists only because its isogeny carries a point map independent of the
function-field pullback, so separability and the kernel are a priori unrelated there. The kernel
here is defined from the pullback, so that witness has no counterpart.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]

/-- **The kernel of an isogeny**: the points whose translation fixes every pulled-back function. -/
noncomputable def ker (φ : Isogeny W₁ W₂) : AddSubgroup (W₁⁄F).toAffine.Point :=
  translationFixingSubgroup W₁ φ.fieldPullback.fieldRange

/-- The defining equation of `ker`. -/
theorem ker_def (φ : Isogeny W₁ W₂) :
    φ.ker = translationFixingSubgroup W₁ φ.fieldPullback.fieldRange := (rfl)

/-- **A point is in the kernel exactly when it translates every pulled-back function to
itself.** -/
@[simp]
theorem mem_ker_iff {φ : Isogeny W₁ W₂} {P : (W₁⁄F).toAffine.Point} :
    P ∈ φ.ker ↔ ∀ z ∈ φ.fieldPullback.fieldRange, translation W₁ P z = z := by
  rw [ker_def]; exact mem_translationFixingSubgroup_iff W₁

/-- **The kernel is finite**, the pulled-back field being of finite index. -/
instance finite_ker (φ : Isogeny W₁ W₂) : Finite φ.ker :=
  φ.ker_def ▸ finite_translationFixingSubgroup W₁ φ.fieldPullback.fieldRange

/-- **Postcomposition can only enlarge the kernel**: a function pulled back from `W₃` arrives
through `W₂`, so a translation fixing everything from `W₂` fixes it too. -/
theorem ker_le_ker_comp {W₃ : WeierstrassCurve.Affine F} (ψ : Isogeny W₂ W₃)
    (φ : Isogeny W₁ W₂) : φ.ker ≤ (ψ.comp φ).ker := by
  rw [ker_def, ker_def]
  refine translationFixingSubgroup_antitone W₁ ?_
  rintro _ ⟨z, rfl⟩
  exact AlgHom.mem_fieldRange.2 ⟨ψ.fieldPullback z, by rw [comp_fieldPullback]; rfl⟩

/-- **The pulled-back field is fixed by the kernel.** The kernel's interaction with the fixed-field
operation, so that a consumer can use `ker` without unfolding it to a fixing subgroup. This is the
inclusion that holds for every isogeny; the reverse one is the content of
`card_ker_eq_degree_iff`. -/
theorem fieldPullback_fieldRange_le_translationFixedField_ker (φ : Isogeny W₁ W₂) :
    φ.fieldPullback.fieldRange ≤ translationFixedField W₁ φ.ker := by
  rw [ker_def]; exact le_translationFixedField_translationFixingSubgroup W₁ _

/-- **The kernel order divides the separable degree.** The extension cut out by the kernel is
Galois, hence separable, so its degree — the order of the kernel — is one factor of the separable
degree of the whole extension.

This is the general form of the identity a point count needs: the separable degree is what the
kernel can see, and the missing factor is the separable degree of the pulled-back field inside the
field the kernel cuts out. -/
theorem card_ker_dvd_separableDegree (φ : Isogeny W₁ W₂) :
    Nat.card φ.ker ∣ φ.separableDegree := by
  have hle := φ.fieldPullback_fieldRange_le_translationFixedField_ker
  -- `extendScalars hle` is the same subfield seen over `φ^*K(W₂)`; the two share a carrier, so
  -- these transport definitionally, which instance search does not see through
  have hsep : Algebra.IsSeparable (IntermediateField.extendScalars hle) W₁.FunctionField :=
    inferInstanceAs (Algebra.IsSeparable (translationFixedField W₁ φ.ker) W₁.FunctionField)
  have hrk : Module.finrank (IntermediateField.extendScalars hle) W₁.FunctionField =
      Nat.card φ.ker := finrank_translationFixedField W₁ φ.ker
  have htop : Field.finSepDegree (IntermediateField.extendScalars hle) W₁.FunctionField =
      Nat.card φ.ker := by
    rw [Field.finSepDegree_eq_finrank_of_isSeparable, hrk]
  rw [separableDegree_def, ← Field.finSepDegree_mul_finSepDegree_of_isAlgebraic
    φ.fieldPullback.fieldRange (IntermediateField.extendScalars hle) W₁.FunctionField, htop]
  exact Dvd.intro_left _ rfl

/-- **The separable degree bounds the kernel**, sharpening the bound by the degree. -/
theorem card_ker_le_separableDegree (φ : Isogeny W₁ W₂) :
    Nat.card φ.ker ≤ φ.separableDegree :=
  Nat.le_of_dvd φ.separableDegree_pos φ.card_ker_dvd_separableDegree

/-- **The degree bounds the kernel**, the separable degree being at most the degree. The bound is
often strict, this being the rational kernel: equality needs the isogeny to be separable and its
geometric kernel to be rational. -/
theorem card_ker_le_degree (φ : Isogeny W₁ W₂) : Nat.card φ.ker ≤ φ.degree :=
  φ.card_ker_le_separableDegree.trans <| by
    rw [separableDegree_def, degree_def]; exact Field.finSepDegree_le_finrank _ _

/-- **An isogeny of separable degree one has a trivial kernel here**, the bound leaving no room.
This is the right hypothesis: a purely inseparable isogeny such as Frobenius has separable degree
one, so its kernel in this point-valued sense is trivial whatever its degree — its scheme-theoretic
kernel, which this file does not model, is not. -/
theorem ker_eq_bot_of_separableDegree_eq_one {φ : Isogeny W₁ W₂} (h : φ.separableDegree = 1) :
    φ.ker = ⊥ :=
  φ.ker.eq_bot_of_card_le (h ▸ φ.card_ker_le_separableDegree)

/-- **An isogeny of degree one has trivial kernel.** -/
theorem ker_eq_bot_of_degree_eq_one {φ : Isogeny W₁ W₂} (h : φ.degree = 1) : φ.ker = ⊥ :=
  φ.ker.eq_bot_of_card_le (h ▸ φ.card_ker_le_degree)

/-- **The kernel counts the degree exactly when it cuts out the pulled-back field.** This is a
*reduction*, not the separable-locus theorem: one inclusion holds for free, so the cardinality
statement and the reverse inclusion are two names for the same thing. What it buys is a single
field-theoretic statement to aim at in place of a cardinality one.

That inclusion is where separability enters, and over a base field that is not separably closed it
can fail: the kernel here consists of the rational points, while the extension is cut out by the
geometric ones. Deriving it from separability and rationality of the geometric kernel is not done
here. -/
theorem card_ker_eq_degree_iff (φ : Isogeny W₁ W₂) :
    Nat.card φ.ker = φ.degree ↔
      translationFixedField W₁ φ.ker ≤ φ.fieldPullback.fieldRange := by
  have hle := φ.fieldPullback_fieldRange_le_translationFixedField_ker
  have htower := IntermediateField.relfinrank_mul_finrank_top hle
  rw [finrank_translationFixedField W₁ φ.ker, ← degree_def] at htower
  refine ⟨fun hcard ↦ ?_, fun h ↦ ?_⟩
  · refine IntermediateField.relfinrank_eq_one_iff.1 ?_
    rw [hcard] at htower
    exact Nat.eq_of_mul_eq_mul_right φ.degree_pos (htower.trans (one_mul _).symm)
  · have hfield : translationFixedField W₁ φ.ker = φ.fieldPullback.fieldRange := le_antisymm h hle
    rw [← finrank_translationFixedField W₁ φ.ker, hfield, ← degree_def]

/-- **The identity isogeny has trivial kernel.** -/
@[simp]
theorem ker_id (W : WeierstrassCurve.Affine F) [W.IsElliptic] : (id W).ker = ⊥ :=
  ker_eq_bot_of_degree_eq_one (degree_id W)

end TauCeti.Isogeny

end
