/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Surjectivity of `Point.toClass`, and what it is equivalent to

Mathlib builds `WeierstrassCurve.Affine.Point.toClass : W.Point →+ Additive (ClassGroup
W.CoordinateRing)` and proves it **injective**, realising the points of an affine Weierstrass
curve as a subgroup of the affine ideal class group. It does not prove surjectivity.

This file names the missing half as a predicate and proves it *equivalent* to surjectivity, so
that a later proof of either immediately yields the group isomorphism.

## Main definitions

* `WeierstrassCurve.Affine.Point.ClassRepresentableByPoints`: every ideal class is
  trivial or the class of `XYIdeal' h` for a nonsingular affine point.
* `WeierstrassCurve.Affine.Point.toClassEquivOfSurjective`: the group isomorphism
  `W.Point ≃+ Additive (ClassGroup W.CoordinateRing)` obtained from a proof of surjectivity.

## Main results

* `WeierstrassCurve.Affine.Point.toClass_surjective_iff_classRepresentableByPoints`:
  surjectivity of `toClass` is equivalent to that predicate.

## What this is, mathematically

`ClassRepresentableByPoints` says every element of `ClassGroup W.CoordinateRing` is the class of
an `XYIdeal'` at a nonsingular affine point, or trivial. It is stated for an arbitrary affine
Weierstrass curve; nothing here assumes smoothness or ellipticity, and no divisor group occurs in
the definition.

On a smooth genus-1 curve, and under the identification of the affine ideal class group with
degree-zero divisor classes, it becomes the familiar divisor-reduction statement — every such
class is `(P) - (O)` for a rational point `P`. That is the reading which motivates isolating the
predicate, since it turns "prove `toClass` is surjective" into the form the geometric proof takes;
but it is an interpretation under extra hypotheses, not the content of the definition.

## What is deliberately not here

**No proof that either side holds.** The two directions below are formal — they unfold `toClass`
and re-package a witness — and neither carries an ellipticity hypothesis. A proof of the
predicate does: it recovers a point from an ideal and needs that point to be nonsingular, which
comes from `Δ ≠ 0`. That step is a separate slice and will carry `[W.IsElliptic]`.

Keeping the split at exactly this line is the point of the file. Everything here is true of any
affine Weierstrass curve over a field, so nothing downstream that only needs the *equivalence*
has to assume ellipticity to get it.

## Design

`toClassEquivOfSurjective` takes surjectivity as an explicit argument rather than as an
instance or a hypothesis class. Mathlib's `toClass_injective` supplies the other half of
bijectivity unconditionally, so the isomorphism is exactly as available as a surjectivity proof
is, and a consumer that obtains one by any route can use it without this file knowing which.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at the
roadmap's HasseWeil pin `dev/hasse-weil @ 513e83879e2f`, file
`HasseWeil/Pic0/ToClassSurjective.lean` (by Chris Birkbeck), declarations
`ClassRepresentableByPoints`, `mem_range_toClass_of_classRep`,
`toClass_surjective_of_classRepresentableByPoints`,
`classRepresentableByPoints_of_toClass_surjective`,
`toClass_surjective_iff_classRepresentableByPoints`, `toClassEquiv_of_surjective` and
`toClassEquiv_of_surjective_apply`. The names above are the source's; the theorems keep them, and
the two naming the `def` are respelt `toClassEquivOfSurjective` and
`toClassEquivOfSurjective_apply` here, because a `def` with an underscore fails this repository's
`defsWithUnderscore` linter.

That file is 920 lines and splits at its line 319: everything above is stated over
`{F} [Field F] {W} [DecidableEq F]`, and everything from `eq_XYIdeal_of_finrank_quotient_eq_one`
onward adds `[W.IsElliptic]`. This port takes the first block only, which is why nothing here
assumes ellipticity. The roadmap describes `toClass_surjective` and `toClassEquiv` as carrying
"no ellipticity hypothesis" (`TauCetiRoadmap/EllipticCurves/README.md:1095`); that is accurate of
this layer and not of the source's headline surjectivity theorem.
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} [DecidableEq F]

/-- **Every ideal class is represented by a point.** Each element of the affine ideal class group
`ClassGroup W.CoordinateRing` is either trivial or the class of `XYIdeal' h` for a nonsingular
affine point `(x, y)`.

This is stated for an arbitrary affine Weierstrass curve: neither smoothness nor ellipticity is
assumed, and no divisor group appears in the definition. Under the hypotheses that make `W` a
smooth genus-1 curve, and the identification of `ClassGroup W.CoordinateRing` with degree-zero
divisor classes, it reads as the familiar statement that every such class is `(P) - (O)` for a
rational point `P` — but that reading is an interpretation, not part of what is defined here.

It is exactly the characterisation of the range of `toClass` needed for surjectivity — see
`toClass_surjective_iff_classRepresentableByPoints`. -/
def ClassRepresentableByPoints (W : _root_.WeierstrassCurve.Affine F) : Prop :=
  ∀ g : ClassGroup W.CoordinateRing,
    g = 1 ∨ ∃ (x y : F) (h : W.Nonsingular x y),
      g = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W := W) h)

/-- Each class of an `XYIdeal'`, and the trivial class, lies in the range of `toClass`. This is
the content-free half of the range characterisation: it only unfolds `toClass`. -/
private theorem mem_range_toClass_of_classRep (g : ClassGroup W.CoordinateRing)
    (hg : g = 1 ∨ ∃ (x y : F) (h : W.Nonsingular x y),
      g = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W := W) h)) :
    Additive.ofMul g ∈ Set.range (toClass (W := W)) := by
  obtain hg | ⟨x, y, h, hg⟩ := hg
  · exact ⟨0, by rw [toClass_zero, hg]; rfl⟩
  · exact ⟨some x y h, by rw [toClass_some, hg]; rfl⟩

/-- Representability of every ideal class by a point implies surjectivity of `toClass`. -/
theorem toClass_surjective_of_classRepresentableByPoints (hrep : ClassRepresentableByPoints W) :
    Function.Surjective (toClass (W := W)) := by
  intro c
  obtain ⟨P, hP⟩ := mem_range_toClass_of_classRep (Additive.toMul c) (hrep _)
  exact ⟨P, by rwa [ofMul_toMul] at hP⟩

/-- Surjectivity of `toClass` implies every ideal class is represented by a point. -/
theorem classRepresentableByPoints_of_toClass_surjective
    (hsurj : Function.Surjective (toClass (W := W))) :
    ClassRepresentableByPoints W := by
  intro g
  obtain ⟨P, hP⟩ := hsurj (Additive.ofMul g)
  cases P with
  | zero =>
      left
      rw [← zero_def, toClass_zero] at hP
      exact (Additive.ofMul.injective hP).symm
  | some x y h =>
      right
      refine ⟨x, y, h, ?_⟩
      rw [toClass_some] at hP
      exact (Additive.ofMul.injective hP).symm

/-- **Surjectivity of `toClass` is equivalent to representability of every ideal class.**
This records exactly what remains to be proved for full surjectivity: that every ideal class is
represented by a rational point. On a smooth genus-1 curve that is divisor reduction. -/
theorem toClass_surjective_iff_classRepresentableByPoints :
    Function.Surjective (toClass (W := W)) ↔ ClassRepresentableByPoints W :=
  ⟨classRepresentableByPoints_of_toClass_surjective,
    toClass_surjective_of_classRepresentableByPoints⟩

/-- **The group isomorphism `W.Point ≃+ Additive (ClassGroup W.CoordinateRing)`**, parametrised
by a proof of surjectivity. Mathlib's `toClass_injective` is the other half of bijectivity and
needs no hypothesis, so any proof of surjectivity upgrades `toClass` to an isomorphism.

The body is not exposed; `toClassEquivOfSurjective_apply` below is the computation rule. -/
noncomputable def toClassEquivOfSurjective (hsurj : Function.Surjective (toClass (W := W))) :
    W.Point ≃+ Additive (ClassGroup W.CoordinateRing) :=
  AddEquiv.ofBijective toClass ⟨toClass_injective, hsurj⟩

-- Proved in term mode rather than by the `rfl` tactic: term-mode elaboration checks at full
-- transparency and so crosses the module boundary that the tactic does not. This is why
-- `toClassEquivOfSurjective` needs no `@[expose]`.
@[simp]
theorem toClassEquivOfSurjective_apply
    (hsurj : Function.Surjective (toClass (W := W))) (P : W.Point) :
    toClassEquivOfSurjective hsurj P = toClass P := (rfl)

end WeierstrassCurve.Affine.Point
