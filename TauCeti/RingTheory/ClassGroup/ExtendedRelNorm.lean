/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: `ClassGroup.extendedHom` and `ClassGroup.relNorm` are the two composands, and
-- `ClassGroup.extendedIdeal` / `Ideal.relNorm0` appear in the computation rule.
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import TauCeti.RingTheory.ClassGroup.RelNorm

/-!
# Extending a class into an overring and norming it back down

Two rings map into a common overring `M`: a ring `A` along `Algebra A M`, and a Dedekind domain
`R` over which `M` is module-finite. Extending an ideal class from `A` into `M`
(`ClassGroup.extendedHom`) and then taking its relative norm down to `R`
(`ClassGroup.relNorm`) is a homomorphism `ClassGroup A →* ClassGroup R`. This file names that
composite and gives its computation rule on an integral representative.

The two directions are independent of one another: the extension needs only that `A → M` is an
injective map of domains, while the norm needs `M` module-finite over `R`. Neither ring need map
to the other, and in the intended application they do not — `A` and `R` are the coordinate rings
of the source and target of an isogeny, and `M` is the integral closure of the target's
coordinate ring in the source's function field, which receives both.

## Main definitions

* `ClassGroup.extendedRelNormHom`: extend a class from `A` into `M`, then norm down to `R`.

## Main results

* `ClassGroup.extendedRelNormHom_mk0`: its value on the class of a nonzero integral ideal, as
  the class of that ideal's extension into `M` normed back down.

## Implementation notes

**The definition and its computation rule sit at different levels, deliberately.**
`ClassGroup.extendedRelNormHom` needs only `IsDomain A`: `ClassGroup.extendedHom` asks for
domains with `Module.IsTorsionFree A M`, and the norm side constrains `M` and `R` alone. The
computation rule needs `IsDedekindDomain A` as well, and unavoidably — it speaks about
`ClassGroup.mk0` on `A`, and Mathlib states `ClassGroup.extendedHom_mk0` under that hypothesis
too. So the stronger assumption is carried on the one declaration that uses it rather than on
the whole file.

This is original work. Mathlib carries both composands but not the composite, and no
`relNorm`-of-an-extension appears there in any spelling; the same-ring specialisation
`relNorm ∘ extendedHom` — which is the `Module.finrank` power map rather than a map between
different class groups — is a separate statement and does not subsume this one.

## Provenance

No AINTLIB material is ported, but that repository has closely related work which motivated
this file's shape, and the relationship is worth stating rather than leaving implicit. At
`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `dev/modular-curves @ 513e83879e2f`:

* `HasseWeil/Pic0/IsogenyClassGroup.lean` (`classNorm`, `classMap`, `classNorm_comp_classMap`)
  is the **endomorphism** case — `α : Isogeny E E`, so both sides are
  `ClassGroup E.CoordinateRing` and the extension is twisted by `ch.toAlgebra`. That is the
  same-ring composite, not a map between two class groups. Its header also records a genuine
  instance diamond in that formulation: with the source and target ring literally equal, Lean
  cannot keep two `Algebra R FF` structures apart. Stating this at three distinct types
  `A`, `M`, `R` avoids the diamond by construction rather than by `@`-elaboration, which is
  the reason for the three-type signature above.
* `HasseWeil/EC/IsogenyAG/TwoCurveNormConorm.lean` is genuinely two-curve, but at the
  **field** level: its `conorm` is `Algebra.norm : K(E₁) →* K(E₂)`, not a class-group map. Its
  header records why the coordinate-ring route is unavailable for a two-curve isogeny — there
  is no comorphism `F[E₂] → F[E₁]`, since `φ*(x_gen₂)` has poles on the affine kernel — and
  routes around it through `integralClosure (localized φ*F[E₂]) K(E₁)`, the object TauCeti
  calls `Isogeny.intermediateRing`. So the source reaches for the intermediate ring for
  exactly the reason this API exists; what it does not do is take the class-group composite
  through it.
-/

public section

open scoped nonZeroDivisors

namespace ClassGroup

variable (A M R : Type*) [CommRing A] [CommRing M] [CommRing R]
  [IsDedekindDomain M] [IsDedekindDomain R] [Algebra A M] [Module.IsTorsionFree A M]
  [Algebra R M] [Module.Finite R M] [Module.IsTorsionFree R M]

variable [IsDomain A] in
/-- **Extend a class into `M`, then norm it down to `R`.** The extension direction is Mathlib's
`ClassGroup.extendedHom`, along `A → M`; the norm is `ClassGroup.relNorm`, down the module-finite
extension `M / R`. The two share only the overring `M`, so this is a map between the class groups
of two rings with no map between them. -/
noncomputable def extendedRelNormHom : ClassGroup A →* ClassGroup R :=
  relNorm.comp (extendedHom A M)

/-- The value of `ClassGroup.extendedRelNormHom` on the class of a nonzero integral ideal: extend
the ideal into `M`, take its relative norm down to `R`, and read off the class. This is the
computation rule, obtained from `ClassGroup.extendedHom_mk0` and `ClassGroup.relNorm_mk0`.

Unlike the definition this needs `A` Dedekind, since it speaks about `ClassGroup.mk0` on `A`. -/
@[simp]
theorem extendedRelNormHom_mk0 [IsDedekindDomain A] (I : (Ideal A)⁰) :
    extendedRelNormHom A M R (ClassGroup.mk0 I) =
      ClassGroup.mk0 (Ideal.relNorm0 R (extendedIdeal A M I)) := by
  rw [extendedRelNormHom, MonoidHom.comp_apply, extendedHom_mk0, relNorm_mk0]

end ClassGroup
