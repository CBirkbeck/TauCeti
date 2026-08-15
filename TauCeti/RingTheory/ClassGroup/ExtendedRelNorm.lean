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

The two directions constrain different data. The extension asks that `A → M` be an injective map
of domains; the norm asks that `M` be a Dedekind domain, module-finite and torsion-free over the
Dedekind domain `R`. `M` therefore carries hypotheses from both sides and is not merely a common
overring. What is independent is `A` and `R`: neither need map to the other, and in the intended
application they do not — they are the coordinate rings of the source and target of an isogeny,
and `M` is the integral closure of the target's coordinate ring in the source's function field,
which receives both.

## Main definitions

* `ClassGroup.extendedRelNormHom`: extend a class from `A` into `M`, then norm down to `R`.

## Main results

* `ClassGroup.extendedRelNormHom_mk0`: its value on the class of a nonzero integral ideal, as
  the class of that ideal's extension into `M` normed back down.

## Implementation notes

**The definition and its computation rule sit at the same level, deliberately.**
`ClassGroup.extendedRelNormHom` would elaborate under the weaker `IsDomain A`, since
`ClassGroup.extendedHom` asks only for domains with `Module.IsTorsionFree A M`. It is not stated
there. The computation rule unavoidably needs `IsDedekindDomain A` — it speaks about
`ClassGroup.mk0` on `A`, and Mathlib states `ClassGroup.extendedHom_mk0` under that hypothesis —
so at the weaker level the definition would have an unexposed body and no lemma relating it to
either composand: opaque to every consumer. Generality that nothing can characterise is not
generality, so both declarations carry `IsDedekindDomain A`.

**Why the three types are distinct.** With the source and target ring literally equal — the
endomorphism case — Lean cannot keep two `Algebra R FF` structures apart, an instance diamond the
source of the same construction records in its own header. Stating the composite at three types
avoids it by construction rather than by `@`-elaboration.

## Provenance

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md:1092` lists
`ClassGroup.extendedRelNormHom` among the components of D. Angdinata's shared isogeny development,
under the same flag the sibling `Isogeny` files carry.

No AINTLIB material is ported, but that repository carries the two nearest relatives, and the
shape of this file follows from how each falls short of the composite. At
`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `dev/hasse-weil @ 513e83879e2f`, by Chris Birkbeck:

* `HasseWeil/Pic0/IsogenyClassGroup.lean` (`classNorm`, `classMap`, `classNorm_comp_classMap`)
  is the **endomorphism** case — both sides are `ClassGroup E.CoordinateRing` — so it is the
  same-ring composite, not a map between two class groups. It is where the instance diamond
  above is recorded.
* `HasseWeil/EC/IsogenyAG/TwoCurveNormConorm.lean` is genuinely two-curve but at the **field**
  level: its `conorm` is `Algebra.norm : K(E₁) →* K(E₂)`, not a class-group map. It reaches for
  `integralClosure (localized φ*F[E₂]) K(E₁)` — the object TauCeti calls
  `Isogeny.intermediateRing` — for the same reason this API exists, without taking the
  class-group composite through it.
-/

public section

open scoped nonZeroDivisors

namespace ClassGroup

variable (A M R : Type*) [CommRing A] [CommRing M] [CommRing R]
  [IsDedekindDomain M] [IsDedekindDomain R] [Algebra A M] [Module.IsTorsionFree A M]
  [Algebra R M] [Module.Finite R M] [Module.IsTorsionFree R M]

variable [IsDedekindDomain A]

/-- **Extend a class into `M`, then norm it down to `R`.** The extension direction is Mathlib's
`ClassGroup.extendedHom`, along `A → M`; the norm is `ClassGroup.relNorm`, down the module-finite
extension `M / R`. The two share only the overring `M`, so this is a map between the class groups
of two rings with no map between them. -/
noncomputable def extendedRelNormHom : ClassGroup A →* ClassGroup R :=
  relNorm.comp (extendedHom A M)

/-- The value of `ClassGroup.extendedRelNormHom` on the class of a nonzero integral ideal: extend
the ideal into `M`, take its relative norm down to `R`, and read off the class. This is the
computation rule, obtained from `ClassGroup.extendedHom_mk0` and `ClassGroup.relNorm_mk0`.

`IsDedekindDomain A` is what `ClassGroup.mk0` on `A` needs; see the implementation notes for why
the definition carries it too. -/
@[simp]
theorem extendedRelNormHom_mk0 (I : (Ideal A)⁰) :
    extendedRelNormHom A M R (ClassGroup.mk0 I) =
      ClassGroup.mk0 (Ideal.relNorm0 R (extendedIdeal A M I)) := by
  rw [extendedRelNormHom, MonoidHom.comp_apply, extendedHom_mk0, relNorm_mk0]

end ClassGroup
