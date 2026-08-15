/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.GroupTheory.Congruence.Basic

/-!
# The relative norm on ideal class groups

For a finite extension `S / R` of Dedekind domains, Mathlib's relative ideal norm
`Ideal.relNorm R : Ideal S →*₀ Ideal R` is multiplicative and sends principal ideals to
principal ideals (`Ideal.relNorm_singleton`), so it descends to a group homomorphism
`ClassGroup.relNorm : ClassGroup S →* ClassGroup R` on ideal class groups.

The descent is along `ClassGroup.mk0 : (Ideal S)⁰ →* ClassGroup S`, which is surjective. Since
`(Ideal S)⁰` is a monoid rather than a group, `MonoidHom.liftOfSurjective` does not apply; the
descent instead goes through the monoid congruence `Con.ker` and
`Con.quotientKerEquivOfSurjective`.

## Main definitions

* `Ideal.relNorm0 : (Ideal S)⁰ →* (Ideal R)⁰`: the relative ideal norm on nonzero ideals.
* `ClassGroup.relNorm : ClassGroup S →* ClassGroup R`.
* `Ideal.extend0 : (Ideal R)⁰ →* (Ideal S)⁰`: ideal extension along `algebraMap R S`, on
  nonzero ideals.
* `ClassGroup.extend : ClassGroup R →* ClassGroup S`: the class-group extension map, the partner
  of `relNorm` in the other direction.

## Main results

* `ClassGroup.relNorm_mk0`: `relNorm (mk0 I) = mk0 (relNorm0 I)`, the defining computation on an
  integral representative, and `ClassGroup.extend_mk0` likewise.
* `ClassGroup.relNorm_extend`: **extend then norm is the `finrank`-th power**,
  `relNorm (extend c) = c ^ Module.finrank R S`, with `ClassGroup.relNorm_comp_extend` the same
  statement as an identity of monoid homomorphisms.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Pic0/ClassGroupNorm.lean`, declarations `relNorm0`, `mk0CompRelNorm0`,
`mk0CompRelNorm0_apply`, `mk0CompRelNorm0_eq_of_mk0_eq`, `ClassGroup.relNorm`,
`ClassGroup.relNorm_mk0` and `ClassGroup.relNorm_mk0'`; and, for the extension direction,
`map0`, `mk0CompMap0`, `mk0CompMap0_apply`, `mk0CompMap0_eq_of_mk0_eq`, `ClassGroup.map`,
`ClassGroup.map_mk0` and `ClassGroup.relNorm_comp_map`.

Deviations from the source. It descends by `Function.surjInv` on `ClassGroup.mk0_surjective`, with
`Function.surjInv_eq` rewrites discharging `map_one'` and `map_mul'`; the congruence route used
here needs no choice plumbing in the proofs. It assumes `IsDomain` and `IsIntegrallyClosed`
alongside `IsDedekindDomain` for both rings, which are implied. Its intermediate
`mk0CompRelNorm0` and that lemma's `_apply` are inlined, the well-definedness fact being stated
directly about `mk0 ∘ relNorm0`. Finally its `relNorm_mk0'`, a restatement of `relNorm_mk0` with
the membership proof spelled out inline, is not ported.

The extension direction follows the same deviations, and two more. Its `ClassGroup.map` is renamed
`ClassGroup.extend`: `map` is the standard name for the *ideal*-level operation this descends from,
and a `ClassGroup.map` would collide with it on sight. Its `ClassGroup.map_one` and
`ClassGroup.map_mul` are not ported — both are `map_one`/`map_mul` applied to a bundled
`MonoidHom`, so they restate what the bundling already gives.

Its `Ideal.relNorm_map_algebraMap` is **not** ported either, and this is not a deviation of taste:
that lemma converts `Ideal.relNorm_algebraMap`'s exponent from
`Module.finrank (FractionRing R) (FractionRing S)` to `Module.finrank R S`. In the Mathlib pinned
here `Ideal.relNorm_algebraMap` already concludes `= I ^ Module.finrank R S`, so the conversion is
a no-op and the lemma performing it (`finrank_of_isFractionRing`) is deprecated. The source itself
says the arithmetic core "is already available in mathlib as `Ideal.relNorm_algebraMap`".
-/

public section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

variable (R) in
/-- The relative ideal norm restricted to nonzero ideals, using that it reflects `⊥`
(`Ideal.relNorm_eq_bot_iff`). -/
noncomputable def Ideal.relNorm0 : (Ideal S)⁰ →* (Ideal R)⁰ :=
  ((Ideal.relNorm R).toMonoidHom.domRestrict (Ideal S)⁰).codRestrict (Ideal R)⁰ fun I =>
    mem_nonZeroDivisors_iff_ne_zero.mpr <|
      Ideal.relNorm_eq_bot_iff.not.mpr <| mem_nonZeroDivisors_iff_ne_zero.mp I.2

@[simp]
theorem Ideal.coe_relNorm0 (I : (Ideal S)⁰) :
    (Ideal.relNorm0 R I : Ideal R) = Ideal.relNorm R (I : Ideal S) :=
  (rfl)

namespace ClassGroup

/-- **Well-definedness of the class-group relative norm**: integral ideals with the same class have
relative norms with the same class.

By `ClassGroup.mk0_eq_mk0_iff` the hypothesis says `span {x} * I = span {y} * J` for nonzero
`x y : S`; applying `Ideal.relNorm` and using `Ideal.relNorm_singleton` turns this into the same
relation between the norms, with the nonzero elements `Algebra.intNorm R S x` and
`Algebra.intNorm R S y`. -/
private theorem mk0_relNorm0_eq_of_mk0_eq {I J : (Ideal S)⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (Ideal.relNorm0 R I) = ClassGroup.mk0 (Ideal.relNorm0 R J) := by
  -- `Algebra.intNorm_ne_zero` needs the fraction fields to form a finite extension; the lifted
  -- algebra is deliberately not an instance, so it is supplied here.
  let _ : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R (FractionRing S)
  have : IsScalarTower R (FractionRing R) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization R (FractionRing R) (FractionRing S) S
  have : IsScalarTower R S (FractionRing S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite.of_isLocalization R S R⁰
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨Algebra.intNorm R S x, Algebra.intNorm R S y,
    Algebra.intNorm_ne_zero.mpr hx, Algebra.intNorm_ne_zero.mpr hy, ?_⟩
  rw [Ideal.coe_relNorm0, Ideal.coe_relNorm0, ← Ideal.relNorm_singleton (R := R) x,
    ← Ideal.relNorm_singleton (R := R) y, ← map_mul, ← map_mul, hxy]

/-- The **relative norm on class groups**, induced by `Ideal.relNorm`.

Every class has an integral representative, since `ClassGroup.mk0` is surjective, and the class of
the norm does not depend on the representative; `ClassGroup.relNorm_mk0` is the resulting
computation. -/
noncomputable def relNorm : ClassGroup S →* ClassGroup R :=
  ((Con.ker (ClassGroup.mk0 (R := S))).lift ((ClassGroup.mk0 (R := R)).comp (Ideal.relNorm0 R))
      fun _ _ h => mk0_relNorm0_eq_of_mk0_eq h).comp
    (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm.toMonoidHom

/-- The relative norm of the class represented by a nonzero ideal `I` is the class represented by
`I`'s relative norm. This is the computation rule for `ClassGroup.relNorm`. -/
@[simp]
theorem relNorm_mk0 (I : (Ideal S)⁰) :
    relNorm (R := R) (ClassGroup.mk0 I) = ClassGroup.mk0 (Ideal.relNorm0 R I) := by
  have h : (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm
      (ClassGroup.mk0 (R := S) I) = (I : (Con.ker (ClassGroup.mk0 (R := S))).Quotient) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  rw [relNorm, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl

variable (S) in
omit [Module.Finite R S] in
/-- The extension of an integral ideal along `algebraMap R S`, restricted to nonzero ideals.

Extension reflects `⊥` because `algebraMap R S` is injective
(`Ideal.map_eq_bot_iff_of_injective`), which is what keeps it inside `(Ideal S)⁰`. -/
noncomputable def _root_.Ideal.extend0 : (Ideal R)⁰ →* (Ideal S)⁰ where
  toFun I := ⟨Ideal.map (algebraMap R S) (I : Ideal R), by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, ← bot_eq_zero,
      Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S), bot_eq_zero,
      ← ne_eq, ← mem_nonZeroDivisors_iff_ne_zero]
    exact I.2⟩
  map_one' := by ext; simp [Ideal.one_eq_top, Ideal.map_top]
  map_mul' I J := by ext; simp [Ideal.map_mul]

omit [Module.Finite R S] in
@[simp]
theorem _root_.Ideal.coe_extend0 (I : (Ideal R)⁰) :
    (Ideal.extend0 S I : Ideal S) = Ideal.map (algebraMap R S) (I : Ideal R) :=
  (rfl)

omit [Module.Finite R S] in
/-- **Well-definedness of the class-group extension**: integral ideals with the same class have
extensions with the same class.

By `ClassGroup.mk0_eq_mk0_iff` the hypothesis says `span {x} * I = span {y} * J` for nonzero
`x y : R`. Extension is multiplicative and carries `span {x}` to `span {algebraMap R S x}`
(`Ideal.map_span`), and those generators stay nonzero because `algebraMap R S` is injective. -/
private theorem mk0_extend0_eq_of_mk0_eq {I J : (Ideal R)⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (Ideal.extend0 S I) = ClassGroup.mk0 (Ideal.extend0 S J) := by
  have hinj := FaithfulSMul.algebraMap_injective R S
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  have hspan : ∀ a : R, Ideal.span {algebraMap R S a}
      = Ideal.map (algebraMap R S) (Ideal.span {a}) := fun a => by
    rw [Ideal.map_span, Set.image_singleton]
  refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨algebraMap R S x, algebraMap R S y,
    (map_ne_zero_iff _ hinj).mpr hx, (map_ne_zero_iff _ hinj).mpr hy, ?_⟩
  rw [Ideal.coe_extend0, Ideal.coe_extend0, hspan x, hspan y, ← Ideal.map_mul, ← Ideal.map_mul,
    hxy]

omit [Module.Finite R S] in
/-- The **extension map on class groups**, induced by `Ideal.map (algebraMap R S)`.

The partner of `ClassGroup.relNorm` in the other direction, descended the same way: every class has
an integral representative and the class of the extension does not depend on which. -/
noncomputable def extend : ClassGroup R →* ClassGroup S :=
  ((Con.ker (ClassGroup.mk0 (R := R))).lift ((ClassGroup.mk0 (R := S)).comp (Ideal.extend0 S))
      fun _ _ h => mk0_extend0_eq_of_mk0_eq h).comp
    (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm.toMonoidHom

omit [Module.Finite R S] in
/-- The extension of the class represented by a nonzero ideal `I` is the class represented by `I`'s
extension. This is the computation rule for `ClassGroup.extend`. -/
@[simp]
theorem extend_mk0 (I : (Ideal R)⁰) :
    extend (S := S) (ClassGroup.mk0 I) = ClassGroup.mk0 (Ideal.extend0 S I) := by
  have h : (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm
      (ClassGroup.mk0 (R := R) I) = (I : (Con.ker (ClassGroup.mk0 (R := R))).Quotient) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  rw [extend, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl

/-- **Norm of an extended ideal is the `finrank`-th power**, on nonzero ideals: the
`(Ideal R)⁰`-level form of Mathlib's `Ideal.relNorm_algebraMap`, which supplies the whole
arithmetic content. -/
theorem _root_.Ideal.relNorm0_extend0 (I : (Ideal R)⁰) :
    Ideal.relNorm0 R (Ideal.extend0 S I) = I ^ Module.finrank R S := by
  refine Subtype.ext ?_
  rw [Ideal.coe_relNorm0, Ideal.coe_extend0, SubmonoidClass.coe_pow]
  exact Ideal.relNorm_algebraMap S (I : Ideal R)

/-- **Extending a class and taking its relative norm raises it to the `finrank`-th power.**

Mathlib's `Ideal.relNorm_algebraMap` needs no separability, Galois or perfect-field hypothesis, so
neither does this. -/
theorem relNorm_extend (c : ClassGroup R) :
    relNorm (extend (S := S) c) = c ^ Module.finrank R S := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [extend_mk0, relNorm_mk0, Ideal.relNorm0_extend0]
  exact map_pow ClassGroup.mk0 I (Module.finrank R S)

/-- `ClassGroup.relNorm_extend` as an identity of monoid homomorphisms. -/
theorem relNorm_comp_extend :
    (relNorm (R := R)).comp (extend (S := S)) = powMonoidHom (Module.finrank R S) := by
  ext c
  rw [MonoidHom.comp_apply, powMonoidHom_apply, relNorm_extend]

end ClassGroup
