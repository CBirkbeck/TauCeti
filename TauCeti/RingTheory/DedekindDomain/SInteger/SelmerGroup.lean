/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.NthRoot
public import TauCeti.RingTheory.DedekindDomain.SInteger.ClassGroup
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

/-!
# The fundamental exact sequence of the Selmer group, and its finiteness

Let `R` be a Dedekind domain with fraction field `K`, let `S` be a set of height-one primes of `R`
and let `n : ℕ`. Mathlib defines the Selmer group `K⟮S, n⟯` as the subgroup of `Kˣ ⧸ (Kˣ)ⁿ` of
classes whose `v`-adic valuation is divisible by `n` for every `v ∉ S`, and its module docstring
records as `TODO` both *"maps in the sequence"*, *"proofs of exactness of the sequence"* and
*"proofs of finiteness for global fields"*. This file supplies all three, in the form
```
1 → 𝒪_S(K)ˣ / (𝒪_S(K)ˣ)ⁿ → K⟮S, n⟯ → Cl_S(R)[n] → 1
```
where `𝒪_S(K) = Set.integer S K` is the ring of `S`-integers and the `S`-class group `Cl_S(R)` is
`ClassGroup (S.integer K)`.

## The dictionary that makes it work

The `S`-integers are a Dedekind domain with fraction field `K` whose height-one primes are exactly
the `v ∉ S` (`IsDedekindDomain.integerHeightOneSpectrumEquiv`), valuation-compatibly
(`IsDedekindDomain.valuation_integerHeightOneSpectrumEquiv`). Under that dictionary the Selmer
condition on a class `u(Kˣ)ⁿ` says exactly that the principal fractional ideal `(u)` of `𝒪_S` has
all of its multiplicities divisible by `n` — this is `mem_selmerGroup_iff_mem_unitsNDivisible` —
so the right-hand map is the `n`-th root class map
`TauCeti.AlgebraicGeometry.WeilDivisor.nthRootClass` of the `S`-integers, descended along the
surjection `unitsNDivisibleToSelmerGroup`.

## Main definitions

* `IsDedekindDomain.unitToSelmerGroup`: the left-hand map, from the `S`-units to `K⟮S, n⟯`.
* `IsDedekindDomain.unitModPowToSelmerGroup`: the same map after dividing out `n`-th powers of
  `S`-units, which is the left-hand map of the exact sequence proper.
* `IsDedekindDomain.unitsNDivisibleToSelmerGroup`: the surjection onto `K⟮S, n⟯` from the units of
  `K` whose principal `𝒪_S`-ideal is `n`-divisible.
* `IsDedekindDomain.selmerGroupToClassGroup`: the right-hand map, to `ClassGroup (S.integer K)`.

## Main results

* `IsDedekindDomain.mem_selmerGroup_iff_mem_unitsNDivisible`: the Selmer condition on a
  representative is `n`-divisibility of its principal `𝒪_S`-ideal.
* `IsDedekindDomain.ker_selmerGroupToClassGroup`: **exactness in the middle** — a Selmer class has
  trivial `n`-th-root ideal class exactly when an `S`-unit represents it. This half needs no
  `n ≠ 0`.
* `IsDedekindDomain.range_selmerGroupToClassGroup`: **exactness on the right** — the image is the
  `n`-torsion of the `S`-class group. (Surjectivity onto the whole class group is false in
  general.)
* `IsDedekindDomain.finite_selmerGroup`: **the Selmer group `K⟮S, n⟯` is finite** when `Cl(R)` is
  finite, `Rˣ` is finitely generated, `S` is finite and `n ≠ 0`.

Finiteness is not automatic for a general Dedekind domain — it already fails for `R = K` a field
whose unit group is not `n`-divisible of finite index — and the exact sequence isolates what is
needed: finite generation of the `S`-units and finiteness of the `S`-class group. Both are on hand,
as `Set.unit_fg_of_units` and `IsDedekindDomain.finite_integer_classGroup`, and both are
`instance`s, so `finite_selmerGroup` takes the hypotheses in the form the arithmetic supplies them:
`[Finite (ClassGroup R)]`, `[Monoid.FG Rˣ]`, `[Finite S]` and `[NeZero n]`. For `R` the ring of
integers of a number field these are the class number theorem and Dirichlet's unit theorem.

## References

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at the
`EllipticCurves` roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), whose treatment this
follows. The names differ: the substrate that source keeps in its own `FractionalIdeal` file is
already here as `TauCeti.AlgebraicGeometry.WeilDivisor.nthRootClass` and its neighbours, and the
`S`-integer dictionary is already here under `IsDedekindDomain.integer*`, so only the Selmer layer
itself is adapted. Following this repository's convention for adapted material, the upstream
authorship is credited here rather than in the copyright header.
-/

public section

open FractionalIdeal IsDedekindDomain.HeightOneSpectrum TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R)) (n : ℕ)

/-! ### The left-hand map: `S`-units into the Selmer group -/

/-- The class of an `S`-unit lies in the Selmer group `K⟮S, n⟯`: away from `S` an `S`-unit has
trivial valuation, so in particular a valuation divisible by `n`. -/
noncomputable def unitToSelmerGroup : S.unit K →* selmerGroup (K := K) (S := S) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), fun v hv ↦ by
    rw [valuationOfNeZeroMod_mk_eq_one_iff]
    simp [(valuationOfNeZero_eq_one_iff v (x : Kˣ)).mpr (x.property v hv)]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The Selmer class of an `S`-unit is, underneath the subtype, just its class in `Kˣ ⧸ (Kˣ)ⁿ`. -/
@[simp]
lemma coe_unitToSelmerGroup (x : S.unit K) :
    (unitToSelmerGroup K S n x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      QuotientGroup.mk (x : Kˣ) :=
  (rfl)

/-- The left-hand map of the fundamental exact sequence: an `S`-unit modulo `n`-th powers of
`S`-units maps to the Selmer group `K⟮S, n⟯`. -/
noncomputable def unitModPowToSelmerGroup :
    (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) →*
      selmerGroup (K := K) (S := S) (n := n) :=
  QuotientGroup.lift _ (unitToSelmerGroup K S n) <| by
    rintro _ ⟨x, rfl⟩
    exact Subtype.ext <| (QuotientGroup.eq_one_iff _).mpr ⟨(x : Kˣ), rfl⟩

/-- Dividing out the `n`-th powers of `S`-units does not change the image: the two left-hand maps
have the same range. -/
@[simp]
lemma range_unitModPowToSelmerGroup :
    (unitModPowToSelmerGroup K S n).range = (unitToSelmerGroup K S n).range := by
  ext
  refine ⟨?_, fun ⟨y, hy⟩ ↦ ⟨QuotientGroup.mk y, hy⟩⟩
  rintro ⟨y, rfl⟩
  induction y using QuotientGroup.induction_on with
  | H y => exact ⟨y, rfl⟩

/-! ### The Selmer condition as `n`-divisibility of an ideal -/

/-- Transport of the integer-valued valuation along the correspondence between the height-one
primes of `R` away from `S` and those of the `S`-integers. -/
lemma valuationOfNeZero_integerHeightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S})
    (u : Kˣ) : (integerHeightOneSpectrumEquiv K S v).valuationOfNeZero u
      = (v : HeightOneSpectrum R).valuationOfNeZero u := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, valuationOfNeZero_eq,
    valuation_integerHeightOneSpectrumEquiv K S v (u : K)]

/-- The `v`-adic order of a unit is minus the multiplicity of its principal fractional ideal.
This is the `Multiplicative ℤ`-valued form of
`fractionalIdeal_count_toPrincipalIdeal_eq_neg_log_valuation`, which states the same fact through
`WithZero.log` of the `ℤₘ₀`-valued valuation. It is needed at two different base rings below — `R`
itself and the `S`-integers — so it is stated for a general Dedekind domain with fraction field
`K`. -/
private lemma toAdd_valuationOfNeZero_eq_neg_count {T : Type*} [CommRing T] [IsDedekindDomain T]
    [Algebra T K] [IsFractionRing T K] (w : HeightOneSpectrum T) (u : Kˣ) :
    Multiplicative.toAdd (w.valuationOfNeZero u) = -count K w (spanSingleton T⁰ (u : K)) := by
  have h := fractionalIdeal_count_toPrincipalIdeal_eq_neg_log_valuation (R := T) (K := K) w u
  rw [coe_toPrincipalIdeal, ← valuationOfNeZero_eq] at h
  rw [h, neg_neg]
  rfl

/-- The class of `u` lies in the Selmer group `K⟮S, n⟯` exactly when the principal fractional
ideal `(u)` of the `S`-integers has all of its multiplicities divisible by `n`. This is the
dictionary that turns the Selmer condition into a statement about ideals of `𝒪_S`, and hence
lets the `n`-th root class map act as the right-hand map of the exact sequence. -/
lemma mem_selmerGroup_iff_mem_unitsNDivisible (u : Kˣ) :
    (QuotientGroup.mk u : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      u ∈ unitsNDivisible (S.integer K) K n := by
  have lhs : (QuotientGroup.mk u : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      ∀ v ∉ S, (n : ℤ) ∣ Multiplicative.toAdd ((v : HeightOneSpectrum R).valuationOfNeZero u) :=
    forall₂_congr fun v _ ↦ valuationOfNeZeroMod_mk_eq_one_iff v n u
  have rhs : u ∈ unitsNDivisible (S.integer K) K n ↔
      ∀ w : HeightOneSpectrum (S.integer K),
        (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
    rw [mem_unitsNDivisible]
    exact forall_congr' fun w ↦ by
      rw [toAdd_valuationOfNeZero_eq_neg_count K w u, Int.dvd_neg]
  rw [lhs, rhs]
  refine ⟨fun h w ↦ ?_, fun h v hv ↦ ?_⟩
  · rw [← (integerHeightOneSpectrumEquiv K S).apply_symm_apply w,
      valuationOfNeZero_integerHeightOneSpectrumEquiv K S _ u]
    exact h _ ((integerHeightOneSpectrumEquiv K S).symm w).property
  · have hw := h (integerHeightOneSpectrumEquiv K S ⟨v, hv⟩)
    rwa [valuationOfNeZero_integerHeightOneSpectrumEquiv K S ⟨v, hv⟩ u] at hw

/-! ### The surjection from the `n`-divisible units -/

/-- The surjection from the units of `K` whose principal `𝒪_S`-ideal is `n`-divisible onto the
Selmer group `K⟮S, n⟯`, given by taking the class modulo `n`-th powers. -/
noncomputable def unitsNDivisibleToSelmerGroup :
    unitsNDivisible (S.integer K) K n →* selmerGroup (R := R) (K := K) (S := S) (n := n) :=
  ((QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range).comp
    (unitsNDivisible (S.integer K) K n).subtype).codRestrict _
      fun u ↦ (mem_selmerGroup_iff_mem_unitsNDivisible K S n (u : Kˣ)).mpr u.2

/-- Underneath the codomain restriction, `unitsNDivisibleToSelmerGroup` is the quotient map. -/
@[simp]
lemma coe_unitsNDivisibleToSelmerGroup (u : unitsNDivisible (S.integer K) K n) :
    (unitsNDivisibleToSelmerGroup K S n u : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      QuotientGroup.mk (u : Kˣ) :=
  (rfl)

/-- **Every Selmer class is represented by an `n`-divisible unit.** This is what lets the `n`-th
root class map be transported from `unitsNDivisible` to the Selmer group. -/
lemma unitsNDivisibleToSelmerGroup_surjective :
    Function.Surjective (unitsNDivisibleToSelmerGroup K S n) := by
  rintro ⟨c, hc⟩
  induction c using QuotientGroup.induction_on with
  | H u => exact ⟨⟨u, (mem_selmerGroup_iff_mem_unitsNDivisible K S n u).mp hc⟩, rfl⟩

/-- The kernel of `unitsNDivisibleToSelmerGroup` is contained in that of the `n`-th root class
map: a unit that is an `n`-th power in `Kˣ` has principal `n`-th root. This is what lets the
`n`-th root class map descend to the Selmer group. -/
lemma ker_unitsNDivisibleToSelmerGroup_le :
    (unitsNDivisibleToSelmerGroup K S n).ker ≤ (nthRootClass (S.integer K) K n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hu)
  exact (nthRootClass_eq_one_iff (S.integer K) K u).mpr
    ⟨1, w, by rw [map_one, one_mul]; exact hw⟩

/-! ### The right-hand map, and exactness -/

/-- The right-hand map of the fundamental exact sequence: a Selmer class is sent to the ideal
class of the `n`-th root of the principal ideal `(u)` of any representative `u`, in the class
group of the `S`-integers. Obtained by descending the `n`-th root class map along
`unitsNDivisibleToSelmerGroup`. -/
noncomputable def selmerGroupToClassGroup :
    selmerGroup (R := R) (K := K) (S := S) (n := n) →* ClassGroup (S.integer K) :=
  (QuotientGroup.lift _ (nthRootClass (S.integer K) K n)
      (ker_unitsNDivisibleToSelmerGroup_le K S n)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (unitsNDivisibleToSelmerGroup_surjective K S n)).symm.toMonoidHom

/-- The defining property of `selmerGroupToClassGroup`: on the class of an `n`-divisible unit it
agrees with the `n`-th root class map it descends from. Every computation with the right-hand map
goes through this lemma, after `unitsNDivisibleToSelmerGroup_surjective` supplies a
representative. -/
lemma selmerGroupToClassGroup_unitsNDivisibleToSelmerGroup
    (u : unitsNDivisible (S.integer K) K n) :
    selmerGroupToClassGroup K S n (unitsNDivisibleToSelmerGroup K S n u) =
      nthRootClass (S.integer K) K n u := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _
      (unitsNDivisibleToSelmerGroup_surjective K S n)).symm
        (unitsNDivisibleToSelmerGroup K S n u) = QuotientGroup.mk u := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [selmerGroupToClassGroup, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h,
    QuotientGroup.lift_mk']

/-- **Exactness in the middle of the fundamental exact sequence.** A Selmer class has trivial
`n`-th-root ideal class exactly when it is represented by an `S`-unit.

No `[NeZero n]` is needed, unlike on the right-hand exactness below: `nthRootClass_eq_one_iff`
is stated here for every `n`, degenerate `n = 0` included. -/
theorem ker_selmerGroupToClassGroup :
    (selmerGroupToClassGroup K S n).ker = (unitToSelmerGroup K S n).range := by
  ext x
  obtain ⟨u, rfl⟩ := unitsNDivisibleToSelmerGroup_surjective K S n x
  rw [MonoidHom.mem_ker, selmerGroupToClassGroup_unitsNDivisibleToSelmerGroup,
    nthRootClass_eq_one_iff (S.integer K) K]
  constructor
  · rintro ⟨a, w, hw⟩
    refine ⟨(S.unitEquivUnitsInteger K).symm a, Subtype.ext ?_⟩
    change (QuotientGroup.mk _ : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      QuotientGroup.mk (u : Kˣ)
    have hcoe : ((S.unitEquivUnitsInteger K).symm a : Kˣ) =
        Units.map (algebraMap (S.integer K) K : S.integer K →* K) a := Units.ext rfl
    -- The two representatives differ by `w ^ n`, which is what the quotient divides out.
    refine QuotientGroup.eq.mpr ?_
    rw [hcoe, ← hw, inv_mul_cancel_left]
    exact ⟨w, rfl⟩
  · rintro ⟨s, hs⟩
    obtain ⟨w, hw⟩ := QuotientGroup.eq.mp (congrArg Subtype.val hs)
    refine ⟨S.unitEquivUnitsInteger K s, w, ?_⟩
    have hmap : Units.map (algebraMap (S.integer K) K : S.integer K →* K)
        (S.unitEquivUnitsInteger K s) = (s : Kˣ) := Units.ext rfl
    rw [powMonoidHom_apply] at hw
    rw [hmap, hw, mul_inv_cancel_left]
    rfl

/-- **Exactness on the right of the fundamental exact sequence.** The image of
`selmerGroupToClassGroup` is the `n`-torsion of the class group of the `S`-integers; surjectivity
onto the full class group fails in general. -/
theorem range_selmerGroupToClassGroup [NeZero n] :
    (selmerGroupToClassGroup K S n).range =
      (powMonoidHom n : ClassGroup (S.integer K) →* ClassGroup (S.integer K)).ker := by
  ext c
  rw [MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := unitsNDivisibleToSelmerGroup_surjective K S n x
    rw [selmerGroupToClassGroup_unitsNDivisibleToSelmerGroup]
    exact nthRootClass_pow _ _ _ _
  · intro hc
    obtain ⟨I, rfl⟩ : ∃ I, ClassGroup.mk K I = c :=
      ClassGroup.induction (K := K) (fun I ↦ ⟨I, rfl⟩) c
    rw [← map_pow, ClassGroup.mk_eq_one_iff_exists] at hc
    obtain ⟨x, hx⟩ := hc
    have hcount (v : HeightOneSpectrum (S.integer K)) :
        count K v (spanSingleton (S.integer K)⁰ (x : K)) =
          n * count K v ((I : (FractionalIdeal (S.integer K)⁰ K)ˣ) :
            FractionalIdeal (S.integer K)⁰ K) := by
      rw [← coe_toPrincipalIdeal, hx, Units.val_pow_eq_pow_val, count_pow]
    have hmem : x ∈ unitsNDivisible (S.integer K) K n :=
      mem_unitsNDivisible.mpr fun v ↦ by rw [hcount v]; exact Dvd.intro _ rfl
    refine ⟨unitsNDivisibleToSelmerGroup K S n ⟨x, hmem⟩, ?_⟩
    rw [selmerGroupToClassGroup_unitsNDivisibleToSelmerGroup, nthRootClass_apply]
    congr 1
    refine units_eq_of_forall_count_eq _ _ fun v ↦ ?_
    rw [count_nthRootHom, coe_unitsNDivisibleToNDivisible, coe_toPrincipalIdeal, hcount v,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne n))]

/-! ### Finiteness -/

variable (R) in
/-- **The Selmer group `K⟮S, n⟯` is finite**, provided that the class group of `R` is finite, that
`Rˣ` is finitely generated, that `S` is finite and that `n ≠ 0`. This discharges the `TODO`
*"proofs of finiteness for global fields"* of `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`.

The image of `unitModPowToSelmerGroup` is finite, because its source is the quotient of the
finitely generated commutative group of `S`-units by its `n`-th powers. By
`ker_selmerGroupToClassGroup` that image is the kernel of `selmerGroupToClassGroup`, whose target
`ClassGroup (S.integer K)` is finite; a group with finite kernel and finite quotient is finite. -/
theorem finite_selmerGroup [Finite (ClassGroup R)] [Monoid.FG Rˣ] [Finite S] [NeZero n] :
    Finite (selmerGroup (K := K) (S := S) (n := n)) := by
  have hker : Finite (selmerGroupToClassGroup K S n).ker := by
    rw [ker_selmerGroupToClassGroup, ← range_unitModPowToSelmerGroup]
    have : Finite (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) :=
      Subgroup.finiteIndex_iff_finite_quotient.mp <|
        Subgroup.finiteIndex_range_powMonoidHom_of_fg _ (NeZero.ne n)
    exact Finite.Set.finite_range _
  have : Finite (selmerGroup (K := K) (S := S) (n := n) ⧸ (selmerGroupToClassGroup K S n).ker) :=
    .of_injective _ (QuotientGroup.kerLift_injective (selmerGroupToClassGroup K S n))
  exact Finite.of_subgroup_quotient (selmerGroupToClassGroup K S n).ker

end IsDedekindDomain

end
