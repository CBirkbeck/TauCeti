/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.RingTheory.Length

/-!
# Krull–Akizuki: an integral closure that is Noetherian without separability

Let `A` be a Noetherian domain of Krull dimension at most one, let `K` be its fraction field and
let `L` be a finite extension of `K`. This file proves that the integral closure of `A` in `L` is
a Noetherian ring. No separability of `L / K` is assumed, and the integral closure is *not* claimed
to be a finite `A`-module — it need not be.

The engine is a length bound. Write `aM` for the image of multiplication by `a` on a module `M`,
which is `LinearMap.range (LinearMap.lsmul A M a)`. For a finite-dimensional `K`-vector space `V`,
an arbitrary `A`-submodule `M ≤ V` and a nonzero `a : A`,

```text
length_A (M ⧸ aM) ≤ dim_K V * length_A (A ⧸ aA),
```

and the right-hand side is finite because the quotient by a nonzero principal ideal of a
one-dimensional Noetherian domain has finite length. Applied to `M` the integral closure sitting
inside `V = L`, this makes `B ⧸ aB` a Noetherian `A`-module, which is enough to finitely generate
every ideal of `B`.

## Main results

* `TauCeti.length_quotient_lsmul_ideal`: the rank-one case,
  `length (I ⧸ aI) = length (A ⧸ aA)` for a non-zero-divisor `a` and an ideal `I` with `A ⧸ I` of
  finite length.
* `TauCeti.length_quotient_lsmul_le_finrank`: the Krull–Akizuki length bound displayed above.
* `TauCeti.integralClosure.isNoetherianRing`: **Krull–Akizuki**, the Noetherian conclusion.

The general facts about `Module.length` that the bound rests on — additivity along a filtration,
and the reduction of a length bound to finitely generated submodules — are in
`TauCeti/RingTheory/Length.lean`.

## Proof outline

The bound is proved by induction on `n ≥ dim_K U` for a `K`-subspace `U` containing `M`, with `M`
finitely generated (`length_quotient_lsmul_le_of_finrank_le`);
`TauCeti.length_quotient_lsmul_le_of_forall_fg` then removes the finite generation. The inductive
step runs on a projection built from a functional supplied by Mathlib's
`Module.Projective.exists_dual_eq_one`; `ker_id_sub_smulRight` and `finrank_ker_inf_add_one` are
the rest of that construction, isolated. Filtration
additivity splits `length (M ⧸ aM)` into the part supported on `N = M ⊓ K ∙ x` and the part seen
by the projection `e`. The first is bounded by the rank-one case, the second is
`length (e M ⧸ a e M)`, and `e M` lies one dimension lower.

## Design

`Ring.KrullDimLE 1` is used rather than `Ring.DimensionLEOne`; both predicates live in the pinned
Mathlib, and `Ring.krullDimLE_one_iff_of_noZeroDivisors` unfolds the former into exactly the
latter's content over a domain, so a caller holding either one can supply the other.

Multiplication by `a` is written as `LinearMap.range (LinearMap.lsmul A M a)` throughout rather
than as a pointwise scalar action on submodules. That keeps every statement inside the plain
`Submodule` API and makes `TauCeti.comap_subtype_map_lsmul` — the compatibility of the two
readings of `aN` for a submodule `N` — the only place the identification is needed.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), which names
`RingTheory/IntegralClosure/NormalizationFinite` among the three supports of D. Angdinata's
isogeny development. The file
`TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/IntermediateRing/Dedekind.lean` records the
missing piece precisely: its Dedekind conclusion carries a separability hypothesis only because
every Mathlib route to Noetherianity of an integral closure sits under the section variable
`[Algebra.IsSeparable K L]` declared at `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
line 147. This file lands the Noetherian half of that module and removes that obstruction;
finiteness of the normalization (the Nagata/N-2 half) is separate and is not proved here.

This is original mathematics for the project, not a port. The pinned Mathlib has no Krull–Akizuki
and no `IsNagata` / `IsJapanese` / `IsExcellent`. AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache-2.0), at the revision the roadmap pins for its HasseWeil project
(`dev/hasse-weil @ 513e83879e2f`), states the result only in the separable case and obtains it
from Mathlib — `HasseWeil/Curves/NormConormIntegralClosure.lean:88` (`instDedekindB`) and
`HasseWeil/Curves/RamificationFinite.lean:90` — so it supplies nothing reusable here.
The argument follows the classical one (Matsumura, *Commutative Ring Theory*, Theorem 11.7).
-/

public section

namespace TauCeti

/-! ### The dimension-dropping projection

The three lemmas of this section are the inductive step's tool: a functional normalised at `x`,
the projection it defines, and the dimension it removes.
-/

section Projection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If `φ x = 1` then `id - φ(·) • x` kills exactly the line through `x`. -/
private theorem ker_id_sub_smulRight (φ : Module.Dual K V) {x : V} (hφx : φ x = 1) :
    LinearMap.ker (LinearMap.id - LinearMap.smulRight φ x) = K ∙ x := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, sub_eq_zero, Submodule.mem_span_singleton]
  exact ⟨fun h => ⟨φ y, h.symm⟩, by rintro ⟨c, rfl⟩; simp [hφx]⟩

/-- Cutting a subspace containing `x` by the kernel of a functional normalised at `x` removes
exactly one dimension. -/
private theorem finrank_ker_inf_add_one [Module.Finite K V] (φ : Module.Dual K V) {x : V}
    (hφx : φ x = 1) {U : Submodule K V} (hxU : x ∈ U) :
    Module.finrank K ↥(LinearMap.ker φ ⊓ U) + 1 = Module.finrank K ↥U := by
  have hx : x ≠ 0 := fun h => by rw [h, map_zero] at hφx; exact zero_ne_one hφx
  set W : Submodule K V := K ∙ x with hWdef
  have hWU : W ≤ U := by
    rw [hWdef, Submodule.span_le]
    exact Set.singleton_subset_iff.mpr hxU
  have hsup : W ⊔ (LinearMap.ker φ ⊓ U) = U := by
    refine le_antisymm (sup_le hWU inf_le_right) fun u hu => ?_
    have h1 : φ u • x ∈ W := Submodule.mem_span_singleton.mpr ⟨φ u, rfl⟩
    have h2 : u - φ u • x ∈ LinearMap.ker φ ⊓ U :=
      ⟨by simp [hφx], U.sub_mem hu (U.smul_mem _ hxU)⟩
    have hdec : u = φ u • x + (u - φ u • x) := by abel
    rw [hdec]
    exact Submodule.add_mem_sup h1 h2
  have hinf : W ⊓ (LinearMap.ker φ ⊓ U) = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨hyW, hyU'⟩ := hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyW
    have hc0 : c = 0 := by simpa [hφx] using hyU'.1
    simp [hc0]
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker φ ⊓ U)
  rw [hsup, hinf, finrank_span_singleton hx, finrank_bot] at hadd
  omega

end Projection

/-! ### The induced map on a linear image -/

section Kernel

variable {A V : Type*} [CommRing A] [AddCommGroup V] [Module A V]

/-- The kernel of the map `M → eM ⧸ a·eM` induced by a linear endomorphism `e` is
`aM ⊔ (M ⊓ ker e)`. -/
private theorem ker_mkQ_comp_codRestrict {V : Type*} [AddCommGroup V] [Module A V]
    (e : V →ₗ[A] V) (M : Submodule A V) (a : A) :
    LinearMap.ker ((LinearMap.range (LinearMap.lsmul A ↥(M.map e) a)).mkQ ∘ₗ
        LinearMap.codRestrict (M.map e) (e ∘ₗ M.subtype)
          (fun y => Submodule.mem_map_of_mem y.2))
      = LinearMap.range (LinearMap.lsmul A ↥M a) ⊔
          Submodule.comap M.subtype (LinearMap.ker e) := by
  set g : ↥M →ₗ[A] ↥(M.map e) :=
    LinearMap.codRestrict (M.map e) (e ∘ₗ M.subtype) (fun y => Submodule.mem_map_of_mem y.2)
  refine le_antisymm (fun y hy => ?_) (sup_le ?_ ?_)
  · -- `e y ∈ a·eM` means `e y = e (a v)` for some `v ∈ M`, so `y - a v` lies in `M ⊓ ker e`.
    have hgy : g y ∈ LinearMap.range (LinearMap.lsmul A ↥(M.map e) a) := by
      rwa [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, hw⟩ := hgy
    obtain ⟨v, hv, hvw⟩ := w.2
    have hgyv : e ((y : ↥M) : V) = a • ((w : ↥(M.map e)) : V) := by
      have hval := congrArg (fun t : ↥(M.map e) => (t : V)) hw
      simpa [g] using hval.symm
    have hkey : e (((y : ↥M) : V) - a • v) = 0 := by
      rw [map_sub, map_smul, hvw, hgyv, sub_self]
    have hmemM : ((y : ↥M) : V) - a • v ∈ M := M.sub_mem y.2 (M.smul_mem a hv)
    have hdec : y = a • (⟨v, hv⟩ : ↥M) + ⟨((y : ↥M) : V) - a • v, hmemM⟩ := by
      ext; simp
    rw [hdec]
    exact Submodule.add_mem_sup ⟨⟨v, hv⟩, rfl⟩ hkey
  · rintro _ ⟨z, rfl⟩
    have hgz : g (LinearMap.lsmul A ↥M a z) = LinearMap.lsmul A ↥(M.map e) a (g z) := by
      simp [g, LinearMap.lsmul_apply, map_smul]
    rw [LinearMap.mem_ker, LinearMap.comp_apply, hgz, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨g z, rfl⟩
  · intro z hz
    have hgz : g z = 0 := Subtype.ext hz
    rw [LinearMap.mem_ker, LinearMap.comp_apply, hgz, map_zero]

end Kernel

/-! ### The rank-one case -/

section Domain

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- In a Noetherian ring of Krull dimension at most one, the quotient by an ideal containing a
non-zero-divisor has finite length. -/
theorem isFiniteLength_quotient_of_mem_nonZeroDivisors [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    (I : Submodule A A) {x : A} (hxI : x ∈ I) (hx : x ∈ nonZeroDivisors A) :
    IsFiniteLength A (A ⧸ I) := by
  have hle : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
  refine (isFiniteLength_quotient_span_singleton A hx).of_surjective
    (f := Submodule.mapQ _ _ LinearMap.id (by simpa using hle)) ?_
  intro y
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective I y
  exact ⟨Submodule.Quotient.mk z, rfl⟩

omit [IsDomain A] in
/-- **The rank-one case of the Krull–Akizuki bound.** For an ideal `I` with `A ⧸ I` of finite
length and a non-zero-divisor `a`, `length (I ⧸ aI) = length (A ⧸ aA)`. -/
theorem length_quotient_lsmul_ideal (I : Submodule A A) (hI : IsFiniteLength A (A ⧸ I))
    (a : A) (ha : a ∈ nonZeroDivisors A) :
    Module.length A (↥I ⧸ LinearMap.range (LinearMap.lsmul A ↥I a))
      = Module.length A (A ⧸ Ideal.span {a}) := by
  have hinj : Function.Injective (LinearMap.lsmul A A a) := by
    intro u v huv
    simp only [LinearMap.lsmul_apply, smul_eq_mul] at huv
    have hz : a * (u - v) = 0 := by rw [mul_sub, huv, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp ha).1 _ hz)
  have hfin : Module.length A (A ⧸ I) ≠ ⊤ := Module.length_ne_top_iff.mpr hI
  have hlsmul : LinearMap.lsmul A A a = LinearMap.toSpanSingleton A A a :=
    LinearMap.ext fun x => mul_comm a x
  have hspan : LinearMap.range (LinearMap.lsmul A A a) = Ideal.span {a} := by
    rw [hlsmul, LinearMap.range_toSpanSingleton]
  set R : Submodule A A := LinearMap.range (LinearMap.lsmul A A a) with hR
  set P : Submodule A A := I.map (LinearMap.lsmul A A a) with hPdef
  -- Multiplication by `a` carries `A ⧸ I` isomorphically onto the image of `aA` in `A ⧸ aI`.
  have hmul : Module.length A (R.map P.mkQ) = Module.length A (A ⧸ I) := by
    rw [length_map_mkQ, hR, hPdef]
    have h16 : Submodule.comap (LinearMap.range (LinearMap.lsmul A A a)).subtype
          (I.map (LinearMap.lsmul A A a))
        = I.map (LinearEquiv.ofInjective (LinearMap.lsmul A A a) hinj).toLinearMap := by
      ext ⟨x, hx⟩
      simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_map,
        LinearEquiv.coe_coe, LinearEquiv.ofInjective_apply, Subtype.ext_iff]
    rw [h16]
    exact ((Submodule.Quotient.equiv _ _
      (LinearEquiv.ofInjective (LinearMap.lsmul A A a) hinj) rfl).length_eq).symm
  have hleI : P ⊔ I = I := by
    refine sup_eq_right.mpr ?_
    rw [hPdef, Submodule.map_le_iff_le_comap]
    intro x hx
    simpa [LinearMap.lsmul_apply] using I.smul_mem a hx
  have hleA : P ⊔ R = R :=
    sup_eq_right.mpr (by rw [hPdef, hR, LinearMap.range_eq_map]; exact Submodule.map_mono le_top)
  -- Compare the filtrations `aI ≤ I ≤ A` and `aI ≤ aA ≤ A`, then cancel the finite common term.
  have eqA := length_quotient_eq_length_map_add_length_quotient_sup I P
  have eqB := length_quotient_eq_length_map_add_length_quotient_sup R P
  rw [hleI, length_map_mkQ, comap_subtype_map_lsmul] at eqA
  rw [hleA, hmul] at eqB
  rw [eqB] at eqA
  rw [← hspan]
  exact (WithTop.add_left_cancel hfin (eqA.trans (add_comm _ _))).symm

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- **The rank-one case for a finitely generated `A`-submodule of the fraction ring.** -/
theorem length_quotient_lsmul_fractionRing_le_of_fg [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    (J : Submodule A K) (hJ : J.FG) (a : A) (ha : a ≠ 0) :
    Module.length A (↥J ⧸ LinearMap.range (LinearMap.lsmul A ↥J a))
      ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  rcases eq_or_ne J ⊥ with rfl | hJ0
  · refine le_trans (le_of_eq ?_) zero_le
    refine Module.length_eq_zero_iff.mpr ⟨fun p q => ?_⟩
    obtain ⟨p', rfl⟩ := Submodule.mkQ_surjective _ p
    obtain ⟨q', rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Subsingleton.elim p' q']
  -- Clear denominators: some nonzero `d` carries `J` into the image of `A`.
  obtain ⟨s, hs⟩ := hJ
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) s
  set d : A := (b : A)
  have hd0 : d ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hdK : algebraMap A K d ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne hd0
  have hinjd : Function.Injective (LinearMap.lsmul A K d) := by
    intro u v huv
    simp only [LinearMap.lsmul_apply, Algebra.smul_def] at huv
    exact mul_left_cancel₀ hdK huv
  have hinjK : Function.Injective (Algebra.linearMap A K) := IsFractionRing.injective A K
  have hsub : J.map (LinearMap.lsmul A K d) ≤ LinearMap.range (Algebra.linearMap A K) := by
    rw [Submodule.map_le_iff_le_comap, ← hs, Submodule.span_le]
    intro y hy
    obtain ⟨z, hz⟩ := hb y hy
    exact ⟨z, by simpa using hz⟩
  -- so `J` is isomorphic to an ideal, and the ideal case applies.
  set I : Submodule A A :=
    Submodule.comap (Algebra.linearMap A K) (J.map (LinearMap.lsmul A K d))
  have hmapI : I.map (Algebra.linearMap A K) = J.map (LinearMap.lsmul A K d) :=
    Submodule.map_comap_eq_self hsub
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h, Submodule.map_bot] at hmapI
    refine hJ0 (le_bot_iff.mp fun y hy => ?_)
    have hmem : LinearMap.lsmul A K d y ∈ Submodule.map (LinearMap.lsmul A K d) J :=
      Submodule.mem_map_of_mem hy
    rw [← hmapI, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact hinjd (by simpa using hmem)
  have e : ↥J ≃ₗ[A] ↥I :=
    (Submodule.equivMapOfInjective _ hinjd J).trans
      ((Submodule.equivMapOfInjective _ hinjK I).trans (LinearEquiv.ofEq _ _ hmapI)).symm
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  rw [length_quotient_lsmul_congr e a]
  exact le_of_eq (length_quotient_lsmul_ideal I
    (isFiniteLength_quotient_of_mem_nonZeroDivisors I hyI (mem_nonZeroDivisors_of_ne_zero hy0))
    a (mem_nonZeroDivisors_of_ne_zero ha))

/-! ### The rank induction -/

variable {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

/-- **The Krull–Akizuki length bound for a finitely generated submodule**, relative to any bound
`n` on the dimension of a `K`-subspace containing it. -/
private theorem length_quotient_lsmul_le_of_finrank_le [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Module.Finite K V] (a : A) (ha : a ≠ 0) (n : ℕ) (U : Submodule K V)
    (hU : Module.finrank K U ≤ n) (M : Submodule A V) (hM : M ≤ U.restrictScalars A)
    (hfg : M.FG) :
    Module.length A (↥M ⧸ LinearMap.range (LinearMap.lsmul A ↥M a))
      ≤ n * Module.length A (A ⧸ Ideal.span {a}) := by
  induction n generalizing U M with
  | zero =>
      have hU0 : U = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)
      have hM0 : M = ⊥ := by
        refine le_bot_iff.mp fun y hy => ?_
        have hyU := hM hy
        rw [hU0] at hyU
        simpa using hyU
      subst hM0
      simp
  | succ n ih =>
      rcases eq_or_ne M ⊥ with rfl | hM0
      · simp
      -- Phase 1: build the projection `e` killing the line `K ∙ x` through some `0 ≠ x ∈ M`.
      obtain ⟨x, hxM, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
      obtain ⟨φ, hφx⟩ := Module.Projective.exists_dual_eq_one K hx0
      set e : V →ₗ[K] V := LinearMap.id - LinearMap.smulRight φ x with hedef
      have hkere : LinearMap.ker e = K ∙ x := ker_id_sub_smulRight φ hφx
      set eA : V →ₗ[A] V := e.restrictScalars A
      have hkereA : LinearMap.ker eA = (K ∙ x).restrictScalars A := by
        ext y; exact (Submodule.ext_iff.mp hkere y)
      have hxU : x ∈ U := hM hxM
      have hrkU' : Module.finrank K ↥(LinearMap.ker φ ⊓ U) ≤ n := by
        have := finrank_ker_inf_add_one φ hφx hxU
        omega
      -- Phase 2: split `length (M ⧸ aM)` along `N = M ⊓ K ∙ x`.
      set P : Submodule A ↥M := LinearMap.range (LinearMap.lsmul A ↥M a) with hPdef
      set N : Submodule A ↥M := Submodule.comap M.subtype ((K ∙ x).restrictScalars A)
      have hMfin : Module.Finite A ↥M := Module.Finite.iff_fg.mpr hfg
      have hNfg : N.FG := IsNoetherian.noetherian N
      -- Phase 3: `φ` embeds `N` in `K`, so the rank-one case bounds the `N` part.
      set ι : ↥N →ₗ[A] K := (φ.restrictScalars A) ∘ₗ M.subtype ∘ₗ N.subtype
      have hιinj : Function.Injective ι := by
        rw [injective_iff_map_eq_zero]
        intro z hz
        have hzW : ((z : ↥M) : V) ∈ K ∙ x := z.2
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzW
        have hc0 : c = 0 := by
          have hz' : φ ((z : ↥M) : V) = 0 := hz
          rw [← hc] at hz'
          simpa [hφx] using hz'
        exact Subtype.ext (Subtype.ext (by rw [← hc, hc0, zero_smul]; simp))
      have hJfg : (LinearMap.range ι).FG := by
        rw [LinearMap.range_eq_map]
        exact (Module.finite_def.mp (Module.Finite.iff_fg.mpr hNfg)).map ι
      have hterm1 : Module.length A (N.map P.mkQ) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
        rw [length_map_mkQ]
        calc Module.length A (↥N ⧸ Submodule.comap N.subtype P)
            ≤ Module.length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N a)) := by
              refine length_quotient_le_of_le ?_
              rintro y ⟨z, rfl⟩
              exact ⟨(z : ↥M), rfl⟩
          _ ≤ Module.length A (A ⧸ Ideal.span {a}) := by
              rw [length_quotient_lsmul_congr (LinearEquiv.ofInjective ι hιinj) a]
              exact length_quotient_lsmul_fractionRing_le_of_fg _ hJfg a ha
      -- Phase 4: the rest is `e M ⧸ a·e M`, one dimension lower, so the hypothesis applies.
      set M' : Submodule A V := M.map eA
      have hM'U : M' ≤ (LinearMap.ker φ ⊓ U).restrictScalars A := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨by simp [eA, hedef, hφx], by
          simpa [eA, hedef] using U.sub_mem (hM hy) (U.smul_mem _ hxU)⟩
      set Q : Submodule A ↥M' := LinearMap.range (LinearMap.lsmul A ↥M' a)
      set g : ↥M →ₗ[A] ↥M' :=
        LinearMap.codRestrict M' (eA ∘ₗ M.subtype) (fun y => Submodule.mem_map_of_mem y.2)
      have hgsurj : Function.Surjective g := by
        rintro ⟨_, y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      have hker : LinearMap.ker (Q.mkQ ∘ₗ g) = P ⊔ N := by
        rw [ker_mkQ_comp_codRestrict eA M a, hkereA]
      have hterm2 : Module.length A (↥M ⧸ (P ⊔ N)) ≤ n * Module.length A (A ⧸ Ideal.span {a}) := by
        rw [← hker, (LinearMap.quotKerEquivOfSurjective (Q.mkQ ∘ₗ g)
          ((Submodule.mkQ_surjective Q).comp hgsurj)).length_eq]
        exact ih (LinearMap.ker φ ⊓ U) hrkU' M' hM'U (hfg.map eA)
      rw [length_quotient_eq_length_map_add_length_quotient_sup N P]
      calc Module.length A (N.map P.mkQ) + Module.length A (↥M ⧸ (P ⊔ N))
          ≤ Module.length A (A ⧸ Ideal.span {a}) + n * Module.length A (A ⧸ Ideal.span {a}) :=
            add_le_add hterm1 hterm2
        _ = (n + 1 : ℕ) * Module.length A (A ⧸ Ideal.span {a}) := by
            push_cast; rw [add_mul, one_mul, add_comm]

/-- **Krull–Akizuki's length bound.** For any `A`-submodule `M` of a finite-dimensional
`K`-vector space `V` — finitely generated or not — and any nonzero `a : A`,
`length (M ⧸ aM) ≤ dim_K V * length (A ⧸ aA)`. -/
theorem length_quotient_lsmul_le_finrank [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Module.Finite K V] (M : Submodule A V) (a : A) (ha : a ≠ 0) :
    Module.length A (↥M ⧸ LinearMap.range (LinearMap.lsmul A ↥M a))
      ≤ Module.finrank K V * Module.length A (A ⧸ Ideal.span {a}) := by
  refine length_quotient_lsmul_le_of_forall_fg fun N hN => ?_
  rw [length_quotient_lsmul_congr
    (Submodule.equivMapOfInjective M.subtype (Submodule.subtype_injective M) N) a]
  exact length_quotient_lsmul_le_of_finrank_le a ha (Module.finrank K V) (⊤ : Submodule K V)
    (le_of_eq (finrank_top K V)) (N.map M.subtype) (fun x _ => Submodule.mem_top) (hN.map _)

end Domain

/-! ### Krull–Akizuki -/

section IntegralClosure

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
variable {L : Type*} [Field L] [Algebra A L]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- A nonzero ideal of the integral closure meets `A` in a nonzero element. -/
theorem exists_ne_zero_algebraMap_mem (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
    {𝔟 : Ideal (integralClosure A L)} (h0 : 𝔟 ≠ ⊥) :
    ∃ a : A, a ≠ 0 ∧ algebraMap A (integralClosure A L) a ∈ 𝔟 := by
  obtain ⟨β, hβ𝔟, hβ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hβL : (β : L) ≠ 0 := fun h => hβ0 (Subtype.ext h)
  -- Some `A`-multiple of `β⁻¹` is integral, and multiplying it by `β` lands that `a` in `𝔟`.
  obtain ⟨a, ha0, hint⟩ : ∃ a : A, a ≠ 0 ∧ IsIntegral A (a • ((β : L)⁻¹)) := by
    have halg : IsAlgebraic A ((β : L)⁻¹) :=
      (IsFractionRing.isAlgebraic_iff A K L).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    exact halg.exists_integral_multiple
  refine ⟨a, ha0, ?_⟩
  have hmul : algebraMap A (integralClosure A L) a
      = (⟨a • ((β : L)⁻¹), hint⟩ : integralClosure A L) * β := by
    refine Subtype.ext ?_
    push_cast
    rw [smul_mul_assoc, inv_mul_cancel₀ hβL, Algebra.smul_def, mul_one]
  rw [hmul]
  exact Ideal.mul_mem_left _ _ hβ𝔟

/-- **Krull–Akizuki.** The integral closure of a Noetherian domain of Krull dimension at most one
in a finite extension `L` of its fraction field is a Noetherian ring. No separability of `L` over
the fraction field is assumed, and the integral closure need not be a finite `A`-module. -/
theorem integralClosure.isNoetherianRing (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] :
    IsNoetherianRing (integralClosure A L) := by
  classical
  rw [isNoetherianRing_iff_ideal_fg]
  intro 𝔟
  rcases eq_or_ne 𝔟 ⊥ with rfl | h0
  · exact Submodule.fg_bot
  have halgK : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  obtain ⟨a, ha0, hα𝔟⟩ := exists_ne_zero_algebraMap_mem (L := L) K h0
  set α : integralClosure A L := algebraMap A _ a with hαdef
  set P : Submodule A (integralClosure A L) :=
    LinearMap.range (LinearMap.lsmul A (integralClosure A L) a) with hPdef
  -- The length bound makes `B ⧸ aB` a Noetherian `A`-module.
  have hlenA : Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_of_mem_nonZeroDivisors _
      (Ideal.mem_span_singleton_self a) (mem_nonZeroDivisors_of_ne_zero ha0))
  have hlen : Module.length A ((integralClosure A L) ⧸ P) ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top _) hlenA)
      (length_quotient_lsmul_le_finrank (K := K)
        (Subalgebra.toSubmodule (integralClosure A L)) a ha0)
  have hnoeth : IsNoetherian A ((integralClosure A L) ⧸ P) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hlen)).1
  -- So the image of `𝔟` there is `A`-spanned by finitely many elements, which we lift into `𝔟`.
  set T : Submodule A (integralClosure A L) := 𝔟.restrictScalars A
  obtain ⟨s, hs⟩ := hnoeth.noetherian (T.map P.mkQ)
  have hex : ∀ y : (integralClosure A L) ⧸ P,
      ∃ z : integralClosure A L, y ∈ T.map P.mkQ → z ∈ 𝔟 ∧ P.mkQ z = y := by
    intro y
    by_cases hy : y ∈ T.map P.mkQ
    · obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨z, fun _ => ⟨hz, hzy⟩⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose lft hlft using hex
  have hsmem : ∀ y ∈ s, y ∈ T.map P.mkQ := fun y hy => by
    rw [← hs]; exact Submodule.subset_span hy
  have himg : (P.mkQ : _ → _) '' ((s.image lft : Finset _) : Set _) = (s : Set _) := by
    ext y
    simp only [Finset.coe_image, Set.image_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [(hlft z (hsmem z hz)).2]
      exact hz
    · intro hy
      exact ⟨y, hy, (hlft y (hsmem y hy)).2⟩
  -- Those lifts together with `a` generate `𝔟` over the integral closure.
  refine ⟨insert α (s.image lft), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le, Finset.coe_insert, Set.insert_subset_iff]
    refine ⟨hα𝔟, ?_⟩
    intro z hz
    rw [Finset.coe_image, Set.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact (hlft y (hsmem y (Finset.mem_coe.mp hy))).1
  · intro x hx
    have hxq : P.mkQ x ∈
        Submodule.map P.mkQ (Submodule.span A ((s.image lft : Finset _) : Set _)) := by
      rw [Submodule.map_span, himg, hs]
      exact Submodule.mem_map_of_mem hx
    have hmem : x ∈ P ⊔ Submodule.span A ((s.image lft : Finset _) : Set _) := by
      rw [← Submodule.comap_map_mkQ]
      exact hxq
    refine (sup_le ?_ ?_ : P ⊔ Submodule.span A ((s.image lft : Finset _) : Set _)
      ≤ Submodule.restrictScalars A (Ideal.span ((insert α (s.image lft) : Finset _) : Set _)))
      hmem
    · rintro _ ⟨z, rfl⟩
      rw [Submodule.restrictScalars_mem, LinearMap.lsmul_apply, hαdef, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      intro y hy
      exact Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hy)))

end IntegralClosure

end TauCeti
