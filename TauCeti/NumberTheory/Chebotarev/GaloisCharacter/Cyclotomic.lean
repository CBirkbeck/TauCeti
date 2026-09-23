/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Weight
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Basic
public import TauCeti.NumberTheory.NumberField.Ideal.ArtinMap
import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Global.RayClass.Residue

/-!
# Cyclotomic Galois characters as ray class characters

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K`, and let `𝔪` be the
modulus of `K` with finite part `(m)` and every real place in its infinite part. The Galois group
of `F / K` is abelian, and its Artin map on the fractional ideals prime to `m` is trivial on the
ray of `𝔪`: for `x ≡ 1 mod 𝔪` the principal ideal `(x)` has absolute norm `≡ 1 mod m`, and the
Artin automorphism of an ideal acts on the `m`-th roots of unity by raising them to its absolute
norm. The Artin map therefore factors through the ray class group of `𝔪`, and every character `χ`
of `Gal(F/K)` gives a ray class character `χ ∘ artin` of `𝔪`.

On the integral ideals prime to `m`, the ideal weight `galoisCharacterWeight χ` of `χ` agrees with
that ray class character.

## Main definitions

* `TauCeti.GlobalNumberFields.cyclotomicModulus`: the modulus of `K` with finite part `(m)` and
  every real place in its infinite part.
* `TauCeti.GlobalNumberFields.cyclotomicArtin`: the Artin map
  `RayClassGroup (cyclotomicModulus K m) →* (F ≃ₐ[K] F)`.

## Main results

* `TauCeti.GlobalNumberFields.cyclotomicArtin_idealClass_of_isArithFrobAt`: the Artin map sends
  the ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`.
* `TauCeti.GlobalNumberFields.autToPow_cyclotomicArtin_idealClass`: the cyclotomic character of
  the Artin automorphism of an integral ideal `I` prime to `m` is `𝔑 I mod m`.
* `MonoidHom.galoisCharacterWeight_eq_onIdeals`: on the integral ideals prime to `m`, the ideal
  weight of a character `χ` of `Gal(F/K)` is the ray class character `χ ∘ cyclotomicArtin`.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

open NumberFieldArithmetic

section Modulus

variable (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m]

/-- **The cyclotomic modulus** of level `m`: finite part the ideal `(m)` of `𝓞 K`, and every real
place of `K` in the infinite part. -/
noncomputable def cyclotomicModulus : Modulus K where
  finitePart := Ideal.span {(m : 𝓞 K)}
  finitePart_ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr (NeZero.ne m)
  infinitePart := (narrowModulus K).infinitePart

@[simp] theorem cyclotomicModulus_finitePart :
    (cyclotomicModulus K m).finitePart = Ideal.span {(m : 𝓞 K)} := (rfl)

@[simp] theorem mem_cyclotomicModulus_infinitePart (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ (cyclotomicModulus K m).infinitePart :=
  mem_narrowModulus_infinitePart w

variable {K m}

/-- A prime lies in the support of the cyclotomic modulus exactly when it divides `m`. -/
theorem mem_cyclotomicModulus_support_iff {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ (cyclotomicModulus K m).support ↔ (m : 𝓞 K) ∈ v.asIdeal := by
  rw [Modulus.mem_support_iff, cyclotomicModulus_finitePart, Ideal.dvd_span_singleton]

/-- A height-one prime is prime to the cyclotomic modulus exactly when it does not divide `m`. -/
theorem asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff {v : HeightOneSpectrum (𝓞 K)} :
    v.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m) ↔ (m : 𝓞 K) ∉ v.asIdeal := by
  refine (Modulus.mem_integralIdealsPrimeTo.trans
    (Modulus.isCoprimeTo_iff.trans Ideal.isPrimeTo_iff.symm)).trans
      (Ideal.isPrimeTo_asIdeal_iff.trans ?_)
  rw [Finset.mem_coe, mem_cyclotomicModulus_support_iff]

end Modulus

section Auxiliary

variable {K : Type*} [Field K] [NumberField K]

/-- Two homomorphisms out of the integral ideals prime to `S` agree once they agree on the primes
outside `S`: those primes generate the monoid. -/
private theorem integralIdealsAway_hom_ext {M : Type*} [Monoid M]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f g : integralIdealsAway (K := K) S →* M}
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∈ integralIdealsAway (K := K) S),
      f ⟨v.asIdeal, hv⟩ = g ⟨v.asIdeal, hv⟩) : f = g := by
  refine MonoidHom.ext fun ⟨I, hI⟩ ↦ ?_
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl (mem_integralIdealsAway_iff.mp hI).1
  | h₂ x hx =>
    have h1 : (⟨x, hI⟩ : integralIdealsAway (K := K) S) = 1 :=
      Subtype.ext ((Ideal.isUnit_iff.mp hx).trans Ideal.one_eq_top.symm)
    rw [h1, map_one, map_one]
  | h₃ a p ha hp ih =>
    obtain ⟨hpa, hS⟩ := mem_integralIdealsAway_iff.mp hI
    have hpS : p ∈ integralIdealsAway (K := K) S := mem_integralIdealsAway_iff.mpr
      ⟨hp.ne_zero, fun v hv hvp ↦ hS v hv (hvp.mul_right a)⟩
    have haS : a ∈ integralIdealsAway (K := K) S := mem_integralIdealsAway_iff.mpr
      ⟨ha, fun v hv hva ↦ hS v hv (hva.mul_left p)⟩
    have hsplit : (⟨p * a, hI⟩ : integralIdealsAway (K := K) S) = ⟨p, hpS⟩ * ⟨a, haS⟩ := rfl
    have := Ideal.isPrime_of_prime hp
    rw [hsplit, map_mul, map_mul, ih haS, h ⟨p, this, hp.ne_zero⟩ hpS]

/-- **Congruent integers have congruent norms.** If `a ≡ b` modulo `(m)` in `𝓞 K`, then
`N(a) ≡ N(b) mod m`. -/
private theorem intCast_norm_eq_of_sub_mem {m : ℕ} {a b : 𝓞 K}
    (h : a - b ∈ Ideal.span {(m : 𝓞 K)}) :
    ((Algebra.norm ℤ a : ℤ) : ZMod m) = ((Algebra.norm ℤ b : ℤ) : ZMod m) := by
  classical
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have hab : a = b + (m : 𝓞 K) * c := by rw [mul_comm, hc]; ring
  let B := Module.Free.chooseBasis ℤ (𝓞 K)
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det B]
  change Int.castRingHom (ZMod m) _ = Int.castRingHom (ZMod m) _
  rw [RingHom.map_det, RingHom.map_det, hab, map_add, map_mul, map_natCast, map_add, map_mul,
    map_natCast, ← Matrix.diagonal_natCast, ZMod.natCast_self, Matrix.diagonal_zero, zero_mul,
    add_zero]

/-- Two integers of the same sign that are congruent modulo `m` have congruent absolute values. -/
private theorem natCast_natAbs_eq_of_mul_pos {m : ℕ} {z w : ℤ} (hzw : 0 < z * w)
    (h : (z : ZMod m) = w) : (z.natAbs : ZMod m) = w.natAbs := by
  rw [← Int.cast_natCast, ← Int.cast_natCast (R := ZMod m) w.natAbs, Int.natCast_natAbs,
    Int.natCast_natAbs]
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩
  · rw [abs_of_pos hz, abs_of_pos hw, h]
  · rw [abs_of_neg hz, abs_of_neg hw, Int.cast_neg, Int.cast_neg, h]

/-- The ideal `(m)` of `𝓞 K` is proper unless `m = 1`. -/
private theorem span_natCast_ne_top {m : ℕ} (hm : m ≠ 1) : Ideal.span {(m : 𝓞 K)} ≠ ⊤ := by
  intro h
  have hnorm := Ideal.absNorm_eq_one_iff.mpr h
  rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap,
    Int.natAbs_pow, Int.natAbs_natCast] at hnorm
  exact hm ((pow_eq_one_iff.mp hnorm).resolve_right Module.finrank_pos.ne')

/-- A nonzero integer congruent to one modulo `(m)` generates an ideal prime to the cyclotomic
modulus. -/
private theorem span_singleton_mem_of_sub_one_mem {m : ℕ} [NeZero m] {c : 𝓞 K} (hc0 : c ≠ 0)
    (hc : c - 1 ∈ Ideal.span {(m : 𝓞 K)}) :
    Ideal.span {c} ∈ integralIdealsPrimeTo (cyclotomicModulus K m) := by
  refine mem_integralIdealsAway_iff.mpr ⟨?_, fun v hv hvc ↦ ?_⟩
  · rwa [Ne, Ideal.span_singleton_eq_bot]
  have hcv : c ∈ v.asIdeal := Ideal.dvd_span_singleton.mp hvc
  have h1 : c - 1 ∈ v.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr (mem_cyclotomicModulus_support_iff.mp hv) hc
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using sub_mem hcv h1))

end Auxiliary

section Cyclotomic

/-- The Galois group of a cyclotomic extension is commutative. -/
private theorem commute_cyclotomic {K : Type*} [Field K] (F : Type*) [Field F] [Algebra K F]
    (m : ℕ) [IsCyclotomicExtension {m} K F] (σ τ : F ≃ₐ[K] F) : Commute σ τ :=
  (IsCyclotomicExtension.isMulCommutative {m} K F).is_comm.comm σ τ

/-- A cyclotomic extension is unramified at every prime not dividing the level. -/
private theorem isUnramifiedAt_of_notMem_support {K : Type*} [Field K] [NumberField K]
    (F : Type*) [Field F] [NumberField F] [Algebra K F] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ (cyclotomicModulus K m).support) (Q : Ideal (𝓞 F)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal] : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  rw [mem_cyclotomicModulus_support_iff] at hv
  by_contra hQ
  have hmQ : (m : 𝓞 F) ∈ Q := Ideal.le_of_dvd (dvd_differentIdeal_iff.mpr hQ)
    (IsCyclotomicExtension.natCast_mem_differentIdeal K F m)
  refine hv ?_
  rw [Ideal.LiesOver.over (P := Q) (p := v.asIdeal), Ideal.mem_comap]
  simpa using hmQ

variable {K : Type*} [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F]
  [Algebra K F] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

/-- The Artin map of `F / K` on the fractional ideals prime to `m`. -/
private noncomputable def cyclotomicArtinAway :
    idealsPrimeTo (cyclotomicModulus K m) →* (F ≃ₐ[K] F) :=
  artinHomAway (commute_cyclotomic F m) (cyclotomicModulus K m).support
    fun _ hv Q _ _ ↦ isUnramifiedAt_of_notMem_support F m hv Q

/-- The Artin map of `F / K` on the integral ideals prime to `m`. -/
private noncomputable def cyclotomicArtinIntegral :
    integralIdealsPrimeTo (cyclotomicModulus K m) →* (F ≃ₐ[K] F) :=
  artinHomAwayIntegral (commute_cyclotomic F m) (cyclotomicModulus K m).support
    fun _ hv Q _ _ ↦ isUnramifiedAt_of_notMem_support F m hv Q

/-- The integral Artin map is the fractional one read on the ideals the integral ones generate. -/
private theorem cyclotomicArtinIntegral_apply
    (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    cyclotomicArtinIntegral F m I =
      cyclotomicArtinAway F m (integralIdealsAwayHom (cyclotomicModulus K m).support I) :=
  artinHomAwayIntegral_apply _ _ _ I

/-- At a prime not dividing `m`, the integral Artin map is the Frobenius. -/
private theorem cyclotomicArtinIntegral_prime (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m))
    (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver v.asIdeal] {σ : F ≃ₐ[K] F}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    cyclotomicArtinIntegral F m ⟨v.asIdeal, hv⟩ = σ :=
  artinHomAwayIntegral_apply_prime _ _ _ v
    (mem_cyclotomicModulus_support_iff.not.mpr
      (asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv)) hv Q σ hσ

/-- **The cyclotomic character of the integral Artin map is the absolute norm.** -/
private theorem autToPow_cyclotomicArtinIntegral {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    (hζ.autToPow K (cyclotomicArtinIntegral F m I) : ZMod m) =
      Ideal.absNorm (I : Ideal (𝓞 K)) := by
  let f : integralIdealsPrimeTo (cyclotomicModulus K m) →* ZMod m :=
    (Units.coeHom (ZMod m)).comp ((hζ.autToPow K).comp (cyclotomicArtinIntegral F m))
  let g : integralIdealsPrimeTo (cyclotomicModulus K m) →* ZMod m :=
    (Nat.castRingHom (ZMod m)).toMonoidHom.comp
      ((Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ).toMonoidHom.comp
        (integralIdealsPrimeTo (cyclotomicModulus K m)).subtype)
  have hfg : f = g := integralIdealsAway_hom_ext fun v hv ↦ by
    obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 F)))
    obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
    have hm : (m : 𝓞 K) ∉ v.asIdeal :=
      asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv
    simp only [f, g, MonoidHom.comp_apply, Units.coeHom_apply,
      cyclotomicArtinIntegral_prime F m v hv Q hσ, hσ.autToPow_eq_absNorm hζ v hm Q]
    rfl
  exact DFunLike.congr_fun hfg I

/-- **The Artin map of `F / K` kills the ray of the cyclotomic modulus.** -/
private theorem ray_le_ker_cyclotomicArtinAway :
    ray (cyclotomicModulus K m) ≤ (cyclotomicArtinAway F m).ker := by
  intro J hJ
  obtain ⟨x, hx, hxJ⟩ := mem_ray_iff.mp hJ
  rw [MonoidHom.mem_ker]
  have hζ := IsCyclotomicExtension.zeta_spec m K F
  refine hζ.autToPow_injective K ?_
  rw [map_one]
  rcases eq_or_ne m 1 with rfl | hm1
  · exact Subsingleton.elim _ _
  -- Write `x = a / b` with `a ≡ b ≡ 1 mod m`.
  have hxp : x ∈ primeToSubgroup (cyclotomicModulus K m) :=
    congruenceSubgroup_le_primeToSubgroup _ (mem_congruenceSubgroup.mpr hx)
  obtain ⟨a, b, hb, hab⟩ := exists_algebraMap_eq_mul_of_mem_primeToSubgroup hxp
  rw [cyclotomicModulus_finitePart] at hb
  have ha : a - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
    have h1 := congrArg Units.val (residueHom_eq_one_of_mem_congruenceSubgroup (x := ⟨x, hxp⟩)
      (mem_congruenceSubgroup.mpr hx))
    rw [coe_residueHom, residue_eq ⟨x, hxp⟩ (by rwa [cyclotomicModulus_finitePart]) hab,
      Units.val_one, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at h1
    exact h1
  have hne0 {c : 𝓞 K} (hc : c - 1 ∈ Ideal.span {(m : 𝓞 K)}) : c ≠ 0 := fun h ↦
    span_natCast_ne_top hm1 ((Ideal.eq_top_iff_one _).mpr (by simpa [h] using neg_mem hc))
  have hIa := span_singleton_mem_of_sub_one_mem (hne0 ha) ha
  have hIb := span_singleton_mem_of_sub_one_mem (hne0 hb) hb
  -- In `idealsPrimeTo`, `(a) = (x) * (b)`.
  have hsplit : integralIdealsAwayHom _ ⟨Ideal.span {a}, hIa⟩ =
      J * integralIdealsAwayHom _ ⟨Ideal.span {b}, hIb⟩ := by
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul, coe_integralIdealsAwayHom, coe_integralIdealsAwayHom,
      ← hxJ, coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      hab, mul_comm]
  -- The two norms are congruent modulo `m` and have the same sign.
  have hxpos : 0 < Algebra.norm ℚ (x : K) :=
    norm_pos_of_isTotallyPositive x.ne_zero (isTotallyPositive_iff.mpr fun w hw ↦
      hx.pos (mem_cyclotomicModulus_infinitePart K m ⟨w, hw⟩))
  have hNab : ((Algebra.norm ℤ a : ℤ) : ℚ) = (Algebra.norm ℤ b : ℤ) * Algebra.norm ℚ (x : K) := by
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int, ← map_mul]
    exact congrArg _ hab
  have hNb : ((Algebra.norm ℤ b : ℤ) : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr (hne0 hb))
  have hsign : 0 < Algebra.norm ℤ a * Algebra.norm ℤ b := by
    have : (0 : ℚ) < (Algebra.norm ℤ a : ℤ) * (Algebra.norm ℤ b : ℤ) := by
      rw [hNab, mul_right_comm]
      exact mul_pos (mul_self_pos.mpr hNb) hxpos
    exact_mod_cast this
  have hnorm : (Ideal.absNorm (Ideal.span {a}) : ZMod m) = Ideal.absNorm (Ideal.span {b}) := by
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
    exact natCast_natAbs_eq_of_mul_pos hsign
      (intCast_norm_eq_of_sub_mem (by simpa using sub_mem ha hb))
  -- Hence the cyclotomic characters of `(a)` and `(b)` agree, and that of `(x)` is trivial.
  have hua := autToPow_cyclotomicArtinIntegral F m hζ ⟨_, hIa⟩
  have hub := autToPow_cyclotomicArtinIntegral F m hζ ⟨_, hIb⟩
  have key := congrArg (fun I ↦ hζ.autToPow K (cyclotomicArtinAway F m I)) hsplit
  simp only [map_mul] at key
  have hab' : hζ.autToPow K (cyclotomicArtinAway F m (integralIdealsAwayHom _ ⟨_, hIa⟩)) =
      hζ.autToPow K (cyclotomicArtinAway F m (integralIdealsAwayHom _ ⟨_, hIb⟩)) :=
    Units.ext (by rw [← cyclotomicArtinIntegral_apply, ← cyclotomicArtinIntegral_apply, hua, hub,
      hnorm])
  exact mul_eq_right.mp (key.symm.trans hab')

variable (K) in
/-- **The Artin map of a cyclotomic extension on the ray class group.** For `F = K(μ_m)` the
Artin map of the abelian extension `F / K` on the fractional ideals prime to `m` is trivial on the
ray of `cyclotomicModulus K m`, and so factors through its ray class group. -/
noncomputable def cyclotomicArtin : RayClassGroup (cyclotomicModulus K m) →* (F ≃ₐ[K] F) :=
  rayClassLift (cyclotomicArtinAway F m) (ray_le_ker_cyclotomicArtinAway F m)

/-- On the ray class of an integral ideal, `cyclotomicArtin` is the integral Artin map. -/
private theorem cyclotomicArtin_idealClass (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    cyclotomicArtin K F m (idealClass _ I) = cyclotomicArtinIntegral F m I := by
  rw [idealClass_apply, cyclotomicArtin, rayClassLift_rayClassMk, cyclotomicArtinIntegral_apply]

/-- **The Artin map sends the ray class of a prime to its Frobenius.** At a height-one prime `𝔭`
not dividing `m`, every arithmetic Frobenius at every prime of `𝓞 F` above `𝔭` is the image of
the ray class of `𝔭`. -/
theorem cyclotomicArtin_idealClass_of_isArithFrobAt (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭 : 𝔭.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m))
    (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] {σ : F ≃ₐ[K] F}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    cyclotomicArtin K F m (idealClass _ ⟨𝔭.asIdeal, h𝔭⟩) = σ := by
  rw [cyclotomicArtin_idealClass]
  exact cyclotomicArtinIntegral_prime F m 𝔭 h𝔭 Q hσ

/-- **Cyclotomic reciprocity on ideals.** The cyclotomic character of the Artin automorphism of
an integral ideal `I` prime to `m` is the absolute norm of `I` modulo `m`. -/
theorem autToPow_cyclotomicArtin_idealClass {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    (hζ.autToPow K (cyclotomicArtin K F m (idealClass _ I)) : ZMod m) =
      Ideal.absNorm (I : Ideal (𝓞 K)) := by
  rw [cyclotomicArtin_idealClass]
  exact autToPow_cyclotomicArtinIntegral F m hζ I

end Cyclotomic

end TauCeti.GlobalNumberFields

namespace MonoidHom

open TauCeti.GlobalNumberFields NumberField.Chebotarev
open scoped IsMulCommutative

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

/-- **The ideal weight of a cyclotomic Galois character is a ray class character.** For a
character `χ` of `Gal(F/K)` with `F = K(μ_m)`, the ideal weight `galoisCharacterWeight χ` agrees,
on the integral ideals prime to `m`, with the ray class character `χ ∘ cyclotomicArtin K F m` of
`cyclotomicModulus K m`. -/
theorem galoisCharacterWeight_eq_onIdeals (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    galoisCharacterWeight (L := F) χ (I : Ideal (𝓞 K)) =
      (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ) := by
  let f : integralIdealsPrimeTo (cyclotomicModulus K m) →* ℂ :=
    (galoisCharacterWeight (L := F) χ).toMonoidWithZeroHom.toMonoidHom.comp
      (integralIdealsPrimeTo (cyclotomicModulus K m)).subtype
  let g : integralIdealsPrimeTo (cyclotomicModulus K m) →* ℂ :=
    (Units.coeHom ℂ).comp (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)))
  have hfg : f = g := integralIdealsAway_hom_ext fun v hv ↦ by
    have hvS : v ∉ (cyclotomicModulus K m).support := mem_cyclotomicModulus_support_iff.not.mpr
      (asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv)
    have hur : ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q := fun Q _ _ ↦
      isUnramifiedAt_of_notMem_support F m hvS Q
    obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 F)))
    obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
    have := IsCyclotomicExtension.isMulCommutative {m} K F
    have : v.asIdeal.IsMaximal := v.isMaximal
    have hout : (artinSymbol (L := F) v.asIdeal hur).out = σ := by
      exact isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ((Quotient.out_eq _).trans
        (artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal hur Q σ hσ)))
    change galoisCharacterWeight (L := F) χ v.asIdeal = _
    rw [galoisCharacterWeight_apply_of_unramified χ v hur, hout]
    simp only [g, MonoidHom.comp_apply, Units.coeHom_apply, RayClassCharacter.onIdeals_apply,
      cyclotomicArtin_idealClass_of_isArithFrobAt F m v hv Q hσ]
  exact DFunLike.congr_fun hfg I

end MonoidHom
