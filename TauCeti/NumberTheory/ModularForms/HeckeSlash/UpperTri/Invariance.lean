/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Sum

/-!
# Equivariance of the upper-triangular Hecke sum at level-supported indices

`UpperTri/Sum.lean` defines `heckeSlashUpperTri k p f = ∑_{b < p} f ∣[k] !![1, b; 0, p]`, and
`UpperTri/Periodic.lean` shows it preserves invariance under the single matrix `T`. That is far
short of an operator: to act on `M_k(Γ₁(N))` the sum has to preserve invariance under the whole
group. This file proves the basic case when `p` divides the level, then obtains every index
supported on the level by composing those basic sums.

## The permutation

Write `γ = !![a, b; c, d] ∈ Γ₀(N)`, so `N ∣ c` and hence `p ∣ c`. Then

`!![1, j; 0, p] · γ = !![a + jc, b + jd; pc, pd]`,

and one asks for a factorisation `γ' · !![1, j'; 0, p]` with `γ' ∈ Γ₀(N)`. Matching entries forces
`γ' = !![a + jc, b'; pc, d - cj']` and `p b' = b + jd - (a + jc) j'`, so `j'` must solve

`(a + jc) j' ≡ b + jd (mod p)`.

That has a unique solution in `[0, p)` exactly when `a + jc` is invertible modulo `p`, and
`upperTriShift p γ j` is it. On `Γ₀(p)` invertibility is automatic and uniform in `j`: `p ∣ c`
collapses `a + jc` to `a`, and the determinant identity `ad - bc = 1` reduces to `ad ≡ 1 (mod p)`,
exhibiting `d` as the inverse of `a`, so the solution takes the closed form

`j' = d b + j d² mod p`.

It is a bijection of `Fin p` there, because `d²` is again invertible modulo `p`. Slashing
therefore permutes the summands, and the sum is unchanged up to the scalar by which `γ'` acts
on `f`.

The map is defined by the general formula rather than the closed one because the closed form is
false off `Γ₀(p)`: when `p ∤ c` the entry `a + jc` varies with `j` and can vanish, and then the
congruence has no solution at all. The definition and the general factorisation below are stated
at exactly the offsets where it does — those with `a + jc` invertible.

Two facts make that scalar behave. The new lower-right entry is `d - c j' ≡ d (mod N)`, so `γ'`
has the *same* `Gamma0Map` value as `γ`; and if `γ ∈ Γ₁(N)` then `γ' ∈ Γ₁(N)`. So the hypothesis
on `f` is only ever used at matrices congruent to `γ` in the relevant sense, which is what lets
the nebentypus version below carry a fixed character.

⚠ `p ∣ N` is essential to the direct permutation argument, not a convenience. The general
level-supported theorem below instead composes sums at prime divisors of `N`. When `p` is prime
and `p ∤ N`, the classical double coset has one further left coset, represented by
`!![p, 0; 0, 1]` up to a `Γ₀(N)` twist, and the sum over the upper-triangular representatives
alone is *not* invariant.

## Main definitions

* `HeckeRing.GL2.upperTriShift`: the offset map, `j ↦ (a + jc)⁻¹ (b + jd) mod p`.

## Main results

* `HeckeRing.GL2.mul_upperTriShift_natCast`: it solves `(a + jc) j' ≡ b + jd (mod p)` whenever
  `a + jc` is invertible.
* `HeckeRing.GL2.upperTriShift_natCast_of_mem_Gamma0`: on `Γ₀(p)` it is `j ↦ d b + j d² mod p`.
* `HeckeRing.GL2.upperTriShift_bijective`: on `Γ₀(p)` it is a bijection of `Fin p`.
* `HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul_of_isUnit`: the factorisation
  `!![1, j; 0, p] · γ = γ' · !![1, j'; 0, p]` with `γ' ∈ Γ₀(N)`, from the two facts the argument
  consumes — `a + jc` invertible modulo `p`, and `N ∣ p c`.
* `HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul`: the same at `γ ∈ Γ₀(p)`, where the first
  hypothesis holds for every offset at once. A `γ ∈ Γ₀(N / p)` gives `N ∣ p c` only in the
  presence of `p ∣ N`, and gives `γ ∈ Γ₀(p)` only when `p² ∣ N`; that is the level-descent case,
  not the hypothesis.
* `HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul_of_mem_Gamma0`: its specialisation to
  `p ∣ N` and `γ ∈ Γ₀(N)`, whose conclusion is the modulo-`N` congruence of the lower-right
  entry.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0`: the equivariance, stated with an
  arbitrary scalar so that both corollaries below are instances of it.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_mem_Gamma1`: the sum of a `Γ₁(N)`-invariant
  function is `Γ₁(N)`-invariant.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_nebentypus`: the sum of a function with
  nebentypus `χ` has nebentypus `χ`.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_mapGL_of_nebentypus_of_primeFactors_subset`: the same
  conclusion for every index whose prime factors divide `N`.

## References

The generality of the offset map follows the descent formalisation in the AINTLIB
`LeanModularForms` project (`LeanModularForms/StrongMultiplicityOne/DescentCosets.lean`, Chris
Birkbeck, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), whose
`descend_exists_fin_isUnit_mul_eq` and `descendCosetList_action_upper_tri_extra` solve the same
congruence at each call site. No code is adapted from it.

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane HeckeRing.GLn CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ}

/-- **The offset map**, `j ↦ (a + j c)⁻¹ (b + j d) mod p`, where `γ = !![a, b; c, d]`.

`a + j c` and `b + j d` are the top-left and top-right entries of `!![1, j; 0, p] · γ`
before dividing by `p`, so this is the unique solution in `[0, p)` of
`(a + j c) j' ≡ b + j d (mod p)` — whenever `a + j c` is invertible modulo `p`. Outside that case
the value is `ZMod`'s junk inverse and means nothing, so every lemma that reads a value off the
map carries the invertibility hypothesis. -/
def upperTriShift (p : ℕ) [NeZero p] (γ : SL(2, ℤ)) (j : Fin p) : Fin p :=
  ⟨(((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)⁻¹
    * ((γ 0 1 + (j : ℕ) * γ 1 1 : ℤ) : ZMod p)).val, ZMod.val_lt _⟩

/-- The value of `upperTriShift` in `ZMod p`. Deliberately not a `simp` lemma: the junk inverse on
the right is not a normal form, and the two facts callers want are `mul_upperTriShift_natCast` and
`upperTriShift_natCast_of_mem_Gamma0`. -/
lemma upperTriShift_natCast (p : ℕ) [NeZero p] (γ : SL(2, ℤ)) (j : Fin p) :
    ((upperTriShift p γ j : ℕ) : ZMod p)
      = ((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)⁻¹ * ((γ 0 1 + (j : ℕ) * γ 1 1 : ℤ) : ZMod p) :=
  ZMod.natCast_rightInverse _

/-- **The defining congruence.** For `a + j c` invertible modulo `p`, `upperTriShift p γ j` solves
`(a + j c) j' ≡ b + j d (mod p)`, and lying in `[0, p)` it is the only solution. -/
lemma mul_upperTriShift_natCast [NeZero p] {γ : SL(2, ℤ)} {j : Fin p}
    (hA : IsUnit (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p))) :
    ((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p) * ((upperTriShift p γ j : ℕ) : ZMod p)
      = ((γ 0 1 + (j : ℕ) * γ 1 1 : ℤ) : ZMod p) := by
  rw [upperTriShift_natCast, ← mul_assoc, ZMod.mul_inv_of_unit _ hA, one_mul]

/-- On `Γ₀(p)` the entry `a + j c` collapses to `a`, because `c ≡ 0`. -/
@[simp] lemma intCast_apply_zero_zero_add_natCast_mul_apply_one_zero_of_mem_Gamma0
    {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p) (j : Fin p) :
    ((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p) = ((γ 0 0 : ℤ) : ZMod p) := by
  push_cast
  rw [Gamma0_mem.mp hγp, mul_zero, add_zero]

/-- **`a + j c` is invertible on `Γ₀(p)`**, for every offset: it is `a` there, which
`CongruenceSubgroup.isUnit_intCast_apply_zero_zero_of_mem_Gamma0` already knows to be a unit.
This is what makes the whole of `Fin p` an admissible index set, with no offset left out. -/
lemma isUnit_intCast_apply_zero_zero_add_natCast_mul_apply_one_zero_of_mem_Gamma0
    {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p) (j : Fin p) :
    IsUnit (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)) := by
  rw [intCast_apply_zero_zero_add_natCast_mul_apply_one_zero_of_mem_Gamma0 hγp]
  exact isUnit_intCast_apply_zero_zero_of_mem_Gamma0 hγp

/-- **On `Γ₀(p)` the offset map is `j ↦ d b + j d²`.** The closed form the equivariance argument
below uses, and the reason the map is a bijection there: `d` is the inverse of `a`, and `d²` is
again a unit. -/
@[simp] lemma upperTriShift_natCast_of_mem_Gamma0 [NeZero p] {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p)
    (j : Fin p) : ((upperTriShift p γ j : ℕ) : ZMod p)
      = ((γ 1 1 * γ 0 1 + (j : ℕ) * (γ 1 1 * γ 1 1) : ℤ) : ZMod p) := by
  rw [upperTriShift_natCast,
    intCast_apply_zero_zero_add_natCast_mul_apply_one_zero_of_mem_Gamma0 hγp,
    ZMod.inv_eq_of_mul_eq_one _ _ ((γ 1 1 : ℤ) : ZMod p)
      (intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγp)]
  push_cast
  ring

/-- **The offset map is a bijection.** For `γ ∈ Γ₀(p)`, `d` is the inverse of `a` modulo `p`,
so the map gives the unique solution in `[0, p)` of `a j' ≡ b + j d (mod p)`.
Two offsets with the same shift differ by an element killed by the unit `d²`. -/
lemma upperTriShift_bijective [NeZero p] {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p) :
    Function.Bijective (upperTriShift p γ) := by
  refine Finite.injective_iff_bijective.mp fun j j' hjj ↦ ?_
  have had := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγp
  have h := congrArg (fun m : Fin p ↦ ((m : ℕ) : ZMod p)) hjj
  simp only [upperTriShift_natCast_of_mem_Gamma0 hγp] at h
  push_cast at h
  have hud : IsUnit ((γ 1 1 : ℤ) : ZMod p) :=
    IsUnit.of_mul_eq_one _ (by simpa [mul_comm] using had)
  have hcancel : ((j : ℕ) : ZMod p) = ((j' : ℕ) : ZMod p) :=
    (hud.mul hud).mul_left_inj.mp (by linear_combination h)
  exact Fin.val_injective (by
    simpa [ZMod.val_natCast_of_lt j.isLt, ZMod.val_natCast_of_lt j'.isLt] using
      congrArg ZMod.val hcancel)

/-- The matrix identity behind the coset factorisation, with the four entries of the second
factor given by hypothesis. Stated separately so that the computation runs on atoms: the
entries of `γ` and `γ'` never have to be unfolded inside it. -/
private lemma upperTriRep_mul_mapGL_eq {p : ℕ} (j j' : Fin p) (γ γ' : SL(2, ℤ))
    (h00 : γ' 0 0 = γ 0 0 + (j : ℕ) * γ 1 0)
    (h01 : (p : ℤ) * γ' 0 1
      = γ 0 1 + (j : ℕ) * γ 1 1 - (γ 0 0 + (j : ℕ) * γ 1 0) * (j' : ℕ))
    (h10 : γ' 1 0 = (p : ℤ) * γ 1 0)
    (h11 : γ' 1 1 = γ 1 1 - γ 1 0 * (j' : ℕ)) :
    upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p j' := by
  have c00 := congrArg (Int.cast : ℤ → ℚ) h00
  have c01 := congrArg (Int.cast : ℤ → ℚ) h01
  have c10 := congrArg (Int.cast : ℤ → ℚ) h10
  have c11 := congrArg (Int.cast : ℤ → ℚ) h11
  push_cast at c00 c01 c10 c11
  refine Units.ext (Matrix.ext fun r t ↦ ?_)
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, coe_upperTriRep, coe_upperTriRep, mapGL_coe_matrix, mapGL_coe_matrix]
  fin_cases r <;> fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, algebraMap_int_eq, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply, one_mul, mul_one, mul_zero,
      add_zero, zero_mul, zero_add] <;>
    [linear_combination -c00; linear_combination -c01 - ((j' : ℕ) : ℚ) * c00;
      linear_combination -c10; linear_combination -((j' : ℕ) : ℚ) * c10 - (p : ℚ) * c11]

/-- **The coset factorisation.** The product `!![1, j; 0, p] · γ` factors as
`γ' · !![1, j'; 0, p]` with `γ' ∈ Γ₀(N)` and `j'` the shifted offset, and the new lower-right
entry is `d - c j'`.

The two hypotheses are exactly what the factorisation consumes, and neither mentions how `p` and
`N` are related. `a + j c` invertible modulo `p` — for the single offset `j` at hand, not
uniformly — is what makes the offset `j'` exist; `N ∣ p c` is what puts the lower-left entry
`p c` of `γ'` back in `Γ₀(N)`. Neither `p ∣ N` nor any membership at a level built from `N` is
assumed, so `p ∤ N` is not excluded. The `Γ₀(p)` specialisation below, where invertibility holds
for every offset at once and the map is a bijection, is the form callers usually want.

The lower-right entry is given as an equation rather than as a congruence because the modulus
at which it is useful varies with the caller; the equivariance below reads off the congruence
modulo `N` it needs from that equation and `Γ₀(N)`-membership. -/
theorem exists_mem_Gamma0_upperTriRep_mul_of_isUnit [NeZero p] {γ : SL(2, ℤ)} {j : Fin p}
    (hA : IsUnit (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)))
    (hpc : (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0) : ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 N ∧
      (γ' 1 1 : ℤ) = γ 1 1 - γ 1 0 * ((upperTriShift p γ j : ℕ) : ℤ) ∧
      upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p (upperTriShift p γ j) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  -- the entry `b'` is an integer: the defining congruence of the offset map is exactly `p ∣ …`
  have hdvd : (p : ℤ) ∣ γ 0 1 + (j : ℕ) * γ 1 1
      - (γ 0 0 + (j : ℕ) * γ 1 0) * ((upperTriShift p γ j : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hmul := mul_upperTriShift_natCast hA
    push_cast at hmul ⊢
    linear_combination -hmul
  obtain ⟨b', hb'⟩ := hdvd
  set j' := upperTriShift p γ j with hj'
  have hdet' : (!![γ 0 0 + (j : ℕ) * γ 1 0, b';
      (p : ℤ) * γ 1 0, γ 1 1 - γ 1 0 * ((j' : ℕ) : ℤ)]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + (γ 1 0 : ℤ) * hb'
  -- the witness, with its four entries read off once, so that nothing below depends on how the
  -- `SL(2, ℤ)` subtype and the matrix literal reduce
  set γ' : SL(2, ℤ) := ⟨_, hdet'⟩ with hγ'
  have e00 : γ' 0 0 = γ 0 0 + (j : ℕ) * γ 1 0 := by simp [hγ']
  have e01 : γ' 0 1 = b' := by simp [hγ']
  have e10 : γ' 1 0 = (p : ℤ) * γ 1 0 := by simp [hγ']
  have e11 : γ' 1 1 = γ 1 1 - γ 1 0 * ((j' : ℕ) : ℤ) := by simp [hγ']
  refine ⟨γ', Gamma0_mem.mpr ?_, e11, upperTriRep_mul_mapGL_eq _ _ _ _ e00 ?_ e10 e11⟩
  · rw [e10]; exact hpc
  · rw [e01]; exact hb'.symm

/-- **The coset factorisation at `γ ∈ Γ₀(p)`.** The specialisation in which every offset is
admissible at once: on `Γ₀(p)` the entry `a + j c` is `a`, a unit for every `j`, so the general
statement applies uniformly and the offset map is the closed form `j ↦ d b + j d²`. -/
theorem exists_mem_Gamma0_upperTriRep_mul [NeZero p] {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p)
    (hpc : (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0) (j : Fin p) : ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 N ∧
      (γ' 1 1 : ℤ) = γ 1 1 - γ 1 0 * ((upperTriShift p γ j : ℕ) : ℤ) ∧
      upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p (upperTriShift p γ j) :=
  exists_mem_Gamma0_upperTriRep_mul_of_isUnit
    (isUnit_intCast_apply_zero_zero_add_natCast_mul_apply_one_zero_of_mem_Gamma0 hγp j) hpc

/-- **The coset factorisation at `γ ∈ Γ₀(N)`.** The specialisation of
`exists_mem_Gamma0_upperTriRep_mul` that `p ∣ N` and `γ ∈ Γ₀(N)` afford: both hypotheses of the
general statement follow, and the lower-right entry `d - c j'` becomes a congruence modulo `N`,
so `γ'` has the same `Gamma0Map` value as `γ`. That congruence is what lets the equivariance
below carry a fixed character, and it is the form every `Γ₀(N)` caller wants. -/
theorem exists_mem_Gamma0_upperTriRep_mul_of_mem_Gamma0 [NeZero p] (hpN : p ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) (j : Fin p) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 N ∧ ((γ' 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p (upperTriShift p γ j) := by
  obtain ⟨γ', hγ', hdd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul
    (Gamma0_le_Gamma0_of_dvd hpN hγ) (by rw [Int.cast_mul, Gamma0_mem.mp hγ, mul_zero]) j
  refine ⟨γ', hγ', ?_, hmul⟩
  rw [hdd]
  push_cast
  rw [Gamma0_mem.mp hγ]
  ring

/-- **The upper-triangular sum is `Γ₀(N)`-equivariant at `p ∣ N`.** The hypothesis is imposed
only at matrices of `Γ₀(N)` with the same lower-right entry modulo `N` as `γ`, which is all the
factorisation ever produces; the scalar `u` is left free so that the two corollaries below —
`Γ₁(N)`-invariance and nebentypus transport — are both instances. -/
theorem heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0 (k : ℤ) [NeZero p] (hpN : p ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) {f : ℍ → ℂ} {u : ℂ}
    (hf : ∀ δ ∈ Gamma0 N, ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) →
      f ∣[k] (mapGL ℚ δ : GL (Fin 2) ℚ) = u • f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ)
      = u • heckeSlashUpperTri k p f := by
  rw [heckeSlashUpperTri_def, SlashAction.sum_slash, Finset.smul_sum]
  have key : ∀ j : Fin p,
      (f ∣[k] (upperTriRep p j : GL (Fin 2) ℚ)) ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ)
        = u • (f ∣[k] (upperTriRep p (upperTriShift p γ j) : GL (Fin 2) ℚ)) := fun j ↦ by
    obtain ⟨γ', hγ', hdd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul_of_mem_Gamma0 hpN hγ j
    rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul, hf γ' hγ' hdd,
      ModularForm.rat_smul_slash_of_det_pos k (det_upperTriRep_pos p _) f u]
  rw [Finset.sum_congr rfl fun j _ ↦ key j]
  exact Fintype.sum_bijective (upperTriShift p γ)
    (upperTriShift_bijective (Gamma0_le_Gamma0_of_dvd hpN hγ))
    (fun j ↦ u • (f ∣[k] (upperTriRep p (upperTriShift p γ j) : GL (Fin 2) ℚ)))
    (fun j ↦ u • (f ∣[k] (upperTriRep p j : GL (Fin 2) ℚ))) fun _ ↦ rfl

/-- **The upper-triangular sum preserves `Γ₁(N)`-invariance at `p ∣ N`** — the invariance that
turns it into an operator on `M_k(Γ₁(N))`. -/
theorem heckeSlashUpperTri_slash_mapGL_of_mem_Gamma1 (k : ℤ) [NeZero p] (hpN : p ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) {f : ℍ → ℂ}
    (hf : ∀ δ ∈ Gamma1 N, f ∣[k] (mapGL ℚ δ : GL (Fin 2) ℚ) = f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ) = heckeSlashUpperTri k p f := by
  have h11 : ((γ 1 1 : ℤ) : ZMod N) = 1 := (mem_Gamma1_iff.mp hγ).2
  have h := heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0 (u := 1) k hpN
    (Gamma1_in_Gamma0 N hγ) (f := f) fun δ hδ hd ↦ by
      rw [hf δ (mem_Gamma1_iff.mpr ⟨hδ, hd.trans h11⟩), one_smul]
  rwa [one_smul] at h

/-- **The upper-triangular sum preserves the nebentypus at `p ∣ N`**: if `f` transforms under
`Γ₀(N)` by the character `χ`, so does `heckeSlashUpperTri k p f`. This is the function-level
statement behind the fact that the operator preserves `M_k(N, χ)`. -/
theorem heckeSlashUpperTri_slash_mapGL_of_nebentypus (k : ℤ) [NeZero p] (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) (γ : ↥(Gamma0 N)) {f : ℍ → ℂ}
    (hf : ∀ δ : ↥(Gamma0 N), f ∣[k] (mapGL ℚ (δ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits δ)) : ℂ) • f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits γ)) : ℂ) • heckeSlashUpperTri k p f := by
  apply heckeSlashUpperTri_slash_mapGL_of_mem_Gamma0 k hpN γ.2
  intro δ hδ hd
  have hmap : (Gamma0Map N).toHomUnits ⟨δ, hδ⟩ = (Gamma0Map N).toHomUnits γ := Units.ext hd
  rw [hf ⟨δ, hδ⟩, hmap]

/-- **The upper-triangular sum preserves the nebentypus at every index supported on the level.**
If `f` transforms under `Γ₀(N)` by the character `χ`, so does `heckeSlashUpperTri k n f`.

The divisor case above does not apply directly at `n = q ^ 2`, since `Γ₀(N)` need not lie in
`Γ₀(q ^ 2)`. Instead the index is peeled apart one prime at a time, and the composition law for
upper-triangular sums reduces to the divisor case. -/
theorem heckeSlashUpperTri_slash_mapGL_of_nebentypus_of_primeFactors_subset (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) (hn0 : n ≠ 0)
    (hn : n.primeFactors ⊆ N.primeFactors) (γ : ↥(Gamma0 N)) {f : ℍ → ℂ}
    (hf : ∀ δ : ↥(Gamma0 N), f ∣[k] (mapGL ℚ (δ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits δ)) : ℂ) • f) :
    heckeSlashUpperTri k n f ∣[k] (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ)
      = (↑(χ ((Gamma0Map N).toHomUnits γ)) : ℂ) • heckeSlashUpperTri k n f := by
  induction n using Nat.strong_induction_on generalizing γ with
  | _ n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [heckeSlashUpperTri_one]
      exact hf γ
    · have hq : n.minFac.Prime := Nat.minFac_prime hn1
      have hqn : n.minFac ∣ n := Nat.minFac_dvd n
      have hqN : n.minFac ∣ N :=
        (Nat.mem_primeFactors.mp (hn (Nat.mem_primeFactors.mpr ⟨hq, hqn, hn0⟩))).2.1
      have hm0 : n / n.minFac ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqn) hq.pos).ne'
      have hmlt : n / n.minFac < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hq.one_lt
      have hmn : (n / n.minFac).primeFactors ⊆ N.primeFactors :=
        (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hqn) hn0).trans hn
      have _ : NeZero n.minFac := ⟨hq.ne_zero⟩
      have key : heckeSlashUpperTri k n f
          = heckeSlashUpperTri k n.minFac (heckeSlashUpperTri k (n / n.minFac) f) := by
        rw [heckeSlashUpperTri_heckeSlashUpperTri k n.minFac (n / n.minFac) f,
          Nat.div_mul_cancel hqn]
      rw [key]
      exact heckeSlashUpperTri_slash_mapGL_of_nebentypus k hqN χ γ
        fun δ ↦ ih _ hmlt hm0 hmn δ

end HeckeRing.GL2

end
