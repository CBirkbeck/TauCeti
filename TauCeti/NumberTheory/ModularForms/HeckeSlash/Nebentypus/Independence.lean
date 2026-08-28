/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Independence
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Invariance

/-!
# The twisted slash sum depends only on the double coset

`HeckeSlash/Independence.lean` proves that `heckeSlashSum k D f` is `∑ᵢ f ∣[k] aᵢ` for *any*
family `(aᵢ)` of representatives of the right cosets of `Γ₁ δ Γ₂`, provided `f` is `Γ₁`-invariant.
This file is the nebentypus-twisted counterpart.

## Why this is a theorem and not bookkeeping

In the untwisted setting a change of representatives moves each summand `f ∣[k] aᵢ` by an element
of `Γ₁`, and invariance absorbs it. Here `f` is only a `χ`-eigenfunction, so the slash genuinely
changes — and what repairs it is the *weight*: the summand carries `delta0NebentypusChar χ` of its
own representative, and that character factor is exactly the inverse of the eigenvalue the slash
picks up. So the weighted summand, unlike the bare slash, is a function of the right coset alone.

That cancellation is `delta0NebentypusChar_smul_slash_mapGL_mul` of
`HeckeSlash/Nebentypus/Invariance.lean`, which states it for a representative presented as
`γ · x`. The only work here is to feed it a right-coset equality instead, and then to run the
untwisted file's comparison of two enumerations unchanged.

## Main results

* `HeckeRing.GL2.smul_slash_eq_of_rightCoset_eq`: the weighted slash of a `χ`-eigenfunction
  depends only on the right coset `Γ₀(N) x`.
* `HeckeRing.GL2.twistedHeckeSlashSum_eq_sum_of_rightCosets`: `twistedHeckeSlashSum k χ D f` is
  the weighted sum over any family of representatives of the right cosets.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) [NeZero N]

omit [NeZero N] in
/-- **The weighted slash depends only on the right coset.** For a `χ`-eigenfunction `f` and
representatives `x`, `y` of `Δ₀(N)` lying in the same right coset of `Γ₀(N)`, the weighted slashes
agree.

This is the twisted counterpart of `slash_eq_of_rightCoset_eq`, and it is where the whole content
of the independence below sits: there invariance makes the bare slash coset-dependent, here it is
the character weight that does it. The cancellation itself is
`delta0NebentypusChar_smul_slash_mapGL_mul`; all this adds is the passage from a right-coset
equality to the factorisation `y = γ · x` that lemma consumes. -/
theorem smul_slash_eq_of_rightCoset_eq (f : ℍ → ℂ) (hf : f ∈ functionCharSpace k χ)
    {x y : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) (hy : y ∈ Delta0 N)
    (h : MulOpposite.op x • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
        Set (GL (Fin 2) ℚ)) =
      MulOpposite.op y • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
        Set (GL (Fin 2) ℚ))) :
    (delta0NebentypusChar N χ ⟨y, hy⟩ : ℂ) • (f ∣[k] y) =
      (delta0NebentypusChar N χ ⟨x, hx⟩ : ℂ) • (f ∣[k] x) := by
  obtain ⟨γ, hγ, hmap⟩ := Subgroup.mem_map.mp ((rightCoset_eq_iff _).mp h)
  exact delta0NebentypusChar_smul_slash_mapGL_mul k χ f hf ⟨γ, hγ⟩ hx hy
    (by rw [hmap, inv_mul_cancel_right])

variable (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

-- The enumeration `∑` needs, as in `Nebentypus/Basic.lean` and `Nebentypus/Composition.lean`.
attribute [local instance] Fintype.ofFinite

/-- **The twisted slash sum of a `χ`-eigenfunction is the weighted sum over any decomposition of
the double coset into right cosets.** If the right cosets `Γ₀(N) aᵢ` are pairwise distinct and
cover `Γ₀(N) D.out Γ₀(N)`, and every `aᵢ` lies in `Δ₀(N)`, then `twistedHeckeSlashSum k χ D f` is
`∑ᵢ χ'(aᵢ) • (f ∣[k] aᵢ)`.

So the twisted operator, like the untwisted one, is attached to the double coset rather than to
the representatives `twistedHeckeSlashSum` happens to choose.

The hypothesis `ha` has no untwisted counterpart and is forced by the weight: an arbitrary
representative must lie in `Δ₀(N)` for the twisting character to be applied to it at all, whereas
the bare slash of `heckeSlashSum_eq_sum_of_rightCosets` asks nothing of `aᵢ`. The chosen
representatives satisfy it by `rightCosetRep_mem_Delta0`.

The proof is the untwisted one with its per-summand step replaced: the comparison of the two
enumerations is identical, and only `smul_slash_eq_of_rightCoset_eq` differs. -/
theorem twistedHeckeSlashSum_eq_sum_of_rightCosets {ι : Type*} [Fintype ι]
    (a : ι → GL (Fin 2) ℚ) (ha : ∀ i, a i ∈ Delta0 N)
    (hcover : doubleCoset (D.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) =
      ⋃ i, MulOpposite.op (a i) • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
        Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)))
    (f : ℍ → ℂ) (hf : f ∈ functionCharSpace k χ) :
    twistedHeckeSlashSum k χ D f =
      ∑ i, (delta0NebentypusChar N χ ⟨a i, ha i⟩ : ℂ) • (f ∣[k] a i) := by
  classical
  have hcover' : doubleCoset (D.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) =
      ⋃ v, MulOpposite.op (rightCosetRep D v) •
        (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) := by
    simpa only [rightCosetRep_def] using
      doubleCoset_eq_iUnion_rightCosets _ _ (D.out : GL (Fin 2) ℚ)
  have hinj' : Function.Injective fun v : DecompQuotient ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹ ↦
      MulOpposite.op (rightCosetRep D v) •
        (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) := by
    simpa only [rightCosetRep_def] using
      op_mul_out_inv_smul_injective _ _ (D.out : GL (Fin 2) ℚ)
  have hself : ∀ x : GL (Fin 2) ℚ, x ∈ MulOpposite.op x •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) := fun x ↦
    (mem_rightCoset_iff x).mpr (by rw [mul_inv_cancel]; exact one_mem _)
  have hmatch : ∀ x y : GL (Fin 2) ℚ, x ∈ MulOpposite.op y •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) →
      MulOpposite.op x • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
          Set (GL (Fin 2) ℚ)) =
        MulOpposite.op y • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
          Set (GL (Fin 2) ℚ)) := fun x y hxy ↦
    (rightCoset_eq_iff _).mpr (by simpa using inv_mem ((mem_rightCoset_iff y).mp hxy))
  have key : ∀ i, ∃ v, MulOpposite.op (a i) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op (rightCosetRep D v) •
        (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) := by
    intro i
    have hmem : a i ∈ doubleCoset (D.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) := by
      rw [hcover]; exact Set.mem_iUnion_of_mem i (hself (a i))
    rw [hcover'] at hmem
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hmem
    exact ⟨v, hmatch _ _ hv⟩
  have key' : ∀ v, ∃ i, MulOpposite.op (rightCosetRep D v) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op (a i) •
        (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) := by
    intro v
    have hmem : rightCosetRep D v ∈ doubleCoset (D.out : GL (Fin 2) ℚ)
        ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
      rw [hcover']; exact Set.mem_iUnion_of_mem v (hself (rightCosetRep D v))
    rw [hcover] at hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    exact ⟨i, hmatch _ _ hi⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ι → DecompQuotient ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹, ∀ i,
      MulOpposite.op (a i) •
          (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) =
        MulOpposite.op (rightCosetRep D (φ i)) •
          (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) :=
    ⟨fun i ↦ (key i).choose, fun i ↦ (key i).choose_spec⟩
  have hcoset : ∀ i j, φ i = φ j → MulOpposite.op (a i) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op (a j) •
        (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) :=
    fun i j hij ↦ by rw [hφ i, hφ j, hij]
  have hbij : Function.Bijective φ := by
    refine ⟨fun i j hij ↦ hinj (hcoset i j hij), fun v ↦ ?_⟩
    obtain ⟨i, hi⟩ := key' v
    exact ⟨i, (hinj' (hi.trans (hφ i))).symm⟩
  rw [twistedHeckeSlashSum_def]
  refine (Fintype.sum_bijective φ hbij _ _ fun i ↦ ?_).symm
  rw [nebentypusWeight_def]
  exact (smul_slash_eq_of_rightCoset_eq k χ f hf (ha i)
    (rightCosetRep_mem_Delta0 D (φ i)) (hφ i)).symm

end HeckeRing.GL2

end
