/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimeCosets
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.ModularForm
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Prime

/-!
# The twisted operator of `diag(1, p)` is the classical `Tₚ` on `S_k(N, χ)`

The `Γ₀(N)` Hecke ring acts on the nebentypus space `S_k(N, χ)` through the `χ`-twisted slash
sums (`HeckeSlash/Nebentypus/*`), while the classical `Tₚ` on `S_k(Γ₁(N))` is the untwisted sum
over `Γ₁(N)` cosets (`HeckeSlash/Prime.lean`). This file identifies the two at every prime `p`:
on `S_k(N, χ)` the twisted operator of the generator `diag(1, p)` **is** the classical `Tₚ`.

## Why the twist disappears

Over `Γ₀(N)` the right cosets of `diag(1, p)` are named by the same `p + 1` representatives as
over `Γ₁(N)` (`Gamma0/Diagonal/PrimeCosets.lean`): `!![1, j; 0, p]` and `σ · diag(p, 1)` with
`σ ∈ Γ₀(N)` of bottom row `(N, p)`. The twisting character reads the upper-left unit of a
representative: it is `1` on the upper-triangular ones, and on `σ · diag(p, 1)` it is `χ(σ₀₀ p)`,
which is `1` because `σ₀₀ p ≡ 1 (mod N)` by the determinant. So every weight is `1`, and the only
character that survives is the nebentypus factor `χ(p)` produced by slashing `f` by `σ` — exactly
the factor the classical formula carries on the `Γ₁(N)` side.

## Main results

* `HeckeRing.GL2.coe_twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0_of_prime`: for `p ∤ N`
  prime and `f ∈ S_k(N, χ)`, the twisted operator of `diagCosetGamma0 N ![1, p]` at `f` is
  `heckeTCuspNat k p f`, as functions on `ℍ`.
* `HeckeRing.GL2.coe_twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0_of_dvd`: the same at a
  prime `p ∣ N`, where both operators are the upper-triangular `Uₚ`.
* `HeckeRing.GL2.delta0NebentypusChar_upperTriRep`,
  `HeckeRing.GL2.delta0NebentypusChar_mapGL_mul_scaleRep`: the twisting character is `1` on both
  kinds of representative.

## Scope

Only cusp forms; the modular-form version is not treated here.

## Provenance

The prime case of `heckeRingHomCharSpace_D_p_eq_scalar_charRestrict` of the AINTLIB
`LeanModularForms` project (`LeanModularForms/HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean`,
Chris Birkbeck, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>). In the source the
twist runs the other way, so its statement carries a factor `χ(p)⁻¹`; with this repository's
convention (`Nebentypus/Basic.lean`, "Which way the character goes") the factor is `1` and the
identification is exact.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {N p : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

/-- The twisting character is trivial on an upper-triangular representative: its upper-left
entry is `1`. -/
lemma delta0NebentypusChar_upperTriRep (j : Fin p) (hmem : upperTriRep p j ∈ Delta0 N) :
    delta0NebentypusChar N χ ⟨upperTriRep p j, hmem⟩ = 1 := by
  rw [delta0NebentypusChar_apply]
  have h : (Delta0UpperUnit N ⟨upperTriRep p j, hmem⟩ : ZMod N)
      = ((!![1, (j : ℕ); 0, (p : ℕ)] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) := by
    refine Delta0UpperUnit_apply_val N ?_
    change ((upperTriRep p j : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = _
    rw [coe_upperTriRep]
    ext i l
    fin_cases i <;> fin_cases l <;> simp
  have hu : Delta0UpperUnit N ⟨upperTriRep p j, hmem⟩ = 1 := Units.ext (by simpa using h)
  rw [hu, map_one]

/-- The twisting character is trivial on the twisted representative `σ · diag(p, 1)`: its
upper-left entry is `σ₀₀ p ≡ 1 (mod N)`, by the determinant of `σ`. -/
lemma delta0NebentypusChar_mapGL_mul_scaleRep (hp : 0 < p) {σ : SL(2, ℤ)}
    (hσ10 : σ 1 0 = (N : ℤ)) (hσ11 : σ 1 1 = (p : ℤ))
    (hmem : mapGL ℚ σ * scaleRep p ∈ Delta0 N) :
    delta0NebentypusChar N χ ⟨mapGL ℚ σ * scaleRep p, hmem⟩ = 1 := by
  rw [delta0NebentypusChar_apply]
  have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one σ
  have h : (Delta0UpperUnit N ⟨mapGL ℚ σ * scaleRep p, hmem⟩ : ZMod N)
      = ((!![σ 0 0 * (p : ℤ), σ 0 1; σ 1 0 * (p : ℤ), σ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0
          : ZMod N) := by
    refine Delta0UpperUnit_apply_val N ?_
    change ((mapGL ℚ σ * scaleRep p : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = _
    rw [Units.val_mul, coe_mapGL_int_rat_fin_two, coe_scaleRep p hp]
    ext i l
    fin_cases i <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : ((σ 0 0 * (p : ℤ) : ℤ) : ZMod N) = 1 := by
    have : σ 0 0 * (p : ℤ) = 1 + σ 0 1 * (N : ℤ) := by
      rw [← hσ10]
      linear_combination hdet - σ 0 0 * hσ11
    rw [this]
    push_cast
    simp
  have hu : Delta0UpperUnit N ⟨mapGL ℚ σ * scaleRep p, hmem⟩ = 1 :=
    Units.ext (by simpa [h1] using h)
  rw [hu, map_one]

/-- The double coset of the chosen representative of `diagCosetGamma0 N ![1, p]` is that of
`diag(1, p)`: `HeckeCoset.toSet_eq_doubleCoset_rep` read against `diagCosetGamma0_toSet`. -/
private theorem doubleCoset_out_diagCosetGamma0 (p : ℕ) :
    doubleCoset ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).out :
        GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) =
      doubleCoset (natDiagGL 2 ![1, p]) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  rw [← HeckeCoset.rep_def]
  exact (HeckeCoset.toSet_eq_doubleCoset_rep _).symm.trans (diagCosetGamma0_toSet N _ _)

/-- **The twisted operator of `diag(1, p)` on `S_k(N, χ)` is the classical `Tₚ`**, at a prime
`p ∤ N`: the `Γ₀(N)` right cosets of `diag(1, p)` are named by the same representatives as the
`Γ₁(N)` ones, the twisting character is trivial on all of them, and on the twisted representative
`σ · diag(p, 1)` the slash by `σ ∈ Γ₀(N)` produces the nebentypus factor `χ(p)` that the classical
formula carries. -/
theorem coe_twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0_of_prime [NeZero N] (hp : p.Prime)
    (h : Nat.Coprime p N) (f : cuspFormCharSpace k χ) :
    ⇑((twistedHeckeSlashCuspFormCharEnd k χ
        (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) f :
          CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ⇑(heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hσ : gamma0Twist N p h ∈ Gamma0 N :=
    Gamma0_mem.mpr (by rw [gamma0Twist_apply_one_zero h]; exact_mod_cast ZMod.natCast_self N)
  rw [coe_twistedHeckeSlashCuspFormCharEnd_eq_sum k χ _ (primeRep (gamma0Twist N p h) p)
      ((doubleCoset_out_diagCosetGamma0 p).trans
        (doubleCoset_natDiagGL_Gamma0_eq_iUnion_rightCosets_of_prime hp
          (gamma0Twist_apply_one_zero h) (gamma0Twist_apply_one_one h)))
      (op_primeRep_smul_injective (G := Gamma0 N) hp.one_lt (gamma0Twist_apply_one_one h)) f,
    Fintype.sum_option, heckeTCuspNat_def,
    coe_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_mem_cuspFormCharSpace k hp h χ f.2,
    heckeSlashUpperTri_def]
  simp only [primeRep_some, primeRep_none, delta0NebentypusChar_upperTriRep χ,
    delta0NebentypusChar_mapGL_mul_scaleRep χ hp.pos (gamma0Twist_apply_one_zero h)
      (gamma0Twist_apply_one_one h), Units.val_one, one_smul]
  have hslash : ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
        ∣[k] (mapGL ℚ (gamma0Twist N p h) * scaleRep p)
      = (χ (ZMod.unitOfCoprime p h) : ℂ)
        • (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] scaleRep p) := by
    have hunit : (Gamma0Map N).toHomUnits ⟨gamma0Twist N p h, hσ⟩ = ZMod.unitOfCoprime p h := by
      refine Units.ext ?_
      rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply, gamma0Twist_apply_one_one h,
        ZMod.coe_unitOfCoprime]
      push_cast
      rfl
    rw [SlashAction.slash_mul, ModularForm.rat_slash k (mapGL ℚ (gamma0Twist N p h)), map_mapGL,
      (mem_cuspFormCharSpace_iff_nebentypus k χ _).mp f.2 ⟨gamma0Twist N p h, hσ⟩, hunit,
      ModularForm.rat_smul_slash_of_det_pos k (det_scaleRep_pos p)]
  rw [hslash]
  exact add_comm _ _

/-- **At a prime dividing the level, the twisted operator of `diag(1, p)` is `Uₚ`**: the `Γ₀(N)`
right cosets of `diag(1, p)` are the `p` upper-triangular ones, every weight is `1`, and the
classical `Tₚ` is the upper-triangular operator (`heckeTCuspNat_eq_upperTri`). -/
theorem coe_twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0_of_dvd [NeZero N] (hp : p.Prime)
    (hpN : p ∣ N) (f : cuspFormCharSpace k χ) :
    ⇑((twistedHeckeSlashCuspFormCharEnd k χ
        (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) f :
          CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ⇑(heckeTCuspNat k p (_hn := NeZero.of_dvd hpN)
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have : NeZero p := NeZero.of_dvd hpN
  rw [coe_twistedHeckeSlashCuspFormCharEnd_eq_sum k χ _ (upperTriRep p)
      ((doubleCoset_out_diagCosetGamma0 p).trans
        (doubleCoset_natDiagGL_Gamma0_eq_iUnion_rightCosets_of_dvd hp hpN))
      (op_upperTriRep_smul_injective (G := Gamma0 N)) f,
    heckeTCuspNat_eq_upperTri k hpN, coe_heckeSlashUpperTriCuspFormEnd, heckeSlashUpperTri_def]
  simp only [delta0NebentypusChar_upperTriRep χ, Units.val_one, one_smul]

end HeckeRing.GL2
