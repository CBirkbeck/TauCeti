/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.QExpansion
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators

/-!
# `Tₚ` commutes with the degeneracy operator `V_d`

The degeneracy operator `V_d : S_k(Γ₁(M)) → S_k(Γ₁(N))`, `(V_d f) τ = f (d τ)`, raises the level
along `d * M ∣ N`. This file proves that it commutes with the Hecke operator `Tₚ` at every prime
`p` coprime to `N`, the input to the statement that `Tₚ` preserves the old and new subspaces.

## The shape of the proof

`Tₚ` at a prime is `heckeSlashUpperTri k p f + (⟨p⟩ f) ∣[k] diag(p, 1)`, and `V_d` is — up to the
normalising scalar `d ^ (k - 1)` — the slash by `diag(d, 1)`. So the theorem splits into a
statement about each summand, and each is proved in the `diag(d, 1)`-slash form, where the
normalising scalars are absent:

* the upper-triangular sum, `heckeSlashUpperTri_slash_natDiagGL`. The two slashes do **not**
  commute termwise: `diag(d, 1) · !![1, b; 0, p]` is `!![1, d b; 0, p] · diag(d, 1)`, whose upper
  entry `d b` leaves the range `b < p`. Writing `d b = q p + r` puts the excess into `T ^ q`,
  which the level-`M` invariance of `f` absorbs, leaving the representative `r`. Coprimality of
  `d` and `p` makes `b ↦ r` a permutation of `Fin p`, so the sum is merely reindexed.
* the diamond term, which commutes because `diag(d, 1)` and `diag(p, 1)` do
  (`TauCeti.scaleGL_mul`), once `TauCeti.CuspForm.diamondOpCusp_levelRaise` has moved `⟨p⟩`
  across `V_d`.

## Main results

* `HeckeRing.GL2.heckeSlashUpperTri_slash_natDiagGL`: the upper-triangular sum commutes with the
  slash by `diag(d, 1)`, for any `Γ₁(M)`-invariant function and any `d` coprime to `p`.
* `HeckeRing.GL2.heckeTCuspNat_levelRaise`: **`Tₚ (V_d f) = V_d (Tₚ f)`** for `p` prime and
  coprime to the raised level `N`.

## Provenance

The mathematics follows `heckeT_p_all_levelRaise_comm` and its supporting lemmas in the AINTLIB
[`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) project, file
`LeanModularForms/HeckeRIngs/GL2/Newforms/LevelRaiseComm.lean`, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck, lines 45–311.
No proof code is transcribed: that development works with bare coset functions `heckeT_p_ut` and
`heckeT_p_fun` and a `Γ₁`-shift matrix of its own, and splits `Tₚ` on whether `p` divides the
level, whereas here `Tₚ` is the single-formula operator of `HeckeSlash/Prime.lean`, the shift is
Mathlib's `ModularGroup.T`, and the level-raise is the general `TauCeti.CuspForm.levelRaise` of
`Degeneracy.lean`, stated at `d * M ∣ N` rather than at `d * M = N`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.6.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn TauCeti

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {M d N p : ℕ} (k : ℤ)

/-! ### The shift matrix -/

/-- Every power of the translation `T = !![1, 1; 0, 1]` lies in `Γ₁(M)`, at every level: its
diagonal is `1` and its lower-left entry is `0` before any reduction. -/
private lemma T_zpow_mem_Gamma1 (M : ℕ) (q : ℤ) : ModularGroup.T ^ q ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [ModularGroup.coe_T_zpow, -map_zpow]

/-- A `Γ₁(M)`-invariant function is fixed by the rational slash of any power of `T`. -/
private lemma slash_mapGL_T_zpow {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma1 M).map (mapGL ℝ), f ∣[k] γ = f) (q : ℤ) :
    f ∣[k] (mapGL ℚ (ModularGroup.T ^ q) : GL (Fin 2) ℚ) = f :=
  ModularForm.slash_eq_of_mem_map_mapGL hf (Subgroup.mem_map_of_mem _ (T_zpow_mem_Gamma1 M q))

/-! ### The upper-triangular representatives under `diag(d, 1)` -/

/-- The matrix of a power of `T` over `ℚ`. `map_zpow` is disabled: it moves the exponent outside
`mapGL`, where the entrywise description of `T` no longer applies. -/
private lemma coe_mapGL_T_zpow (q : ℤ) :
    (↑(mapGL ℚ (ModularGroup.T ^ q)) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (q : ℚ); 0, 1] := by
  simp [-map_zpow]

/-- **The commutation of `diag(d, 1)` past an upper-triangular representative.** Both sides are
`!![d, d b; 0, p]`: on the right, `d b = q p + r` is split so that the representative index `r`
is again in range, at the cost of the shift `T ^ q`. -/
private lemma natDiagGL_mul_upperTriRep (hd : 0 < d) (b : Fin p) {q r : ℕ} (hr : r < p)
    (hqr : d * (b : ℕ) = q * p + r) :
    natDiagGL 2 ![d, 1] * upperTriRep p b =
      mapGL ℚ (ModularGroup.T ^ (q : ℤ)) * (upperTriRep p ⟨r, hr⟩ * natDiagGL 2 ![d, 1]) := by
  have hd1 : ∀ i : Fin 2, 0 < ![d, 1] i := fun i ↦ by fin_cases i <;> simp [hd]
  have hmod : (d : ℚ) * ((b : ℕ) : ℚ) = (q : ℚ) * (p : ℚ) + (r : ℚ) := by exact_mod_cast hqr
  have hdiag : (↑(natDiagGL 2 ![d, 1]) : Matrix (Fin 2) (Fin 2) ℚ) = !![(d : ℚ), 0; 0, 1] := by
    rw [natDiagGL_coe 2 _ hd1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hdiag, coe_upperTriRep, coe_upperTriRep,
    coe_mapGL_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linarith

/-- **Positive natural diagonal matrices commute.** This is what makes the diamond term of `Tₚ`
pass through `V_d`: both are slashes by a `diag(·, 1)`. -/
private lemma natDiagGL_comm (hd : 0 < d) (hp : 0 < p) :
    natDiagGL 2 ![d, 1] * natDiagGL 2 ![p, 1] = natDiagGL 2 ![p, 1] * natDiagGL 2 ![d, 1] := by
  have hd1 : ∀ i : Fin 2, 0 < ![d, 1] i := fun i ↦ by fin_cases i <;> simp [hd]
  have hp1 : ∀ i : Fin 2, 0 < ![p, 1] i := fun i ↦ by fin_cases i <;> simp [hp]
  rw [natDiagGL_mul 2 _ _ hd1 hp1, natDiagGL_mul 2 _ _ hp1 hd1, mul_comm ![d, 1] ![p, 1]]

/-! ### Reindexing by multiplication -/

/-- Multiplication by `d` modulo `p` permutes `Fin p` when `d` and `p` are coprime. -/
private noncomputable def mulModEquiv (hp : 0 < p) (hdp : Nat.Coprime d p) : Fin p ≃ Fin p :=
  haveI : NeZero p := ⟨hp.ne'⟩
  Equiv.ofBijective (fun b ↦ ⟨d * (b : ℕ) % p, Nat.mod_lt _ hp⟩)
    (Finite.injective_iff_bijective.mp (by
      intro b₁ b₂ hb
      have hcast : ((d * (b₁ : ℕ) : ℕ) : ZMod p) = ((d * (b₂ : ℕ) : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by simpa using congrArg Fin.val hb)
      rw [Nat.cast_mul, Nat.cast_mul] at hcast
      have hunit : IsUnit ((d : ℕ) : ZMod p) := (ZMod.isUnit_iff_coprime d p).mpr hdp
      have hval : ((b₁ : ℕ) : ZMod p) = ((b₂ : ℕ) : ZMod p) := hunit.mul_left_cancel hcast
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hval
      rwa [Nat.mod_eq_of_lt b₁.isLt, Nat.mod_eq_of_lt b₂.isLt, Fin.val_eq_val] at this))

@[simp]
private lemma mulModEquiv_apply (hp : 0 < p) (hdp : Nat.Coprime d p) (b : Fin p) :
    (mulModEquiv hp hdp b : ℕ) = d * (b : ℕ) % p := (rfl)

/-! ### The upper-triangular sum against `diag(d, 1)` -/

/-- **The upper-triangular slash sum commutes with the slash by `diag(d, 1)`**, for `d` coprime
to `p` and any function invariant under `Γ₁(M)`. This is the level-raising half of
`heckeTCuspNat_levelRaise`, stated before the normalising scalar of `V_d` is introduced. -/
theorem heckeSlashUpperTri_slash_natDiagGL (hd : 0 < d) (hp : 0 < p) (hdp : Nat.Coprime d p)
    {f : ℍ → ℂ} (hf : ∀ γ ∈ (Gamma1 M).map (mapGL ℝ), f ∣[k] γ = f) :
    heckeSlashUpperTri k p (f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ)) =
      heckeSlashUpperTri k p f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ) := by
  rw [heckeSlashUpperTri_def, heckeSlashUpperTri_def, SlashAction.sum_slash]
  rw [← Equiv.sum_comp (mulModEquiv hp hdp) fun b ↦ (f ∣[k] upperTriRep p b) ∣[k]
    (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ)]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← SlashAction.slash_mul,
    natDiagGL_mul_upperTriRep hd b (Nat.mod_lt _ hp) (Nat.div_add_mod' (d * (b : ℕ)) p).symm,
    SlashAction.slash_mul, slash_mapGL_T_zpow k hf, SlashAction.slash_mul]
  rfl

/-! ### `Tₚ` and `V_d` -/

/-- **`Tₚ` commutes with the degeneracy operator `V_d`.** For `d * M ∣ N` and a prime `p` coprime
to `N`, raising the level of `f` and then applying `Tₚ` at level `N` agrees with applying `Tₚ` at
level `M` and then raising the level.

Coprimality is not decoration: at `p ∣ N` the diamond term of `Tₚ` vanishes at level `N` but need
not vanish at level `M`, and `b ↦ d b mod p` stops being a permutation once `p ∣ d`. -/
theorem heckeTCuspNat_levelRaise [NeZero N] (hdvd : d * M ∣ N) (hp : p.Prime)
    (hpN : Nat.Coprime p N) (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero d := ⟨fun hd ↦ NeZero.ne N (by simpa [hd] using hdvd)⟩
    haveI : NeZero M := ⟨fun hM ↦ NeZero.ne N (by simpa [hM] using hdvd)⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeTCuspNat k p (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) f) =
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) (heckeTCuspNat k p f) := by
  have : NeZero d := ⟨fun hd ↦ NeZero.ne N (by simpa [hd] using hdvd)⟩
  have : NeZero M := ⟨fun hM ↦ NeZero.ne N (by simpa [hM] using hdvd)⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hMdvd : M ∣ N := (Dvd.intro_left d rfl).trans hdvd
  have hpM : Nat.Coprime p M := hpN.coprime_dvd_right hMdvd
  have hpd : Nat.Coprime p d := hpN.coprime_dvd_right ((dvd_mul_right d M).trans hdvd)
  have hf : ∀ γ ∈ (Gamma1 M).map (mapGL ℝ), ⇑f ∣[k] γ = ⇑f :=
    fun γ hγ ↦ SlashInvariantFormClass.slash_action_eq f γ hγ
  have hunits : ZMod.unitsMap hMdvd (ZMod.unitOfCoprime p hpN) = ZMod.unitOfCoprime p hpM := by
    ext
    simp [ZMod.unitsMap_def, ZMod.coe_unitOfCoprime]
  have hscale : ∀ g : ℍ → ℂ, g ∣[k] scaleGL d = g ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ) :=
    fun g ↦ by rw [ModularForm.rat_slash, map_natDiagGL_d_one_eq_scaleGL]
  refine DFunLike.coe_injective ?_
  simp only [coe_heckeTCuspNat_prime k hp, CuspForm.coe_levelRaise,
    diamondOpCuspNat_of_coprime k hpN, diamondOpCuspNat_of_coprime k hpM,
    CuspForm.diamondOpCusp_levelRaise hdvd k (ZMod.unitOfCoprime p hpN) f, hunits,
    SlashAction.add_slash, smul_add, heckeSlashUpperTri_smul, hscale]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [heckeSlashUpperTri_slash_natDiagGL k hdpos hp.pos hpd.symm hf]
  · rw [ModularForm.rat_smul_slash_of_det_pos k (det_scaleRep_pos p), ← SlashAction.slash_mul,
      ← SlashAction.slash_mul, scaleRep_def, natDiagGL_comm hdpos hp.pos]

end HeckeRing.GL2
