/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Basic
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

* the upper-triangular sum, `heckeSlashUpperTri_slash_scaleRep_comm`. The two slashes do **not**
  commute termwise: `diag(d, 1) · !![1, b; 0, p]` is `!![1, d b; 0, p] · diag(d, 1)`, whose upper
  entry `d b` leaves the range `b < p`. Writing `d b = q p + r` puts the excess into `T ^ q`,
  which the level-`M` invariance of `f` absorbs, leaving the representative `r`. Coprimality of
  `d` and `p` makes `b ↦ r` a permutation of `Fin p`, so the sum is merely reindexed.
* the diamond term, which commutes because natural diagonal matrices do —
  `HeckeRing.GLn.natDiagGL_comm` — once `TauCeti.CuspForm.diamondOpCusp_levelRaise` has moved
  `⟨p⟩` across `V_d`.

## Main results

* `HeckeRing.GL2.heckeSlashUpperTri_slash_scaleRep_comm`: the upper-triangular sum commutes with
  the slash by `scaleRep d = diag(d, 1)`, for any function fixed by the powers of `T` and any `d`
  coprime to `p`.
* `HeckeRing.GL2.heckeTCuspNat_levelRaise`: **`Tₚ (V_d f) = V_d (Tₚ f)`** for `p` prime and
  coprime to the raised level `N`.

## Provenance

The mathematics follows `heckeT_p_all_levelRaise_comm` and its supporting lemmas in the AINTLIB
[`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) project, file
`LeanModularForms/HeckeRIngs/GL2/Newforms/LevelRaiseComm.lean`, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck, lines 45–311.
No proof code is transcribed: that development works with bare coset functions `heckeT_p_ut` and
`heckeT_p_fun` and a `Γ₁`-shift matrix of its own, and splits `Tₚ` on whether `p` divides the
level, whereas here `Tₚ` is the single-formula operator of `HeckeSlash/Operators.lean`, the shift is
Mathlib's `ModularGroup.T`, and the level-raise is the general `TauCeti.CuspForm.levelRaise` of
`ModularForms/Degeneracy.lean`, stated at `d * M ∣ N` rather than at `d * M = N`.

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

/-- A `Γ₁(M)`-invariant function is fixed by the rational slash of any power of `T`. -/
private lemma slash_mapGL_T_zpow {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma1 M).map (mapGL ℝ), f ∣[k] γ = f) (q : ℤ) :
    f ∣[k] (mapGL ℚ (ModularGroup.T ^ q) : GL (Fin 2) ℚ) = f :=
  ModularForm.slash_eq_of_mem_map_mapGL hf (Subgroup.mem_map_of_mem _ (T_zpow_mem_Gamma1 M q))

/-! ### The upper-triangular representatives under `diag(d, 1)` -/

/-- **The commutation of `scaleRep d = diag(d, 1)` past an upper-triangular representative.**
Both sides are `!![d, d b; 0, p]`: on the right, `d b = q p + r` is split so that the
representative index `r` is again in range, at the cost of the shift `T ^ q`. -/
private lemma scaleRep_mul_upperTriRep (hd : 0 < d) (b : Fin p) {q r : ℕ} (hr : r < p)
    (hqr : d * (b : ℕ) = q * p + r) :
    scaleRep d * upperTriRep p b =
      mapGL ℚ (ModularGroup.T ^ (q : ℤ)) * (upperTriRep p ⟨r, hr⟩ * scaleRep d) := by
  have hmod : (d : ℚ) * ((b : ℕ) : ℚ) = (q : ℚ) * (p : ℚ) + (r : ℚ) := by exact_mod_cast hqr
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scaleRep d hd, coe_upperTriRep,
    coe_upperTriRep]
  ext i j
  -- three of the four entries close by `simp`; the bullet makes the surviving one explicit, so a
  -- change in the simp set fails here rather than silently redirecting `linarith`.
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linarith

/-! ### Reindexing by multiplication -/

/-- Multiplication by `d` modulo `p` permutes `Fin p` when `d` and `p` are coprime.  Injectivity
is `Nat.ModEq.cancel_left_of_coprime`: the two indices are already congruent mod `p`, and both
are below `p`. -/
private noncomputable def mulModEquiv (hp : 0 < p) (hdp : Nat.Coprime d p) : Fin p ≃ Fin p :=
  Equiv.ofBijective (fun b ↦ ⟨d * (b : ℕ) % p, Nat.mod_lt _ hp⟩)
    (Finite.injective_iff_bijective.mp fun b₁ b₂ hb ↦ Fin.ext (by
      have := Nat.ModEq.cancel_left_of_coprime hdp.symm (congrArg Fin.val hb)
      rwa [Nat.ModEq, Nat.mod_eq_of_lt b₁.isLt, Nat.mod_eq_of_lt b₂.isLt] at this))

/-- The index the permutation sends `b` to, as a natural number. -/
@[simp]
private lemma coe_mulModEquiv (hp : 0 < p) (hdp : Nat.Coprime d p) (b : Fin p) :
    (mulModEquiv hp hdp b : ℕ) = d * (b : ℕ) % p := (rfl)

/-! ### The upper-triangular sum against `diag(d, 1)` -/

/-- **The upper-triangular slash sum commutes with the slash by `scaleRep d = diag(d, 1)`**, for
`d` coprime to `p` and any function fixed by the rational slash of every power of `T`. This is
the level-raising half of `heckeTCuspNat_levelRaise`, stated before the normalising scalar of
`V_d` is introduced.

Invariance under the powers of `T` is all the reindexing consumes: no level enters the
statement, and a `Γ₁(M)`-invariant function meets the hypothesis via `slash_mapGL_T_zpow`. -/
theorem heckeSlashUpperTri_slash_scaleRep_comm (hd : 0 < d) (hp : 0 < p)
    (hdp : Nat.Coprime d p) {f : ℍ → ℂ}
    (hT : ∀ q : ℤ, f ∣[k] (mapGL ℚ (ModularGroup.T ^ q) : GL (Fin 2) ℚ) = f) :
    heckeSlashUpperTri k p (f ∣[k] (scaleRep d : GL (Fin 2) ℚ)) =
      heckeSlashUpperTri k p f ∣[k] (scaleRep d : GL (Fin 2) ℚ) := by
  rw [heckeSlashUpperTri_def, heckeSlashUpperTri_def, SlashAction.sum_slash]
  rw [← Equiv.sum_comp (mulModEquiv hp hdp) fun b ↦ (f ∣[k] upperTriRep p b) ∣[k]
    (scaleRep d : GL (Fin 2) ℚ)]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  -- the reindexed representative is `d b mod p`, by the defining lemma of `mulModEquiv`
  have hb : mulModEquiv hp hdp b = ⟨d * (b : ℕ) % p, Nat.mod_lt _ hp⟩ :=
    Fin.ext (coe_mulModEquiv hp hdp b)
  rw [← SlashAction.slash_mul,
    scaleRep_mul_upperTriRep hd b (Nat.mod_lt _ hp) (Nat.div_add_mod' (d * (b : ℕ)) p).symm,
    SlashAction.slash_mul, hT, SlashAction.slash_mul, hb]

/-! ### `Tₚ` and `V_d` -/

/-- **`Tₚ` commutes with the degeneracy operator `V_d`.** For `d * M ∣ N` and a prime `p` coprime
to `N`, raising the level of `f` and then applying `Tₚ` at level `N` agrees with applying `Tₚ` at
level `M` and then raising the level.

Coprimality is not decoration: at `p ∣ N` the diamond term of `Tₚ` vanishes at level `N` but need
not vanish at level `M`, and `b ↦ d b mod p` stops being a permutation once `p ∣ d`. -/
theorem heckeTCuspNat_levelRaise (hdvd : d * M ∣ N) (hp : p.Prime)
    (hpN : Nat.Coprime p N) (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero N := ⟨fun hN ↦ hp.ne_one (by simpa [hN] using hpN)⟩
    haveI : NeZero d := ⟨fun hd ↦ NeZero.ne N (by simpa [hd] using hdvd)⟩
    haveI : NeZero M := ⟨fun hM ↦ NeZero.ne N (by simpa [hM] using hdvd)⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeTCuspNat k p (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) f) =
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) (heckeTCuspNat k p f) := by
  have : NeZero N := ⟨fun hN ↦ hp.ne_one (by simpa [hN] using hpN)⟩
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
  have hscale : ∀ g : ℍ → ℂ, g ∣[k] scaleGL d = g ∣[k] (scaleRep d : GL (Fin 2) ℚ) :=
    fun g ↦ by rw [ModularForm.rat_slash, scaleRep_def, map_natDiagGL_d_one_eq_scaleGL]
  refine DFunLike.coe_injective ?_
  simp only [coe_heckeTCuspNat_prime k hp, CuspForm.coe_levelRaise,
    diamondOpCuspNat_of_coprime k hpN, diamondOpCuspNat_of_coprime k hpM,
    CuspForm.diamondOpCusp_levelRaise hdvd k (ZMod.unitOfCoprime p hpN) f, hunits,
    SlashAction.add_slash, smul_add, heckeSlashUpperTri_smul, hscale]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [heckeSlashUpperTri_slash_scaleRep_comm k hdpos hp.pos hpd.symm
      (slash_mapGL_T_zpow k hf)]
  · rw [ModularForm.rat_smul_slash_of_det_pos k (det_scaleRep_pos p), ← SlashAction.slash_mul,
      ← SlashAction.slash_mul, scaleRep_def, scaleRep_def, natDiagGL_comm]

end HeckeRing.GL2
