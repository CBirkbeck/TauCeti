/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Descent
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CuspForm
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelCommute
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelRaise.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelRaise.Commute
public import TauCeti.NumberTheory.ModularForms.Newforms.SquarefreeDecomposition

/-!
# The coefficient formula of the descent

For a prime `p ∣ N`, a squarefree `L` coprime to `p` whose primes divide `N`, and a cusp form
`f ∈ S_k(Γ₁(N), χ)` whose nebentypus is pulled back from level `N / p` and which vanishes at
every index coprime to `p L`, the descent `Φ = descendSlash k p N` satisfies

`a_m(Φ f) = (|family| / p) · a_m(g)`  for every `m` coprime to `L`,

where `g` is the coprime filter of `f` read at level `L N / p`. Rescaling by the nonzero
`|family| = descendMatrixCount p N` turns that into the **descent witness**: a cusp form
`F ∈ S_k(Γ₁(N / p), χ₀)` with `a_m(F) = a_{pm}(f)` at every `m` coprime to `L` — one prime
peeled off `f`, with its coefficients shifted by `p`. This is Miyake's Lemma 4.6.14, and the
inductive step of his Lemma 4.6.8.

The proof splits `f = Δ + V_p g` at level `L N`. The level-raise descends to
`(|family| / p) • g` (`Descent/LevelRaise/Commute.lean`), and the difference `Δ` vanishes at
every index coprime to `L`, so the squarefree decomposition writes it as `∑_{q ∈ l.primeFactors}
V_q F_q` (`SquarefreeDecomposition.lean`); the descent commutes with each `V_q` and kills it at
the indices coprime to `L`.

## Main results

* `TauCeti.qExpansion_coeff_descendSlash_eq_zero_of_coprime`: the descent of a form vanishing at
  the indices coprime to a squarefree `l` again vanishes there.
* `TauCeti.qExpansion_coeff_descendSlash_eq_of_coprime`: the coefficient formula above.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_coeff_mul_of_coprime`: the descent
  witness.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/InductiveStep.lean` —
`miyake_4_6_14_coeff_formula` with its `delta_vanishing_*` helpers, and the rescaling of
`HeckeDescent.lean`. The source keeps the descent as an explicit coset list and transports forms
across equalities of levels by casts; here the descent is `descendSlash`/`descendCuspForm`,
levels are related by divisibility, and the vanishing half is stated on its own so that the
squarefree decomposition enters once.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemmas 4.6.8 and 4.6.14.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.7.
-/
public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N p L : ℕ} {k : ℤ}

/-- **The difference `f − V_p g` vanishes at the indices coprime to `L`.** At `n = p m` both
have the coefficient `a_{pm}(f)`; at `p ∤ n` the index is coprime to `p L`, so `a_n(f) = 0`,
and `V_p g` is supported on the multiples of `p`. -/
private theorem qExpansion_coeff_ofLe_sub_levelRaise_eq_zero (hp : p.Prime) (hpN : p ∣ N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0)
    {g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k}
    (hg : ∀ m, (qExpansion 1 g).coeff m =
      if Nat.Coprime m L then (qExpansion 1 f).coeff (p * m) else 0)
    (n : ℕ) (hn : Nat.Coprime n L) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (qExpansion 1 ⇑(_root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left N L)) f -
      CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd
        (dvd_of_eq (Nat.mul_div_cancel' (dvd_mul_of_dvd_right hpN L)))) g)).coeff n = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _),
    map_sub, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
      (one_mem_strictPeriods_Gamma1_map _), _root_.CuspForm.coe_ofLe]
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    rw [ite_eq_left (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.pos, hg,
      ite_eq_left (Nat.coprime_mul_iff_left.mp hn).2, sub_self]
  · simp only [hpn, ↓reduceIte, sub_zero]
    exact hvan n (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hpn).symm hn)

/-- **The difference `f − V_p g` has the nebentypus of `f`, read at level `L N`.** -/
private theorem ofLe_sub_levelRaise_mem_cuspFormCharSpace (hp : p.Prime) (hpN : p ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    {g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k}
    (hg : g ∈ cuspFormCharSpace k
      (χ₀.comp (ZMod.unitsMap (Nat.mul_div_assoc L hpN ▸ dvd_mul_left (N / p) L)))) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left N L)) f -
      CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd
        (dvd_of_eq (Nat.mul_div_cancel' (dvd_mul_of_dvd_right hpN L)))) g ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_mul_left N L))) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine Submodule.sub_mem _ (CuspForm.ofLe_mem_cuspFormCharSpace χ (dvd_mul_left N L) hf) ?_
  have h := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd
    (dvd_of_eq (Nat.mul_div_cancel' (dvd_mul_of_dvd_right hpN L))) _ hg
  rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp] at h
  rwa [hcomp, MonoidHom.comp_assoc, ZMod.unitsMap_comp]

/-! ### The descent of the difference vanishes at the indices coprime to `L` -/

section Core

variable {M : ℕ}

/-- **The `m`-th coefficient of `f + g`**, for cusp forms of level `Γ₁(M)`: the `q`-expansion is
additive where the cusp functions are analytic at `0`, which a bundled form supplies. -/
private theorem qExpansion_coeff_add (f g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 ⇑(f + g)).coeff m =
      (qExpansion 1 ⇑f).coeff m + (qExpansion 1 ⇑g).coeff m := by
  rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map _),
    map_add]

/-- **The `m`-th coefficient of `c • f`**, for a cusp form of level `Γ₁(M)`. -/
private theorem qExpansion_coeff_smul (c : ℂ) (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (m : ℕ) :
    (qExpansion 1 ⇑(c • f)).coeff m = c * (qExpansion 1 ⇑f).coeff m := by
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map _),
    map_smul, smul_eq_mul]

/-- The function underlying a finite sum of cusp forms is the sum of the functions.

This is `map_sum` for `FunLike.coeAddMonoidHom`, restated with the coercion written as `⇑`: that
is the form the goals below are in, and `rw` matches syntactically. -/
private theorem coe_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ⇑(∑ i ∈ s, F i : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) = ∑ i ∈ s, ⇑(F i) :=
  map_sum (FunLike.coeAddMonoidHom (CuspForm ((Gamma1 M).map (mapGL ℝ)) k) ℍ ℂ) F s

/-- The `m`-th coefficient of a finite sum of cusp forms of level `Γ₁(M)`.

Not an instance of `map_sum` for `ModularForm.qExpansionAddHom`: that hom is stated for the
bundled type `ModularForm Γ k`, while the summands here are cusp forms read as functions on `ℍ`,
for which the additivity of `qExpansion` is the class-polymorphic `ModularForm.qExpansion_add`
used at each step below. -/
private theorem qExpansion_coeff_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 ⇑(∑ i ∈ s, F i : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)).coeff m =
      ∑ i ∈ s, (qExpansion 1 (F i)).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, FunLike.coe_zero, qExpansion_zero, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, qExpansion_coeff_add, ih]

/-- **A character over a lowered character is lowered.** If `χ'` modulo `N'` and `χ₀ ∘ π` modulo
`M` have the same pull-back to a common multiple `M'`, where `χ₀` has level `M / p` and
`M ∣ N'`, then `χ'` is the pull-back of `χ₀ ∘ π` modulo `N' / p`: the pull-back to `M'` is
injective on characters, by the surjectivity of `ZMod.unitsMap`. -/
private theorem eq_comp_unitsMap_of_comp_unitsMap_eq {M' N' : ℕ} [NeZero M'] (hpM : p ∣ M)
    (hpN' : p ∣ N') (hMpN'p : M / p ∣ N' / p) (hMN' : M ∣ N') (hN'M' : N' ∣ M')
    {χM : (ZMod M)ˣ →* ℂˣ} {χ₀ : (ZMod (M / p))ˣ →* ℂˣ}
    (hcomp : χM = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) {χ' : (ZMod N')ˣ →* ℂˣ}
    (h : χ'.comp (ZMod.unitsMap hN'M') = χM.comp (ZMod.unitsMap (hMN'.trans hN'M'))) :
    χ' = (χ₀.comp (ZMod.unitsMap hMpN'p)).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN')) := by
  rw [hcomp, MonoidHom.comp_assoc, ZMod.unitsMap_comp] at h
  refine MonoidHom.ext fun u ↦ ?_
  obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hN'M' u
  have hv := congrArg (fun ψ ↦ ψ v) h
  simp only [MonoidHom.comp_apply] at hv ⊢
  rw [hv, ← MonoidHom.comp_apply (ZMod.unitsMap _) (ZMod.unitsMap _), ZMod.unitsMap_comp,
    ← MonoidHom.comp_apply (ZMod.unitsMap _) (ZMod.unitsMap _), ZMod.unitsMap_comp]

/-- **A peeled summand descends to a level-raise of a bundled descent.** For `F` of level
`Γ₁(M l² / q)` with a nebentypus lying over the lowered one, the descent at level `M l²` of the
function `V_q F` is `V_q` of the descent of `F`, bundled at level `Γ₁(M l² / p)`:
`descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_cuspFormCharSpace`, read through
`descendCuspForm`. -/
private theorem descendSlash_smul_slash_scaleGL_eq_coe_levelRaise (hp : p.Prime) {l q : ℕ}
    (hpM : p ∣ M) (hq : q.Prime) (hql : q ∣ l) (hpl : Nat.Coprime p l)
    [NeZero (M * l ^ 2 / q)] (hpN' : p ∣ M * l ^ 2 / q) (hMN' : M ∣ M * l ^ 2 / q)
    (hle : q * (M * l ^ 2 / q / p) ∣ M * l ^ 2 / p)
    {χM : (ZMod M)ˣ →* ℂˣ} {χ₀ : (ZMod (M / p))ˣ →* ℂˣ}
    (hcomp : χM = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))
    {χ' : (ZMod (M * l ^ 2 / q))ˣ →* ℂˣ}
    (hχ' : χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right (hql.trans (dvd_pow_self l two_ne_zero)) M))) =
      χM.comp (ZMod.unitsMap (Nat.dvd_mul_right M (l ^ 2))))
    {F : CuspForm ((Gamma1 (M * l ^ 2 / q)).map (mapGL ℝ)) k} (hF : F ∈ cuspFormCharSpace k χ') :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ∃ hcomp' : χ' = (χ₀.comp (ZMod.unitsMap ((Nat.div_dvd_div_iff_right hpM hpN').mpr
        hMN'))).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN')),
      descendSlash k p (M * l ^ 2) ((q : ℂ) ^ (1 - k) • (⇑F ∣[k] scaleGL q)) =
        ⇑(CuspForm.levelRaise q (Gamma1_map_le_conjAct_scaleGL_of_dvd hle)
          (descendCuspForm k hp hpN' hcomp' hF)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have hqMl : q ∣ M * l ^ 2 := dvd_mul_of_dvd_right (hql.trans (dvd_pow_self l two_ne_zero)) M
  have : NeZero (M * l ^ 2) := ⟨fun h ↦ NeZero.ne (M * l ^ 2 / q) (by rw [h, Nat.zero_div])⟩
  have hcomp' := eq_comp_unitsMap_of_comp_unitsMap_eq hpM hpN'
    ((Nat.div_dvd_div_iff_right hpM hpN').mpr hMN') hMN' (Nat.div_dvd_of_dvd hqMl) hcomp hχ'
  refine ⟨hcomp', ?_⟩
  have h := descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_cuspFormCharSpace k hp hpN'
    (hpl.coprime_dvd_right hql) hcomp' hF
  rw [CuspForm.coe_levelRaise, Nat.mul_div_cancel' hqMl] at h
  rw [h, CuspForm.coe_levelRaise, coe_descendCuspForm]

/-- The `n`-th coefficient of the sum of the level-raised peeled pieces: `a_{n/q}(F_q)` summed
over the primes `q ∣ l` dividing `n`. -/
private theorem qExpansion_coeff_sum_levelRaise {l : ℕ}
    (F : ∀ q ∈ l.primeFactors, CuspForm ((Gamma1 (M * l ^ 2 / q)).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 ⇑(∑ q ∈ l.primeFactors.attach,
        haveI : NeZero q.1 := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩
        CuspForm.levelRaise q.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd (dvd_of_eq
          (Nat.mul_div_cancel' (dvd_mul_of_dvd_right
            ((Nat.dvd_of_mem_primeFactors q.2).trans (dvd_pow_self l two_ne_zero)) M))))
          (F q.1 q.2) : CuspForm ((Gamma1 (M * l ^ 2)).map (mapGL ℝ)) k)).coeff n =
      ∑ q ∈ l.primeFactors.attach,
        if q.1 ∣ n then (qExpansion 1 (F q.1 q.2)).coeff (n / q.1) else 0 := by
  rw [qExpansion_coeff_finset_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have : NeZero q.1 := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩
  exact CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
    (one_mem_strictPeriods_Gamma1_map _) _ _ n

/-- **The squarefree decomposition, as an identity of functions.** For `Δ ∈ S_k(Γ₁(M), χ)` with
`a_n(Δ) = 0` at the indices coprime to a squarefree `l`, the peeled pieces `F_q` of level
`M l² / q` (Lemma 4.6.7) satisfy `Δ = ∑_{q ∣ l} V_q F_q` as functions on `ℍ`: both sides are
cusp forms of level `Γ₁(M l²)` with the same `q`-expansion. -/
private theorem exists_coe_eq_sum_coe_levelRaise_of_squarefree [NeZero M] {l : ℕ}
    (hsq : Squarefree l) {χ : (ZMod M)ˣ →* ℂˣ} {Δ : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hΔ : Δ ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n l → (qExpansion 1 Δ).coeff n = 0) :
    ∃ (F : ∀ q ∈ l.primeFactors, CuspForm ((Gamma1 (M * l ^ 2 / q)).map (mapGL ℝ)) k)
      (χ' : ∀ q ∈ l.primeFactors, (ZMod (M * l ^ 2 / q))ˣ →* ℂˣ),
      (∀ q (hq : q ∈ l.primeFactors), F q hq ∈ cuspFormCharSpace k (χ' q hq)) ∧
      (∀ q (hq : q ∈ l.primeFactors),
        (χ' q hq).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right
          ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero)) M))) =
          χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (l ^ 2)))) ∧
      ⇑Δ = ∑ q ∈ l.primeFactors.attach,
        haveI : NeZero q.1 := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩
        ⇑(CuspForm.levelRaise q.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd (dvd_of_eq
          (Nat.mul_div_cancel' (dvd_mul_of_dvd_right
            ((Nat.dvd_of_mem_primeFactors q.2).trans (dvd_pow_self l two_ne_zero)) M))))
          (F q.1 q.2)) := by
  obtain ⟨F, χ', hF, hχ', hcoeff⟩ :=
    exists_qExpansion_coeff_eq_sum_primeFactors_of_squarefree χ hΔ hsq hvan
  refine ⟨F, χ', hF, hχ', ?_⟩
  have hM : M ∣ M * l ^ 2 := Nat.dvd_mul_right M _
  -- the difference of the two sides, as a cusp form of level `Γ₁(M l²)`
  set D : CuspForm ((Gamma1 (M * l ^ 2)).map (mapGL ℝ)) k :=
    _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd hM) Δ -
      ∑ q ∈ l.primeFactors.attach,
        haveI : NeZero q.1 := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩
        CuspForm.levelRaise q.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd (dvd_of_eq
          (Nat.mul_div_cancel' (dvd_mul_of_dvd_right
            ((Nat.dvd_of_mem_primeFactors q.2).trans (dvd_pow_self l two_ne_zero)) M))))
          (F q.1 q.2) with hDdef
  -- its `q`-expansion vanishes: the coefficient identity of the decomposition
  have hD : qExpansion 1 D = 0 := by
    ext n
    rw [hDdef, FunLike.coe_sub,
      ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub,
      _root_.CuspForm.coe_ofLe, qExpansion_coeff_sum_levelRaise, hcoeff n, map_zero, sub_self]
  -- so the difference is zero
  have : Fact (IsCusp OnePoint.infty ((Gamma1 (M * l ^ 2)).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma1_map _)⟩
  have hfun : ⇑D = 0 := (qExpansion_eq_zero_iff one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex D (one_mem_strictPeriods_Gamma1_map _))
    (ModularFormClass.holo D) (ModularFormClass.bdd_at_infty D)).mp hD
  rw [hDdef, FunLike.coe_sub, _root_.CuspForm.coe_ofLe, coe_finset_sum] at hfun
  exact sub_eq_zero.mp hfun

/-- The descent slash sum of a finite sum of functions is the sum of the descents. -/
private theorem descendSlash_finset_sum [NeZero p] {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) :
    descendSlash k p M (∑ i ∈ s, f i) = ∑ i ∈ s, descendSlash k p M (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, descendSlash_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, descendSlash_add, ih]

/-- **Each peeled piece descends to a form supported on the multiples of its prime.** The
descent at level `M l²` of the level-raise `V_q F_q` is `V_q` of the bundled descent of `F_q`
(`descendSlash_smul_slash_scaleGL_eq_coe_levelRaise`), whose `m`-th coefficient vanishes when
`q ∤ m`. -/
private theorem exists_descendSlash_coe_levelRaise_eq_coe_and_coeff_eq_zero [NeZero M]
    (hp : p.Prime) (hpM : p ∣ M) {l : ℕ} (hl : l ≠ 0) (hpl : Nat.Coprime p l)
    {χ : (ZMod M)ˣ →* ℂˣ} {χ₀ : (ZMod (M / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))
    {F : ∀ q ∈ l.primeFactors, CuspForm ((Gamma1 (M * l ^ 2 / q)).map (mapGL ℝ)) k}
    {χ' : ∀ q ∈ l.primeFactors, (ZMod (M * l ^ 2 / q))ˣ →* ℂˣ}
    (hF : ∀ q (hq : q ∈ l.primeFactors), F q hq ∈ cuspFormCharSpace k (χ' q hq))
    (hχ' : ∀ q (hq : q ∈ l.primeFactors),
      (χ' q hq).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right
        ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero)) M))) =
        χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (l ^ 2))))
    {m : ℕ} (hm : Nat.Coprime m l) (q : {x // x ∈ l.primeFactors}) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero q.1 := ⟨(Nat.prime_of_mem_primeFactors q.2).ne_zero⟩
    ∃ W : CuspForm ((Gamma1 (M * l ^ 2 / p)).map (mapGL ℝ)) k,
      descendSlash k p (M * l ^ 2) ⇑(CuspForm.levelRaise q.1
        (Gamma1_map_le_conjAct_scaleGL_of_dvd (dvd_of_eq (Nat.mul_div_cancel'
          (dvd_mul_of_dvd_right
            ((Nat.dvd_of_mem_primeFactors q.2).trans (dvd_pow_self l two_ne_zero)) M))))
        (F q.1 q.2)) = ⇑W ∧ (qExpansion 1 W).coeff m = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hq : q.1.Prime := Nat.prime_of_mem_primeFactors q.2
  have : NeZero q.1 := ⟨hq.ne_zero⟩
  have hql : q.1 ∣ l := Nat.dvd_of_mem_primeFactors q.2
  have hq2 : q.1 ∣ l ^ 2 := hql.trans (dvd_pow_self l two_ne_zero)
  have hqMl : q.1 ∣ M * l ^ 2 := dvd_mul_of_dvd_right hq2 M
  have hMN' : M ∣ M * l ^ 2 / q.1 := Dvd.intro _ (Nat.mul_div_assoc M hq2).symm
  have hpN' : p ∣ M * l ^ 2 / q.1 := hpM.trans hMN'
  have : NeZero (M * l ^ 2 / q.1) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero
      (Nat.mul_ne_zero (NeZero.ne M) (pow_ne_zero 2 hl))) hqMl) hq.pos).ne'⟩
  have hle : q.1 * (M * l ^ 2 / q.1 / p) ∣ M * l ^ 2 / p :=
    dvd_of_eq (by rw [← Nat.mul_div_assoc q.1 hpN', Nat.mul_div_cancel' hqMl])
  obtain ⟨hcomp', hW⟩ := descendSlash_smul_slash_scaleGL_eq_coe_levelRaise hp hpM hq hql hpl
    hpN' hMN' hle hcomp (hχ' q.1 q.2) (hF q.1 q.2)
  refine ⟨_, by rw [CuspForm.coe_levelRaise]; exact hW, ?_⟩
  rw [CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
    (one_mem_strictPeriods_Gamma1_map _)]
  have hqm : ¬ q.1 ∣ m := fun h ↦
    hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (hm.coprime_dvd_right hql).symm h)
  simp only [hqm, ↓reduceIte]

/-- **The descent of a form vanishing off `l` vanishes at the indices coprime to `l`** (the core
of Miyake's Lemma 4.6.14). For `Δ ∈ S_k(Γ₁(M), χ)` with `χ` pulled back from `χ₀` modulo `M / p`,
vanishing at every index coprime to a squarefree `l` coprime to `p`, the descent
`descendSlash k p M Δ` has `a_m = 0` at every `m` coprime to `l`: `Δ = ∑_{q ∣ l} V_q F_q`, the
descent commutes with each `V_q`, and each `V_q` of a bundled descent is supported on the
multiples of `q`. -/
theorem qExpansion_coeff_descendSlash_eq_zero_of_coprime [NeZero M] (hp : p.Prime) (hpM : p ∣ M)
    {l : ℕ} (hsq : Squarefree l) (hpl : Nat.Coprime p l) {χ : (ZMod M)ˣ →* ℂˣ}
    {χ₀ : (ZMod (M / p))ˣ →* ℂˣ} (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))
    {Δ : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hΔ : Δ ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n l → (qExpansion 1 Δ).coeff n = 0) (m : ℕ) (hm : Nat.Coprime m l) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (qExpansion 1 (descendSlash k p M ⇑Δ)).coeff m = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F, χ', hF, hχ', hΔsum⟩ := exists_coe_eq_sum_coe_levelRaise_of_squarefree hsq hΔ hvan
  -- the descent at level `M` is the descent at level `M l²`
  have h08a := descendSlash_mul_left_of_coprime k hp hpM (hpl.pow_right 2) (f := ⇑Δ)
    fun ε hε ↦ SlashInvariantFormClass.slash_action_eq Δ _ (Subgroup.mem_map_of_mem _ hε)
  rw [Nat.mul_comm] at h08a
  rw [← h08a, hΔsum, descendSlash_finset_sum]
  -- each summand descends to `V_q` of a bundled descent, supported on the multiples of `q`
  have hterm := exists_descendSlash_coe_levelRaise_eq_coe_and_coeff_eq_zero hp hpM hsq.ne_zero
    hpl hcomp hF hχ' hm
  choose W hW hW0 using hterm
  rw [Finset.sum_congr rfl fun q _ ↦ hW q, ← coe_finset_sum, qExpansion_coeff_finset_sum]
  exact Finset.sum_eq_zero fun q _ ↦ hW0 q

end Core

/-! ### The coefficient formula of the descent -/

/-- The nebentypus of `f` read at level `L N` is the pull-back of `χ₀` read at level `L N / p`. -/
private theorem comp_unitsMap_eq_comp_unitsMap_of_comp {L : ℕ} (hpN : p ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    χ.comp (ZMod.unitsMap (dvd_mul_left N L)) =
      (χ₀.comp (ZMod.unitsMap (Nat.mul_div_assoc L hpN ▸ dvd_mul_left (N / p) L))).comp
        (ZMod.unitsMap (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right hpN L))) := by
  rw [hcomp, MonoidHom.comp_assoc, ZMod.unitsMap_comp, MonoidHom.comp_assoc, ZMod.unitsMap_comp]


/-- **The coefficients of the descent** (Miyake, Lemma 4.6.14). Let `f ∈ S_k(Γ₁(N), χ)` with `χ`
pulled back from `χ₀` modulo `N / p`, vanishing at every index coprime to `p L` for a squarefree
`L` coprime to `p`, and let `g` of level `L N / p` carry the coefficients of `f` along the
multiples of `p`: `a_m(g) = a_{pm}(f)` for `m` coprime to `L`, and `a_m(g) = 0` otherwise. Then
at every `m` coprime to `L`, `a_m(descendSlash k p N f) = (|family| / p) · a_m(g)`. -/
theorem qExpansion_coeff_descendSlash_eq_of_coprime [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    {L : ℕ} (hL : Squarefree L) (hpL : Nat.Coprime p L) {χ : (ZMod N)ˣ →* ℂˣ}
    {χ₀ : (ZMod (N / p))ˣ →* ℂˣ} (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0)
    {g : CuspForm ((Gamma1 (L * N / p)).map (mapGL ℝ)) k}
    (hg : g ∈ cuspFormCharSpace k
      (χ₀.comp (ZMod.unitsMap (Nat.mul_div_assoc L hpN ▸ dvd_mul_left (N / p) L))))
    (hgcoeff : ∀ m, (qExpansion 1 g).coeff m =
      if Nat.Coprime m L then (qExpansion 1 f).coeff (p * m) else 0)
    (m : ℕ) (hm : Nat.Coprime m L) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (qExpansion 1 (descendSlash k p N ⇑f)).coeff m =
      (descendMatrixCount p N : ℂ) / p * (qExpansion 1 g).coeff m := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (L * N) := ⟨Nat.mul_ne_zero hL.ne_zero (NeZero.ne N)⟩
  have hpM : p ∣ L * N := dvd_mul_of_dvd_right hpN L
  -- the descent at level `N` is the descent at level `L N`
  have h08a := descendSlash_mul_left_of_coprime k hp hpN hpL (f := ⇑f)
    fun ε hε ↦ SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hε)
  -- `f = Δ + V_p g` at level `L N`
  set Vg := CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd
    (dvd_of_eq (Nat.mul_div_cancel' hpM))) g with hVg
  set Δ := _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left N L)) f - Vg
    with hΔ
  have hfΔ : ⇑f = ⇑Δ + ⇑Vg := by
    rw [hΔ, FunLike.coe_sub, _root_.CuspForm.coe_ofLe, sub_add_cancel]
  -- the level-raise descends to a multiple of `g`
  have hVg' : descendSlash k p (L * N) ⇑Vg = ((descendMatrixCount p N : ℂ) / p) • ⇑g := by
    rw [hVg, CuspForm.coe_levelRaise, descendSlash_smul_slash_scaleGL k hp hpM g,
      descendMatrixCount_mul_left_of_coprime hpL N]
  -- the difference descends to a form vanishing at `m`
  have hχM := comp_unitsMap_eq_comp_unitsMap_of_comp hpN (L := L) hcomp
  have hΔχ : Δ ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (dvd_mul_left N L))) :=
    ofLe_sub_levelRaise_mem_cuspFormCharSpace hp hpN hcomp hf hg
  have hD0 : (qExpansion 1 (descendSlash k p (L * N) ⇑Δ)).coeff m = 0 :=
    qExpansion_coeff_descendSlash_eq_zero_of_coprime hp hpM hL hpL hχM hΔχ
      (qExpansion_coeff_ofLe_sub_levelRaise_eq_zero hp hpN hvan hgcoeff) m hm
  -- add the two `q`-expansions through the bundled descent
  rw [← h08a, hfΔ, descendSlash_add, hVg', ← coe_descendCuspForm k hp hpM hχM hΔχ,
    ← FunLike.coe_smul, ← FunLike.coe_add, qExpansion_coeff_add, coe_descendCuspForm, hD0,
    zero_add, qExpansion_coeff_smul]


/-! ### The descent witness -/

/-- **The descent witness** (Miyake, Lemma 4.6.8, the inductive step). For `f ∈ S_k(Γ₁(N), χ)`
with `χ` pulled back from `χ₀` modulo `N / p`, vanishing at every index coprime to `p L` for a
squarefree `L` coprime to `p` whose primes divide `N`, there is `F ∈ S_k(Γ₁(N / p), χ₀)` with
`a_m(F) = a_{pm}(f)` at every `m` coprime to `L`: the descent of `f`, rescaled by
`p / |family|`, by the coefficient formula of the descent and the coprime-filter descent. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_coeff_mul_of_coprime [NeZero N]
    (hp : p.Prime) (hpN : p ∣ N) {L : ℕ} (hL : Squarefree L) (hLN : L.primeFactors ⊆ N.primeFactors)
    (hpL : Nat.Coprime p L) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hvan : ∀ n, Nat.Coprime n (p * L) → (qExpansion 1 f).coeff n = 0) :
    ∃ F : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k, F ∈ cuspFormCharSpace k χ₀ ∧
      ∀ m, Nat.Coprime m L → (qExpansion 1 F).coeff m = (qExpansion 1 f).coeff (p * m) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g, hg, hgcoeff⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_coeff_mul χ hf hp hpN hcomp hL hLN
      hpL hvan
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hcount : (descendMatrixCount p N : ℂ) ≠ 0 := by
    by_cases h : p ^ 2 ∣ N
    · rw [descendMatrixCount_of_sq_dvd h]
      exact hp0
    · rw [descendMatrixCount_of_not_sq_dvd h]
      exact_mod_cast p.succ_ne_zero
  refine ⟨((p : ℂ) / descendMatrixCount p N) • descendCuspForm k hp hpN hcomp hf,
    Submodule.smul_mem _ _ (descendCuspForm_mem_cuspFormCharSpace k hp hpN hcomp hf),
    fun m hm ↦ ?_⟩
  rw [qExpansion_coeff_smul, coe_descendCuspForm,
    qExpansion_coeff_descendSlash_eq_of_coprime hp hpN hL hpL hcomp hf hvan hg hgcoeff m hm,
    hgcoeff m, ite_eq_left hm]
  field_simp


end TauCeti
