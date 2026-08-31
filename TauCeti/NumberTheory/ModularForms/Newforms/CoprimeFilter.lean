/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Nat.Squarefree
public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported

/-!
# Coprime-index filters on `S_k(Γ₁(N), χ)`

Miyake's Lemma 4.6.5: a cusp form `f ∈ S_k(Γ₁(N), χ)` can be *filtered* at a divisor of the
level. For a nonzero `L` all of whose primes already divide `N`, there is a cusp form `g` at a
raised level, again with nebentypus `χ` read there, whose `q`-expansion keeps exactly the
coefficients at indices coprime to `L`:

`aₙ(g) = aₙ(f)` when `(n, L) = 1`, and `aₙ(g) = 0` otherwise.

Only the *primes* of `L` do any filtering, so the level `g` lives at is `∏ L.primeFactors`
times `N`. For squarefree `L` that product is `L` itself, which is the level `L * N` at which
Miyake states the lemma.

Subtracting that filter from `f` leaves the complementary *`h`-form*, which keeps exactly the
coefficients at indices **not** coprime to `L`. It is obtained at the single level `N * L ^ 2`,
which is what the filter costs when the primes of `L` are not assumed to divide `N`: a prime
already dividing `N` is paid for out of `L`, while one that does not needs a second factor to
climb to and back down from, so `L` enters squared.

## Main results

* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`: the filter, for an
  arbitrary nonzero `L`, at level `∏ L.primeFactors * N`.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_squarefree`:
  Miyake's Lemma 4.6.5 as stated, at level `L * N`.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero`: the `h`-form,
  the complementary filter for a squarefree `L`, at level `N * L ^ 2`.

## Implementation notes

The construction is one prime at a time. At a single `p` the witness is `f - V_p (T_p f)`, read
at level `p * N`; the `q`-expansion identities `TauCeti.CuspForm.qExpansion_levelRaise_coeff_Gamma1`
and `HeckeRing.GL2.qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset` make the two
contributions cancel at exactly the indices divisible by `p`. Neither of those needs `p` to be
prime, only that its prime factors already divide the level, so the single-`p` step is stated
at that generality; primality is used only to compose the filters, where
`Nat.Coprime n (q * m)` has to split as `¬ q ∣ n` and `Nat.Coprime n m`.

Iterating over `L.primeFactors` raises the level by one prime per step, so the induction is on
the number of primes left to peel and the level it lands at is existentially quantified, with
the equation `M' = ∏ S * M` recorded alongside. That keeps the recursion free of any transport
along an equality of levels: the caller substitutes the equation once, at a concrete level.

The `h`-form needs the same peeling but at a level *fixed in advance*, since its answer is
required at `N * L ^ 2`. `TauCeti.HasFilterRoom` is what makes that possible: it records, per
prime, the room the target level must already contain for that prime's step, and the two
`HasFilterRoom` transport lemmas carry it along each level raise. The same discipline on
transport applies. A prime `q` outside `N` is reached by restricting to `q * N` and filtering
there, so the step lands at `q * (q * N)`; that is `N * q ^ 2`, but only up to an equation of
naturals, and the level is deliberately left in the shape the construction produced. The
equation is used only inside proofs of divisibility, never to move a cusp form between levels.

## Provenance

Adapted from AINTLIB's `StrongMultiplicityOne/LevelChangeCharSpace.lean` (see References): the
declarations `miyake_4_6_5_single_prime_dvd_N` and `miyake_4_6_5_iterated_L` with their two
`q`-expansion and `ite`-composition helpers. Deliberate differences from the source: the
source's `hp : p.Prime` is dropped from the single-`p` step and from the `q`-expansion
cancellation, neither proof using it; the `Squarefree (∏ S)` hypothesis the source threads
through the recursion only to feed itself disappears once the conclusion is stated at the level
`∏ S * M`; and the nonzero-`L` statement is exposed here, the source stating only the
squarefree form at this stage (its `_general` variant generalizes the target level, not `L`).

`coprime_prod_primeFactors_iff` is AINTLIB's `coprime_prod_primeFactors_iff_coprime`, which
lives one file up in `StrongMultiplicityOne.lean`. It is restated here for an arbitrary nonzero
`L` rather than for the ambient level, and proved from `Nat.dvd_prod_primeFactors_pow_self`
instead of by contradiction on a common prime divisor.

The `h`-form and its prescribed-level recursion are adapted from the same source file: the
declarations `miyake_4_6_5_single_prime_coprime_to_N`, `miyake_4_6_5_iterated_helper_general`,
`miyake_4_6_5_iterated_L_general` and `miyake_h_form_general`, together with the two
`dvd_conditions_*` arithmetic lemmas, restated here as `TauCeti.HasFilterRoom.mul_left_of_dvd`
and `TauCeti.HasFilterRoom.mul_right_sq_of_not_dvd`. Deliberate differences from the source:
the repeated divisibility side condition is named as `TauCeti.HasFilterRoom` rather than spelled
out in six signatures; the source's `finish_peel_step`, `peel_step_of_dvd_N` and
`peel_step_of_not_dvd_N` each take the whole induction hypothesis as an explicit argument, and
are replaced here by two hypothesis-free lemmas —
`TauCeti.exists_intermediate_of_filter_step`, which absorbs the case split on `q ∣ N` and
reports only the intermediate level it reached, and
`TauCeti.mem_and_qExpansion_coeff_eq_of_filter_comp`, stated over the *result* of the recursive
call — leaving the induction itself with no case split; the source's `hp : p.Prime` is again
dropped from the single-`p` step, which needs only that `p` be nonzero; the source casts the
level along `p * (p * N) = N * p ^ 2` with `Eq.ndrec`, whereas here the step is stated at
`q * (q * N)` and the equation is used only on divisibility statements; and the final
`q`-expansion computation uses `ModularForm.qExpansion_sub` directly in place of the source's
`sub_eq_add_neg` rewriting through `qExpansion_add` and `qExpansion_neg`.

## References

* [Miyake, *Modular forms*][miyake1989], Lemma 4.6.5.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, files
  `projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/LevelChangeCharSpace.lean`
  and `projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne.lean`.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

open HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The `q`-expansion of `f - V_p (T_p f)`.** Read at level `p * N`, the level-raise of
`T_p f` reproduces exactly the coefficients of `f` at the indices divisible by `p`, so the
difference is `f` with those indices deleted. Primality of `p` is not needed: what makes
`T_p` act by `aₘ(T_p f) = a_{p m}(f)` is that `p`'s prime factors already divide `N`. -/
private theorem qExpansion_coeff_ofLe_sub_levelRaise_heckeTCuspNat {p : ℕ} [NeZero p]
    (hpN : p.primeFactors ⊆ N.primeFactors) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N p)) f -
          CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL N p)
            (heckeTCuspNat (N := N) k p f))).coeff n =
      if p ∣ n then 0 else (qExpansion 1 f).coeff n := by
  rw [_root_.ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub,
    CuspForm.qExpansion_levelRaise_coeff_Gamma1 N _ n,
    qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset k p hpN f (n / p),
    CuspForm.coe_ofLe]
  by_cases hpn : p ∣ n <;> simp [hpn, Nat.mul_div_cancel']

/-- **Composing a coprimality filter with a prime one.** Deleting the indices divisible by a
prime `q` from the indices coprime to `m` leaves exactly the indices coprime to `q * m`. -/
private theorem ite_coprime_ite_dvd_eq_ite_coprime_mul {α : Type*} [Zero α] {q : ℕ}
    (hq : q.Prime) (n m : ℕ) (a : α) :
    (if Nat.Coprime n m then (if q ∣ n then 0 else a) else 0) =
      if Nat.Coprime n (q * m) then a else 0 := by
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_comm, hq.coprime_iff_not_dvd, ite_and]
  split_ifs <;> rfl

/-- **Coprimality only sees the primes.** For nonzero `L`, an `n` is coprime to `L` exactly
when it is coprime to the product of `L`'s prime factors. -/
private theorem coprime_prod_primeFactors_iff {n L : ℕ} (hL : L ≠ 0) :
    Nat.Coprime n (L.primeFactors.prod id) ↔ Nat.Coprime n L :=
  ⟨fun h ↦ (h.pow_right L).coprime_dvd_right (Nat.dvd_prod_primeFactors_pow_self hL),
    fun h ↦ h.coprime_dvd_right (Nat.prod_primeFactors_dvd L)⟩

/-- **The filter at a single level-supported `p`.** From `f ∈ S_k(Γ₁(N), χ)` and a nonzero `p`
whose prime factors all divide `N`, the form `f - V_p (T_p f)` lies in `S_k(Γ₁(p * N), χ)` and
carries the coefficients of `f` at the indices *not* divisible by `p`, the rest deleted. `p`
need be neither prime nor a prime power; only its prime support is constrained. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {p : ℕ} [NeZero p]
    (hpN : p.primeFactors ⊆ N.primeFactors) :
    ∃ g : CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N p))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if p ∣ n then 0 else (qExpansion 1 f).coeff n :=
  ⟨CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N p)) f -
      CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL N p) (heckeTCuspNat (N := N) k p f),
    Submodule.sub_mem _ (CuspForm.ofLe_mem_cuspFormCharSpace χ _ hf)
      (CuspForm.levelRaise_mem_cuspFormCharSpace N p χ
        (heckeTCuspNat_mem_cuspFormCharSpace_of_primeFactors_subset k χ p hpN hf)),
    qExpansion_coeff_ofLe_sub_levelRaise_heckeTCuspNat hpN f⟩

/-- The iterated filter, by induction on the number of primes still to be peeled off. The level
it lands at is existentially quantified together with the equation naming it, so that no step of
the recursion has to transport a cusp form along an equality of levels. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_prod (m : ℕ) :
    ∀ {M : ℕ} [NeZero M] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
      {g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}, g ∈ cuspFormCharSpace k χ →
      ∀ S : Finset ℕ, S ⊆ M.primeFactors → S.card = m → ∃ (M' : ℕ) (hMM' : M ∣ M'),
        M' = S.prod id * M ∧ ∃ g' : CuspForm ((Gamma1 M').map (mapGL ℝ)) k,
          g' ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hMM')) ∧
          ∀ n, (qExpansion 1 g').coeff n =
            if Nat.Coprime n (S.prod id) then (qExpansion 1 g).coeff n else 0 := by
  induction m with
  | zero =>
    intro M _ k χ g hg S _ hScard
    obtain rfl := Finset.card_eq_zero.mp hScard
    exact ⟨M, dvd_rfl, by simp, g, by simpa [ZMod.unitsMap_self] using hg,
      fun _ ↦ by simp [Nat.Coprime]⟩
  | succ m ih =>
    intro M _ k χ g hg S hS hScard
    obtain ⟨q, hqS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hqM : q ∈ M.primeFactors := hS hqS
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqM
    have : NeZero q := ⟨hq.ne_zero⟩
    have hMqM : M ∣ q * M := Nat.dvd_mul_left M q
    have : NeZero (q * M) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M)⟩
    obtain ⟨g₁, hg₁, hg₁q⟩ :=
      exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd χ hg
        (Nat.primeFactors_mono (Nat.dvd_of_mem_primeFactors hqM) (NeZero.ne M))
    have hprod : S.prod id = q * (S.erase q).prod id := (Finset.mul_prod_erase _ _ hqS).symm
    obtain ⟨M', hM'dvd, hM'eq, g', hg', hg'q⟩ :=
      ih _ hg₁ (S.erase q)
        (fun _ hr ↦ Nat.primeFactors_mono hMqM (NeZero.ne _) (hS (Finset.mem_of_mem_erase hr)))
        (by rw [Finset.card_erase_of_mem hqS, hScard]; omega)
    refine ⟨M', hMqM.trans hM'dvd, by rw [hM'eq, hprod]; ring, g', ?_, fun n ↦ ?_⟩
    · simpa only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] using hg'
    · rw [hg'q n, hg₁q n, hprod]
      exact ite_coprime_ite_dvd_eq_ite_coprime_mul hq n _ _

/-- **The coprime-index filter.** For `f ∈ S_k(Γ₁(N), χ)` and a nonzero `L` whose primes all
divide `N`, there is a cusp form `g` of level `∏ L.primeFactors * N`, with the nebentypus `χ`
read at that level, whose `q`-expansion is that of `f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

Only the primes of `L` matter, both to the filter and to the level: `Nat.Coprime n L` depends
only on `L`'s prime support, and the construction peels off one prime of `L` at a time. The
squarefree case, where the level is `L * N`, is
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_squarefree`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ}
    [NeZero L] (hLN : L.primeFactors ⊆ N.primeFactors) :
    ∃ g : CuspForm ((Gamma1 (L.primeFactors.prod id * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k
        (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N (L.primeFactors.prod id)))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  obtain ⟨M', hM'dvd, hM'eq, g, hg, hgq⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_prod L.primeFactors.card χ hf
      L.primeFactors hLN rfl
  subst hM'eq
  exact ⟨g, hg, fun n ↦ by simp only [hgq n, coprime_prod_primeFactors_iff (NeZero.ne L)]⟩

/-- **Miyake's Lemma 4.6.5, the coprime-index filter at squarefree `L`.** For
`f ∈ S_k(Γ₁(N), χ)` and a squarefree `L` whose primes all divide `N`, there is a cusp form `g`
of level `L * N`, with the nebentypus `χ` read at that level, whose `q`-expansion is that of
`f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

This is `exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime` at a squarefree `L`,
where `∏ L.primeFactors` is `L` itself. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_squarefree
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} (hL : Squarefree L)
    (hLN : L.primeFactors ⊆ N.primeFactors) :
    ∃ g : CuspForm ((Gamma1 (L * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N L))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  have : NeZero L := ⟨hL.ne_zero⟩
  have hprod : L.primeFactors.prod id = L := by
    simpa using Nat.prod_primeFactors_of_squarefree hL
  have key := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime χ hf hLN
  rwa [hprod] at key


/-- **Room to filter one more prime.** `HasFilterRoom p N M` says the target level `M` can still
absorb a filtering step at `p` above the level `N`: a `p` that does not already divide `N` has to
find `p ^ 2` inside `M`, because reaching it costs two level raises, while a `p` that does divide
`N` only needs one more `p` inside `M / N`. -/
private abbrev HasFilterRoom (p N M : ℕ) : Prop :=
  (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N)

/-- Raising the level from `N` to `q * N` keeps the room at every prime `r ≠ q`, provided the
step at `q` was itself paid for out of `M / N`. -/
private theorem HasFilterRoom.mul_left_of_dvd {N M q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hrq : r ≠ q) (hr_room : HasFilterRoom r N M) (hq_div : q ∣ M / N) :
    HasFilterRoom r (q * N) M := by
  obtain ⟨hr_not, hr_dvd⟩ := hr_room
  refine ⟨fun h ↦ hr_not fun hrN ↦ h (hrN.mul_left q), fun h ↦ ?_⟩
  have hrN : r ∣ N :=
    (hr.dvd_mul.mp h).resolve_left fun h' ↦ hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h')
  rw [show M / (q * N) = M / N / q by rw [mul_comm q N, Nat.div_div_eq_div_mul]]
  obtain ⟨c, hc⟩ :=
    ((Nat.coprime_primes hr hq).mpr hrq).mul_dvd_of_dvd_of_dvd (hr_dvd hrN) hq_div
  exact ⟨c, by rw [hc, show r * q * c = r * c * q by ring, Nat.mul_div_cancel _ hq.pos]⟩

/-- Raising the level from `N` to `N * q ^ 2` keeps the room at every prime `r ≠ q`, provided
`M` really did contain the `q ^ 2` that a `q` outside `N` costs. -/
private theorem HasFilterRoom.mul_right_sq_of_not_dvd {N M q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hrq : r ≠ q) (hqN : ¬ q ∣ N) (hNM : N ∣ M) (hr_room : HasFilterRoom r N M)
    (hq2 : q ^ 2 ∣ M) : HasFilterRoom r (N * q ^ 2) M := by
  obtain ⟨hr_not, hr_dvd⟩ := hr_room
  refine ⟨fun h ↦ hr_not fun hrN ↦ h (hrN.mul_right (q ^ 2)), fun h ↦ ?_⟩
  have hrN : r ∣ N :=
    (hr.dvd_mul.mp h).resolve_right fun h' ↦
      hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h'))
  have hq2' : q ^ 2 ∣ M / N := by
    rw [(Nat.mul_div_cancel' hNM).symm] at hq2
    exact ((hq.coprime_iff_not_dvd.mpr hqN).pow_left 2).dvd_of_dvd_mul_left hq2
  rw [show M / (N * q ^ 2) = M / N / q ^ 2 by rw [Nat.div_div_eq_div_mul]]
  obtain ⟨c, hc⟩ :=
    (((Nat.coprime_primes hr hq).mpr hrq).pow_right 2).mul_dvd_of_dvd_of_dvd (hr_dvd hrN) hq2'
  exact ⟨c, by rw [hc, show r * q ^ 2 * c = r * c * q ^ 2 by ring,
    Nat.mul_div_cancel _ (pow_pos hq.pos 2)]⟩

/-- **The filter at a `q` that need not divide the level.** Restricting `f` to level `q * N`
puts `q` into the prime support of the level, after which the single-step filter applies and
lands at `q * (q * N)`. The level is left in exactly that shape: it is `N * q ^ 2`, but only up
to an equation of naturals, and rewriting along that equation here would mean transporting a
cusp form. Callers use the equation on divisibility statements instead. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_not_dvd
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {q : ℕ} [NeZero q] :
    ∃ g : CuspForm ((Gamma1 (q * (q * N))).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k
        (χ.comp (ZMod.unitsMap ((Nat.dvd_mul_left N q).trans (Nat.dvd_mul_left _ q)))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if q ∣ n then 0 else (qExpansion 1 f).coeff n := by
  have hNqN : N ∣ q * N := Nat.dvd_mul_left N q
  have : NeZero (q * N) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne N)⟩
  obtain ⟨g, hg, hgq⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd (χ.comp (ZMod.unitsMap hNqN))
      (CuspForm.ofLe_mem_cuspFormCharSpace χ hNqN hf)
      (Nat.primeFactors_mono (Nat.dvd_mul_right q N) (NeZero.ne _))
  exact ⟨g, by simpa only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] using hg,
    fun n ↦ by rw [hgq n, CuspForm.coe_ofLe]⟩

/-- **Composing one prime's filter with the filter for the rest.** The intermediate form
`g` deletes the multiples of `q`, and `g'` keeps from `g` only the indices coprime to `m`; the
two together keep exactly the indices coprime to `q * m`. Stated over the *result* of the
recursive call rather than over the recursion itself, so that no helper has to carry an
induction hypothesis in its signature. -/
private theorem mem_and_qExpansion_coeff_eq_of_filter_comp {N N' M : ℕ} {k : ℤ} {q m : ℕ}
    (hq : q.Prime) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {g : CuspForm ((Gamma1 N').map (mapGL ℝ)) k}
    {g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hNM : N ∣ M) {hNN' : N ∣ N'} {hN'M : N' ∣ M}
    (hg' : g' ∈ cuspFormCharSpace k ((χ.comp (ZMod.unitsMap hNN')).comp (ZMod.unitsMap hN'M)))
    (hgq : ∀ n, (qExpansion 1 g).coeff n = if q ∣ n then 0 else (qExpansion 1 f).coeff n)
    (hg'q : ∀ n, (qExpansion 1 g').coeff n =
      if Nat.Coprime n m then (qExpansion 1 g).coeff n else 0) :
    g' ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n, (qExpansion 1 g').coeff n =
        if Nat.Coprime n (q * m) then (qExpansion 1 f).coeff n else 0 :=
  ⟨by simpa only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] using hg',
    fun n ↦ by
      rw [hg'q n, hgq n]
      exact ite_coprime_ite_dvd_eq_ite_coprime_mul hq n _ _⟩

/-- **One peeling step, on either side of `q ∣ N`.** There is an intermediate level `N'` between
`N` and `M` at which `f` has already been filtered at `q`, and at which every prime of `S` still
to be peeled keeps its room. The two cases differ only in where they land: `q * N` when `q`
already divides `N`, and `q * (q * N)` when it does not and the climb must be paid for twice. -/
private theorem exists_intermediate_of_filter_step {N M : ℕ} [NeZero N] {k : ℤ} {q : ℕ}
    (hq : q.Prime) (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) (hNM : N ∣ M) {S : Finset ℕ} (hqS : q ∈ S)
    (hSprime : ∀ p ∈ S, p.Prime) (hroom : ∀ p ∈ S, HasFilterRoom p N M) :
    ∃ N', N' ≠ 0 ∧ ∃ (hNN' : N ∣ N') (_ : N' ∣ M),
      (∀ p ∈ S.erase q, HasFilterRoom p N' M) ∧
      ∃ g : CuspForm ((Gamma1 N').map (mapGL ℝ)) k,
        g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNN')) ∧
        ∀ n, (qExpansion 1 g).coeff n = if q ∣ n then 0 else (qExpansion 1 f).coeff n := by
  have : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨hq_not, hq_dvd⟩ := hroom q hqS
  by_cases hqN : q ∣ N
  · have : NeZero (q * N) := ⟨Nat.mul_ne_zero hq.ne_zero (NeZero.ne N)⟩
    obtain ⟨g, hg, hgq⟩ := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd χ hf
      (Nat.primeFactors_mono hqN (NeZero.ne N))
    exact ⟨q * N, Nat.mul_ne_zero hq.ne_zero (NeZero.ne N), Nat.dvd_mul_left N q,
      calc q * N = N * q := by ring
        _ ∣ N * (M / N) := Nat.mul_dvd_mul_left N (hq_dvd hqN)
        _ = M := Nat.mul_div_cancel' hNM,
      fun p hp ↦ (hroom p (Finset.mem_of_mem_erase hp)).mul_left_of_dvd hq
        (hSprime p (Finset.mem_of_mem_erase hp)) (Finset.ne_of_mem_erase hp) (hq_dvd hqN),
      g, hg, hgq⟩
  · have hne : q * (q * N) ≠ 0 :=
      Nat.mul_ne_zero hq.ne_zero (Nat.mul_ne_zero hq.ne_zero (NeZero.ne N))
    have : NeZero (q * (q * N)) := ⟨hne⟩
    have hsq : q * (q * N) = N * q ^ 2 := by ring
    obtain ⟨g, hg, hgq⟩ :=
      exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd_of_not_dvd χ hf (q := q)
    refine ⟨q * (q * N), hne, (Nat.dvd_mul_left N q).trans (Nat.dvd_mul_left _ q), ?_, ?_,
      g, hg, hgq⟩
    · rw [hsq]
      exact ((hq.coprime_iff_not_dvd.mpr hqN).symm.pow_right 2).mul_dvd_of_dvd_of_dvd hNM
        (hq_not hqN)
    · intro p hp
      rw [hsq]
      exact (hroom p (Finset.mem_of_mem_erase hp)).mul_right_sq_of_not_dvd hq
        (hSprime p (Finset.mem_of_mem_erase hp)) (Finset.ne_of_mem_erase hp) hqN hNM (hq_not hqN)

/-- **The iterated filter at a prescribed level.** Peeling the primes of `S` off `f` one at a
time, landing at a level `M` fixed in advance rather than at one manufactured by the recursion.
That is what `HasFilterRoom` buys: each prime `p ∈ S` is guaranteed the room its own step will
cost, so the recursion never has to raise `M`. Induction is on the number of primes left. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_room (m : ℕ) :
    ∀ {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
      {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}, f ∈ cuspFormCharSpace k χ →
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → S.card = m → Squarefree (S.prod id) →
      ∀ {M : ℕ} [NeZero M] (hNM : N ∣ M), S.prod id ∣ M → (∀ p ∈ S, HasFilterRoom p N M) →
        ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
          g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
          ∀ n, (qExpansion 1 g).coeff n =
            if Nat.Coprime n (S.prod id) then (qExpansion 1 f).coeff n else 0 := by
  induction m with
  | zero =>
    intro N _ k χ f hf S _ hScard _ M _ hNM _ _
    obtain rfl := Finset.card_eq_zero.mp hScard
    exact ⟨CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd hNM) f,
      CuspForm.ofLe_mem_cuspFormCharSpace χ hNM hf, fun n ↦ by simp [CuspForm.coe_ofLe]⟩
  | succ m ih =>
    intro N _ k χ f hf S hSprime hScard hSsq M _ hNM hSM hroom
    obtain ⟨q, hqS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hq : q.Prime := hSprime q hqS
    have hprod : S.prod id = q * (S.erase q).prod id := (Finset.mul_prod_erase _ _ hqS).symm
    have hEM : (S.erase q).prod id ∣ M := dvd_trans ⟨q, by rw [hprod]; ring⟩ hSM
    obtain ⟨N', hN'0, hNN', hN'M, hroom', g, hg, hgq⟩ :=
      exists_intermediate_of_filter_step hq χ hf hNM hqS hSprime hroom
    have : NeZero N' := ⟨hN'0⟩
    obtain ⟨g', hg', hg'q⟩ := ih (χ.comp (ZMod.unitsMap hNN')) hg (S.erase q)
      (fun p hp ↦ hSprime p (Finset.mem_of_mem_erase hp))
      (by rw [Finset.card_erase_of_mem hqS, hScard]; omega)
      (hprod ▸ hSsq).of_mul_right hN'M hEM hroom'
    obtain ⟨h₁, h₂⟩ := mem_and_qExpansion_coeff_eq_of_filter_comp hq χ hNM hg' hgq hg'q
    exact ⟨g', h₁, fun n ↦ by rw [hprod]; exact h₂ n⟩

/-- The iterated filter for a squarefree `L`, at a prescribed level `M` with room for every
prime of `L`. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_room_squarefree
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} (hL : Squarefree L) {M : ℕ} [NeZero M]
    (hNM : N ∣ M) (hLM : L ∣ M) (hroom : ∀ p ∈ L.primeFactors, HasFilterRoom p N M) :
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n, (qExpansion 1 g).coeff n =
        if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  have hprod : L.primeFactors.prod id = L := by
    simpa using Nat.prod_primeFactors_of_squarefree hL
  obtain ⟨g, hg, hgq⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_room L.primeFactors.card χ hf
      L.primeFactors (fun _ ↦ Nat.prime_of_mem_primeFactors) rfl (by rw [hprod]; exact hL) hNM
      (by rw [hprod]; exact hLM) hroom
  exact ⟨g, hg, fun n ↦ by simpa only [hprod] using hgq n⟩

/-- **Miyake's `h`-form.** For `f ∈ S_k(Γ₁(N), χ)` and a squarefree `L`, there is a cusp form
`h` of level `N * L ^ 2`, with the nebentypus `χ` read at that level, whose `q`-expansion is
that of `f` restricted to the indices *not* coprime to `L`:

`aₙ(h) = if (n, L) = 1 then 0 else aₙ(f)`.

It is `f` minus its coprime-index filter, so this is the complement of
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`. The level `N * L ^ 2` is what
the filter costs: a prime of `L` already dividing `N` is paid for out of `L`, and one that does
not needs a second factor, which is why `L` enters squared. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ}
    [NeZero L] (hL : Squarefree L) :
    ∃ h : CuspForm ((Gamma1 (N * L ^ 2)).map (mapGL ℝ)) k,
      h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right N (L ^ 2)))) ∧
      ∀ n, (qExpansion 1 h).coeff n =
        if Nat.Coprime n L then 0 else (qExpansion 1 f).coeff n := by
  have hNM : N ∣ N * L ^ 2 := Nat.dvd_mul_right N (L ^ 2)
  have : NeZero (N * L ^ 2) := ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (NeZero.ne L))⟩
  obtain ⟨g, hg, hgq⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_room_squarefree χ hf hL hNM
      (dvd_mul_of_dvd_right (dvd_pow_self L two_ne_zero) N) fun p hp ↦ by
        have hpL : p ∣ L := Nat.dvd_of_mem_primeFactors hp
        refine ⟨fun _ ↦ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpL 2) N, fun _ ↦ ?_⟩
        rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N))]
        exact dvd_pow hpL two_ne_zero
  refine ⟨CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd hNM) f - g,
    Submodule.sub_mem _ (CuspForm.ofLe_mem_cuspFormCharSpace χ hNM hf) hg, fun n ↦ ?_⟩
  rw [FunLike.coe_sub, _root_.ModularForm.qExpansion_sub one_pos
    (one_mem_strictPeriods_Gamma1_map _), map_sub, hgq n, CuspForm.coe_ofLe]
  split_ifs <;> simp
end TauCeti
