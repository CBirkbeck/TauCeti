/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Independence
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Recurrence
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# The eigenvalue system of a good Hecke eigenform

The eigenvalues of a good Hecke eigenform `f` (`EigenformAwayFromLevel`) inherit the
multiplication table of the `Γ₀(N)` Hecke ring: they are multiplicative on coprime indices, and
along the powers of a good prime `p` they satisfy the Diamond–Shurman recurrence
`λ_{p^{r+2}} = λ_p λ_{p^{r+1}} − χ(p) p^{k−1} λ_{p^r}`, because the scalar coset `T(p, p)` acts on
the character space by `χ(p) p^{k−2}`. Nothing here touches Fourier coefficients: the three
identities `eigenvalue_one`, `eigenvalue_mul` and `eigenvalue_prime_pow_add_two` are images of
relations in the ring under `heckeRingHomCuspCharSpace`, evaluated on the (nonzero) form; the
remaining statements are consequences (a congruence in the index, the prime-square instance, and
the cancellation argument below).

These identities are what the strong-multiplicity-one argument consumes: they let the eigenvalues
at composite good indices be read off the eigenvalues at good primes and the character.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_one`: `λ₁ = 1`.
* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_mul`: `λ_{mn} = λ_m λ_n` for coprime good
  indices.
* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_prime_pow_add_two`: the recurrence along the
  powers of a good prime, and its first instance
  `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_prime_sq`.
* `HeckeRing.GL2.EigenformAwayFromLevel.eigenArithmeticFunction`: the eigenvalue system extended by
  zero to a total `ArithmeticFunction ℂ`, with
  `isMultiplicative_eigenArithmeticFunction` and `hasPrimePowerRec_eigenArithmeticFunction` —
  together, exactly the hypotheses of
  `ArithmeticFunction.IsMultiplicative.linearIndependent_of_rec`.
* `HeckeRing.GL2.EigenformAwayFromLevel.recWeight`: the weight `χ(p) p ^ (k - 1)` of that
  recurrence, which depends on the level, weight and character but **not on the form** — the
  sharing the independence theorem needs.

The statements build the coprimality proofs guarding `eigenvalue` from their hypotheses
(`Nat.coprime_mul_iff_left`, `Nat.Coprime.pow_left`, cast along the coercion lemmas of `ℕ+`); by
proof irrelevance they rewrite whichever proof a consumer holds, and `eigenvalue_congr` moves
between spellings of an index.

## Provenance

The multiplicativity and the prime-square identity appear as
`Eigenform.coeff_eq_coeff_one_mul_eigenvalue` and `eigenvalue_at_prime_sq_of_coeff_one_ne_zero`
in the AINTLIB `LeanModularForms` project
(`LeanModularForms/StrongMultiplicityOne/ConstantMultiple.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), derived there from
the Fourier coefficients of a normalised eigenform. Here both are read off the Hecke ring
instead, so no normalisation and no coefficient formula is needed.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section


namespace HeckeRing.GL2.EigenformAwayFromLevel

variable {N : ℕ} [NeZero N] {k : ℤ} (f : EigenformAwayFromLevel N k)

/-- The form, as a nonzero vector of its character space. -/
private theorem mk_ne_zero :
    (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) ≠ 0 :=
  fun h ↦ f.ne_zero (congrArg Subtype.val h)

/-- Two scalars acting alike on the form are equal. -/
private theorem eq_of_smul_eq {a b : ℂ}
    (h : a • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) =
      b • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ)) : a = b :=
  smul_left_injective ℂ f.mk_ne_zero h

/-- The eigenvalue depends only on the index, not on the coprimality proof or on how the index
is spelled. -/
theorem eigenvalue_congr {m n : ℕ+} (hmn : m = n) {hm : Nat.Coprime m N} {hn : Nat.Coprime n N} :
    f.eigenvalue m hm = f.eigenvalue n hn := by
  subst hmn
  rfl

/-- The eigenvalue at `1` is `1`: the ring element at index `1` is the identity. -/
@[simp]
theorem eigenvalue_one : f.eigenvalue 1 (Nat.coprime_one_left N) = 1 := by
  refine f.eq_of_smul_eq ?_
  rw [← f.isEigen 1 (Nat.coprime_one_left N), PNat.one_coe, heckeTCompositeGamma0_one, map_one,
    Module.End.one_apply, one_smul]

/-- **Multiplicativity on coprime good indices**: `λ_{mn} = λ_m λ_n`, the image of the coprime
multiplication rule `heckeTCompositeGamma0_mul_of_coprime` of the Hecke ring. -/
theorem eigenvalue_mul {m n : ℕ+} (hmn : Nat.Coprime m n) (hm : Nat.Coprime m N)
    (hn : Nat.Coprime n N) :
    f.eigenvalue (m * n) (PNat.mul_coe m n ▸ Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩) =
      f.eigenvalue m hm * f.eigenvalue n hn := by
  refine f.eq_of_smul_eq ?_
  rw [← f.isEigen (m * n) (PNat.mul_coe m n ▸ Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩),
    PNat.mul_coe, heckeTCompositeGamma0_mul_of_coprime N hmn, map_mul, Module.End.mul_apply,
    f.isEigen n hn, map_smul, f.isEigen m hm, smul_smul, mul_comm]

/-- The recurrence block `heckeTGeneratorRecGamma0 N p v` acts by `λ_{p^v}` at a good prime. -/
private theorem heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 {p : ℕ+}
    (hp : (p : ℕ).Prime) {v : ℕ} (hv : Nat.Coprime ((p ^ v : ℕ+) : ℕ) N) :
    heckeRingHomCuspCharSpace k f.χ (heckeTGeneratorRecGamma0 N p v)
        ⟨f.toCuspForm, f.mem_charSpace⟩ =
      f.eigenvalue (p ^ v) hv • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) := by
  have h := f.isEigen (p ^ v) hv
  rwa [PNat.pow_coe, heckeTCompositeGamma0_prime_pow N hp] at h

/-- **The recurrence along the powers of a good prime**:
`λ_{p^{r+2}} = λ_p λ_{p^{r+1}} − χ(p) p^{k−1} λ_{p^r}`. This is the image of the defining
recurrence of the ring on the character space
(`heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ_apply`), evaluated on the form. -/
theorem eigenvalue_prime_pow_add_two {p : ℕ+} (hp : (p : ℕ).Prime) (hpN : Nat.Coprime p N)
    (r : ℕ) :
    f.eigenvalue (p ^ (r + 2)) (PNat.pow_coe p (r + 2) ▸ hpN.pow_left (r + 2)) =
      f.eigenvalue p hpN *
          f.eigenvalue (p ^ (r + 1)) (PNat.pow_coe p (r + 1) ▸ hpN.pow_left (r + 1)) -
        (f.χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          f.eigenvalue (p ^ r) (PNat.pow_coe p r ▸ hpN.pow_left r) := by
  have hc (v : ℕ) : Nat.Coprime ((p ^ v : ℕ+) : ℕ) N := PNat.pow_coe p v ▸ hpN.pow_left v
  -- the generator acts by `λ_p`
  have eₚ : heckeRingHomCuspCharSpace k f.χ (heckeTGeneratorGamma0 N p)
      ⟨f.toCuspForm, f.mem_charSpace⟩ =
      f.eigenvalue p hpN • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) := by
    have := f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp (hc 1)
    rwa [heckeTGeneratorRecGamma0_one, f.eigenvalue_congr (pow_one p) (hn := hpN)] at this
  -- the ring's two-step recurrence at the form, with `p • S_p` already read as `χ(p) p^{k−1}`
  have h := heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ_apply k f.χ hp.pos hpN
    ⟨f.toCuspForm, f.mem_charSpace⟩ r
  rw [f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp (hc r),
    f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp (hc (r + 1)),
    f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp (hc (r + 2)), map_smul, eₚ,
    smul_smul, smul_smul, ← sub_smul] at h
  rw [f.eq_of_smul_eq h]
  ring

/-- **The prime-square identity**: `λ_{p²} = λ_p² − χ(p) p^{k−1}` at a good prime. -/
theorem eigenvalue_prime_sq {p : ℕ+} (hp : (p : ℕ).Prime) (hpN : Nat.Coprime p N) :
    f.eigenvalue (p ^ 2) (PNat.pow_coe p 2 ▸ hpN.pow_left 2) =
      f.eigenvalue p hpN ^ 2 - (f.χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) := by
  have hc (v : ℕ) : Nat.Coprime ((p ^ v : ℕ+) : ℕ) N := PNat.pow_coe p v ▸ hpN.pow_left v
  have e₀ : f.eigenvalue (p ^ 0) (hc 0) = 1 :=
    (f.eigenvalue_congr (pow_zero p)).trans f.eigenvalue_one
  have e₁ : f.eigenvalue (p ^ (0 + 1)) (hc (0 + 1)) = f.eigenvalue p hpN :=
    f.eigenvalue_congr (by rw [zero_add, pow_one])
  rw [f.eigenvalue_prime_pow_add_two hp hpN 0, e₀, e₁, mul_one, sq]

/-! ### The eigenvalue system as an arithmetic function -/

/-- **The weight of the shared prime-power recurrence**, `w p = χ(p) p ^ (k - 1)` at a good prime
and `0` at a bad one.

It depends on the level, the weight and the nebentypus — **not on the eigenform** — which is
exactly the sharing that `ArithmeticFunction.HasPrimePowerRec` and the independence theorem above
it require. Two eigenforms of the same level, weight and character therefore satisfy the *same*
recurrence, and that is what lets a relation between them be cut down one prime at a time. -/
noncomputable def recWeight (N : ℕ) (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (p : ℕ) : ℂ :=
  if hp : Nat.Coprime p N then (χ (ZMod.unitOfCoprime p hp) : ℂ) * (p : ℂ) ^ (k - 1) else 0

/-- The weight at a good prime. -/
theorem recWeight_of_coprime {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {p : ℕ}
    (h : Nat.Coprime p N) :
    recWeight N k χ p = (χ (ZMod.unitOfCoprime p h) : ℂ) * (p : ℂ) ^ (k - 1) := by
  unfold recWeight
  rw [dite_eq_left_of_eq_true (eq_true h)]

/-- The weight at a bad prime is `0` — which is what makes the recurrence hold there, every other
term vanishing too. -/
theorem recWeight_of_not_coprime {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {p : ℕ}
    (h : ¬ Nat.Coprime p N) : recWeight N k χ p = 0 := by
  unfold recWeight
  rw [dite_eq_right_of_eq_false (eq_false h)]

/-- **The eigenvalue system, extended by zero to an `ArithmeticFunction`.**

`EigenformAwayFromLevel.eigenvalue` is defined only at indices coprime to the level, and carries
the coprimality proof as an argument. The independence theorem wants a total
`ArithmeticFunction ℂ`, so the values at indices sharing a factor with `N` are set to `0` — which
is the choice that keeps the function multiplicative, since a bad index stays bad under
multiplication. -/
noncomputable def eigenArithmeticFunction (f : EigenformAwayFromLevel N k) :
    ArithmeticFunction ℂ where
  toFun n := if h : 0 < n ∧ Nat.Coprime n N then f.eigenvalue ⟨n, h.1⟩ h.2 else 0
  map_zero' := by simp

theorem eigenArithmeticFunction_apply_of_coprime {n : ℕ} (hn : 0 < n) (h : Nat.Coprime n N) :
    f.eigenArithmeticFunction n = f.eigenvalue ⟨n, hn⟩ h := by
  unfold eigenArithmeticFunction
  simp only [ArithmeticFunction.coe_mk]
  split
  next => rfl
  next hc => exact absurd ⟨hn, h⟩ hc

@[simp]
theorem eigenArithmeticFunction_apply_of_not_coprime {n : ℕ} (h : ¬ Nat.Coprime n N) :
    f.eigenArithmeticFunction n = 0 := by
  unfold eigenArithmeticFunction
  simp only [ArithmeticFunction.coe_mk]
  split
  next hc => exact absurd hc.2 h
  next => rfl

/-- **The extended eigenvalue system is multiplicative.** On coprime good indices this is
`eigenvalue_mul`; a product with a bad factor is bad, so both sides vanish there. -/
theorem isMultiplicative_eigenArithmeticFunction :
    (f.eigenArithmeticFunction).IsMultiplicative := by
  constructor
  · rw [f.eigenArithmeticFunction_apply_of_coprime Nat.one_pos (Nat.coprime_one_left N)]
    exact (f.eigenvalue_congr (show (⟨1, Nat.one_pos⟩ : ℕ+) = 1 from rfl)).trans
      f.eigenvalue_one
  · intro m n hmn
    by_cases hm : Nat.Coprime m N
    · by_cases hn : Nat.Coprime n N
      · rcases Nat.eq_zero_or_pos m with rfl | hm0
        · simp
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp
        rw [f.eigenArithmeticFunction_apply_of_coprime (Nat.mul_pos hm0 hn0)
            (Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩),
          f.eigenArithmeticFunction_apply_of_coprime hm0 hm,
          f.eigenArithmeticFunction_apply_of_coprime hn0 hn]
        exact (f.eigenvalue_congr
            (show (⟨m * n, Nat.mul_pos hm0 hn0⟩ : ℕ+) = ⟨m, hm0⟩ * ⟨n, hn0⟩ from rfl)).trans
          (f.eigenvalue_mul (m := ⟨m, hm0⟩) (n := ⟨n, hn0⟩) hmn hm hn)
      · rw [f.eigenArithmeticFunction_apply_of_not_coprime hn,
          f.eigenArithmeticFunction_apply_of_not_coprime
            (fun h ↦ hn (Nat.coprime_mul_iff_left.mp h).2), mul_zero]
    · rw [f.eigenArithmeticFunction_apply_of_not_coprime hm,
        f.eigenArithmeticFunction_apply_of_not_coprime
          (fun h ↦ hm (Nat.coprime_mul_iff_left.mp h).1), zero_mul]

/-- **The extended eigenvalue system obeys the shared prime-power recurrence.**

At a good prime this is `eigenvalue_prime_pow_add_two`. At a bad prime every term vanishes: the
positive powers of `p` are not coprime to `N`, so the extension is `0` there, and `recWeight` is
`0` as well — which is what makes the single equation hold uniformly in `p`, as
`ArithmeticFunction.HasPrimePowerRec` demands.

Together with `isMultiplicative_eigenArithmeticFunction` this is the whole hypothesis of
`ArithmeticFunction.IsMultiplicative.linearIndependent_of_rec`: eigenforms of one level, weight
and character with distinct eigenvalue systems are linearly independent. -/
theorem hasPrimePowerRec_eigenArithmeticFunction :
    ArithmeticFunction.HasPrimePowerRec f.eigenArithmeticFunction (recWeight N k f.χ) := by
  rw [ArithmeticFunction.hasPrimePowerRec_iff]
  intro p hp r
  by_cases hpN : Nat.Coprime p N
  · have hcp : ∀ j : ℕ, Nat.Coprime (p ^ j) N := fun j ↦ hpN.pow_left j
    have hpos : ∀ j : ℕ, 0 < p ^ j := fun j ↦ pow_pos hp.pos j
    rw [f.eigenArithmeticFunction_apply_of_coprime (hpos (r + 2)) (hcp (r + 2)),
      f.eigenArithmeticFunction_apply_of_coprime hp.pos hpN,
      f.eigenArithmeticFunction_apply_of_coprime (hpos (r + 1)) (hcp (r + 1)),
      f.eigenArithmeticFunction_apply_of_coprime (hpos r) (hcp r)]
    rw [recWeight_of_coprime hpN]
    -- `(⟨p, _⟩ : ℕ+) ^ j` and `⟨p ^ j, _⟩` are the same term up to the positivity proof, which
    -- proof irrelevance identifies, so the ring identity applies as it stands
    exact f.eigenvalue_prime_pow_add_two (p := ⟨p, hp.pos⟩) hp hpN r
  · have hbad : ∀ j : ℕ, 0 < j → ¬ Nat.Coprime (p ^ j) N := fun j hj hc ↦
      hpN ((Nat.coprime_pow_left_iff hj p N).mp hc)
    rw [f.eigenArithmeticFunction_apply_of_not_coprime (hbad (r + 2) (by omega)),
      f.eigenArithmeticFunction_apply_of_not_coprime hpN]
    rw [recWeight_of_not_coprime hpN]
    ring

end HeckeRing.GL2.EigenformAwayFromLevel
