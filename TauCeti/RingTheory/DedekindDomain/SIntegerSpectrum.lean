/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger

/-!
# The height one spectrum of a ring of `S`-integers

Let `R` be a Dedekind domain with fraction field `K` and `S` a set of height-one primes of `R`.
`TauCeti/RingTheory/DedekindDomain/SInteger.lean` shows that the ring of `S`-integers is again a
Dedekind domain, so it has a height one spectrum of its own. This file identifies that spectrum:
the primes of `𝒪_S` are exactly the primes of `R` **not** in `S`, via `v ↦ 𝒪_S ∩ v`
(`integerHeightOneSpectrumEquiv`), and the correspondence carries the valuations across unchanged
(`valuation_integerHeightOneSpectrumEquiv`).

The two directions are `integerPrimeOverOfNotMem`, extending `v ∉ S` to `𝒪_S`,
and `integerPrimeUnder`, contracting a prime of `𝒪_S` to `R`. That they are mutually inverse is
`integer_comap_map_asIdeal` in one direction and `integer_map_comap_eq` — every ideal of `𝒪_S` is
extended — in the other.

Inverting `S` therefore removes exactly the primes of `S` from the spectrum and changes nothing
else, which is why the Selmer group of `𝒪_S` relative to `∅` is the Selmer group of `R` relative
to `S`. That identification is what
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 needs for weak Mordell–Weil: the finiteness of
`A(S, 2)` is the finiteness of a Selmer group over `𝒪_S`.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), the source the roadmap's §Provenance
names for the Layer 6 Mordell–Weil lane. Following this repository's convention for adapted
material, the upstream authorship is credited here rather than in the copyright header. This is
the height-one-spectrum half of that file; the Dedekind property came first, and the class-group
computation `Cl(𝒪_S) ≃* Cl(R) ⧸ ⟨[v] : v ∈ S⟩` follows in the PR that consumes it.
-/

public section

open IsDedekindDomain

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

/-- For `v ∉ S`, the extension of `v` to `𝒪_S` is a proper ideal. -/
lemma integer_map_asIdeal_ne_top {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal ≠ ⊤ := by
  -- The extension lands inside the ideal of `S`-integers of `v`-valuation `< 1`, which does not
  -- contain `1`.
  set f := algebraMap R (S.integer K) with hf
  -- the `S`-integers of `v`-valuation `< 1` form an ideal, because `v` is bounded by `1` on all
  -- of `𝒪_S` when `v ∉ S`
  let 𝔪 : Ideal (S.integer K) :=
    { carrier := {x | v.valuation K (x : K) < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by
        rw [Set.mem_ofPred_eq, Subalgebra.coe_add]
        exact lt_of_le_of_lt ((v.valuation K).map_add _ _) (max_lt ha hb)
      smul_mem' := fun c {a} ha ↦ by
        have hc : v.valuation K (c : K) ≤ 1 := (Set.mem_integer_iff K S).mp c.property v hv
        rw [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul]
        calc v.valuation K (c : K) * v.valuation K (a : K)
            ≤ 1 * v.valuation K (a : K) := by gcongr
          _ = v.valuation K (a : K) := one_mul _
          _ < 1 := ha }
  have hle : Ideal.map f v.asIdeal ≤ 𝔪 :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
      have : v.valuation K ((f a : S.integer K) : K) < 1 := by
        rw [Subalgebra.coe_algebraMap]; exact (v.valuation_lt_one_iff_mem a).mpr ha
      exact this
  intro htop
  have h1 : v.valuation K ((1 : S.integer K) : K) < 1 := le_trans htop.ge hle Submodule.mem_top
  simp at h1

/-- For `v ∉ S`, contracting the extension of `v` returns `v`. -/
lemma integer_comap_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).comap (algebraMap R (S.integer K))
      = v.asIdeal := by
  refine (v.isMaximal.eq_of_le ?_ Ideal.le_comap_map).symm
  rw [Ne, Ideal.comap_eq_top_iff]
  exact integer_map_asIdeal_ne_top K S hv

/-- For `v ∉ S`, the extension of `v` to `𝒪_S` is maximal. -/
lemma integer_isMaximal_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).IsMaximal := by
  set f := algebraMap R (S.integer K) with hf
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (integer_map_asIdeal_ne_top K S hv)
  have hcle : v.asIdeal ≤ M.comap f :=
    (integer_comap_map_asIdeal K S hv).ge.trans (Ideal.comap_mono hle)
  have hceq : M.comap f = v.asIdeal :=
    (v.isMaximal.eq_of_le (hM.isPrime.comap f).ne_top hcle).symm
  rwa [← integer_map_comap_eq K S M, hceq] at hM

/-- For `v ∉ S`, the extension of `v` to `𝒪_S` is nonzero. -/
lemma integer_map_asIdeal_ne_bot {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal ≠ ⊥ := by
  -- `v` is nonzero and `R → 𝒪_S` is injective.
  intro h
  refine v.ne_bot ?_
  rw [← integer_comap_map_asIdeal K S hv, h,
    Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R (S.integer K))]

/-- The prime of `𝒪_S` above a prime `v ∉ S` of `R`: the extension of `v`. -/
noncomputable def integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    HeightOneSpectrum (S.integer K) where
  asIdeal := Ideal.map (algebraMap R (S.integer K)) v.asIdeal
  isPrime := (integer_isMaximal_map_asIdeal K S hv).isPrime
  ne_bot := integer_map_asIdeal_ne_bot K S hv

@[simp] lemma integerPrimeOverOfNotMem_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (integerPrimeOverOfNotMem K S hv).asIdeal
      = Ideal.map (algebraMap R (S.integer K)) v.asIdeal := by
  simp only [integerPrimeOverOfNotMem]

/-- The prime of `R` below a prime `P` of `𝒪_S`: its contraction. -/
noncomputable def integerPrimeUnder (P : HeightOneSpectrum (S.integer K)) :
    HeightOneSpectrum R where
  asIdeal := P.asIdeal.comap (algebraMap R (S.integer K))
  isPrime := P.isPrime.comap _
  ne_bot := integer_comap_ne_bot K S P.ne_bot

@[simp] lemma integerPrimeUnder_asIdeal (P : HeightOneSpectrum (S.integer K)) :
    (integerPrimeUnder K S P).asIdeal = P.asIdeal.comap (algebraMap R (S.integer K)) := by
  simp only [integerPrimeUnder]

/-- A prime under a prime of `𝒪_S` never lies in `S`. -/
lemma integerPrimeUnder_notMem (P : HeightOneSpectrum (S.integer K)) :
    integerPrimeUnder K S P ∉ S := by
  -- The primes of `S` become the unit ideal in `𝒪_S`, and a prime is not the unit ideal.
  intro hv
  have h1 := integer_map_asIdeal_eq_top K S hv
  rw [integerPrimeUnder_asIdeal, integer_map_comap_eq] at h1
  exact P.isPrime.ne_top h1

/-- **The primes of `𝒪_S` are exactly the primes of `R` not in `S`.** -/
noncomputable def integerHeightOneSpectrumEquiv :
    {v : HeightOneSpectrum R // v ∉ S} ≃ HeightOneSpectrum (S.integer K) where
  toFun v := integerPrimeOverOfNotMem K S v.property
  invFun P := ⟨integerPrimeUnder K S P, integerPrimeUnder_notMem K S P⟩
  left_inv v := Subtype.ext <| HeightOneSpectrum.ext <| integer_comap_map_asIdeal K S v.property
  right_inv P := HeightOneSpectrum.ext <| integer_map_comap_eq K S P.asIdeal

@[simp] lemma integerHeightOneSpectrumEquiv_apply (v : {v : HeightOneSpectrum R // v ∉ S}) :
    integerHeightOneSpectrumEquiv K S v = integerPrimeOverOfNotMem K S v.property := by
  simp only [integerHeightOneSpectrumEquiv, Equiv.coe_fn_mk]

@[simp] lemma integerHeightOneSpectrumEquiv_symm_apply (P : HeightOneSpectrum (S.integer K)) :
    ((integerHeightOneSpectrumEquiv K S).symm P : HeightOneSpectrum R)
      = integerPrimeUnder K S P := by
  simp only [integerHeightOneSpectrumEquiv, Equiv.coe_fn_symm_mk]

/-- For `v ∉ S`, the contraction of the extension of `v ^ n` is `v ^ n`. -/
lemma integer_comap_map_pow {v : HeightOneSpectrum R} (hv : v ∉ S) (n : ℕ) :
    (Ideal.map (algebraMap R (S.integer K)) (v.asIdeal ^ n)).comap
        (algebraMap R (S.integer K)) = v.asIdeal ^ n := by
  -- The contraction divides `v ^ n`, so it is `v ^ j` for some `j`; extending back forces `j = n`.
  set f := algebraMap R (S.integer K) with hf
  have hP0 : Ideal.map f v.asIdeal ≠ 0 := integer_map_asIdeal_ne_bot K S hv
  have hPnu : ¬ IsUnit (Ideal.map f v.asIdeal) :=
    fun h ↦ integer_map_asIdeal_ne_top K S hv (Ideal.isUnit_iff.mp h)
  refine le_antisymm ?_ Ideal.le_comap_map
  have hdvd : (Ideal.map f (v.asIdeal ^ n)).comap f ∣ v.asIdeal ^ n :=
    Ideal.dvd_iff_le.mpr Ideal.le_comap_map
  obtain ⟨j, -, hassoc⟩ := (dvd_prime_pow v.prime n).mp hdvd
  rw [associated_iff_eq] at hassoc
  have hmapQ : Ideal.map f ((Ideal.map f (v.asIdeal ^ n)).comap f) =
      Ideal.map f (v.asIdeal ^ n) := integer_map_comap_eq K S _
  rw [hassoc, Ideal.map_pow, Ideal.map_pow] at hmapQ
  rw [hassoc, (pow_inj_of_not_isUnit hPnu hP0).mp hmapQ]

-- The count form of Mathlib's `intValuation_le_pow_iff_mem`, which characterises membership of a
-- prime power by the valuation: unfolding the valuation of a nonzero element to `exp (-count)`
-- turns that characterisation into the count comparison below. Private: it is a spelling change
-- for this one proof, not API — Mathlib's valuation form is the statement to use.
private lemma le_count_iff_mem_pow {A : Type*} [CommRing A] [IsDedekindDomain A]
    (w : HeightOneSpectrum A) {b : A} (hb : b ≠ 0) (k : ℕ) :
    k ≤ Associates.count (Associates.mk w.asIdeal) (Associates.mk (Ideal.span {b})).factors
      ↔ b ∈ w.asIdeal ^ k := by
  rw [← w.intValuation_le_pow_iff_mem, w.intValuation_apply, w.intValuationDef_if_neg hb,
    WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]

/-- For `v ∉ S`, the `Pᵥ`-adic valuation of an element of `R`, computed in `𝒪_S`, is its `v`-adic
valuation. -/
@[simp]
lemma intValuationDef_integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) (a : R) :
    (integerPrimeOverOfNotMem K S hv).intValuationDef (algebraMap R (S.integer K) a)
      = v.intValuationDef a := by
  -- The prime-power chains `v ^ k` and `Pᵥ ^ k` have matching membership, so the two
  -- factorisation counts agree, and each valuation is `exp` of minus its count.
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hfa : algebraMap R (S.integer K) a ≠ 0 := fun h ↦ ha
    (FaithfulSMul.algebraMap_injective R (S.integer K)
      (h.trans (map_zero (algebraMap R (S.integer K))).symm))
  have hmem (k : ℕ) : a ∈ v.asIdeal ^ k ↔
      algebraMap R (S.integer K) a ∈ (integerPrimeOverOfNotMem K S hv).asIdeal ^ k := by
    rw [integerPrimeOverOfNotMem_asIdeal, ← Ideal.map_pow, ← Ideal.mem_comap,
      integer_comap_map_pow K S hv]
  suffices h : Associates.count (Associates.mk (integerPrimeOverOfNotMem K S hv).asIdeal)
        (Associates.mk (Ideal.span {algebraMap R (S.integer K) a})).factors =
      Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {a})).factors by
    rw [v.intValuationDef_if_neg ha,
      (integerPrimeOverOfNotMem K S hv).intValuationDef_if_neg hfa, h]
  refine Nat.le_antisymm ?_ ?_
  · exact (le_count_iff_mem_pow v ha _).mpr
      ((hmem _).mpr ((le_count_iff_mem_pow (integerPrimeOverOfNotMem K S hv) hfa _).mp le_rfl))
  · exact (le_count_iff_mem_pow (integerPrimeOverOfNotMem K S hv) hfa _).mpr
      ((hmem _).mp ((le_count_iff_mem_pow v ha _).mp le_rfl))

/-- **The correspondence preserves valuations**: the valuation of `𝒪_S` at the prime above `v` is
the valuation of `R` at `v`. -/
@[simp]
lemma valuation_integerHeightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S}) (x : K) :
    (integerHeightOneSpectrumEquiv K S v).valuation K x
      = (v : HeightOneSpectrum R).valuation K x := by
  have hR (a : R) : (integerHeightOneSpectrumEquiv K S v).valuation K (algebraMap R K a)
      = (v : HeightOneSpectrum R).valuation K (algebraMap R K a) := by
    have e1 : (integerHeightOneSpectrumEquiv K S v).valuation K (algebraMap R K a)
        = (integerPrimeOverOfNotMem K S v.property).intValuationDef
            (algebraMap R (S.integer K) a) := by
      rw [IsScalarTower.algebraMap_apply R (S.integer K) K a,
        HeightOneSpectrum.valuation_of_algebraMap]
      rfl
    rw [e1, intValuationDef_integerPrimeOverOfNotMem K S v.property a,
      HeightOneSpectrum.valuation_of_algebraMap]
    rfl
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, map_div₀, hR a, hR b]

end IsDedekindDomain

end
