/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# The height one spectrum of a ring of `S`-integers

Let `R` be a Dedekind domain with fraction field `K` and `S` a set of height-one primes of `R`.
`TauCeti/RingTheory/DedekindDomain/SInteger/Basic.lean` shows that the ring of `S`-integers is
again a Dedekind domain, so it has a height one spectrum of its own. This file identifies that
spectrum:
the primes of `𝒪_S` are exactly the primes of `R` **not** in `S`, via `v ↦ v · 𝒪_S`
(`integerHeightOneSpectrumEquiv`), and the correspondence carries the valuations across unchanged
(`valuation_integerHeightOneSpectrumEquiv`).

The two directions are `integerPrimeOverOfNotMem`, extending `v ∉ S` to `𝒪_S`, and
`integerPrimeUnder`, contracting a prime of `𝒪_S` back to `R`. That they are mutually inverse is
Mathlib's `Ideal.comap_map_eq_self_of_isMaximal` in one direction — the extension of a maximal
`v ∉ S` stays proper, so contracting it returns `v` — and `integer_map_comap_eq` — every ideal of
`𝒪_S` is extended — in the other.

The valuations transfer through Mathlib's `HeightOneSpectrum.valuation_liesOver`, which relates the
valuation at a prime to the valuation at the prime below it by the ramification index. Here that
index is `1` (`ramificationIdx'_integerPrimeOverOfNotMem`): the extended ideal *is* the prime
above, and a nonzero prime of a Dedekind domain does not lie in its own square. Both readings of
the transfer are supplied — `valuation_integerPrimeOverOfNotMem` for a prime of `R` avoiding `S`,
and `valuation_integerPrimeUnder` for an arbitrary prime of `𝒪_S`.

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
  -- of `𝒪_S` when `v ∉ S`.
  -- This is deliberately built by hand rather than pulled back from
  -- `IsLocalRing.maximalIdeal (v.valuation K).valuationSubring`: that comap needs an algebra map
  -- `𝒪_S → 𝒪_v`, and no such instance exists, because the inclusion holds precisely *because*
  -- `v ∉ S`. Supplying it is Stoll's `toSubring_le_valuationSubring`, which is not ported — and
  -- it is the same fact this proof establishes inline from `Set.mem_integer_iff`.
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
    -- membership of `𝔪` is by construction the valuation bound, so the `show` is the only step
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦
      show v.valuation K ((f a : S.integer K) : K) < 1 by
        rw [Subalgebra.coe_algebraMap]; exact (v.valuation_lt_one_iff_mem a).mpr ha
  intro htop
  -- if the extension were `⊤` then `1` would lie in `𝔪`, i.e. would have `v`-valuation `< 1`
  have h1 : v.valuation K ((1 : S.integer K) : K) < 1 := le_trans htop.ge hle Submodule.mem_top
  simp at h1

/-- For `v ∉ S`, the extension of `v` to `𝒪_S` is maximal. -/
lemma isMaximal_integer_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).IsMaximal := by
  set f := algebraMap R (S.integer K) with hf
  have := v.isMaximal
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (integer_map_asIdeal_ne_top K S hv)
  have hcle : v.asIdeal ≤ M.comap f :=
    (Ideal.comap_map_eq_self_of_isMaximal f (integer_map_asIdeal_ne_top K S hv)).ge.trans
      (Ideal.comap_mono hle)
  have hceq : M.comap f = v.asIdeal :=
    (v.isMaximal.eq_of_le (hM.isPrime.comap f).ne_top hcle).symm
  rwa [← integer_map_comap_eq K S M, hceq] at hM

/-- The prime of `𝒪_S` above a prime `v ∉ S` of `R`: the extension of `v`. -/
noncomputable def integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    HeightOneSpectrum (S.integer K) where
  asIdeal := Ideal.map (algebraMap R (S.integer K)) v.asIdeal
  isPrime := (isMaximal_integer_map_asIdeal K S hv).isPrime
  ne_bot := Ideal.map_ne_bot_of_ne_bot v.ne_bot

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
  left_inv v := Subtype.ext <| HeightOneSpectrum.ext <|
    have := (v : HeightOneSpectrum R).isMaximal
    Ideal.comap_map_eq_self_of_isMaximal _ (integer_map_asIdeal_ne_top K S v.property)
  right_inv P := HeightOneSpectrum.ext <| integer_map_comap_eq K S P.asIdeal

@[simp] lemma integerHeightOneSpectrumEquiv_apply (v : {v : HeightOneSpectrum R // v ∉ S}) :
    integerHeightOneSpectrumEquiv K S v = integerPrimeOverOfNotMem K S v.property := by
  simp only [integerHeightOneSpectrumEquiv, Equiv.coe_fn_mk]

@[simp] lemma integerHeightOneSpectrumEquiv_symm_apply_coe (P : HeightOneSpectrum (S.integer K)) :
    ((integerHeightOneSpectrumEquiv K S).symm P : HeightOneSpectrum R)
      = integerPrimeUnder K S P := by
  simp only [integerHeightOneSpectrumEquiv, Equiv.coe_fn_symm_mk]

/-- For `v ∉ S`, the prime of `𝒪_S` above `v` lies over `v`. -/
instance liesOver_integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (integerPrimeOverOfNotMem K S hv).asIdeal.LiesOver v.asIdeal where
  over := by
    have := v.isMaximal
    rw [Ideal.under, integerPrimeOverOfNotMem_asIdeal,
      Ideal.comap_map_eq_self_of_isMaximal _ (integer_map_asIdeal_ne_top K S hv)]

/-- **Inverting `S` is unramified away from `S`**: for `v ∉ S` the extension `R → 𝒪_S` has
ramification index `1` at the prime above `v`. The extended ideal *is* that prime, and a nonzero
prime of a Dedekind domain does not lie in its own square. -/
lemma ramificationIdx'_integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.ramificationIdx' v.asIdeal (integerPrimeOverOfNotMem K S hv).asIdeal = 1 := by
  have hle : Ideal.map (algebraMap R (S.integer K)) v.asIdeal
      ≤ (integerPrimeOverOfNotMem K S hv).asIdeal := le_of_eq (by simp)
  refine not_ne_iff.mp fun h => ?_
  rw [Ideal.ramificationIdx'_ne_one_iff hle, integerPrimeOverOfNotMem_asIdeal] at h
  exact absurd (lt_of_lt_of_le (Ideal.pow_lt_self _ (Ideal.map_ne_bot_of_ne_bot v.ne_bot)
    (integer_map_asIdeal_ne_top K S hv) 2 le_rfl) h) (lt_irrefl _)

/-- **The correspondence preserves valuations**: the valuation of `𝒪_S` at the prime above `v` is
the valuation of `R` at `v`. Mathlib's `valuation_liesOver` relates the two by the ramification
index, which is `1` here. -/
@[simp]
lemma valuation_integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) (x : K) :
    (integerPrimeOverOfNotMem K S hv).valuation K x = v.valuation K x := by
  have h := HeightOneSpectrum.valuation_liesOver (A := R) (B := S.integer K) K v
    (integerPrimeOverOfNotMem K S hv) x
  rwa [ramificationIdx'_integerPrimeOverOfNotMem K S hv, pow_one, Algebra.algebraMap_self,
    RingHom.id_apply, eq_comm] at h

/-- The correspondence preserves valuations, phrased through the equivalence. Not a `simp` lemma:
`integerHeightOneSpectrumEquiv_apply` rewrites the left-hand side to
`integerPrimeOverOfNotMem` first, so this form is never in normal form — the `simp` lemma is
`valuation_integerPrimeOverOfNotMem` above. -/
lemma valuation_integerHeightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S}) (x : K) :
    (integerHeightOneSpectrumEquiv K S v).valuation K x
      = (v : HeightOneSpectrum R).valuation K x := by
  rw [integerHeightOneSpectrumEquiv_apply, valuation_integerPrimeOverOfNotMem]

/-- **The correspondence preserves valuations, read downwards**: the valuation of `𝒪_S` at an
arbitrary prime `P` is the valuation of `R` at the prime under `P`. This is the form a consumer
holding a prime of `𝒪_S` — rather than one of `R` avoiding `S` — can apply directly. -/
@[simp]
lemma valuation_integerPrimeUnder (P : HeightOneSpectrum (S.integer K)) (x : K) :
    P.valuation K x = (integerPrimeUnder K S P).valuation K x := by
  have hP : integerPrimeOverOfNotMem K S (integerPrimeUnder_notMem K S P) = P :=
    HeightOneSpectrum.ext (integer_map_comap_eq K S P.asIdeal)
  calc P.valuation K x
      = (integerPrimeOverOfNotMem K S (integerPrimeUnder_notMem K S P)).valuation K x := by
        rw [hP]
    _ = (integerPrimeUnder K S P).valuation K x := valuation_integerPrimeOverOfNotMem K S _ x

end IsDedekindDomain

end
