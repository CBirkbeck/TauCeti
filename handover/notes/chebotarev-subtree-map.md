# Map of TauCeti/NumberTheory/Chebotarev/ (read r839, against origin/main)

Seven files, 52 declarations. I had worked this whole session in
`NumberField/Frobenius/` and `ArithmeticDirichletSeries/` without reading the area's own directory.

| file | decls | what it holds |
|---|---|---|
| `FrobeniusPrimeSet.lean` | 15 | `frobeniusPrimeSet`; membership as `artinSymbol 𝔭 = C`; proof-independence; `mem_..._mk_iff_exists_isArithFrobAt`; equivariance under `AlgEquiv.autCongr`; disjointness of distinct classes |
| `PrimeCounting/VonMangoldt.lean` | 28 | `frobeniusPrimePowerSet`, `frobeniusVonMangoldtCoeff`, `frobeniusPsi`, `frobeniusTheta`, and the ψ − θ comparison |
| `GaloisCharacter/Weight.lean` | 4 | the ideal weight of a Galois character, with a `badPrimes` API |
| `GaloisCharacter/Orthogonality.lean` | 2 | character orthogonality for that weight, and its vanishing on ramified primes |
| `RamifiedPrimes.lean` | 1 | `ramifiedPrimes` as a finite set — **this is Layer 8.3's subject** |
| `AuxiliaryPrime.lean` | 1 | `exists_auxiliaryPrime` |
| `TaggedFixedField.lean` | 1 | `fixedField_zpowers_isCyclotomicExtension` — Layer 9's tagged construction, not 8.2 |

## Layer 8.2's fibre count is ABSENT here, and this is where it belongs

Searched the subtree for `fixedField` (only `TaggedFixedField`, unrelated) and for
`centralizer`/`carrier` (the hits are *prime* carriers in the counting files, not conjugacy-class
carriers). Ran a declaration count per file as a control so the empty results are trustworthy.

So the roadmap's

    #G / (#C * f) = #Centralizer_G(σ) / f

fibre count is unwritten. Its inputs are now all on main or in flight:
* 8.2(2) — #6241 (residue degree as relIndex, degree-one iff membership);
* the group theory — `ConjClasses.card_carrier_mul_orderOf_dvd` and
  `card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf` (#5812, on main);
* the prime-set vocabulary — `frobeniusPrimeSet` and its `mem_..._iff_exists_isArithFrobAt`.

**Do not start it in `NumberField/Frobenius/`.** It is a statement about `frobeniusPrimeSet` fibres
and belongs beside them.

## r862 — 8.2's fixed-field bijection is PARENT-FREE. Both halves verified.

I had been treating **#6241 as a prerequisite** for the fibre count since r840. **It is not.**
`Ideal.inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt` — the `H = ⟨σ⟩` case — has been on
`main` since **#6164**. #6241 *generalises* it to an arbitrary subgroup, which is nicer but is not
what the fibre count needs.

So the bijection `Q ↦ Q ∩ 𝓞 (L^⟨σ⟩)` between the L-side Frobenius fibre and the E-side
degree-one fibre rests entirely on merged material:

| piece | source | status |
|---|---|---|
| forward: `f(𝔓/𝔭) = 1` | `inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt` (#6164) | merged |
| forward: relative Frobenius restricts to `σ` | `restrictScalars_eq_of_inertiaDeg_eq_one` (Tower.lean) | merged |
| injective | `eq_of_smul_eq_of_liesOver_under_fixedField` (#6201) + `IsArithFrobAt.mem_stabilizer` | merged, **verified r859** |
| surjective | `restrictScalars_eq_of_inertiaDeg_eq_one` + `exists_isArithFrobAt` | merged, **verified r862** |
| the *count* on top | `frobenius_fiber_card_mul_orderOf_eq_card_centralizer` | **#6269, open** |

VERIFIED r862 — `scratchpad/chebotarev-82-surjectivity-verified.lean`:

```lean
theorem isArithFrobAt_of_restrictScalars_eq (σ) (Q) (hQ : Q ≠ ⊥) [unramified]
    {τ : L ≃ₐ[↥(fixedField (Subgroup.zpowers σ))] L}
    (hτ : IsArithFrobAt (𝓞 ↥(fixedField (Subgroup.zpowers σ))) τ Q)
    (hf : (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1)
    (hres : AlgEquiv.restrictScalars K τ = σ) :
    IsArithFrobAt (𝓞 K) σ Q
```

Built first try. **This is the call site #6038's `reuse` block predicted** — it said to delete the
wrapper and "at the eventual call site apply `restrictScalars_eq_of_inertiaDeg_eq_one` …". It was
right, and this is that site.

**Plan: the bijection ships as a PR against `main` with no parents.** The count is then one line on
top of it once #6269 merges.
