# ADS Layer 2.3 — the logarithmic-derivative coefficient identity (scoped r853)

## The target

Roadmap §2.3: "Prove support on prime powers **and the exact coefficient identity for the
logarithmic derivative** of an Euler product on its absolute-convergence half-plane."

`VonMangoldt.lean`'s own module docstring says the rest is deliberately deferred:

> This is the algebraic part of Layer 2.3. **The logarithmic-derivative identity named in that
> target additionally requires the Euler-product package of Layer 3**; this file supplies its
> coefficient and exact prime-power support in advance.

**#6233 is that Layer 3 piece.** So this unblocks the moment #6233 lands. STATUS.md agrees:
"Layer 2 is done except that 2.3 lacks the logarithmic-derivative coefficient identity."

## Shape

From #6233's `logDeriv_LSeries_eq_tsum_prime_pow`:

```
logDeriv (LSeries (normCoeff K χ)) s = ∑' (P, e), -(log N(P) * (χ(P)/N(P)^s)^(e+1))
```

and the summand at `A = P^(e+1)` is exactly `-idealTerm (vonMangoldtTransform χ) s A`:

* `MultiplicativeIdealWeight.vonMangoldtTransform_apply_prime_pow` gives
  `χ.toIdealArithmeticFunction.vonMangoldtTransform (P^n) = χ P ^ n * Real.log (absNorm P)` for
  `n > 0`;
* `N(P^(e+1)) = N(P)^(e+1)`, so `χ(A) Λ(A) / N(A)^s = log N(P) · (χ(P)/N(P)^s)^(e+1)`. ✔

Target statement (ideal-indexed first, then regroup):

```
logDeriv (LSeries (normCoeff K χ)) s = -∑' A : (Ideal (𝓞 K))⁰, idealTerm K (vonMangoldtTransform χ) s A
```

then `regroupByNorm : HasSum (idealTerm K f s) L → LSeriesHasSum (normCoeff K f) s L` lifts it to
the `LSeries` form a Tauberian consumer wants.

## The crux, and the vocabulary already in the repo

The reindexing is `(P, e) ↦ P^(e+1)`. **Do not hand-roll it.** `Counting.lean` already has the
destination's vocabulary:

* `IdealPrimePower K` — the subtype of prime-power ideals;
* `primePowerBase`, `primePowerExponent`, `primePowerBase_pow_primePowerExponent`;
* `primePowerExponent_pos`, `primePowerBase_asIdeal_eq` (uniqueness of the base);
* `IdealPrimePower.ofPrime`, `primePowerBase_ofPrime`.

**No `Equiv` between `IdealPrimePower K` and `HeightOneSpectrum (𝓞 K) × ℕ` exists** — checked
`git grep IdealPrimePower ... | grep -iE 'equiv|bij|tsum|Summable'`, empty. That equiv (or a
direct `tsum` bijection) is the one genuinely missing piece. Note it would have exactly one
caller, so weigh [[name-the-caller-before-authoring]]: prefer proving the tsum identity with
`Function.Injective.tsum_eq`/`tsum_eq_tsum_of_ne_zero_bij` over introducing a named `Equiv`,
unless a second consumer shows up.

## Three steps

1. reindex the prime-power tsum as the ideal-indexed tsum of the transform (support: the transform
   vanishes off prime powers, `vonMangoldtTransform_ne_zero_iff`);
2. summability of the ideal-indexed family on the half-plane;
3. `regroupByNorm` to the `LSeries` form.

## Blocking

Stacked on **#6233**. Parent line required; open as a draft until #6233 merges.

---

## r854 update: the crux is a Mathlib API port, and it is standalone

**Correction to the r853 note.** I wrote that the reindexing "would have exactly one caller, so
prefer an injection lemma over a named `Equiv`". That was wrong, and reading Mathlib's own
treatment of the ℕ case is what showed it. `Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean`
proves the analogous logarithmic-derivative identity with a three-lemma pattern:

* `Nat.Primes.prodNatEquiv : Nat.Primes × ℕ ≃ {n // IsPrimePow n}` (`Data/Nat/Factorization/PrimePow.lean:152`)
* `tsum_primes_pow_eq` — `∑' (p) (k), f (p^(k+1)) = ∑' n : {n // IsPrimePow n}, f n`
* `tsum_eq_tsum_primes_of_support_subset_prime_powers` — drops to all of `ℕ`

So the ideal analogue is **a port of an existing Mathlib API**, not a helper invented to shorten one
proof, and it has callers on `main` already: `EulerProduct/Logarithm.lean:80,94` both sum over
`HeightOneSpectrum (𝓞 K) × ℕ`, as does #6233.

**It also does not depend on #6233** — pure indexing over ideals. So it is a standalone PR, and
Layer 2.3's identity then stacks on it plus #6233.

## VERIFIED r854 — `scratchpad/ads-idealprimepower-equiv-verified.lean`

```lean
def idealPrimePowerOf (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) : IdealPrimePower K
@[simp] coe_idealPrimePowerOf, primePowerBase_idealPrimePowerOf, primePowerExponent_idealPrimePowerOf
noncomputable def probeEquiv : HeightOneSpectrum (𝓞 K) × ℕ ≃ IdealPrimePower K
```

Builds clean. `left_inv` is `rintro ⟨P, k⟩; simp` once the three `@[simp]` lemmas are in place;
`right_inv` is `Subtype.ext (Subtype.ext ...)` + `Nat.sub_add_cancel (primePowerExponent_pos A)`.

**Gotcha that cost three builds:** `coe_idealPrimePowerOf := rfl` fails under plain
`public section` with *"Not a definitional equality … all definitions that need to be unfolded to
prove this theorem must be exposed"*. The probe needed `@[expose] public section`. `Counting.lean`
uses a plain `public section`, so **if this lands there, `idealPrimePowerOf` needs `@[expose]`**.

## Remaining for the PR

1. `tsum_primes_pow_eq` analogue (mirror Mathlib's two-line `calc` through the equiv);
2. the support-subset version;
3. placement: `Counting.lean` (751 lines, owns `IdealPrimePower` + both projections) vs a new file;
4. cleanup, receipt, PR body. `Roadmap: ArithmeticDirichletSeries`, no target marker (infrastructure).

---

## r856 update: the crux summand is VERIFIED; one small lemma is genuinely missing

Branch `chebotarev/logderiv-vonmangoldt` = #6233's branch + #6273 cherry-picked (two parents).

### VERIFIED — `scratchpad/ads-layer23-summand-verified.lean`

```lean
idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s (idealPrimePowerOf P k)
  = Complex.log (Ideal.absNorm P.asIdeal : ℂ) * (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ (k + 1)
```

i.e. **#6233's summand and the von Mangoldt ideal term are the same number.** Proof shape:

```lean
  have hpow : (idealPrimePowerOf P k : (Ideal (𝓞 K))⁰) = (⟨P.asIdeal, hmem⟩ : _) ^ (k + 1) :=
    Subtype.ext (by simp)
  rw [idealTerm_def, hpow, MultiplicativeIdealWeight.vonMangoldtTransform_apply_prime_pow _ hP k.succ_pos,
    SubmonoidClass.coe_pow, map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow]
  rw [hlog, Nat.succ_eq_add_one]   -- hlog : Complex.log ↑n = ↑(Real.log ↑n), via ofReal_natCast + ofReal_log
  ring
```

Two gotchas, both cost a build:
* `← Complex.ofReal_log` will **not** fire on `Complex.log ((n : ℕ) : ℂ)` — that coercion is ℕ→ℂ,
  not ℝ→ℂ. Bridge it with `← Complex.ofReal_natCast` first, in a separate `have`.
* `ring` does not identify `x ^ k.succ` with `x * x ^ k`; `Nat.succ_eq_add_one` first.

### The one missing piece

`summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re` (Regroup.lean:134) is exactly the right hook:

```lean
(h : s.re < s'.re) (hs : Summable (idealTerm K f s)) :
    Summable fun I ↦ Real.log (Ideal.absNorm I) * ‖idealTerm K f s' I‖
```

To compare against it I need `‖Λ(A)‖ ≤ Real.log (absNorm A)`. **TauCeti has `vonMangoldt_re_nonneg`
and `vonMangoldt_im` but no such bound** — Mathlib has `ArithmeticFunction.vonMangoldt_le_log` for
`ℕ`, so this is another port, and it belongs in `VonMangoldt.lean` beside `vonMangoldt_re_nonneg`.
Proof: on `P ^ k` it is `log N(P) ≤ log N(P ^ k) = k log N(P)` with `k ≥ 1`; off prime powers `Λ = 0`
and `log N(A) ≥ 0`.

### Remaining, in order

1. `norm_vonMangoldt_le_log` in `VonMangoldt.lean` (port of `vonMangoldt_le_log`);
2. `Summable (idealTerm K (vonMangoldtTransform χ) s)` by comparison, picking `s₀` between the
   abscissa and `s.re` exactly as #6233's `hasDerivAt_tsum_prime_pow` does;
3. support ⊆ prime powers, from `vonMangoldtTransform_ne_zero_iff`;
4. assemble with `tsum_eq_tsum_idealPrimePower_of_support_subset` (#6273) and
   `logDeriv_LSeries_eq_tsum_prime_pow` (#6233).

One PR, two files (`VonMangoldt.lean` + a new one), one topic. **Draft, parents #6233 and #6273.**

---

## r857: steps 1 and 2 of 4 are DONE and committed on `chebotarev/logderiv-vonmangoldt`

**Step 1 — committed.** `IdealArithmeticFunction.norm_vonMangoldt_le_log` in `VonMangoldt.lean`,
placed beside `vonMangoldt_re_nonneg`. Port of `ArithmeticFunction.vonMangoldt_le_log`.
Gotcha: the norm-of-an-`ofReal` lemma here is **`Complex.norm_real` then `Real.norm_eq_abs`** —
`Complex.norm_ofReal` does not exist and `RCLike.norm_ofReal` does not match the goal's shape.

**Step 2 — VERIFIED, `scratchpad/ads-layer23-summable-verified.lean`.**

```lean
theorem summable_idealTerm_vonMangoldtTransform {s : ℂ}
    (hs : idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    Summable (idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s)
```

Shape: take `y` between the abscissa and `s.re` exactly as #6233 does, feed
`summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`, and dominate. Two gotchas:

* that lemma's hypotheses must be passed **by name** (`(h := …) (hs := …)`) — naming `s`/`s'`
  shifts the positional arguments and `hy` lands in the `h` slot;
* `gcongr` gets stuck on `‖Λ A‖ * X ≤ log N(A) * X` (it closes one side and leaves
  `SeminormedAddGroup ?m`). Factor with an explicit `have` and use
  `mul_le_mul_of_nonneg_right` instead.

## Remaining: steps 3 and 4

3. `Function.support (idealTerm K (vonMangoldtTransform χ) s) ⊆ {A | IsPrimePow (A : Ideal (𝓞 K))}`
   — from `IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff` (`div_ne_zero_iff`).
4. Assemble: `logDeriv_LSeries_eq_tsum_prime_pow hs` (#6233), then
   `tsum_eq_tsum_idealPrimePower_of_support_subset` (#6273) with the verified summand identity,
   and `tsum_neg`.

Then cleanup, receipt, PR body: **draft, parents #6233 and #6273**, `Roadmap:
ArithmeticDirichletSeries`, no target marker unless it is judged to *be* Layer 2.3's statement —
it is, so this one **does** carry a marker. Destination file:
`.../EulerProduct/Logarithm/VonMangoldtCoeff.lean`.
