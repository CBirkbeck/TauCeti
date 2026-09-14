# `/cleanup` + `/mathlibable` pass — `TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean` (r705)

## Baseline (Phase 0)

* `lake build` — **not run**. This role's hard rule forbids it because the shared Mathlib cache is broken, and opening the file in the LSP would trigger the same build.
* `lean_diagnostic_messages` — n/a for the same reason. **CI is the compiler.**
* Gate (`prepush.sh`) after the edit: 12 ok, 0 failed, 0 UNRUN.

## Style audit (Phase 2)

* **A.1–A.7:** copyright present; module docstring present and detailed; the two imports are sorted; no section headers; 169 lines; no `set_option`; no `λ`, `$` or `push_neg`.
* **B (linter):** n/a, since no local build was run.
* **C (per declaration):** naming follows Mathlib's `discrim` family and the `Polynomial` namespace. All declarations are public with docstrings. `derivative_quadratic` is deliberately not `@[simp]`, because `simpNF` rejects it; the file says so.

## Mathlib search (Phase 5) — pinned `30a58f7`

* **Loogle `discrim`:** only Mathlib's equation-level API (`discrim_eq_sq_of_quadratic_eq_zero`, `quadratic_eq_zero_iff`, `exists_quadratic_eq_zero`, `discrim_eq_zero_iff`, …).
* **LeanSearch and LeanFinder:** `separable_def`, `separable_def'`, `separable_C_mul_X_pow_add_C_mul_X_add_C` (which needs `(n : R) = 0` and `IsUnit b`), and `Splits.of_natDegree_eq_two` / `Splits.of_degree_eq_two` (a quadratic with a root splits).
* **grep:**
  * `Polynomial.discr` exists, with `discr_of_degree_eq_two`.
  * No polynomial-level criterion relating separability or splitting to `discrim`.
  * No characteristic-2 form of `discrim`.

## Literature (Phase 3)

* **WebSearch ×3:** [Conrad, Separability](https://kconrad.math.uconn.edu/blurbs/galoistheory/separable1.pdf); [Conrad, Galois groups of cubics and quartics](https://kconrad.math.uconn.edu/blurbs/galoistheory/cubicquartic.pdf); [arXiv 1312.6612, Lemma 2.10](https://arxiv.org/pdf/1312.6612) (in characteristic 2, `x² − tx + n` is separable iff `t ≠ 0`); [Conrad, Artin–Schreier](https://kconrad.math.uconn.edu/blurbs/galoistheory/artinschreier.pdf).
* **gpt-6-astra** (via `codex exec`, 47k tokens), on the standard forms:
  * Separable iff `D ≠ 0` in every characteristic.
  * Splits iff there is a root.
  * Away from characteristic 2, splits iff `D` is a square. Counterexample in characteristic 2: `X² + X + 1` over `F₂`.
  * In characteristic 2 with `b ≠ 0`, splits iff `ac/b² ∈ ℘(k)`.
  * References: Milne, *Fields and Galois Theory* §1.7; Conrad, *Galois groups of cubics and quartics in all characteristics*, App. A.
* **gpt-6-astra, generality over a commutative ring:**
  * `IsUnit D` implies separable, with no hypothesis on `a`.
  * The converse needs `IsUnit a`, with reduction modulo maximal ideals. Counterexamples otherwise: `1 + aX²` with `a = t` in `ℚ[t]`, `a = ε` in `ℚ[ε]/(ε²)`, or `a = (1,0)` in `ℚ × ℚ`.
  * The splitting criteria extend when `a` is a unit, when `2` and `a` are units, and in characteristic 2 when `a` and `b` are units.
* **Local references:** n/a, no `.mathlib-quality/references/`.
* **nLab, Stacks, MathOverflow:** n/a. This is elementary field theory, already covered by Milne and Conrad.

## Verdicts (Phase 7)

| declaration | verdict | action |
|---|---|---|
| `discrim_eq_sq_of_two_eq_zero` | YES-add-as-is: no characteristic-2 form in Mathlib; a 2-line computation, named because it explains why the square criterion is vacuous in characteristic 2 | golfed: inlined the single-use `have` |
| `derivative_quadratic` | NO-composable (`simp` + `ring`) but kept: a documented helper, not simp-normal | none |
| `sq_derivative_quadratic_sub_mul_eq_C_discrim` | YES-add-as-is (Bézout identity, not in Mathlib) | docstring points at the new lemma |
| `separable_quadratic_iff_discrim_ne_zero` | YES in its field form, which is the textbook statement. The reverse direction was **YES-but-generalise-first** | **new `separable_quadratic_of_isUnit_discrim` over any `CommRing`**; the field direction is derived from it |
| `splits_quadratic_iff_exists_root` | YES-add-as-is at field level; Mathlib has only one direction | none |
| `splits_quadratic_iff_isSquare` | YES-add-as-is | none |
| `splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero` | YES-add-as-is (Conrad App. A) | none |

**Recorded, not implemented.** Each would be new mathematics, and there is no elaborator here.
* `IsUnit a →` (separable ↔ `IsUnit (discrim a b c)`) over commutative rings.
* The ring-level splitting criteria.
* A restatement via `Polynomial.discr`. This is BORDERLINE: the file deliberately uses `discrim` so that Mathlib's `discrim` API applies to its statements.

**Pre-screened and not chosen:** `Algebra/Group/Subgroup/Pointwise.lean`.
* Its conjugation laws are two-step specialisations: `map_one`/`one_smul`, `map_mul`/`mul_smul`, `map_inv`/`inv_smul_smul`.
* They are kept because `RepresentationTheory/Induction/Conjugate.lean` passes them as named `MulEquiv.subgroupCongr` equations in 12 places.
* `mem_conj_smul` pins the orientation that consumers rely on.
* The only `/cleanup` finding was `conj_inv_smul_smul := by rw [map_inv, inv_smul_smul]`.
