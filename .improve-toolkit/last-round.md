# Last round — r662 (2026-09-12 15:10Z)

## Check a cited precedent before implementing on its authority

#6188's `naming` wants `toLinearEquiv_ofLinearEquiv` moved to root `LinearEquiv` on the receiver
rule, citing `AlgEquiv.toLinearEquiv_ofLinearEquiv` as precedent. That precedent says the opposite:

```lean
namespace AlgEquiv
section OfLinearEquiv
variable (l : A₁ ≃ₗ[R] A₂) (map_one : …) (map_mul : …)
theorem toLinearEquiv_ofLinearEquiv : toLinearEquiv (ofLinearEquiv l map_one map_mul) = l := rfl
```

`l` is an **explicit** `variable`, so a `LinearEquiv` *is* the first explicit argument — and Mathlib
still puts the lemma in `AlgEquiv`, the namespace of `ofLinearEquiv`/`toLinearEquiv`. Contested with
that, plus the standing tension that `api-design` on this same PR is what asked for the declaration
to live in `LinearMap.GeneralLinearGroup`. The reply says what I will do if the conclusion stands.

**The cheapest verification available, and it inverted the conclusion.**

## Waiting a round to keep a failure attributable cost nothing

r661 refused to stack work on #6188 until the `origin/main` merge built. It came back **fully
green** — 11202 jobs, docstrings 9009/9009, `LINT-ENV: PASS` — so the #6426 conflict resolution is
confirmed on its own, and the structural lemmas went on top of a known-good base.

## The deferred branch is discharged — and the handover was one step too cautious

`autCongr_apply` / `autCongr_symm_apply` are in, ported from
`handover/congraut-structural-deferred` and adapted from its semilinear signature to this PR's
linear one. The handover said they could open "only after #6188 lands", because a new declaration
whose first explicit argument is a `LinearEquiv` is a fresh `lint-dot-notation` violation in an
un-rooted namespace. **But #6188 *is* the rooting, so inside it the namespace is already root and
the lemmas are legal.** #6188's own `api-design` asking for exactly them is what made that visible.

Neither is `@[simp]`: the pointwise `*_apply_apply` forms are the simp normal form and both
call-site files name them in their `simp` sets.

## Board (15:10Z) — six open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | building | `awaiting-CI` | reviewer — 9/10, board BEHIND |
| **#6188** | `09242e46b` | building | `awaiting-review` | reviewer — structural lemmas + merge, board BEHIND |
| **#6412** | `360cdfc5b9` | green | `ready-to-merge` | nobody — 10/10, waiting ~2h on the bot |
| **#6418** | `5c73d4c54` | green | `ready-to-merge` | nobody — 10/10 |
| **#6432** | `f9bdb0a8b4` | green | `awaiting-author` | gated on #6188 |

**Boards on #6093 and #6188 are BEHIND. Do NOT re-fix.**

## Next

1. **Watch #6093 on `370dad05e`** (the `Subtype.ext (compFiberEquiv_apply_coe …)` form). If it still
   fails, the RHS defeq (`Equiv.refl`/`Equiv.trans` application) is the suspect — fall back to
   `Equiv.ext fun e ↦ Subtype.ext <| by rw [compFiberEquiv_apply_coe]` and report the CI output.
2. **Watch #6188 on `09242e46b`.** The risky part is `autCongr_symm_apply`'s proof
   (`rw [MulEquiv.symm_apply_eq, autCongr_apply]; exact LinearEquiv.ext fun m ↦ by simp`) — ported
   from the deferred branch, where it was written against the *semilinear* signature. If it fails,
   the `by simp` is the first suspect (r661: a goal printed unchanged means nothing fired).
3. **#6188's remaining `api-design` bullet 1** — `@[simp]` on `toLinearEquiv_ofLinearEquiv`. r656
   proved via CI that it breaks `simpNF` on
   `UpperUnitriangular.congrLinearEquiv_pointsAction_eq_toLin`; the reviewer asks to restate *that*
   lemma first, in a file this PR does not touch. Already reported once with the CI output; if it
   re-fires, weigh a scope contest rather than repeating the report.
4. **#6432** stays gated on #6188 landing (rooting + rename come free on rebase).
5. Six open, so step 5 does **not** trigger. When it does: `ContRepresentation` 141/184,
   `Representation` 134/189, `AbelianVariety.Hom` 41/54, `WeierstrassCurve` 26/27; avoid
   `IsCoveringMap` / `Deck.IsQuotientCoveringMap`. Measure against a **freshly fetched** `origin/main`.

## Settled — do not re-litigate

* **#6093** — keep `@[expose]` on `Function.fiberMap`; `compFiberEquiv` must NOT be exposed;
  `fundamentalGroupEquivFiber_apply_coe`, `fiberMap_comp_apply`, `compFiberEquiv_trans` must NOT be
  `@[simp]`. `movedopens` clean. Conjugacy helper assumes **no connectedness**.
* **#6188** — transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, `rfl`, via
  `ofLinearEquiv`, **NOT `@[simp]`**. `congrAut` → `autCongr`. Structural `autCongr_apply` /
  `autCongr_symm_apply` added, also **not** `@[simp]`. Main merged; 0 behind.
* **#6418** — `isIntegral_char` deleted as an exact Mathlib duplicate; `intCharacter_eq_iff` rooted
  on cohesion. **10/10.**
* **#6412** — roadmap line is in TauCetiRoadmap, out of reach. Contest accepted. **10/10.**

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile (incl. `lint-baseline.txt` and the nolint
allowlist). No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
Before believing a gate FAIL is yours, re-run it on the **pristine head**.
A rubric that went green can go 🟡 again — re-read the board, never a remembered verdict.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**131 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
Run them after any toolkit edit, and mutation-test every new control.
