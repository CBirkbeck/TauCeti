# Last round — r663 (2026-09-12 15:40Z)

## 🎉 #6412 MERGED 15:11:20Z — second landing of this watch

Its last blocker was the `api-design` finding pointing at `TauCetiRoadmap`, contested in r653
because the fix lay in a human-controlled repo no `TauCeti/`-only branch can reach. Accepted in
r655, 10/10, merged. **A correct finding can still be the wrong PR's problem.**

## A "settled" note that records the conclusion but not the condition is a trap

#6093's new `api-design` asks to restore `@[simp]` on
`IsCoveringMap.fundamentalGroupEquivFiber_apply_coe`. My standing note said only *"must NOT be
`@[simp]`"* — right, but it hid *why*, and answering from it would have been unable to show the
reviewer anything. Checking instead:

* `origin/main` carries **both** `@[expose]` on the definition (line 108) **and** `@[simp]` on
  `_apply_coe` (line 143), and is green.
* This branch has **no `@[expose]` in that file at all** — its removal is what an earlier
  `api-design` finding demanded, and that finding now reads ✅.
* Commit `31512e3e` dropped the `@[simp]` after a red build: *"with `@[expose]` gone … the coercion
  lemma is provable by `simp only` from `…_apply`, so marking it `@[simp]` makes it a duplicate rule
  that never fires."*

Three consistent states: expose+simp (`main`), neither (this PR), simp-without-expose (CI-proven
red). The request is the third. Contested with all of it, offering to reinstate both if `api-design`
withdraws its earlier finding in the same breath.

**Record the condition with the conclusion, or the note cannot defend itself.**

## #6432's rejection was of *deferring*, not of sequencing

Re-read rather than remembered. The `naming` fix says *"Rebase onto #6188 **or** move all three
declarations to root `LinearEquiv` here"* and *"rebase onto that relocation **before merging**"* — the
rebase is offered as the fix; the objection is to leaving this head unfixed. Its second bullet asks
for exactly #6188's names.

Did the rename (`autCongr`, `autCongr_apply_apply`, `autCongr_symm_apply_apply`; 36 occurrences,
three files) plus a clean merge of `origin/main` (25 behind). Gate **10 ok, 0 failed**.
**The rename makes the two branches converge**: whichever lands second sees it as already applied
rather than as a conflict.

## Both risky proofs held

#6093 `370dad05e` and #6188 `09242e46b` are both fully green — builds, docstrings 100%,
`LINT-ENV: PASS`. #6188's ported `autCongr_symm_apply` (semilinear-authored, ending in `by simp`)
compiled, and the two new non-simp lemmas did not trip `simpNF`.

## Board (15:40Z) — five open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `awaiting-author` | reviewer — one contested rubric, board ON-HEAD |
| **#6188** | `09242e46b` | green | `awaiting-review` | reviewer — board BEHIND |
| **#6418** | `5c73d4c54` | green | `ready-to-merge` | nobody — 10/10 |
| **#6432** | `4e9891cab` | building | `awaiting-CI` | reviewer — renamed r663, board BEHIND |

**Boards on #6188 and #6432 are BEHIND. Do NOT re-fix.**

## Next

1. **Watch #6432's CI on `4e9891cab`** — a 36-occurrence rename plus a 25-commit merge, neither
   built locally.
2. **#6093** — everything but the contested `api-design` is ♻️ stale/re-run pending, so the next
   board should be close to green. If `api-design` re-fires on the same bullet, do **not** restore
   `@[simp]` alone; the CI-proven red is the answer, and the only implementable alternative is
   reinstating `@[expose]` too, which reverses a green finding.
3. **#6188** — remaining: `api-design` bullet 1 (`@[simp]` on `toLinearEquiv_ofLinearEquiv`, same
   coupled-annotation shape, r656 CI-proven) and `naming` (contested r662 on Mathlib's own
   `AlgEquiv.toLinearEquiv_ofLinearEquiv` precedent). Wait for the board on `09242e46b`.
4. **#6432** — the namespace bullet arrives by rebase when #6188 lands, unless the reviewer asks for
   the duplication; the reply offers it.
5. Five open, so step 5 does **not** trigger. When it does: `ContRepresentation` 141/184,
   `Representation` 134/189, `AbelianVariety.Hom` 41/54, `WeierstrassCurve` 26/27; avoid
   `IsCoveringMap` / `Deck.IsQuotientCoveringMap`. Measure against a **freshly fetched** `origin/main`.

## Settled — with the conditions attached

* **#6093** — `@[expose]` on `Function.fiberMap` **stays** (its whole reduction path is exposed
  down through `Set.MapsTo.restrict`/`Subtype.map`). `@[expose]` on `fundamentalGroupEquivFiber` is
  **removed** by this PR at `api-design`'s request, **and that is why** `_apply_coe` is not `@[simp]`
  — the two are coupled; `main` carries both, this PR carries neither.
  `compFiberEquiv` not exposed; `fiberMap_comp_apply`, `compFiberEquiv_trans` not `@[simp]`.
  `movedopens` clean. Conjugacy helper assumes **no connectedness**.
* **#6188** — transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, `rfl`, via
  `ofLinearEquiv`, **not `@[simp]`** (simpNF, CI-proven r656). `congrAut` → `autCongr`. Structural
  `autCongr_apply` / `autCongr_symm_apply` added, also not `@[simp]` — the pointwise forms are the
  normal form and both call-site files name them. Main merged.
* **#6418** — `isIntegral_char` deleted as an exact Mathlib duplicate; `intCharacter_eq_iff` rooted
  on cohesion. **10/10.**
* **#6432** — renamed to match #6188; namespace move deferred to the rebase.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile. No bare `git stash`. Never #5481.
Never open a PR from `handover/improve-toolkit`. Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
Before believing a gate FAIL is yours, re-run it on the **pristine head**.
A rubric that went green can go 🟡 again — re-read the board, never a remembered verdict.
**Re-read a finding's text too** — r663's #6432 rejection offered the fix I had assumed it refused.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**131 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
