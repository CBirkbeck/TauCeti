# Last round — r659 (2026-09-12 14:18Z)

## 🎉 #6426 MERGED — and the right move was to do nothing

Merged 14:07:54Z by `app/tauceti-review-bot` after ~108 minutes at 10/10 `ready-to-merge`. The delay
was cadence, not a block. **`mergeable: UNKNOWN` is GitHub computing lazily; a long green wait is not
a stuck PR — and merging is never ours.**

## An anonymous proof is an unusable argument

#6093 went red on r658's head. The log was read for the actual `##[error]` (r656's rule) — this time
it *was* the build, six elaboration errors, all in the two law proofs and none in the definition:

```
Fiber.lean:65:11: don't know how to synthesize implicit argument `h`
  @Subtype.map_id E (fun x_1 => x_1 ∈ p ⁻¹' {x}) (?m.22 …)
  ⊢ ∀ (a : E), a ∈ p ⁻¹' {x} → id a ∈ p ⁻¹' {x}
```

**The message contained its own fix.** Lean printed `Subtype.map id (?m.22 …)`, so it *had* unfolded
`fiberMap` — the `Set.MapsTo.restrict` restructure was fine. What it could not do was produce the
`MapsTo` proof, which lived anonymously inside the definition's body; the goal it printed *is* that
argument. Naming it as `Function.mapsTo_fiber` dissolved the problem and let all three laws cite the
generic lemmas, which is what `reuse` asked for. Pushed `606c70e0c`.

**If a generic law takes a side condition as an argument, that side condition must be a
declaration.**

## The gate cannot see docstring attachment

Inserting `mapsTo_fiber` anchored on `@[expose]\ndef fiberMap` put it *between* `fiberMap`'s
docstring and `fiberMap` — two docstrings in a row, `fiberMap` undocumented. **The 15-check gate
passed it unchanged**, because every check is pure Python and docstring attachment is a Lean-level
fact. `lint-env`'s docstring scan would have failed it in CI.

**Anchor an insertion on the docstring, never on the `def`.** A throwaway script that walks back from
each declaration over attribute/comment lines to a preceding `-/` catches this in seconds.

## An UNRUN row is a question nobody asked yet

`movedopens` had reported UNRUN on #6093's new file every single round. Run by hand at last, against
the merge-base `Monodromy/Functoriality.lean` (opens `CategoryTheory`, `unitInterval`) for both moved
blocks — `fiberMap` 56–89, `homeomorphCompFiberEquiv` 204–230:

```
0 resolve ONLY through one of those opens     (both blocks)
```

The r498 defect does not apply to this move. **UNRUN is not a pass.**

## Board (14:18Z) — six open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `606c70e0c` | building | `ci-failed`¹ | reviewer — elaboration fixed r659, board BEHIND |
| **#6188** | `94921c53a` | **green** | `awaiting-review` | reviewer — `LINT-ENV: PASS`, board BEHIND |
| **#6412** | `360cdfc5b9` | green | `ready-to-merge` | nobody — 10/10, awaiting the pipeline |
| **#6418** | `5c73d4c54` | building | `awaiting-review` | reviewer — board BEHIND |
| **#6432** | `f9bdb0a8b4` | green | `awaiting-author` | reviewer — both blockers contested r657 |

¹ `ci-failed` is stale: it describes `c450a5a1e9`, superseded by `606c70e0c`. **Read CI from the
check-runs API for the CURRENT head, never the label.**

**Boards on #6093, #6188 and #6418 are BEHIND. Do NOT re-fix.**

## Next

1. **Watch #6093's CI on `606c70e0c`.** If the `Subtype.map_id (h := …)` / `Subtype.map_comp`
   spellings still fail to elaborate, fall back to `Subtype.ext rfl` for those two laws (the form
   that compiled before r658) and **report the CI output on the `reuse` thread** — the definition
   going through `Set.MapsTo.restrict` is the substantive part of that finding and is already done.
2. Otherwise nothing is owed: every other PR is 10/10, awaiting re-review on a head its board has not
   seen, or contested.
3. Six `improve/*` PRs are open, so step 5 does **not** trigger (it needs fewer than 3). Do not
   prospect yet. When it does: `ContRepresentation` 141/184, `Representation` 134/189,
   `AbelianVariety.Hom` 41/54, `WeierstrassCurve` 26/27; avoid `IsCoveringMap` and
   `Deck.IsQuotientCoveringMap` (overlap #6093). Measure against a **freshly fetched** `origin/main`.
4. Sequencing: **#6188 lands → #6432 rebases (rooting + rename come free) →
   `handover/congraut-structural-deferred` opens as `autCongr_eq` / `autCongr_symm_eq`.**

## Settled — do not re-litigate

* **#6093** — keep `@[expose]` on `Function.fiberMap`; its reduction path is exposed all the way down
  (`Set.MapsTo.restrict`, `Subtype.map` are both in `@[expose] public section`), and `Subtype.map`
  projects to `f x.1` without consulting the `MapsTo` proof. `compFiberEquiv` must NOT be exposed;
  `fundamentalGroupEquivFiber_apply_coe`, `fiberMap_comp_apply` and `compFiberEquiv_trans` must NOT
  be `@[simp]`. The conjugacy helper assumes **no connectedness**, only `hj : Joined (h e₀) f₀`.
  `movedopens` is clean. `documentation` ✅.
* **#6188** — transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, public, `rfl`,
  via `ofLinearEquiv`, **deliberately NOT `@[simp]`** (simpNF, CI-confirmed). `congrAut` → `autCongr`.
* **#6418** — `isIntegral_char` deleted as an exact Mathlib duplicate; `intCharacter_eq_iff` rooted
  on cohesion grounds; only `private intCharacter_def` stays nested.
* **#6412** — roadmap line is in TauCetiRoadmap, out of reach. Contest accepted, 10/10.
* **#6432** — both blockers are #6188's work; contested on sequencing.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.
* **#6188 is ~204 commits behind main** — if it conflicts, merge main in and re-gate.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile (incl. `lint-baseline.txt` and the nolint
allowlist — the RATCHET message asking to delete 7 stale baseline lines is **not** mine to action).
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
Before believing a gate FAIL is yours, re-run it on the **pristine head**.
A rubric that went green can go 🟡 again — re-read the board, never a remembered verdict.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
