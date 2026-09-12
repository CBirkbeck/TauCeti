# Last round — r658 (2026-09-12 13:50Z)

## Clearing a ⛔ starts the rest of the review; it does not end it

#6418's ⛔ `reuse` went ✅ — the `FDRep.isIntegral_char` deletion was accepted. The other rubrics,
which a block had held at "not yet run", then ran and returned **four** 🟡 at once. That is the block
lifting, not a regression. **Expect a cleared block to be followed by more findings.**

All four were two facts in one file, and both are now fixed (`5c73d4c54`):

* The `FDRep.intCharacter` docstring closed by saying the definition sits in `TauCeti.FDRep`, has no
  dot notation, and is written `intCharacter V g`. **The rooting falsified all three in the commit
  that wrote them.** Cited by all four rubrics.
* `intCharacter_eq_iff` stayed nested. The body's argument was sound *and beside the point*: its
  `FDRep` args are implicit, so rooting enables no dot notation — but `api-design` and `placement`
  objected on **cohesion**, since it is the elimination principle for the rooted
  `FDRep.intCharacter`. Rooted, call site qualified (r389), `rootsurplus` answered in the body.

**An argument can be correct and still answer the wrong question.**

## A rubric that went green can go 🟡 again

#6093's `documentation` cleared on `9d13f95872` — but `reuse` **re-fired** with the
`Set.MapsTo.restrict` finding that r655 recorded as gone, and `api-design` returned with a *new*
one. r655's "stale work; do not start it" was true of the board it was written against and false two
rounds later. **Record a verdict with the head it was judged on, and re-read the board before acting
on a remembered one.**

## Board (13:50Z)

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `9d13f95872` | building | `awaiting-CI` | **me — 2 blockers, board ON-HEAD. Next unit.** |
| **#6188** | `94921c53a` | building | `awaiting-CI` | reviewer — board BEHIND, do NOT re-fix |
| **#6412** | `360cdfc5b9` | green | `ready-to-merge` | nobody — 10/10 |
| **#6418** | `5c73d4c54` | building | `review-in-progress` | reviewer — 4 rubrics fixed r657, board BEHIND |
| **#6426** | `54f8eb82b5` | green | `ready-to-merge` | nobody — 10/10, unmerged 83 min; **pipeline's call, never mine** |
| **#6432** | `f9bdb0a8b4` | green | `awaiting-author` | reviewer — both blockers contested r657 |

**Boards on #6188 and #6418 are BEHIND. Do NOT re-fix.**

## Next unit: #6093's two live blockers (board ON-HEAD `9d13f95872`)

* `reuse` — *"The new fibre API reimplements Mathlib's generic subtype-restriction machinery."*
  `Function.fiberMap` rebuilds `Set.MapsTo.restrict`/`Subtype.map`; wants it defined through
  `Set.MapsTo.restrict`, the coercion lemma via `Set.MapsTo.val_restrict_apply`, and the laws via
  `Subtype.map_id`/`Subtype.map_comp`.
* `api-design` — **new**: *"The generalized base-relabeling equivalence lacks the identity and
  composition lemmas."* That is `Homeomorph.compFiberEquiv`. Read the thread before acting.

`Fiber.lean` is created by this PR, so both are in scope — implement, don't contest. **Keep
`@[expose]` on `Function.fiberMap`** (§6, CI-tested) — the old `@[expose]` objection is cleared and
must not be reopened by the restructure. No local build: gate on CI.

## Settled — do not re-litigate

* **#6093** — keep `@[expose]` on `Function.fiberMap`; `compFiberEquiv` must NOT have it;
  `fundamentalGroupEquivFiber_apply_coe` and `fiberMap_comp_apply` must NOT be `@[simp]`. The
  conjugacy helper assumes **no connectedness**, only `hj : Joined (h e₀) f₀`. `documentation` ✅.
* **#6188** — transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, public,
  `rfl`, via `ofLinearEquiv`, **deliberately NOT `@[simp]`** (simpNF, CI-confirmed).
  `congrAut` → `autCongr`.
* **#6418** — `isIntegral_char` deleted as an exact Mathlib duplicate (⛔ cleared).
  `intCharacter_eq_iff` **is** rooted, on cohesion not dot notation. Only `private intCharacter_def`
  stays nested.
* **#6432** — both blockers are #6188's work; contested on sequencing, with the deferred branch
  verified to hold `congrAut_eq`/`congrAut_symm_eq` `_root_`-anchored and already semilinear.

## Sequencing that is now load-bearing

**#6188 lands → #6432 rebases (rooting + rename come free, keeping only the semilinear generality)
→ `handover/congraut-structural-deferred` opens as `autCongr_eq` / `autCongr_symm_eq`.**
The deferred lemmas cannot be added before the rooting: their first explicit argument is a
`LinearEquiv`, so nested they are new `lint-dot-notation` violations and the gate fails.

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
`uvx` is installed at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
Before believing a gate FAIL is yours, re-run it on the **pristine head**.
