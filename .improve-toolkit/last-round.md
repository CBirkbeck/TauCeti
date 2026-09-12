# Last round — r655 (2026-09-12 13:25Z)

## Never cache a finding by its comment id — the pipeline edits in place

Comment `3996026629` on #6093 still reads `created_at 11:07:15Z`. In r653 its body was the ten-file
roadmap-narration finding; it now carries a completely different one (the conjugacy helper's stale
docstring). **Same id, same `created_at`, different finding.**

The handover's "read the board sorted by `updated_at`" rule is usually quoted about the scoreboard.
**It applies to the per-rubric threads too.** Re-read a thread's body before acting on what you
remember it saying.

## Both contests landed (2 for 2)

* **#6412 → 10/10 green.** `api-design` answered *"this clears the finding ✅"*. The finding was
  **factually correct** — the roadmap really did still name the deleted theorem — and cleared anyway
  because the fix lay in `TauCetiRoadmap`, human-controlled and unreachable from a `TauCeti/`-only
  branch. *A correct finding can still be the wrong PR's problem; say why, and say what survives.*
* **#6093** — the r653 scope contest held; the roadmap bullet stayed dropped.

## Before believing a gate FAIL is yours, run it on the pristine head

#6093 shows 4 `FAIL` + 1 `UNRUN`. All five are **byte-identical on the pristine head** — none is
mine. One command separates "pre-existing" from "I broke it" on a 19-file PR.

## Board (13:25Z)

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `9d13f95872` | building | `awaiting-author` | reviewer — **last rubric fixed r655**, board BEHIND |
| **#6188** | `2aaf5e818c` | building | `awaiting-CI` | reviewer — 4 rubrics fixed r654, board BEHIND |
| **#6412** | `360cdfc5b9` | green | → `ready-to-merge` | **nobody — 10/10 green, contest accepted 13:21Z** |
| **#6418** | `d20b665467` | green | `awaiting-review` | reviewer — ⛔ `reuse` fixed r653, board BEHIND |
| **#6426** | `54f8eb82b5` | green | `ready-to-merge` | **nobody — 10/10 green, 0 files outside `TauCeti/`** |
| **#6432** | `f9bdb0a8b4` | green | `awaiting-review` | reviewer — **no board at 57 min**; watch the 64-min edge |

**Boards on #6093, #6188 and #6418 are BEHIND their heads. Those fixes are pushed — do NOT re-fix.**

## ⚠ #6432 collides with the r654 rename

**#6432 is "state `congrAut` at the semilinear generality"** and r654 renamed `congrAut` →
`autCongr` on #6188. Both touch **only** `GeneralLinearGroup/Congr.lean`; #6432 branches from a
`main` with neither the rooting nor the rename, so its diff still says `def congrAut` nested in
`TauCeti.LinearEquiv`.

Whichever lands second needs a rebase. #6432 is smaller and already green, so expect **#6188 to be
rebased onto a semilinear `congrAut`, with the rename re-applied** — three declarations plus 35 call
sites across three files. Nothing is broken now and a conflict cannot merge silently; this is so the
rebase is expected, not discovered.

## Settled — do not re-litigate

* **#6093** — keep `@[expose]` on `Function.fiberMap`; `Equiv.compFiberEquiv` must NOT have it;
  `fundamentalGroupEquivFiber_apply_coe` and `fiberMap_comp_apply` must NOT be `@[simp]`. `naming`,
  `placement`, `api-design`, `generality` cleared. The conjugacy helper assumes **no connectedness** —
  only `hj : Joined (h e₀) f₀`; path-connectedness is how the comparison theorem supplies it.
* **#6188** — transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, public, `rfl`,
  phrased via `ofLinearEquiv`. `congrAut` is now `autCongr` / `autCongr_apply_apply` /
  `autCongr_symm_apply_apply`, verified against `AlgEquiv.autCongr` and `LinearEquiv.conj_apply(_apply)`.
* **#6412** — the roadmap line is in TauCetiRoadmap, out of reach. **Contest accepted.**
* **#6418** — `FDRep.isIntegral_char` deleted, not rooted: an exact duplicate of Mathlib's
  `FDRep.isIntegral_character`.

## Next

1. **Nothing is owed on any PR right now.** #6093, #6188, #6418 are all awaiting re-review on heads
   the boards have not seen. Resist re-fixing.
2. **#6432 is the one to watch** — green, no board, 57 min at 13:25Z. If it passes ~64 min with no
   board for `f9bdb0a8b4`, it is genuinely drive-eligible (counting from `ready_for_review`
   12:25:24Z). **`uvx` is not installed**, so a drive needs
   `curl -LsSf https://astral.sh/uv/install.sh | sh` first. The band is 32–64 min, measured.
3. If a round finds all boards current and nothing blocking, **prospect** (step 5): partial
   candidates are `ContRepresentation` 141/184, `Representation` 134/189, `AbelianVariety.Hom` 41/54,
   `WeierstrassCurve` 26/27. Avoid `IsCoveringMap` and `Deck.IsQuotientCoveringMap` — both overlap
   #6093. Measure against a freshly fetched `origin/main`.
4. `handover/congraut-structural-deferred` opens only **after #6188 lands**, and its
   `congrAut_eq`/`congrAut_symm_eq` must be renamed `autCongr_eq`/`autCongr_symm_eq` first.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* No `uv`/`uvx` — step-4 drives unavailable until installed.
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile. No bare `git stash`. Never #5481.
Never open a PR from `handover/improve-toolkit`. Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
