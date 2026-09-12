# Last round — r658 (2026-09-12 14:02Z)

## `@[expose]` is a claim about a reduction *path*, not one declaration

`reuse` wanted `Function.fiberMap` built from `Set.MapsTo.restrict`. §6 says keep `@[expose]` on it —
but the real hazard was subtler than removing the attribute: `IsCoveringMap.fiberMap_monodromy` needs
`(fiberMap f hf x e : F)` to reduce to `f e` across a module boundary, and exposing *our* definition
helps only if every def its body routes through is exposed too. A non-exposed link stops the
reduction in the same place, with the attribute still sitting there looking correct.

Checked before touching it: `Mathlib/Data/Set/Operations.lean` and `Mathlib/Data/Subtype.lean` both
open `@[expose] public section`. Import closure (1438 modules) also confirmed no new import was
needed.

## A *definitional* index mismatch is not the `HEq` trap

`api-design` wanted identity and composition laws for `Equiv.compFiberEquiv`, and the two sides of
the composition law visibly have different types. That reads like §7's *"`HEq` is the only way
through a type-index mismatch"* — but here the differences are **definitional**: `⇑(h.trans k) ∘ p`
and `⇑k ∘ (⇑h ∘ p)` both reduce to `fun e ↦ k (h (p e))`, `(h.trans k).symm z` reduces to
`h.symm (k.symm z)`, and `⇑(Equiv.refl X) ∘ p` is `p` by eta.

**§7's rule is about indices differing *propositionally*.** When they differ only by unfolding, the
equation states and `Equiv.ext` + `Subtype.ext rfl` closes it. Reading "not syntactically equal" as
"needs `HEq`" would have contested two perfectly implementable lemmas.

## Re-read a PR body when the PR changes under it

#6093's body carried a section headed **"Build status: one proof outstanding"** saying the PR did not
compile. `sandboxed-build` is `success` on both recent heads — the proof was fixed rounds ago and the
body was never updated. It had been telling every reviewer the PR was broken. Two further stale
claims in the same body (`fiberMap`'s body, the lemma count) corrected.

**A PR body outlives the state it describes, exactly as a docstring outlives its review (§8).**

## Board (14:02Z)

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `c450a5a1e` | building | `awaiting-author` | reviewer — **both blockers fixed r658**, board BEHIND |
| **#6188** | `94921c53a` | building | `awaiting-CI` | reviewer — board BEHIND |
| **#6412** | `360cdfc5b9` | green | `ready-to-merge` | nobody — 10/10 |
| **#6418** | `5c73d4c54` | building | `awaiting-CI` | reviewer — board BEHIND |
| **#6426** | `54f8eb82b5` | green | `ready-to-merge` | nobody — 10/10, ~70 min unmerged; **pipeline's call, never mine** |
| **#6432** | `f9bdb0a8b4` | green | `awaiting-author` | reviewer — both blockers contested r657 |

**Boards on #6093, #6188 and #6418 are ALL BEHIND their heads. Do NOT re-fix any of them.**

## Next

1. **Nothing is owed.** Every PR is either 10/10, awaiting re-review on a head its board has not
   seen, or contested. The correct move on a round that finds this is to **wait, or prospect** —
   not to re-open settled findings.
2. Watch #6093 and #6188 CI: r658 and r654 both pushed proof-level changes written without a local
   toolchain (`Set.MapsTo.restrict` restructure; `Equiv.ext`/`Subtype.ext rfl` laws). If either goes
   red, **read the log for the `##[error]`** — r656's failure was `lint-env`, not the build.
3. If a round finds all boards current and nothing blocking, **prospect** (step 5). Partial
   candidates: `ContRepresentation` 141/184, `Representation` 134/189, `AbelianVariety.Hom` 41/54,
   `WeierstrassCurve` 26/27. Avoid `IsCoveringMap` and `Deck.IsQuotientCoveringMap` — both overlap
   #6093. Measure against a **freshly fetched** `origin/main`.
4. Sequencing that is load-bearing: **#6188 lands → #6432 rebases (rooting + rename come free) →
   `handover/congraut-structural-deferred` opens as `autCongr_eq` / `autCongr_symm_eq`.**

## Settled — do not re-litigate

* **#6093** — keep `@[expose]` on `Function.fiberMap` (and its reduction path is exposed all the way
  down); `compFiberEquiv` must NOT be exposed; `fundamentalGroupEquivFiber_apply_coe` and
  `fiberMap_comp_apply` must NOT be `@[simp]`; `compFiberEquiv_trans` is deliberately not `@[simp]`.
  The conjugacy helper assumes **no connectedness**, only `hj : Joined (h e₀) f₀`.
* **#6188** — transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, public,
  `rfl`, via `ofLinearEquiv`, **deliberately NOT `@[simp]`** (simpNF, CI-confirmed).
  `congrAut` → `autCongr`.
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
