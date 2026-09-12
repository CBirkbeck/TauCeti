# Last round — r664 (2026-09-12 15:55Z)

## ⚠ The gate reads `HEAD`. COMMIT BEFORE GATING.

#6432 went red on a rename `prepush` had just passed. Local `0 new`, CI `3 new`.

Every screen in `prepush.sh` is driven by `git diff "$BASE"...HEAD` or `git archive HEAD`. In r663 I
ran it **before committing**, so `lint-dot-notation` archived the previous commit — still holding the
old names — and reported on work that was not in it. The header even claimed it ran "against the
working tree".

**Fixed:** prepush now refuses outright on uncommitted `.lean` changes — the same rule as UNRUN, a
stale pass being worse than no pass. **Controls 131 → 133**, mutation-tested:

```
MUTATION (guard removed):
  PASS  prepush: a clean tree is not refused (r664)
  FAIL  prepush: refuses to gate an uncommitted .lean change (r664) -- missing: UNCOMMITTED
  132 passed, 1 failed
```

Every green before r664 was taken on a tree I had *usually*, but not provably, committed first.

## The dot-notation baseline keys on declaration NAME

r653 established that a **stale** baseline entry is harmless — removing a violation is fine. I
generalised that too far. **Adding a name is not the same as removing one:** renaming a
grandfathered declaration in place un-grandfathers it, and all three renamed declarations came back
as fresh findings with *"baseline entries no longer found"*.

Rooted, they are not flagged at all and the rename is free. So #6432's two `naming` bullets are
**coupled** — a fact about the ratchet, not a preference about ordering. The baseline is human-owned,
so regenerating is not available.

## #6432 reverted to green, coupling reported

Rename reverted (`ba59a9318`), `origin/main` merge kept. Reported on the `naming` thread with the CI
output, offering both routes explicitly — rebase onto #6188, or root-and-rename here in one commit —
and naming the cost of the second rather than hiding it. **A PR must not be left red while a
question is outstanding: revert first, ask second.**

## Board (15:55Z) — five open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `awaiting-author` | reviewer — one contested `api-design`, board ON-HEAD |
| **#6188** | `09242e46b` | green | `awaiting-review` | reviewer — board BEHIND |
| **#6418** | `5c73d4c54` | green | `ready-to-merge` | nobody — 10/10 |
| **#6432** | `ba59a9318` | building | `awaiting-CI` | reviewer — reverted to green, question on the thread |

**#6188's and #6432's boards are BEHIND. Do NOT re-fix.**

## Next

1. **Watch #6432's CI on `ba59a9318`** — it should return to the green it had at `f9bdb0a8b4`.
2. **#6188's board on `09242e46b`** — due since ~15:40 (pushed 15:07, band 32–67 min). If it has not
   arrived by ~16:15 with CI green, step 4 applies and a drive is justified:
   `uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review 6188 --reviewer codex --post`.
3. **#6093** — awaiting the answer to the `api-design` contest (posted 15:38). Everything else is
   ♻️ pending re-run. Do **not** restore `@[simp]` on `fundamentalGroupEquivFiber_apply_coe` alone.
4. **#6432** — do nothing until the `naming` thread answers; both routes are on the table and the
   choice is the reviewer's.
5. Five open, so step 5 does **not** trigger. When it does: `ContRepresentation` 141/184,
   `Representation` 134/189, `AbelianVariety.Hom` 41/54, `WeierstrassCurve` 26/27; avoid
   `IsCoveringMap` / `Deck.IsQuotientCoveringMap`. Measure against a **freshly fetched** `origin/main`.

## Settled — with the conditions attached

* **#6093** — `@[expose]` on `Function.fiberMap` **stays** (whole reduction path exposed through
  `Set.MapsTo.restrict`/`Subtype.map`). `@[expose]` on `fundamentalGroupEquivFiber` is **removed** by
  this PR at `api-design`'s request, **and that is why** `_apply_coe` is not `@[simp]` — coupled;
  `main` carries both, this PR carries neither. `compFiberEquiv` not exposed; `fiberMap_comp_apply`,
  `compFiberEquiv_trans` not `@[simp]`. `movedopens` clean.
* **#6188** — `toLinearEquiv_ofLinearEquiv` is `rfl`, via `ofLinearEquiv`, **not `@[simp]`**
  (simpNF, CI-proven r656). `congrAut` → `autCongr`. Structural `autCongr_apply` /
  `autCongr_symm_apply` added, also not `@[simp]`. Main merged.
* **#6418** — `isIntegral_char` deleted as an exact Mathlib duplicate; `intCharacter_eq_iff` rooted
  on cohesion. **10/10.**
* **#6432** — rename reverted; it is coupled to the relocation by the name-keyed baseline.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile — **including the dot-notation baseline**, which is
why a rename of a flagged declaration is red unless it is rooted in the same commit.
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
**COMMIT BEFORE GATING** — prepush reads HEAD and now refuses a dirty tree.
Before believing a gate FAIL is yours, re-run it on the **pristine head**.
A rubric that went green can go 🟡 again — re-read the board, never a remembered verdict.
Re-read a finding's text too; r663's #6432 rejection offered the fix I had assumed it refused.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**133 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
