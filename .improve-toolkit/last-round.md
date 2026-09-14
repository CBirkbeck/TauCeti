# Last round — r695 (2026-09-14T12:07Z)

## Board

| PR | head | CI | state | whose move |
|---|---|---|---|---|
| **#6093** | `18e85bea2` | **green** | **`awaiting-review`** since ~11:56Z | nobody — board for the `@[expose]` fix + reply 4004781516 is in flight |
| **#6796** | `06e8f7fdf` | **green** | **`awaiting-review`**, ready since 11:45:14Z | nobody — first board ~12:17–12:52Z; do not drive before 12:45Z |
| **#6800** | `716cf35ee` | building (status=in_progress conclusion=- started=2026-09-14T11:52:16Z) | draft, `awaiting-CI` | watch marks ready on green; if still a draft with green CI, `gh pr ready 6800` |
| **#5950** | `a64ba63667` | green | `ready-to-merge`, **NEVER-QUEUED** | **Chris** — do not refresh |

**Three `improve/*` PRs of mine are open → step 5 does not fire.** (#5950 is excluded from the count
since r686: it cannot advance, and counting it would stall prospecting indefinitely.)

## What to expect next

1. **#6093's board.** 9 rubrics were green on the previous head, and `api-design` is the only one that
   was blocking. The new head merged 188 commits of main, so expect every rubric to re-run. If
   `api-design` comes back green, the PR is done; if a rubric raises something new, read it fresh with
   `threadread.py` and answer **LIVE** only.
2. **#6796 and #6800** each draw a first board ~32–67 min after `ready_for_review`. Their bodies already
   answer `slice`/`parallelns` (#6796) and `decldiff`/`rootsurplus`/`slice` (#6800).
3. **Do not drive** any of them before `max(CI-green, ready_for_review)` + 1 h with no board.

## What r691–r692 did

* **`sweep.py` blind spot** (r691): listed 100 PRs repo-wide against 213 open; fixed, controlled, 147/0.
* **#6093** (r691–r692): the r687 contest was read; `api-design` moved to a correct new finding (the
  relocation had made `fiberMap` `@[expose]`); fixed without a new lemma; main merged (188 → 0); body
  rewritten; **green first try**; reply posted after green.
* **Step 5, twice:** #6796 (`Representation.IsIrreducible.nontrivial`, joining its already-rooted
  siblings) and #6800 (`Module.Basis.span_range_extendOfIsLattice`, beside Mathlib's own
  `Module.Basis.extendOfIsLattice`).

## Candidates for a later step 5

Re-run `nscand.py` first. Skip `TauCeti.LinearEquiv.toLinearEquiv_generalLinearEquiv_symm` and
`TauCeti.FDRep.intCharacter_def` (both `private`). The r681 trap namespaces still apply
(`Probability.Kernel`, `PDE.Continuous(On)`, `Probability.AEStronglyMeasurable`,
`Probability.MeasurableSet`, `BilinForm.IsAlt` do not exist in Mathlib). The partial namespaces in
`Lattice.lean` (`TauCeti.Submodule.IsLattice` 3/4, `TauCeti.Submodule` 5/20) are not whole — do not cut.

## Settled

* **Merged this watch:** #6406, #6426, #6412, #6418, #6432, #6188, #6482.
* **#6093** — `scope`, `naming`, `documentation` green; `api-design` answered. Deferred laws on
  `handover/fiber-compfiberequiv-laws-deferred`.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile — **including the dot-notation baseline**, which is
why renaming a flagged declaration is red unless it is rooted in the same commit.
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
**Backticks inside `-m "…"` are COMMAND SUBSTITUTION** — `git commit -m "…\`stale\`…"` silently
drops the word. Escape them (`\\\``) or pass the message with `-F file` (r687 lost one word this
way; every PR-branch commit survived only because they were escaped).
Every PR body needs a standalone `Roadmap: none`.
**PRs here are CROSS-REPO** — head on `CBirkbeck/TauCeti`, base `TauCetiProject/TauCeti`. Always
`gh pr create --repo TauCetiProject/TauCeti --base main --head CBirkbeck:<branch>`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`, then **re-read to verify**.
**Pass an explicit `--limit` to every `gh` listing** — the defaults are 30 rows and truncate silently.
`sweep.py` had it too (r691), at `--limit 100` repo-wide: 213 open PRs pushed both old `improve/*`
rows past the cut and the sweep printed **nothing**, exit 0. **An empty sweep is not an empty board.**
**A draft draws no review** however its label reads — `gh pr ready` the moment CI is green (r650).
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
**COMMIT BEFORE GATING** — prepush reads HEAD and refuses a dirty tree.
**`prepush.sh` takes a base argument.** To tell "my change broke it" from "main moved", re-gate the
pristine head against its **own** merge-base: `prepush.sh $(git merge-base <head> origin/main)`.
**Identical gate counts across a `main` merge prove the merge introduced nothing — they do NOT make
the standing findings safe.** A latent `nsjump`/`decldiff` finding is one waiting for a caller, and
merging `main` is what supplies callers.
**A removed declaration whose namespace is also a TERM does not announce its absence** — it re-reads
as generalized field notation and fails somewhere else entirely (#6093).
**A board finding dated before the current head may be `absent`, not live.** `threadread.py` now
classifies this: answer **LIVE** only; **NOT-RUN** is deferred behind the block.
**Control rows go to plain `grep`** — a bracketed pattern is a character class, and a negative
control asserting one passes for the wrong reason.
**Refresh a scouted branch AT the moment it is opened, not speculatively** — it drifts ~4–6 commits
an hour, so an early refresh is churn and a stale open is #6093's failure mode.
**Verify a staged artefact against something real before trusting it** (r685: the staged
`gh pr create` was wrong and only a real PR's `head.repo` showed it).
A rubric that went green can go 🟡 again; clearing a ⛔ reveals rubrics that never ran; and
**a 🟡 behind a ⛔ may not survive the next board — do not chase it**.
**When a rubric has no satisfiable head, removing the subject is an answer** — provided the work
lands somewhere, and you say where. Twice: #6188 (r675) and #6093 (r681).
**Deleting a declaration means deleting what advertises it** — docstring bullets, overview prose, and
any `variable` only it used.
**A green PR is not a place to apply a lesson** — but an *ejected* one is not green, whatever its
four sweep fields say. Act only on `queuepos.py` saying **`EJECTED`**; `NEVER-QUEUED` (#5950) is not
this role's to fix.
**A `private` declaration is not a rooting target** — no one outside can use the dot notation it
would enable (r691 skipped two). **`open Module` makes `Basis` mean `Module.Basis`** — check the
receiver's real head constant before trusting `mathlibns`'s count for the short name.
**`decldiff` and `rootsurplus` are blind to `open`** (r692): re-namespacing to the receiver's real
head, e.g. `TauCeti.Basis` → `Module.Basis` under `open Module`, reads as a non-rooting plus a
surplus. Correct anyway -- answer it in the body.
**A proof can be changed without an elaborator when the design is read off exact signatures** -- #6093's
`@[expose]` removal went green first try because `monodromy_eq_of_map_eq`'s `Γ : Quotient ex.1 ey`
was read, not guessed, and every cross-module consumer was read before the push.
Verify a rooting target with `mathlibns.py`, never a grep; then **gate it**. **A WHOLE ratio does not
settle a target.**
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form —
**nor whether `to_additive` can derive a name it was given** (`toaddname.py` asks; only CI answers).
**A rooting can break an attribute whose own text never changed** (#6482).
**`stale` on a board means approved-earlier/re-run-pending, not a finding**; `absent` means not yet
judged on this head. `threadread.py` classifies both as NOT ACTIONABLE — answer **LIVE** only.
**147 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11–13 carry this watch's rules** — read them before re-deriving one.
