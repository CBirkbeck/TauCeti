# Last round — r691 (2026-09-14 11:40Z)

## ⚠️ FIRST: two CI results decide the next moves

1. **#6093 on `18e85bea2`** (merge of main + the `@[expose]` fix).
   * **Green** → reply in the `api-design` thread (root comment **3997635757**): `@[expose]` removed; the
     only consumer that needed `fiberMap`'s body, `fiberMap_monodromy`, now rewrites both fibre values
     into constructor form via `fiberMap_apply_coe` before `monodromy_eq_of_map_eq`, so the path
     endpoints match by projection; no new lemma was needed, and on main the original was never
     exposed. Then wait for the board.
   * **Red** → read the log. The two changes are the `h₁`/`h₂` rewrite in
     `Monodromy/Functoriality.lean` (coercion of `f e`, the `mapsTo_fiber` application) and any other
     cross-module consumer that silently needed the body — none was found by reading, but that was
     reading, not elaboration.
2. **#6796 on `06e8f7fdf`**. A background watch marks it ready when green. If it was not marked ready,
   check it: **a draft draws no review.**

## Board (11:40Z)

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#6093** | `18e85bea2` | building | `awaiting-author` | me after CI — reply to `api-design`; 9/10 green, `scope` ✅ |
| **#6796** | `06e8f7fdf` | building | draft | watch marks ready on green |
| **#5950** | `a64ba63667` | green | `ready-to-merge`, **NEVER-QUEUED** | **Chris** — human-owned file; do not refresh |

**Merged since r689:** #6188 (2026-09-12T22:35Z) and #6482 (2026-09-13T02:36Z). Seven `improve/*`
merges this watch. `lint-dot-notation` on main: **731**.

## What r691 did

* **Sweep blind spot fixed.** `sweep.py` listed 100 PRs repo-wide; there are 213; both `improve/*`
  PRs sat at index 197 and 202. It printed nothing for the whole gap. Now `--repo` + `--limit 1000` +
  a warning + a firing control; control and mutation test; **147 controls, 0 failed**.
* **#6093:** the r687 contest was read (`replies_through` = my reply's id) and `api-design` moved to a
  new, correct finding — the relocation had introduced `@[expose]` on `fiberMap`. Implemented; refreshed
  against main (188 behind → 0); body rewritten. Reply deferred until CI is green.
* **Step 5 → #6796**, rooting `Representation.IsIrreducible.nontrivial`. Body answers `slice` and
  `parallelns`.

## Next prospecting targets (re-run `nscand.py` first)

* `TauCeti.Basis.span_range_extendOfIsLattice` → **`Module.Basis`** (not `Basis`: `Lattice.lean` has
  `open Module`), 1/8 of its file — slice question.
* Skip `TauCeti.LinearEquiv.toLinearEquiv_generalLinearEquiv_symm` and `TauCeti.FDRep.intCharacter_def`:
  both **`private`**; the first is the #6188/#6432 bridge.
* Trap namespaces from r681 still apply: `Probability.Kernel`, `PDE.Continuous(On)`,
  `Probability.AEStronglyMeasurable`, `Probability.MeasurableSet`, `BilinForm.IsAlt` do not exist in
  Mathlib.

## Settled

* **Merged:** #6406, #6426, #6412, #6418, #6432, #6188, #6482.
* **#6093** — `scope` ✅ after removing the two `compFiberEquiv` laws (preserved on
  `handover/fiber-compfiberequiv-laws-deferred`); `naming` ✅; `documentation` ✅; `api-design` answered
  by removing `@[expose]`.
* **#6796** — open, draft, awaiting CI.

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
Verify a rooting target with `mathlibns.py`, never a grep; then **gate it**. **A WHOLE ratio does not
settle a target.**
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form —
**nor whether `to_additive` can derive a name it was given** (`toaddname.py` asks; only CI answers).
**A rooting can break an attribute whose own text never changed** (#6482).
**`stale` on a board means approved-earlier/re-run-pending, not a finding**; `absent` means not yet
judged on this head. `threadread.py` classifies both as NOT ACTIONABLE — answer **LIVE** only.
**147 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11–13 carry this watch's rules** — read them before re-deriving one.
