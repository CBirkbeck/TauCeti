# Last round — r686 (2026-09-12 21:07Z)

## #6432 MERGED · step 5 fired · #6482 opened as a draft

**#6432 merged at 21:06:37Z** — the fifth `improve/*` merge of this watch (#6406, #6426, #6412,
#6418, #6432). `lint-dot-notation` on main: **739 → 736**.

Step 5 fired (my open `improve/*` PRs dropped to two) and r685's corrected recipe ran in order:
refresh **6 behind → 0**, gate **14 ok / 2** (`parallelns`, `slice` — exactly the two the body
answers), push `595ce95af → a220f533d`, create.

**PR #6482** — draft, base `main`, `TauCeti/Topology/Algebra/ConstMulAction.lean` only, **+5/−9**,
standalone `Roadmap: none`. Bot labelled it `roadmap/none,awaiting-CI` within the minute.

## ⚠️ FIRST ACTION: mark #6482 ready as soon as CI is green

```
gh pr ready 6482
```

A draft draws **no review**, whatever its label says — r650 lost 64 minutes to exactly this on #6412.
A CI watch on `a220f533d` was running when this round closed. If it went red, read the log: this
branch has never had a CI run, only the gate.

## Board (21:07Z)

| PR | head | CI | label | queue | whose move |
|---|---|---|---|---|---|
| **#6482** | `a220f533d` | building | `awaiting-CI` | — | **me — `gh pr ready` when green** |
| **#6093** | `36f3a07b9` | green | `awaiting-review` | — | nobody — being judged; board `2231e763ee` is BEHIND **by construction** |
| **#6188** | `ec1a68d965` | green | `ready-to-merge` | **pos 7** | nobody — 10/10, waiting its turn |
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **NEVER-QUEUED** | **Chris** — human-owned file; the bot cannot enqueue it. **Do not refresh it.** |

#6093's CI has been green since 20:38Z. Board band 46–64 min → ~21:24–21:42Z. **Do not drive**; step
4's clock has not run an hour.

## What r686 confirmed about staging work ahead

r685's catch was real and load-bearing. The fork-qualified `--head CBirkbeck:…` with explicit
`--repo`/`--base` is what opened #6482; the bare `--head improve/…` staged in r684 would have failed
at the one moment in the watch when step 5 was live. **Verify a staged artefact against something
real** — here, #6432's actual `head.repo`/`base.repo`.

Equally, refreshing *at* the moment beat refreshing speculatively: the branch had drifted **6 behind**
in the ~50 minutes since r681. Refreshing every intervening round would have been churn.

## Next

1. **`gh pr ready 6482`** once `sandboxed-build` is green. Then it draws a board in ~46–64 min.
2. **#6093**: wait for the board. `scope` is answered and six rubrics get judged on this head for the
   **first time** — a fresh 🟡 is a first verdict, not a regression. Run `threadread.py` and answer
   **LIVE** only; `NOT-RUN` text is from an older head.
3. **Do not touch #6188.** 10/10 and queued at pos 7; an edit costs a re-review and the position.
4. **Do not re-diagnose the merge wait.** One serialised FIFO worker, ~25–30 min/merge; position is
   the whole explanation. I got this wrong twice (r676, r679) by reasoning over run lists instead of
   querying the queue.
5. **Next prospecting target when step 5 fires again** — verified ROOT in Mathlib with `mathlibns.py`:
   ```
   ROOT     6  Representation.IsIrreducible   1/1 WHOLE  (1/5 of its file -> slice question)
   ROOT    14  Basis                          1/1 WHOLE  (1/12 of its file)
   ROOT    27  FDRep                          1/1 WHOLE  (1/12 of its file)
   ```
   **Five of the twelve WHOLE candidates are traps** — `Probability.Kernel`, `PDE.Continuous`,
   `PDE.ContinuousOn`, `Probability.AEStronglyMeasurable`, `Probability.MeasurableSet`,
   `BilinForm.IsAlt` name namespaces Mathlib does not have. **A WHOLE ratio does not settle a
   target.** Re-run `nscand.py` first — main moved again with #6432.
6. **Read the tools list before writing a script.** `tools/` has 49: `sweep.py`, `queuepos.py`,
   `ghostref.py`, `threadread.py` (**use this, not jq**), `nscand.py` + `mathlibns.py`, `prepush.sh`
   (the gate, **16 checks**), `minecount.py`.

## Settled

* **#6432, #6418, #6412, #6426, #6406** — **MERGED.** main 759 → **736** across this watch.
* **#6482** — new, draft, awaiting CI. Body answers `parallelns` (the `Subgroup` instance stays
  nested: `TauCeti.Subgroup` is **39 flagged of 62** across a 6-file subtree, so rooting one here is
  the arbitrary cut that blocked #5905 — **not** because Mathlib lacks `Subgroup`, which is root with
  1186 declarations) and `slice` (1 of the file's 2 flagged, same boundary).
* **#6093** — refreshed against main, a real break fixed (`FiberFunctor.lean:87`), `scope` answered by
  removing the two `compFiberEquiv` laws. Deferred on
  `handover/fiber-compfiberequiv-laws-deferred`.
* **#6188** — the `Lattice.lean` rooting **only**. Do not re-add the conjugation API: `scope` ⛔'d
  exactly that, and removing it is what made the PR green.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile — **including the dot-notation baseline**, which is
why renaming a flagged declaration is red unless it is rooted in the same commit.
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
Every PR body needs a standalone `Roadmap: none`.
**PRs here are CROSS-REPO** — head on `CBirkbeck/TauCeti`, base `TauCetiProject/TauCeti`. Always
`gh pr create --repo TauCetiProject/TauCeti --base main --head CBirkbeck:<branch>`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`, then **re-read to verify**.
**Pass an explicit `--limit` to every `gh` listing** — the defaults are 30 rows and truncate silently.
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
Verify a rooting target with `mathlibns.py`, never a grep; then **gate it**. **A WHOLE ratio does not
settle a target.**
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**142 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11–13 carry this watch's rules** — read them before re-deriving one.
