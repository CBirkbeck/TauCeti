# Last round — r676 (2026-09-12 18:50Z)

## The "slow bot" is a merge queue, and it is jammed by a PR that is not mine

All four PRs are now `ready-to-merge` and **nothing is owed on any of them**. None has merged since
#6418 at 16:58:30Z. r673 and r675 wrote that off as the bot running past its cadence; chasing it
properly this round gave the mechanism:

* `main` is behind a GitHub **merge queue** (`merge-queue-main` ruleset) — which is what
  `finalize-merge-group-build` / `publish-merge-group-cache` in every PR's check-runs have been
  saying since the first sweep.
* Merges are **serialised**, each needing its own full merge-group build (~20 min). The "cadence" of
  108 min / 2h / 2h20m was queue latency, not a decision.
* `Auto-merge` is healthy — 200 runs over 39 min: **69 success**, 54 concurrency-cancelled, 2 failure.
* **The queue is jammed**: merge-group run `34711765109`, head
  `gh-readonly-queue/main/pr-6431-…`, 18:37:33Z, `sandboxed-build` **failure**.

**#6431 is not mine** — `roadmap/pathalgebra-acyclic-iff-worker1`, author `chrisromanmiller`, a
roadmap PR. Standing rule: *not yours: anything not under `improve/`*. Recorded, not touched.

### Two corrections worth keeping

* I nearly reported *"Auto-merge is broken, zero successes"* from a 40-run sample that landed
  entirely inside a burst of queued and cancelled runs. Widening to 200 showed 69 successes.
  **A sample of the last N of a high-rate stream is a sample of the last few seconds.**
* **"The bot is slow" was never a mechanism.** Three rounds recorded a number without asking what
  produced it, while the check-runs named the merge queue on every PR. **A number you cannot explain
  is an observation, not a finding.**

## Board (18:50Z) — four open, all green, all `ready-to-merge`, none owing anything

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `ready-to-merge` | nobody — **10/10**, ~3h on the bot |
| **#6188** | `ec1a68d96` | green | `ready-to-merge` | nobody — **10/10** |
| **#6432** | `98bb7e78f` | green | `ready-to-merge` | nobody — **10/10** |

## Next

1. **Do not touch any of the three 10/10 PRs.** An unrequested edit costs a re-review and risks a
   green rubric. If a board re-fires on one, read it fresh — but the expected event is a merge.
2. **When step 5 triggers** — three merges would leave only #5950 — open
   `improve/submonoid-constsmul-root`, **already pushed and gate-clean** (13 ok / 2 questions), as a
   **DRAFT**. Body must answer `parallelns` (the `Subgroup` instance stays nested — a different
   namespace at 39/62) and `slice` (1 of 2 flagged, same reason). Mark ready when CI is green.
   Full evidence in HANDOVER §11.
3. **Re-run `nscand.py` after each merge** — main moved 759 → 735 across this watch, and the WHOLE
   list moves with it. `tools/sweep.py` and `tools/nscand.py` are both in the toolkit now.
4. **Do not re-diagnose the merge wait.** It is a serialised merge queue whose current group failed
   on **#6431**, a roadmap PR that is not ours. Check `gh run list --limit 300 --json event,...`
   filtered to `merge_group` if you want the current state; otherwise leave it. Nothing about it is
   actionable by this role.

## Settled — with the conditions attached

* **#6093** — **10/10.** `@[expose]` on `fundamentalGroupEquivFiber` removed, **and that is why**
  `_apply_coe` is not `@[simp]`.
* **#6418** — **MERGED.**
* **#6188** — **10/10**, and it is the `Lattice.lean` rooting **only**. Do not re-add the conjugation
  API: `scope` ⛔'d exactly that, and removing it is what made the PR green.
* **#6432** — **10/10**: semilinear, rooted, renamed, owns the structural lemmas and call-site
  rewrites.
* **`improve/submonoid-constsmul-root`** — pushed, gate-clean, **no PR**.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile — **including the dot-notation baseline**, which is
why renaming a flagged declaration is red unless it is rooted in the same commit.
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
**COMMIT BEFORE GATING** — prepush reads HEAD and now refuses a dirty tree.
Before believing a gate FAIL is yours, re-run it on the **pristine head**.
A rubric that went green can go 🟡 again; clearing a ⛔ reveals rubrics that never ran; and
**a 🟡 behind a ⛔ may not survive the next board — do not chase it**.
**When rubrics contradict each other across rounds, suspect the PR boundary before the rubrics** —
two PRs editing one file keep drawing each other's findings until they stop overlapping.
**When three rubrics have no satisfiable head, removing the subject is an answer** — provided the
work lands somewhere, and you say where.
**Deleting a declaration means deleting what advertises it**; a rooting destroys the old path
everywhere, docstrings included (`stalequal` catches it).
**A green PR is not a place to apply a lesson.**
Verify a rooting target with `mathlibns.py`, never a grep; then **gate it**.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**135 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11 carries this watch's rules** — read it before re-deriving one.
