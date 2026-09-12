# Last round — r680 (2026-09-12 19:58Z)

## #6093 is GREEN — `sandboxed-build: success` on `2231e763e` (20:02Z)

The r679 chain closed end to end: ejected → 354 behind → merged main (clean) → **red** at
`FiberFunctor.lean:87`, a file the PR never touched → one identifier fixed → **green**. The ejection
had a real cause and the refresh was right; r678 was also right to decline it while the failure was
uncertain. **The ordering is the rule: refresh a green PR only once `queuepos.py` says `EJECTED`.**

**Nothing is owed on it.** The pipeline re-reviews, relabels `ready-to-merge`, and *that label
transition* re-enqueues it — at the **back** of the queue, behind #6432 and #6188. That is the price
of the ejection and there is nothing to shortcut.

Expect the board to return **10/10** — it was 10/10 before the refresh. The PR now carries a **26th
file**, `FiberFunctor.lean`, which is a **required call-site update for the rename**, not scope
creep. Say exactly that if `scope` asks.

## Board (19:58Z)

| PR | head | CI | label | queue | whose move |
|---|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **NEVER-QUEUED** | **Chris** — human-owned `web/examples/Examples.lean`; the bot cannot enqueue it. **Do not refresh it.** |
| **#6093** | `2231e763e` | **green** | `awaiting-CI` | back of queue when relabelled | nobody — board `370dad05e` is BEHIND **by construction**, the fix is already pushed. **Do not re-fix.** |
| **#6188** | `ec1a68d965` | green | `ready-to-merge` | **pos 16** | nobody — 10/10, waiting its turn |
| **#6432** | `98bb7e78f4` | green | `ready-to-merge` | **pos 8** | nobody — 10/10, waiting its turn |

Queue draining on schedule: #6432 **9 → 8**, #6188 **17 → 16** since r679. No `improve/*` merge since
#6418 at 16:58:30Z, and that is **position, not a fault**. Steps 3, 4, 5 were no-ops.

## `queuepos.py` was under-reporting — a default, for the second round running

The bare run printed **2 of 4** PRs. `gh pr list` returns **30 rows by default**, and this repo has
30+ open PRs across `elliptic/`, `modular/`, `cft/`, `chebotarev/`, `adic/`. #6093 and #5950 — the two
oldest — fell off the end, quietly, as two rows of plausible output.

**This is the worst failure this particular tool could have**: a stranded PR is by definition an old
one, so it sits low in a default listing. The check written to catch silently-dropped PRs was
silently dropping the very PRs most likely to be stranded.

Fixed with an explicit `--limit 200` behind a pure `pr_list_cmd()`, plus a warning if the limit is
ever hit. Control + mutation test. **140 controls, 0 failed.**

r679's rule was *query the queue, do not model it*. The sharper version: **query it completely.** Two
rounds running the wrong answer came from a default I never chose — `gh run list` sampling, then
`gh pr list` paging. **Pass an explicit limit to every `gh` listing.**

## `ghostref` run against both queued PRs

r679's defect class only appears once `main` moves, and a queued PR is one nobody will look at again:

```
#6188   4 short forms, all still resolve              0 ghosts
#6432   3 removed, 3 chased across 5053 files         0 ghosts
```

Clean. Worth repeating on anything sitting in the queue while main moves under it.

## Next

1. **Check #6093's build first** (above).
2. **Run `tools/queuepos.py` beside the sweep every round.** Act only on **`EJECTED`** — enqueued,
   then dropped, which never returns on its own. **`NEVER-QUEUED` (#5950) is not this role's to fix.**
3. **Do not re-diagnose the merge wait.** One serialised FIFO worker, ~25–30 min per merge, 30+ deep;
   2.5–3.5 h label→merge is normal. Position is the whole explanation. I got this wrong twice in
   r676 and r679 by reasoning over run lists instead of querying the queue.
4. **Do not touch #6188 or #6432.** Both 10/10 and queued; an unrequested edit costs a re-review and
   its queue position.
5. **When step 5 triggers** — open `improve/submonoid-constsmul-root`, **already pushed and
   gate-clean** (13 ok / 2 questions), as a **DRAFT**. Body must answer `parallelns` (the `Subgroup`
   instance stays nested — different namespace at 39/62) and `slice` (1 of 2 flagged, same reason).
   Mark ready when CI is green. Full evidence in HANDOVER §11.
6. **Re-run `nscand.py` after each merge** — main moved 759 → 735 → **678** across this watch.
7. **Read the tools list before writing a script.** `tools/` has 49: `sweep.py`, `queuepos.py`,
   `ghostref.py`, `threadread.py` (current findings per rubric — **use this, not jq**), `nscand.py` +
   `mathlibns.py` (prospecting), `prepush.sh` (the gate, **16 checks**), `minecount.py`.

## Settled

* **#6418, #6412, #6426, #6406** — **MERGED.**
* **#6093** — refreshed against main (354 behind → 0) **and a real break fixed**: `FiberFunctor.lean`
  arrived on main in #6023 calling `IsCoveringMap.fiberMap`, which this PR generalises to
  `Function.fiberMap`. The branch genuinely did not build against current main.
* **#6188** — the `Lattice.lean` rooting **only**. Do not re-add the conjugation API: `scope` ⛔'d
  exactly that, and removing it is what made the PR green.
* **#6432** — semilinear, rooted, renamed, owns the structural lemmas and call-site rewrites.
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
**Pass an explicit `--limit` to every `gh` listing** — the defaults are 30 rows, and they truncate
without saying so.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
**COMMIT BEFORE GATING** — prepush reads HEAD and now refuses a dirty tree.
**`prepush.sh` takes a base argument.** To tell "my change broke it" from "main moved", re-gate the
pristine head against its **own** merge-base: `prepush.sh $(git merge-base <head> origin/main)`.
Before believing a gate FAIL is yours, re-run it on the **pristine head**.
**Identical gate counts across a `main` merge prove the merge introduced nothing — they do NOT make
the standing findings safe.** A latent `nsjump`/`decldiff` finding is one waiting for a caller, and
merging `main` is exactly what supplies callers. Re-read them against the newly arrived files.
**A removed declaration whose namespace is also a TERM does not announce its absence** — the
reference re-reads as generalized field notation and fails somewhere else entirely (#6093).
A rubric that went green can go 🟡 again; clearing a ⛔ reveals rubrics that never ran; and
**a 🟡 behind a ⛔ may not survive the next board — do not chase it**.
**When rubrics contradict each other across rounds, suspect the PR boundary before the rubrics.**
**When three rubrics have no satisfiable head, removing the subject is an answer** — provided the
work lands somewhere, and you say where.
**Deleting a declaration means deleting what advertises it** (`stalequal` catches it).
**A green PR is not a place to apply a lesson** — but an *ejected* one is not green, whatever its
four sweep fields say.
Verify a rooting target with `mathlibns.py`, never a grep; then **gate it**.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**140 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11–13 carry this watch's rules** — read them before re-deriving one.
