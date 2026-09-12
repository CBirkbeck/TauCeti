# Last round — r677 (2026-09-12 19:00Z)

## Check what the toolkit already has before writing a script

Every round of this watch read blocking findings with a scratchpad `board.py` plus ad-hoc
`gh api … | jq` per rubric. The toolkit ships **`tools/threadread.py`**, with a fixture and two
controls, and it does the job properly:

```
threadread.py <pr>         # only UNRESOLVED rubrics, with the current finding text
threadread.py <pr> --all   # every rubric, state taken from the board
```

It prints each rubric's **current** text with the `updated_at` that actually dates it, and flags
`(EDITED IN PLACE; created=…)` where they differ. Its docstring records the incident that produced
it — **r450** — which is the *same trap* I hit in r655 and wrote up as a fresh lesson. It was already
written down, in code, with controls.

**Use `threadread.py` from now on, not the jq.** Verified live: `threadread.py 6188` →
`0 shown (unresolved only); state from board at ec1a68d965`, correct for a 10/10 PR.

## Nothing owed

Four open, all green, all `ready-to-merge`, no new merges. Step 5 needs fewer than three. The merge
wait is r676's queue jam on **#6431**, a roadmap PR that is not ours — **do not re-diagnose it.**

## Board (19:00Z) — four open, all green, all `ready-to-merge`, none owing anything

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
   list moves with it.
3a. **Read the tools list before writing a script.** `tools/` has 47 of them:
   `sweep.py` (board sweep), `threadread.py` (current findings per rubric — **use this, not jq**),
   `nscand.py` + `mathlibns.py` (prospecting), `prepush.sh` (the gate), `minecount.py` (merge count).
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
