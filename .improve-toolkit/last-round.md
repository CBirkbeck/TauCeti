# Last round — r675 (2026-09-12 18:40Z)

## 🎉 #6188 is 10/10 — and the whole queue is green

`ec1a68d965` came back ten of ten, including the two rubrics that had no satisfiable head one round
earlier. They did not "clear" so much as **lose their subject**: with the conjugation API gone from
the diff there is no `autCongr` for `api-design` or `generality` to ask about, and what remains reads
as what it is — *"a single namespace-rooting refactor of four already-merged declarations"*.

**#6093 10/10 · #6188 10/10 · #6432 10/10**, plus #5950 (Chris's). **Nothing is owed on any PR.**

## When rubrics contradict each other across rounds, suspect the boundary

Five rounds of cross-firing between #6188 and #6432 — `scope` ⛔ removing what `api-design` asked
for, `generality` on each asking for the other's topic, `reuse` taking three positions on one
transport — and the resolution was not an argument on any thread. It was r672 removing `Congr.lean`
from #6188 so the two PRs stopped overlapping.

The evidence it was structural: #6188 went from four files and two topics to **one file, sixteen
lines**, and from three irreconcilable rubrics to ten green, **with no new argument posted**. The
findings were right every time; the PR boundary was wrong.

## Board (18:40Z) — four open, all green, none owing anything

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `ready-to-merge` | nobody — **10/10**, ~3h on the bot |
| **#6188** | `ec1a68d96` | green | (label lagging) | nobody — **10/10** |
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
4. #6093 has been 10/10 for ~3h against an observed cadence of 108 min / 2h / 2h20m. Nothing visible
   blocks it — `mergeable: UNKNOWN` is GitHub's lazy computation and it has zero files outside
   `TauCeti/`. **Note it; never merge it.**

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
