# Last round — r674 (2026-09-12 18:30Z)

## The sweep is a toolkit tool now, not a habit

It had run every round of this watch from a **scratchpad path under `/tmp`** — session-local, gone
when this session ends — while encoding two rules each learned from a wrong answer:

* **a superseded run is not a red build** (r653: it called #6188 `RED:label` on a cancelled duplicate
  while `sandboxed-build` was green and nothing had conclusion `failure`), and
* **the pipeline edits its scoreboard comment in place**, so sort by `updated_at` and compare
  `head_sha` to the PR head; BEHIND means the fix is already pushed.

Now `tools/sweep.py`, with those incidents in its docstring and the CI verdict factored into a pure
`ci_verdict(runs)` so it is testable without the network. **Controls 133 → 135**, mutation-tested:

```
MUTATION (latest-per-name collapsed to any-run):
  FAIL  sweep: a superseded cancelled run is not a red build (r653)
  PASS  sweep: a real failure, a pending run and a live cancel still read red/pending
  134 passed, 1 failed
```

Verified against the live board: identical verdicts to the scratchpad copy on all four PRs.
**The round prompt still calls the `/tmp` path — that copy still works; `tools/sweep.py` is the one
that survives the session.**

## Nothing else owed this round

All four open PRs are green. #6093 and #6432 at **10/10 `ready-to-merge`**; #6188 awaiting a board on
the restructured head; #5950 Chris's. Step 5 needs fewer than three open; there are four.

#6188's `ec1a68d96` went green at **18:25:45Z**, so its board is due 18:57–19:33 — step 4 checked
against the clock, not eyeballed.

Checked the two 10/10 PRs for a cause rather than assuming one: both read `mergeable: UNKNOWN` with
**zero files outside `TauCeti/`** and the `ready-to-merge` label — the identical state #6426, #6412
and #6418 were in before the bot took them. `UNKNOWN` is GitHub computing lazily, not a block.
#6093 has now waited ~3h against an observed cadence of 108 min / 2h / 2h20m: **note it, do not act
on it.**

---

(previous round, retained for its detail)

# r672 (2026-09-12 18:12Z)

## Removing the subject is a legitimate answer to a finding

#6188 had three rubrics with no satisfiable head: `scope` ⛔'d the API expansion and reads ✅ only
while it is out; `api-design` and `generality` asked for it back. r671 deferred one round in case
#6432 merged first and made the problem vanish on rebase — it did not (10/10, waiting on the bot),
and the board re-fired the same two, so the move came due.

**#6188 now changes one file**: `Algebra/Module/Lattice.lean`, rooting the four `extendOfIsLattice`
declarations. The three conjugation files are restored to `origin/main` exactly — the diff contains
no `congrAut`/`autCongr` line. Retitled `refactor(Algebra): root the LinearEquiv.extendOfIsLattice
API`; body and both threads say where the work went.

The gate confirms the shape: **`decldiff` ok — "every declaration change is a rooting" — and
`rootsurplus` ok**, both of which had failed for rounds on the rename pairs and the new lemmas.
13 ok / 2 questions; `lint-dot-notation` 739 → 735, 0 new.

This is not capitulation: the work is in **#6432, 10/10**, semilinear, carrying the structural
lemmas and the call-site rewrites.

## The two PRs are now disjoint

Between them they empty `TauCeti.LinearEquiv` — #6188 takes `Lattice.lean`'s four, #6432 takes the
three conjugation declarations — and neither depends on the other's merge order. Each carries an
`nsslice` HALF-ROOTED row naming the other's half; a gate question, answered in both bodies.

**Two PRs over one file keep drawing each other's findings until they stop overlapping.** Porting
fixes between them (r668) treated the symptom; this removes the cause.

## Board (18:12Z) — four open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `ready-to-merge` | nobody — **10/10**, ~2h35m on the bot |
| **#6188** | `ec1a68d96` | building | `awaiting-author` | reviewer — restructured r672, board BEHIND |
| **#6432** | `98bb7e78f` | green | `ready-to-merge` | nobody — **10/10** |

**#6188's board is BEHIND. Do NOT re-fix.**

## Next

1. **#6188's board on `ec1a68d96`** — the head is green (verified r673). The board judges a PR with
   no conjugation API in it, so `api-design` and `generality` should have no subject. If either
   re-fires *about `extendOfIsLattice`*, that is a new finding — read it fresh, do not reuse the
   old reply.
2. **When step 5 triggers** (two more merges): `improve/submonoid-constsmul-root` is **already
   pushed and gate-clean** (13 ok / 2 questions). Open it as a **DRAFT** with a body answering
   `parallelns` (the `Subgroup` instance stays nested — different namespace, 39/62 partial) and
   `slice` (1 of 2 flagged, same reason); mark ready when CI is green. Full evidence in HANDOVER §11.
3. **Re-run `nscand.py` after each merge** — main moved 759 → 735 across this watch.
4. If #6093 is still unmerged next round it will be ~3h at 10/10, well past the observed cadence
   (108 min, 2h, 2h20m). **Still never ours to merge** — note it, do not act on it.

## Settled — with the conditions attached

* **#6093** — **10/10.** `@[expose]` on `fundamentalGroupEquivFiber` removed, **and that is why**
  `_apply_coe` is not `@[simp]`.
* **#6418** — **MERGED.**
* **#6188** — now the `Lattice.lean` rooting **only**. Do not re-add the conjugation API: `scope`
  ⛔'d exactly that, and it is #6432's.
* **#6432** — **10/10**: semilinear, rooted, renamed, owns the structural lemmas and call-site
  rewrites. **Do not edit it** — green and waiting on the bot.
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
**When three rubrics have no satisfiable head, removing the subject is an answer** — provided the
work lands somewhere, and you say where.
**Deleting a declaration means deleting what advertises it**; a rooting destroys the old path
everywhere, docstrings included (`stalequal` catches it).
**A green PR is not a place to apply a lesson.**
Verify a rooting target with `mathlibns.py`, never a grep; then **gate it**.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**133 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11 carries this watch's rules** — read it before re-deriving one.
