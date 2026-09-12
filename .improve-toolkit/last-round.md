# Last round — r672 (2026-09-12 18:12Z)

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

1. **Watch #6188 on `ec1a68d96`** — it is now a pure rooting of one file, so low risk. Its next
   board judges a PR with no conjugation API in it; `api-design` and `generality` should have no
   subject. If either re-fires *about `extendOfIsLattice`*, that is a new finding — read it fresh.
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
