# Last round — r681 (2026-09-12 20:21Z)

## #6093: `scope` ⛔ cleared by removing the subject — the #6188 move, again

The board came back on the refreshed head `2231e763e` and halted at **one** blocker:

```
✅ correctness   ✅ reuse   ⛔ scope   ▫️ everything else deferred (not yet run)
```

> `Equiv.compFiberEquiv_refl` and `Equiv.compFiberEquiv_trans` are genuinely new mathematical API
> bundled into a namespace/relocation refactor; the description explicitly claims "Roadmap: none."

Right, and the **same shape `scope` ⛔'d on #6188 in r675** — where removing the added lemmas is what
took the PR to 10/10. Implemented rather than argued: both theorems gone, plus the `Main declarations`
bullet, the overview sentence claiming a functoriality the file no longer states, and the `Z` variable
only `compFiberEquiv_trans` used. Nothing else referenced them; `stalequal`/`deadpath`/`ghostref` all
clean afterwards.

**Preserved on `handover/fiber-compfiberequiv-laws-deferred`**, and the PR body says so with a link —
*removing the subject is an answer provided the work lands somewhere, and you say where.* Pushed
`2231e763e → 36f3a07b9`, now **26 files / +423 / −329**. Gate unchanged at `12 ok / 4 failed`.

### Do NOT fix the `naming` finding yet

`threadread.py` still shows a `naming` thread asking to root two `IsQuotientCoveringMap` declarations.
It is dated **2026-09-09** and reads `absent` in the current board's states — it re-runs once `scope`
clears, against a tree seven revisions newer. Wait for the fresh verdict.

## Board (20:21Z)

| PR | head | CI | label | queue | whose move |
|---|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **NEVER-QUEUED** | **Chris** — human-owned file; the bot cannot enqueue it. **Do not refresh it.** |
| **#6093** | `36f3a07b9` | building | `awaiting-CI` | — | nobody — `scope` answered, awaiting the next board |
| **#6188** | `ec1a68d965` | green | `ready-to-merge` | **pos 14** | nobody — 10/10, waiting its turn |
| **#6432** | `98bb7e78f4` | green | `ready-to-merge` | **pos 6** | nobody — 10/10, waiting its turn |

#6432 **7 → 6**, #6188 **15 → 14**. No `improve/*` merge since #6418 — pure position.

**Step 4 was correctly a no-op.** #6093's CI had been green four minutes at sweep time; the pipeline
posted its own board nine minutes later, inside the 32–67 min band. Driving would have burned ~$16 to
reproduce a board already in flight.

## `improve/submonoid-constsmul-root` is now ready to open

It was scouted against much older main and sat **11 behind**. No PR on it, so refreshing cost no
review cycle: merged `origin/main` (clean, 0 behind), re-gated **14 ok / 2 failed** — the two being
the documented `parallelns` and `slice` questions — `ghostref` clean. Pushed `98d76ecb6 → 595ce95af`.

**When step 5 fires, open it as a DRAFT.** Body must answer `parallelns` (the `Subgroup` instance
stays nested — a different namespace at 39/62) and `slice` (1 of 2 flagged, same reason). Mark ready
when CI is green. Full evidence in HANDOVER §11.

## Verified candidate list for the target after that

Refreshed on current main and **checked against Mathlib with `mathlibns.py`** — never a grep (r511 was
wrong on five of six):

```
ROOT   517  Submonoid                      1/1   <- the prepared branch
ROOT     6  Representation.IsIrreducible   1/1   <- next target (1/5 of its file: slice question)
ROOT    14  Basis                          1/1   (1/12 of its file)
ROOT    27  FDRep                          1/1   (1/12 of its file)
ABSENT   0  Probability.Kernel · PDE.Continuous · PDE.ContinuousOn
ABSENT   0  Probability.AEStronglyMeasurable · Probability.MeasurableSet · BilinForm.IsAlt
```

**Five of the twelve WHOLE candidates are traps** — Mathlib has no such namespace, so rooting would
invent one. `Probability.Kernel` ranks 3/3 WHOLE on `nscand` *and* is named in `mathlibns.py`'s own
firing control as known-bad (`ProbabilityTheory.Kernel`). **Ratio does not settle a target.**

## Next

1. **#6093: wait for CI, then the board.** `scope` is answered. Expect the deferred rubrics to run for
   the first time — several have never been judged on this head, so a fresh 🟡 is normal, not a
   regression. The PR's 26th file, `FiberFunctor.lean`, is a **required call-site update for the
   rename**, not scope creep; say so if `scope` asks again.
2. **Run `tools/queuepos.py` beside the sweep.** Act only on **`EJECTED`**; `NEVER-QUEUED` (#5950) is
   not this role's to fix.
3. **Do not re-diagnose the merge wait.** One serialised FIFO worker, ~25–30 min/merge, 30+ deep;
   2.5–3.5 h label→merge is normal. I got this wrong twice (r676, r679) by reasoning over run lists
   instead of querying the queue.
4. **Do not touch #6188 or #6432.** Both 10/10 and queued; an edit costs a re-review and the position.
5. **`lint-dot-notation` on main is 739**, not 678 — 678 is #6093's head figure, i.e. what main reads
   after it merges. (r680's note had this wrong.)
6. **Read the tools list before writing a script.** `tools/` has 49: `sweep.py`, `queuepos.py`,
   `ghostref.py`, `threadread.py` (**use this, not jq**), `nscand.py` + `mathlibns.py`, `prepush.sh`
   (the gate, **16 checks**), `minecount.py`.

## Settled

* **#6418, #6412, #6426, #6406** — **MERGED.**
* **#6093** — refreshed against main, a real break fixed (`FiberFunctor.lean:87`), and `scope`
  answered by removing the two new laws. Deferred on
  `handover/fiber-compfiberequiv-laws-deferred`.
* **#6188** — the `Lattice.lean` rooting **only**. Do not re-add the conjugation API: `scope` ⛔'d
  exactly that, and removing it is what made the PR green.
* **#6432** — semilinear, rooted, renamed, owns the structural lemmas and call-site rewrites.
* **`improve/submonoid-constsmul-root`** — pushed, refreshed, gate-clean, **no PR**.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile — **including the dot-notation baseline**, which is
why renaming a flagged declaration is red unless it is rooted in the same commit.
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`, then **re-read to verify**.
**Pass an explicit `--limit` to every `gh` listing** — the defaults are 30 rows and truncate silently.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
**COMMIT BEFORE GATING** — prepush reads HEAD and refuses a dirty tree.
**`prepush.sh` takes a base argument.** To tell "my change broke it" from "main moved", re-gate the
pristine head against its **own** merge-base: `prepush.sh $(git merge-base <head> origin/main)`.
**Identical gate counts across a `main` merge prove the merge introduced nothing — they do NOT make
the standing findings safe.** A latent `nsjump`/`decldiff` finding is one waiting for a caller, and
merging `main` is what supplies callers. Re-read them against the newly arrived files.
**A removed declaration whose namespace is also a TERM does not announce its absence** — it re-reads
as generalized field notation and fails somewhere else entirely (#6093).
**A board finding dated before the current head may be `absent`, not live** — check the `states` map
in the `tauceti-meta:v1` payload before fixing it.
A rubric that went green can go 🟡 again; clearing a ⛔ reveals rubrics that never ran; and
**a 🟡 behind a ⛔ may not survive the next board — do not chase it**.
**When rubrics contradict each other across rounds, suspect the PR boundary before the rubrics.**
**When a rubric has no satisfiable head, removing the subject is an answer** — provided the work
lands somewhere, and you say where. Twice now: #6188 (r675) and #6093 (r681).
**Deleting a declaration means deleting what advertises it** — docstring bullets, overview prose, and
any `variable` only it used (`stalequal` catches the first, nothing catches the last).
**A green PR is not a place to apply a lesson** — but an *ejected* one is not green, whatever its
four sweep fields say.
Verify a rooting target with `mathlibns.py`, never a grep; then **gate it**. **A WHOLE ratio does not
settle a target** — five of twelve WHOLE candidates name a namespace Mathlib does not have.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**140 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11–13 carry this watch's rules** — read them before re-deriving one.
