# Last round — r679 (2026-09-12 19:30Z)

## The contingency fired, and I had the merge wait wrong twice

**Read this before forming any theory about why a PR has not merged.**

r676 called the merge queue "jammed" on #6431. It was not — #6431 merged at **19:18:04Z**, mid-round.
Then, mid-r679, I reached for a second theory: seven non-`improve/*` PRs had merged while all four of
mine sat, so something must discriminate against `improve/*`. Also wrong — `roadmap/none` is on my
merged PRs too (#6406, #6412, #6418, #6426).

**What is actually true.** `tauceti-review-bot` enqueues on the `ready-to-merge` **label transition**;
the queue then merges strictly **FIFO by enqueue time**, one serialised worker at **~25–30 min per
merge**, **30+ deep**. Eight consecutive PRs confirm it, #6418 included. A label→merge latency of
**2.5–3.5 h is normal**. Position alone explains every wait:

```
pos=10  QUEUED  #6432     ~4–5 h out
pos=18  QUEUED  #6188     ~8–9 h out
```

**Both wrong theories came from reasoning over run lists and merge timestamps. The queue's own state
was one API call away. Query the queue; do not model it** — `tools/queuepos.py`, new this round.

## #6093 was silently ejected — and every field the sweep reads said "healthy"

```
15:43:28  added_to_merge_queue      tauceti-review-bot[bot]
18:54:20  removed_from_merge_queue  github-merge-queue[bot]    <- the instant #6422 merged
```

3h11m enqueued, **never one `merge_group` run**, no comment. Afterwards it still read
`label=ready-to-merge · CI=GREEN · board=ON-HEAD · isDraft=false · mergeable=MERGEABLE`. And because
the bot enqueues on the **label transition**, which had already fired at 15:43:18, **nothing was ever
going to put it back**.

**Acted** (r678 named staleness first suspect at **354 behind**): merged `origin/main` — **clean, zero
conflicts**, 354 → 0, PR diff unchanged at **25 files / +441 / −328**. Gated both heads against their
own bases to separate cause from history:

```
370dad05e vs c8637b9ae (pre-merge, old base) :  11 ok, 4 failed, 1 UNRUN
45812c5f8 vs origin/main  (post-merge)       :  11 ok, 4 failed, 1 UNRUN   <- same four
```

`decldiff`, `nsjump`, `rootsurplus`, `slice` are **pre-existing on a branch that already reached a
green 10/10 board** — body-answerable, not new breakage. Pushed `370dad05e → 45812c5f8`; the bot
relabelled `ready-to-merge` → **`awaiting-CI`** in 20 s. It is back in the pipeline and the next
`ready-to-merge` transition re-enqueues it. This cost a re-review of a 10/10 PR — the price r678
declined on an *uncertain* failure. It stopped being uncertain.

## The merge was vindicated — `sandboxed-build` went RED, and the cause was real

`FiberFunctor.lean:87` — **a file this PR does not touch**, which arrived on main in #6023 inside the
354 commits the branch was behind — still called `IsCoveringMap.fiberMap`, which this PR generalises
to `Function.fiberMap`. **So #6093 genuinely did not build against current main**, which is almost
certainly why the queue ejected it. A textual merge cannot see this: different files, no conflict.

**It did not error as `unknown identifier`.** `IsCoveringMap` is itself a *term of function type*, so
the dead reference silently re-read as generalized field notation — `Function.fiberMap IsCoveringMap …`
— and surfaced as an application type mismatch far from its cause.

**Where I was wrong earlier in this round.** I gated both heads, got `11 ok / 4 failed` on each, and
called the four "pre-existing, therefore body-answerable, not new breakage". Pre-existing was right;
**harmless was wrong.** Two of them were `NS-JUMP  IsCoveringMap.fiberMap became Function.fiberMap`,
pointing straight at the defect. It had simply not bitten, because on the old base no caller existed.
**Identical gate counts prove the merge introduced nothing; they do not make standing findings safe.**
A latent finding is one waiting for a caller, and merging `main` is what supplies callers.

Fixed with one identifier at `FiberFunctor.lean:87`, then swept the tree for the same trap on *every*
name this PR removes (`fiberMap{,_apply_coe,_id_apply,_comp_apply}`,
`homeomorphCompFiberEquiv{,_apply_coe,_symm_apply_coe,_monodromy}`, `Deck.IsQuotientCoveringMap.isRegular`)
— **0 other stale refs**. Pushed `45812c5f8 → 2231e763e`; PR now **26 files / +442 / −329**.

## New in the toolkit — `tools/ghostref.py` and `tools/queuepos.py` (139 controls, 0 failed)

**`ghostref.py`** closes the gap that let the above through. `stalequal` matches the **full** dead
path and prefilters on `TauCeti`, so a **short** reference never reaches its regex; `deadpath`
resolves properly but only inside the PR's **own** files. The uncovered shape is *short references,
in unchanged files, to names this PR removed* — visible only once main supplies a caller.

```
python3 tools/ghostref.py --base <merge-base> . <mathlib> <changed files>
```

It suppresses short forms that still resolve (repo root or Mathlib). Validated on real history:
`45812c5f8` → 1 ghost at `FiberFunctor.lean:87`; `2231e763e` → 0; `#6432` → 0. Now **check 3e2 in
`prepush.sh` (16 checks)**.

The fifth field `sweep.py` cannot see. `queue_verdict()` is pure and control-covered; both new
controls were mutation-tested and each bites on exactly its own mutation.

```
python3 tools/queuepos.py            # all open improve/* PRs
python3 tools/queuepos.py 6093 6188  # named
```

**`EJECTED` is the only actionable verdict** — it was in the queue and is no longer. `QUEUED:pos=30`
is not a problem however long it has sat. Exit 1 on any ejected PR.

**Its first live run caught its own bug**, worth keeping: it flagged **#5950** beside #6093, and told
me to refresh a PR this role must never touch. The two differ in enqueue history, not membership —
#6093 was `added_to_merge_queue` then `removed_from_merge_queue`; **#5950 has no queue events at
all**, because the bot could never enqueue it (human review on a human-owned file). So:

* **`EJECTED`** — enqueued, then dropped. **Mine:** refresh against `main`, re-gate, push.
* **`NEVER-QUEUED`** — no queue events ever. **Not mine:** the branch is not what is wrong.

Both fixture controls passed while the verdict was still wrong, because I had encoded only the case I
had just lived through. **A new check's first live run is part of writing it.**

## Board (19:30Z)

| PR | head | CI | label | queue | whose move |
|---|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **NEVER-QUEUED** | **Chris** — human-owned `web/examples/Examples.lean`; the bot cannot enqueue it. **Do not refresh it.** |
| **#6093** | `2231e763e` | building | `awaiting-CI` | re-entering | nobody — refreshed **and a real break fixed** |
| **#6188** | `ec1a68d96` | green | `ready-to-merge` | **pos 17** | nobody — **10/10**, waiting its turn |
| **#6432** | `98bb7e78f` | green | `ready-to-merge` | **pos 9** | nobody — **10/10**, waiting its turn |

## Next

1. **Run `tools/queuepos.py` every round, beside the sweep.** It is the only check that separates
   "waiting its turn" from "ejected and never coming back". **Act only on `EJECTED`** —
   `NEVER-QUEUED` (#5950) is not this role's to fix.
2. **Do not re-diagnose the merge wait a third time.** A deep queue position is the whole
   explanation.
3. **#6093: confirm `sandboxed-build` is green on `2231e763e` before anything else.** It went red on
   the merge (`FiberFunctor.lean:87`) and the fix is one identifier. If it is red again, read the
   log — do not assume it is the same cause.
   It was 10/10 before the merge, so **expect the board to return 10/10**; the PR now carries a 26th
   file, `FiberFunctor.lean`, which is a **required call-site update for the rename**, not scope
   creep. Say so in the body if `scope` asks. If `generality` re-raises `rootsurplus`/`slice`, those
   findings are pre-existing and were already accepted once.
4. **Do not touch #6188 or #6432.** Both 10/10 and queued. An unrequested edit costs a re-review and
   its queue position.
5. **When step 5 triggers** — open `improve/submonoid-constsmul-root`, **already pushed and
   gate-clean** (13 ok / 2 questions), as a **DRAFT**. Body must answer `parallelns` (the `Subgroup`
   instance stays nested — different namespace at 39/62) and `slice` (1 of 2 flagged, same reason).
   Mark ready when CI is green. Full evidence in HANDOVER §11.
6. **Re-run `nscand.py` after each merge** — main moved 759 → 735 → **678** across this watch, and the
   whole list moves with it.
7. **Read the tools list before writing a script.** `tools/` has 49: `sweep.py`, **`queuepos.py`**, **`ghostref.py`**,
   `threadread.py` (current findings per rubric — **use this, not jq**), `nscand.py` + `mathlibns.py`
   (prospecting), `prepush.sh` (the gate), `minecount.py`.

## Settled

* **#6418, #6412, #6426, #6406** — **MERGED.**
* **#6093** — 10/10 before the refresh; now re-reviewing on a current tree.
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
**139 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11 carries this watch's rules** — read it before re-deriving one.
