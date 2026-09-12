# Last round — r670 (2026-09-12 18:05Z)

## Nothing was owed — and with two PRs at 10/10, that is the finding

All four open PRs are green. #6093 and #6432 sit at **10/10 `ready-to-merge`** waiting on the bot;
#6188 went green on `cc5b861ca` (11202 jobs, `LINT-ENV: PASS`) with its board still on the previous
head; #5950 is Chris's. Step 5 needs fewer than three open; there are four. Step 4's clock has not
run out.

**Two PRs at 10/10 are exactly the state where an unrequested edit costs a re-review and risks a
green rubric.** The round's work went to the handover instead.

## HANDOVER.md §11 — what r654–r669 cost

Everything learned this watch lived only in `last-round.md`, which is rewritten every round, and in a
34 800-line ledger. **A rule that lives only in `last-round.md` survives one round.** §11 now carries
it, each rule pointing at the round that bought it:

* **the gate** — commit before gating (it reads HEAD); it is pure Python and cannot see docstring
  attachment, elaboration or simp-NF; re-run on the pristine head before believing a FAIL;
  `xsibling`'s false positive and why a crying-wolf check is worse than none;
* **the ratchet** — the baseline grandfathers by *declaration name*, so renaming a flagged
  declaration is red unless it is rooted in the same commit;
* **reading the review** — a ⛔ hides rubrics that never ran; a 🟡 behind a ⛔ may not survive; the
  pipeline *edits* findings in place; "tried and failed" is scoped to the position tried; verify a
  cited precedent; when a loop returns to a rejected position look for a sibling PR where it is
  approved; an answer can arrive as a finding rather than a reply;
* **Lean facts** — `@[expose]` is a claim about a reduction *path*; a definitional index mismatch is
  not the `HEq` trap; a goal printed unchanged means nothing fired; deleting a declaration means
  deleting what advertises it;
* **two PRs over one file** — port a fix the moment it is accepted anywhere, but a green PR is not a
  place to apply a lesson;
* **prospecting** — `nscand.py` ranks, `mathlibns.py` decides, then check Mathlib does not already
  have the name; re-rank after every merge. The scouted `TauCeti.Submonoid` target is written out in
  full so the next taker opens it without repeating the measurement.

## Board (18:05Z) — four open, all green

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `ready-to-merge` | nobody — **10/10**, ~2h20m on the bot |
| **#6188** | `cc5b861ca` | green | `awaiting-CI` | reviewer — board BEHIND |
| **#6432** | `98bb7e78f` | green | `ready-to-merge` | nobody — **10/10** |

**#6188's board is BEHIND. Do NOT re-fix.**

## Next

1. **#6188's board on `cc5b861ca`.** `documentation` was fixed; `api-design` (functorial lemmas) and
   `generality` (semilinear) were **contested r669 by quoting its own `scope` ⛔**. If either re-fires
   *with the reviewer explicitly asking for it there despite the block*, implement it — both replies
   committed to that in writing. Otherwise hold.
2. **When step 5 triggers** (#6093 and #6432 merging leaves #5950 + #6188 = two):
   `TauCeti.Submonoid` is scouted and verified — branch `improve/submonoid-constsmul-root` from a
   freshly fetched `origin/main`, root `instance continuousConstSMul` at
   `TauCeti/Topology/Algebra/ConstMulAction.lean:37` to `_root_.Submonoid.`, delete the then-empty
   `namespace Submonoid` wrapper, qualify the one reference in
   `TauCeti.Subgroup.continuousConstSMul`, keep `@[to_additive AddSubmonoid.continuousConstVAdd]`.
   Gate, open as a **DRAFT**, mark ready when CI is green. Full evidence in HANDOVER §11.
3. **Re-run `nscand.py` after each merge** — main moved 759 → 739 this watch and the WHOLE list moves
   with it.

## Settled — with the conditions attached

* **#6093** — **10/10.** `@[expose]` on `fundamentalGroupEquivFiber` removed, **and that is why**
  `_apply_coe` is not `@[simp]`.
* **#6418** — **MERGED.**
* **#6188** — the relocation alone. Transport is the **`private` extensional bridge**
  (`proof-quality` ✅). No structural lemmas, no functorial lemmas, not semilinear — all #6432's, per
  the `scope` ⛔.
* **#6432** — **10/10**: semilinear, rooted, renamed, owns the structural lemmas and call-site
  rewrites.

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
**Deleting a declaration means deleting what advertises it.**
**A green PR is not a place to apply a lesson.**
Verify a rooting target with `mathlibns.py`, never a grep, and check the name is not already there.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**133 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11 now carries this watch's rules** — read it before re-deriving one.
