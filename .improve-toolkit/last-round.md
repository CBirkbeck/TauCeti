# Last round — r650 (2026-09-12 09:16Z)

## Sweep four things, not three

`label` · `CI` · `board head_sha` · **`isDraft`**

r650: #6412 sat green for 64 minutes with **no scoreboard** because it was still a **draft**, while
its label read `awaiting-review` the whole time. **A label says what is wanted, not what is
reachable.** It was also formally step-4 drive-eligible — driving would have spent ~$16 reviewing a
draft and left the cause untouched. *Eligibility under a rule is not the rule's purpose being served.*

**Always finish step 5: open as draft → CI green → `gh pr ready <n>`.**

### The drive clock starts at `ready_for_review`, not at CI-green (r651, measured)

The pipeline's own latency from reviewable to first board: **#6093 46 min, #6406 64 min**. So step
4's hour must be counted from `max(CI-green, ready_for_review)` — otherwise a PR marked ready late
looks eligible immediately and a drive just reproduces the board the pipeline was about to post.

```
gh api repos/$R/issues/<n>/timeline --paginate \
  --jq '[.[]|select(.event=="ready_for_review")]|last|.created_at'
```

## Board

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | — | `ready-to-merge` | **Chris** — `MERGEABLE`/`BLOCKED` on human-owned `web/examples/Examples.lean` |
| **#6406** | `95298f1eb3` | green | `ready-to-merge` | nobody — 0 files outside `TauCeti/`, auto-merge eligible |
| **#6093** | `277fd5ee72` | green | `awaiting-review` | reviewer (board behind → pending) |
| **#6188** | `27465ef69e` | green | `awaiting-review` | reviewer (board behind → pending) |
| **#6412** | `360cdfc5b9` | green | `awaiting-review` | reviewer — **marked ready in r650** |
| **#6418** | `adcce97987` | building | — | me: **mark ready when green** |

## Settled — do not re-litigate

* **#6093** — five original findings all green. Keep `@[expose]` on `Function.fiberMap`; `Equiv.compFiberEquiv` must NOT have it; `fundamentalGroupEquivFiber_apply_coe` must NOT be `@[simp]`. `fiberMap_comp_apply` must NOT be `@[simp]` — `simpNF` rejects it (tested twice, r648); the bullet is contested with CI evidence.
* **#6188** — `api-design` and `reuse` green; semilinear `congrAut` accepted. `extendOfIsLattice` generalised to a domain + fraction field; `[IsDomain R]` deliberately absent (unused).
* **#6418** — `parallelns` and `slice` are one fact twice: `intCharacter_def` is `private` and stays. `intCharacter_eq_iff` stays because its `FDRep` args are **implicit**.

## Gate — 15 checks, **129 controls, 0 failed**

Fixed this session: `rootedin` (all proper suffixes, r643; shadowing judged from the *reference's*
stack, r648), `nsjump` (backticked prose is not a reference, r646; source set is `rem - add`, r649).

**Every new control must be run against the bug, not only against the fix.** r649 nearly shipped one
whose fixture mutation silently threw — it passed on empty input and read green.

**A check's scope is part of its answer**: `stalequal` reported 2 stale paths; the tree had **24** —
it only sees files whose *declarations* changed.

## Prospecting

Measure against a freshly fetched **`origin/main`**, never the checked-out branch (r648 ranked a
target that was already rooted on main). WHOLE rooting lane is exhausted: every WHOLE namespace is an
open PR, one of the 8 ABSENT traps, or a thin 1/1. Partial candidates left:
`ContRepresentation` 141/184, `Representation` 134/189, `AbelianVariety.Hom` 41/54,
`WeierstrassCurve` 26/27. Avoid `IsCoveringMap` 59/67 and `Deck.IsQuotientCoveringMap` 31/32 —
both overlap #6093.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`** until he confirms the cache. Gate on CI.
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump to `369aeb92f4`.
* #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile. No bare `git stash`. Never #5481.
Every PR body needs a standalone `Roadmap: none`.
