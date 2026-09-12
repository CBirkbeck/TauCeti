# TauCeti improver — handover

Written 2026-09-12 by the outgoing improver (Claude Opus 5). Everything you need is either in this
file, in `.improve-toolkit/` on this branch, or on a `handover/*` branch of the fork.

**Branch:** `handover/improve-toolkit` on `github.com/CBirkbeck/TauCeti`. This branch is a delivery
vehicle — it carries `.improve-toolkit/`, which does not belong in `main`. **Never open a PR from
it.**

---

## 1. The role

You are the **TauCeti improver**: a self-directed worker that raises the quality of already-merged
Lean 4 code. You do not add mathematics. You root namespaces so dot notation works, delete
duplicates, weaken hypotheses, fix docstrings, and relocate misplaced declarations.

Work is judged by an AI review pipeline that posts a `tauceti-meta:v1` scoreboard on each PR and
merges it automatically once every rubric is green (for `TauCeti/`-only diffs with green CI).

---

## 2. Binding rules — these are not negotiable

* **NEVER merge or close a PR.** Never `--admin` merge. Landing is the pipeline's job.
* **Push to the `fork` remote (`CBirkbeck/TauCeti`), never `origin`** — origin returns 403.
* **THE SHARED MATHLIB CACHE IS BROKEN.** Do **not** run `lake build`, `lake exe cache get`, or
  `lake update`. Gate on CI instead. This holds until Chris says otherwise. If any build ever runs
  and prints `Built Mathlib.`, kill it immediately.
  *(I measured 0 missing oleans on 2026-09-11, but the prohibition is Chris's to lift, and he has
  not. Do not lift it yourself. It cost me ~10 blind CI cycles on one proof and I still did not
  override it.)*
* **One worktree only:** `~/GitHub/TauCeti/.claude/worktrees/improver-1`. Never another, never the
  rig root. On a new machine, create one worktree and stay in it.
* **Never touch `scripts/`, `.github/`, or the lakefile** — human-owned. Never write
  `scripts/lint-baseline.txt`.
* **Never open a PR or issue in TauCetiRoadmap.**
* **Never bare `git stash`** — the stash stack is shared across worktrees and other agents use it.
  Use `git stash push -u -m "<tag>"` then `apply <sha>`.
* **Not yours:** anything not under `improve/`, and **never #5481**.
* **No new mathematics.** Every PR body needs a standalone line `Roadmap: none`.
* Commit trailer: `Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>` plus a
  `Claude-Session:` line. PR bodies end with the 🤖 Generated with Claude Code line.

---

## 3. The round loop

Run this as a **10-minute cron**. Set it up with `/loop 10m <the prompt below>` or the `schedule`
skill. Mine was `3-59/10 * * * *` — deliberately off the `:00`/`:30` marks so it does not pile onto
the API with every other scheduled job.

The exact prompt I ran:

> Run the next TauCeti improve round. Worktree: `~/GitHub/TauCeti/.claude/worktrees/improver-1`
> (never another, never the rig root). Read `.mathlib-quality/improve/last-round.md` and the ledger
> tail first. Steps in order: (1) sweep the board — for EVERY open `improve/*` PR read its LABEL
> (awaiting-author / awaiting-review / ci-failed / ready-to-merge) **and `isDraft`**, plus the
> `tauceti-meta:v1` scoreboard sorted by `updated_at`; compare board `head_sha` to the PR head; if
> the board is behind, the fix is already pushed — do NOT re-fix. Read CI from the check-runs API,
> not labels. (2) poll merges with `--state merged --limit 200`. (3) fix or contest blocking
> findings on anything labelled `awaiting-author` or `ci-failed`. (4) re-drive a review only when a
> green build has sat an hour with no scoreboard for its head:
> `uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review <PR> --reviewer codex --post`.
> (5) if fewer than 3 `improve/*` PRs are open, prospect one target — branch `improve/<slug>` from
> `origin/main`, extract, gate with `tools/prepush.sh`, open as a draft, **mark ready when CI is
> green**. Then append the round to the ledger and rewrite `last-round.md`. NEVER merge or close a
> PR. Push to the fork remote, not origin (403). THE SHARED MATHLIB CACHE IS BROKEN: do not run
> `lake build` / `lake exe cache get` / `lake update` — gate on CI instead.

### Sweep four fields, not three

`label` · `CI (check-runs API)` · `board head_sha` · **`isDraft`**

A draft PR gets no review. I lost 64 minutes on #6412 because its label read `awaiting-review`
while it was still a draft. **A label says what is wanted, not what is reachable.**

### The drive clock starts at `ready_for_review`, not at CI-green

Measured pipeline latency from reviewable to first board: **#6093 46 min, #6406 64 min**. So count
step 4's hour from `max(CI-green, ready_for_review)`:

```bash
gh api repos/TauCetiProject/TauCeti/issues/<n>/timeline --paginate \
  --jq '[.[]|select(.event=="ready_for_review")]|last|.created_at'
```

Driving early costs ~$16 and reproduces a board the pipeline was about to post anyway.
**Eligibility under a rule is not the rule's purpose being served.**

---

## 4. Open PRs — state as of 2026-09-12 12:15Z

All CI green except #6432 (in flight). Fork branch = the `head` you push to.

| PR | branch | head | label | blocking rubrics | what it needs |
|---|---|---|---|---|---|
| **#5950** | `improve/bialghom-hopfalgebra-root` | `a64ba63667` | `ready-to-merge` | — | **Chris's.** `MERGEABLE` but `BLOCKED`: touches human-owned `web/examples/Examples.lean`. Leave it alone. |
| **#6093** | `improve/iscoveringmap-subtree-root` | `34ac589376` | `awaiting-author` | `api-design`, `documentation`, `reuse` | Read the board, fix or contest. Notes in §6. |
| **#6188** | `improve/linearequiv-root` | `36d148a8d9` | `awaiting-author` | `api-design`, `generality`, `naming`, `proof-quality`, `reuse` | Just narrowed to the rooting only after a `scope` ⛔. See §6 — I predicted these would re-fire. |
| **#6412** | `improve/dedup-tail-le-exchangeablesigma` | `360cdfc5b9` | `awaiting-author` | `api-design` | Deletes a duplicate alias. |
| **#6418** | `improve/fdrep-root` | `adcce97987` | `awaiting-author` | `reuse` | Roots 20 `FDRep` declarations. |
| **#6426** | `improve/lattice-fractionfield` | `54f8eb82b5` | marked ready 12:14Z | — | Awaiting first board. |
| **#6432** | `improve/congraut-semilinear` | `f9bdb0a8b4` | draft | — | **Mark ready when CI goes green.** |

Merged during my watch: **#6406** (`SheafOfModules.LocalGeneratorsData`), #6178, #6148.
`lint-dot-notation` on main went **994 → 741** over the session.

---

## 5. Prepared work waiting on GitHub

* **`handover/congraut-structural-deferred`** (fork) — carries `congrAut_eq` and `congrAut_symm_eq`,
  already written `_root_`-anchored with semilinear signatures. `api-design` asked for these on
  #6188. **They cannot be added while `TauCeti.LinearEquiv` is un-rooted**: their first explicit
  argument is a `LinearEquiv`, so in a nested namespace they create two new `lint-dot-notation`
  violations and the gate fails. **Open them as a PR only after #6188 lands.**
* **`improve/isquotientcoveringmap-root`** (fork) — **superseded and contrary. Do not open.** It
  roots `isCoveringMap_of_comp` (which #6093 already does) *and* the `private`
  `isEvenlyCovered_of_smul_disjoint`, which #6093 deliberately keeps nested on the reading `naming`
  accepted.
* The bench is otherwise **empty**. Future rounds must prospect fresh targets.

---

## 6. Per-PR context you will otherwise re-litigate

**#6093** — the five original findings are all green. Do **not** re-try any of these:
* Keep `@[expose]` on `Function.fiberMap`. Removing it breaks
  `IsCoveringMap.fiberMap_monodromy`, which needs the body across a module boundary.
* `Equiv.compFiberEquiv` must **NOT** have `@[expose]` — its consumer uses only the propositional
  `compFiberEquiv_apply_coe`.
* `fundamentalGroupEquivFiber_apply_coe` must **NOT** be `@[simp]` — `simpNF` proves it from
  `_apply` once `@[expose]` is gone.
* `fiberMap_comp_apply` must **NOT** be `@[simp]` — `simpNF` rejects it. **Tested twice.** The
  inline compatibility proof is the obstacle, not the spelling of the composite; generalising to
  `g ∘ f` did not change it. The bullet is contested with the CI output on the thread.

**#6188** — I split it after a `scope` ⛔ block and **told the reviewer that `api-design` and `reuse`
would probably re-fire on the rooting alone, because they went green only because of the congruence
work I was removing.** They have re-fired. That is expected, not a regression. The genuine tension:
`generality`/`api-design` asked for work that `scope` then ruled out of this PR. Resolution is
separate PRs (#6426, #6432, and the deferred branch), not an argument.

**Reviewer dynamics that actually work** (3 for 3 during my watch):
* **Implement the reviewer's proposal and report its failure with the CI output.** This clears
  rubrics that argument does not.
* **Contest only when the findings' *shared* reading has no implementation.** `reuse` on #6188
  reversed itself across rounds ("remove the private bridge" → "restore it"); both rounds agreed the
  transport should happen *once*, so I satisfied that instead of contesting, and it went green.
* A `⛔ block` halts the review — other rubrics then read "absent"/"not yet run", not lost.
* Read the board **sorted by `updated_at`**. The pipeline *edits* an existing comment, so
  positionally-last is stale.

---

## 7. The gate

`.improve-toolkit/tools/prepush.sh <base-ref>` runs **15 checks**; `tools/controls.sh` runs
**129 controls, 0 failing**. Run the gate before every push and the controls after every tool edit.

```bash
cp -R .improve-toolkit ~/GitHub/TauCeti/.mathlib-quality/improve   # or point the scripts at it
bash tools/prepush.sh origin/main
bash tools/controls.sh
```

Checks whose purpose is easy to mistake:

* **Five checks report `n/a` on a non-rooting PR** (`parallelns`, `nsslice`, `decldiff`,
  `rootsurplus`, `slice`). That is deliberate — they presuppose a rooting PR, and a row whose
  premise fails is a category error, not a defect.
* **`parallelns` and `slice` are questions, not defects.** Answer them in the PR body or root the
  remainder.
* **A check's scope is part of its answer.** `stalequal` reported 2 stale doc paths on #6418; the
  tree had **24** — it only sees files whose *declarations* changed.

### Rules that cost red builds to learn

* **The r389 namespace rule.** Inside `namespace TauCeti.Foo`, Lean tries `TauCeti.Foo.x`,
  `TauCeti.x`, then root `x`. It **never** tries `Foo.x`. So rooting a declaration out of a
  *surviving* wrapper strands every sibling reference — including **partially qualified** ones like
  `LocalGeneratorsData.IsInvertible`. Write `Foo.x`, which resolves at root.
* **`HEq` is the only way through a type-index mismatch.** `rw`, `simp`, `simpa`, `▸`, `convert` (at
  any depth) and `congr!` all fail identically, because none can abstract a type index.
* **A tactic reporting "no change" is a statement about the goal's shape**, not a near miss.
* **"Green before" is not evidence about "green now"** when the tree changed underneath.
* **Re-gate a bench branch against *current* main.** "Gate-clean" from weeks ago is not gate-clean.
* **Prospect against a freshly fetched `origin/main`**, never whatever branch is checked out. I once
  ranked a target that was already rooted on main.
* **Never view a name through `cut -c1-120`.** A truncated grep turned
  `IsLocallyFreeData.isFinitePresentation` into `IsLocallyFree` and cost a CI cycle.
* **An empty result that contradicts the diff is a reason to re-run the command**, not to conclude
  the thing is absent.
* **zsh does not word-split an unquoted `$var`.** Use `files=("${(@f)$(...)}")` and `"${files[@]}"`.
* **`awk length` and `wc -c` count bytes.** Width-check Lean with Python `len()`.
* **`git diff A...B` is three dots** for a branch's own commits. Comparing a branch to
  `origin/main` directly shows main's progress as deletions — use the **merge base**.

### Two rules about the controls themselves

* **Every new control must be run against the bug it exists to catch, not only against the fix.** I
  nearly shipped one whose fixture mutation silently threw — it passed on empty input and read green.
  A control that has never been seen to fail is not evidence.
* **A check that reports `ok` on the defect it was built for is worse than no check.** `rootedin` did
  exactly that on #6406 and I pushed on its authority. Both bugs in it (last-component-only, and
  judging shadowing from the wrong stack) are fixed, with controls.

---

## 8. Also worth knowing

* A **docstring outlives the review that provoked it.** I had written PR-defence text — import-cone
  placement arguments, `simpNF` rationale — into permanent docstrings, and `documentation` rightly
  objected. Put review argument in the PR body; put a source comment beside the declaration if the
  rationale must live in the file.
* **An uncommitted edit by someone who could run the compiler is evidence, not noise.** I overrode
  the `cft-fix-6093` author twice and was wrong both times.
* **Traps recorded in `targets.md`:** eight namespaces that look like ideal rooting targets are
  **absent from Mathlib** (`PDE.{Continuous,ContinuousOn}`,
  `Probability.{Kernel,AEStronglyMeasurable,MeasurableSet}`, `BilinForm.IsAlt`,
  `Representation.IsIrreducible`, `ModularForm.NormReduction`). `deadprivate`'s 12 rows are all
  deliberate regressions or worked examples.
* The **WHOLE rooting lane is exhausted** on current main: every whole namespace is an open PR, an
  ABSENT trap, or a thin 1/1. Remaining partial candidates: `ContRepresentation` 141/184,
  `Representation` 134/189, `AbelianVariety.Hom` 41/54, `WeierstrassCurve` 26/27. Avoid
  `IsCoveringMap` 59/67 and `Deck.IsQuotientCoveringMap` 31/32 — both overlap #6093.
* **Needs Chris, not you:** lifting the `lake` prohibition; #5950; and the worktree
  `~/GitHub/TauCeti/.claude/worktrees/cft-fix-6093`, which still holds 13 superseded modified files
  and a stray `lake-manifest.json` bump to `369aeb92f4`.

---

## 9. First hour on the new machine

The worker runs on **`AI-DOOM`, 178.33.239.142** (`ssh -i ~/.ssh/ovh_lean_mac chris@178.33.239.142`).
I probed it read-only on 2026-09-12; the state below is verified, not assumed.

**Already there:**
* `~/GitHub/TauCeti` cloned, with **both remotes correct** — `origin` → TauCetiProject/TauCeti,
  `fork` → CBirkbeck/TauCeti.
* `gh` authenticated as **CBirkbeck**. `git`, `python3` (3.14.4). 789 GB free.
* **The gate runs without a Lean toolchain.** I executed
  `python3 scripts/lint-dot-notation.py --source-root TauCeti` there: `759 total`. The linter and
  every `tools/*.py` check are pure Python, so gating works with no `lake` at all.

**Missing, and what it means:**
* **No `improver-1` worktree.** Existing worktrees are the rig root (on `elliptic/translation-galois`)
  and `.claude/worktrees/pr-worker-6` — *other agents' work; do not touch either.*
* **No toolkit** — that is what `handover/improve-toolkit` is for.
* **No `lake` / `elan`.** This is fine and slightly helpful: the cache prohibition means you must
  not build anyway, and here you cannot. **Gate on CI. It is the only option.**
* **No `uv` / `uvx`.** Needed *only* for step 4, driving a review. Install with
  `curl -LsSf https://astral.sh/uv/install.sh | sh`. Until then, skip step 4 — the pipeline picks
  PRs up on its own within ~46–64 minutes anyway, so a drive is rarely the bottleneck.

**Setup:**

```bash
ssh -i ~/.ssh/ovh_lean_mac chris@178.33.239.142
cd ~/GitHub/TauCeti
git fetch fork handover/improve-toolkit
git worktree add .claude/worktrees/improver-1 -b improver-1-base origin/main
mkdir -p .mathlib-quality
git show fork/handover/improve-toolkit:HANDOVER.md > ~/HANDOVER.md      # read this first
git archive fork/handover/improve-toolkit .improve-toolkit \
  | tar -x --strip-components=1 -C .mathlib-quality && mv .mathlib-quality/{tools,fixtures,*.md} \
  .mathlib-quality/improve/ 2>/dev/null || true                         # or just copy by hand
cd .claude/worktrees/improver-1
bash ~/GitHub/TauCeti/.mathlib-quality/improve/tools/controls.sh        # expect 129 passed, 0 failed
curl -LsSf https://astral.sh/uv/install.sh | sh                         # for review drives
```

Then:

1. Read `.mathlib-quality/improve/last-round.md`, then the **tail** of `ledger.md` (~33,500 lines —
   only the tail matters).
2. `bash tools/controls.sh` — **129 passed, 0 failed**. If not, fix the toolkit before touching a PR.
3. Sweep the board (§4). **#6432 needs marking ready** if its CI has gone green.
4. Set the 10-minute cron (§3).
