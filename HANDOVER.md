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

---

## 10. Addendum — 2026-09-12, first round actually run on AI-DOOM (r653)

The setup in §9 is right, but three things bite on a machine change. All three are fixed on this
branch; this section records *why*, because each one reads green or reads like a defect elsewhere.

* **The controls will read `125 passed, 4 failed` until you take this branch's fixture.**
  `fixtures/r440-lintcand-ctl/base.tsv` used to carry absolute paths from the authoring machine.
  `lintcand.py` honours an absolute path as-is, so every row resolved to nothing and the firing
  control printed *"4 baseline rows, 4 single-finding files, **0 declarations located**"*. The rows
  are now relative to the fixture root. **The tool was never wrong — the fixture was not portable.**
  Two of those five controls had also been passing *vacuously on empty output*, which is r649's own
  trap. If you ever port these fixtures again, re-run the mutation test: and note that a mutation
  matching the short name's **last component** leaves all five green, because the flagged
  declaration precedes the decoy in the file. Only the faithful r439 defect — the header must *be*
  the bare short name — fails them.

* **A fresh worktree has no `.lake`, and `lint-dot-notation` then errors on BOTH sides.** The gate
  renders that as `FAIL lint-dot-notation: NEW violations` and `rootsurplus UNRUN`, neither of which
  is true. Symlink it — no `lake` is invoked, so the prohibition is untouched:

  ```bash
  ln -sfn ~/GitHub/TauCeti/.lake .claude/worktrees/improver-1/.lake
  echo .lake >> "$(git rev-parse --git-common-dir)/info/exclude"   # /.lake/ in .gitignore is dir-only
  ```

  With it, the check reads base **761** → head **741**, 0 new. **A check that errors on both sides is
  not a comparison — it is two errors.**

* **`gh pr edit` is broken against this repo.** It fails on the projects-classic GraphQL deprecation
  (`repository.pullRequest.projectCards`) and **leaves the body unchanged without saying so** — it
  exits printing only the deprecation notice. Use
  `gh api -X PATCH repos/TauCetiProject/TauCeti/pulls/<n> -F body=@file` and re-read the body after.

**Sweeping CI:** judge each check by its **latest run per name**. A commit's check-runs list carries
every run ever created for that SHA, so a re-dispatch leaves `cancelled` duplicates behind. #6188
read RED on a superseded `label` job while `sandboxed-build` was green and nothing had conclusion
`failure`. **A superseded run is not a red build.**

**One more finding shape to expect:** a rubric can be *correct* and still not be yours. #6412's
`api-design` asks for an edit to `TauCetiRoadmap/Exchangeability/README.md` — a separate,
human-controlled repo this role may not open a PR or issue in, and which no `TauCeti/`-only branch
can reach. Contest it, name the constraint, and say what survives (there, the canonical declaration
under its own name). Do not re-add a deleted duplicate to satisfy a downstream document.

---

## 11. Addendum — rounds r654–r669, one long watch on AI-DOOM

Four PRs merged during it (#6406, #6426, #6412, #6418) and `lint-dot-notation` on main went
**759 → 739**. What follows is only what cost a cycle, or came within one command of costing one.
Everything here is evidenced in the ledger at the round named.

### The gate, and how to not be lied to by it

* **COMMIT BEFORE GATING.** Every screen in `prepush.sh` reads `HEAD` — `git diff BASE...HEAD`,
  `git archive HEAD`. Gating uncommitted work reports on the *previous commit* and calls it green.
  That is how #6432 went red on a rename the gate had just passed: `lint-dot-notation` archived HEAD,
  saw the old names, said `0 new`; CI saw the new ones and said `3 new`. **The gate now refuses a
  dirty tree** (r664, controls 131 → 133, mutation-tested). The script's header used to claim it ran
  "against the working tree"; it never did.
* **The gate is pure Python.** It cannot see docstring attachment, elaboration, or simp normal form.
  A `@[simp]` that `simpNF` will reject, a proof that will not elaborate, and a declaration whose
  docstring attached to the wrong thing all pass it (r656, r659).
* **Before believing a gate FAIL is yours, re-run it on the pristine head.** One command; it
  separates "pre-existing" from "I broke it" on a nineteen-file PR (r655 onwards, used every round).
* **`xsibling` had a false positive** and two rounds reasoned past it with plausible stories before
  the tool's own internals were run against the real file. `_root_.TauCeti.Foo.bar` made its
  lost-wrapper guard read `'TauCeti.TauCeti' not in h` — vacuously true — so `TauCeti` itself was
  reported lost. Fixed with a paired positive/negative control (r661). **A check that cries wolf is
  a check you learn to skim**, which defeats the whole toolkit.

### The dot-notation ratchet

* **`scripts/lint-dot-notation-baseline.txt` grandfathers by DECLARATION NAME.** A *stale* entry is
  harmless — removing a violation is fine. **Adding a name is not the same as removing one:**
  renaming a flagged declaration in place un-grandfathers it, and the rename is red unless the
  declaration is **rooted in the same commit**, where it is not flagged at all (r664, #6432).
  The baseline is human-owned; regenerating it is not available.

### Reading the review

* **Clearing a ⛔ starts the rest of the review, not the merge.** Rubrics behind a block read
  "not yet run", and they all arrive at once when it lifts. Happened three times (r657, r666, r668).
  Plan for it rather than reading it as a regression.
* **A 🟡 sitting behind a ⛔ may not survive the next board — do not chase it.** #6188's `reuse`
  demanded a deletion that, once the ⛔ cleared, vanished while `proof-quality` approved the very
  thing it wanted deleted (r668 → r669).
* **Re-read a finding's text, not your summary of it.** A rejection I had recorded as "sequencing
  refused" actually offered the fix — *"Rebase onto #6188 **or** move all three here"* (r663).
  And the pipeline **edits** a rubric's comment in place: same id, same `created_at`, different
  finding (r655). Never cache a finding by comment id.
* **"Tried and failed" is scoped to the position it was tried in.** `MulEquiv.apply_symm_apply` was
  recorded as not working; that failure was in a `simp only` set, where it never fires because simp
  matches syntactically. As the *proof of a `have`* it works, needing only definitional reduction
  (r665). Record the position with the verdict, or the note misleads its own author.
* **Verify a cited precedent before implementing on its authority.** A `naming` finding cited
  `AlgEquiv.toLinearEquiv_ofLinearEquiv`; that lemma sits in `AlgEquiv`, not `LinearEquiv`, despite
  taking a `LinearEquiv` as its first explicit argument — the citation inverted the finding (r662).
* **When a rubric loop returns to a position it once rejected, look for a sibling PR where that
  position is currently approved.** The `toLinearEquiv` transport went private → public → inline →
  private across four rounds; what settled it was that #6432 carried the identical private bridge
  with `reuse` ✅ (r667).
* **An answer can arrive as a finding rather than as a reply.** A question left on a thread about
  which of two converged PRs should own a file was answered by a `scope` ⛔ on one of them (r668).
  Asking was still right: it named the options, and the block picked one.

### Lean facts worth keeping

* **`@[expose]` is a claim about a whole reduction path, not one declaration.** Rerouting an exposed
  body through a non-exposed def stops the reduction in the same place with the attribute still
  sitting there. Check every def the body routes through — Mathlib's are usually in
  `@[expose] public section`, but check (r658).
* **A *definitional* index mismatch is not §7's `HEq` trap.** §7 is about indices differing
  *propositionally*. When they differ only by unfolding — eta, `∘` associativity, `Equiv.trans`
  reduction — the equation states and `ext` + `rfl` closes it (r658).
* **A goal printed unchanged means the lemma never fired**, not that it fired and fell short (r661).
* **Deleting a declaration means deleting what advertises it** — the module docstring included.
  Twice flagged for exactly this (r667).

### Working two PRs over the same code

* **Port a fix the moment it is accepted anywhere.** #6188 and #6432 drew the same findings on the
  same code; three fixes moved across in one commit (r668).
* **But a green PR is not a place to apply a lesson.** #6432 carried a docstring #6188 was told to
  change, while its own `documentation` read ✅. Left alone (r669).

### Prospecting

* `nscand.py <snapshot> <findings>` ranks namespaces by flagged/total; **`mathlibns.py` decides
  whether the namespace is real, never a grep** (r511 had a grep wrong on five of six).
* **Then check Mathlib does not already have the name.** #6418's ⛔ was an exact duplicate of
  `FDRep.isIntegral_character`; the rooting is what created the clash, since nested the two
  coexisted (r653).
* Re-run the ranking after every merge — main moved 759 → 739 inside one watch.
* **Scouted and ready, not opened** (four PRs were open; step 5 needs fewer than three):
  `TauCeti.Submonoid` 1/1 — `TauCeti/Topology/Algebra/ConstMulAction.lean:37`,
  `instance continuousConstSMul` with `@[to_additive AddSubmonoid.continuousConstVAdd]`, referenced
  once in the same file by `TauCeti.Subgroup.continuousConstSMul`. `Submonoid` is ROOT in Mathlib
  (517 declarations), Mathlib has neither name, and its own `ConstMulAction.lean` uses the identical
  `Units.`/`Prod.`/`MulOpposite.continuousConstSMul` pattern. Being an instance, rooting enables no
  dot notation — the value is emptying the namespace and matching Mathlib's placement.

### Mechanics

* **`gh pr edit` is broken against this repo** — it fails on the projects-classic GraphQL deprecation
  and **leaves the body unchanged without saying so**. Use
  `gh api -X PATCH repos/$R/pulls/<n> -F body=@file`, then re-read the body.
* Judge CI by the **latest run per check name**; a `cancelled` superseded duplicate is not red.
* Measured board latency, reviewable → first board: **32–67 min** across five samples. Count step 4's
  hour from `max(CI-green, ready_for_review)`, and expect the pipeline to beat you to it.
* `uv`/`uvx` are installed at `~/.local/bin`. A drive was never actually needed in this watch.

## 12. Addendum — r679, the merge queue: what it actually does

Two rounds in this watch produced a wrong theory about why green PRs were not merging. Both came
from reasoning over `gh run list` output and merge timestamps instead of querying the queue. **Read
this section before forming a third.**

### The mechanism

1. `tauceti-review-bot` posts a green board and applies **`ready-to-merge`**.
2. On that **label transition** — not on the label's presence — the bot calls `added_to_merge_queue`.
3. GitHub's merge queue merges **strictly FIFO by enqueue time**, one serialised worker at
   **~25–30 min per merge**, and it ran **30+ deep** through r679.

So **label → merge latency of 2.5–3.5 h is normal and is not a fault.** Eight consecutive PRs
confirmed the ordering exactly, including this role's own #6418 (`ready-to-merge` 14:36:32Z, merged
16:58:30Z, with four unrelated PRs interleaved in label order). A PR at position 18 is ~8–9 h out for
no reason other than its position.

Wrong theories this replaces:
* **r676: "the queue is jammed on #6431."** It was not; #6431 merged at 19:18:04Z.
* **r679, mid-round: "something discriminates against `improve/*`."** It does not; `roadmap/none`
  sits on the merged ones too (#6406, #6412, #6418, #6426).

### The one real failure mode: silent ejection

`github-merge-queue[bot]` can drop an entry with **no comment and no `merge_group` run**. #6093 was
enqueued 15:43:28Z, sat **3h11m** without a single merge-group build, and was removed at 18:54:20Z —
the instant the PR ahead of it merged. Afterwards it still read:

```
label=ready-to-merge   CI=GREEN   board=ON-HEAD   isDraft=false   mergeable=MERGEABLE   state=CLEAN
```

**Every field `sweep.py` reads said healthy.** And since the bot enqueues on the *label transition*,
which had already fired, **nothing was ever going to re-enqueue it**. A PR can strand indefinitely in
a state indistinguishable from a PR that is merely waiting its turn.

### The check

`tools/queuepos.py` (added r679, two mutation-tested controls, suite now **137 passed / 0 failed**):

```
python3 tools/queuepos.py            # all open improve/* PRs
python3 tools/queuepos.py 6093 6188  # named; exit 1 if any is stranded
```

`STRANDED` — `ready-to-merge` **and** absent from the queue — **is the only actionable verdict.**
`QUEUED:pos=30` is fine however long it has sat. **Run it beside the sweep every round.**

### The fix for a stranded PR

Refresh the branch so the bot re-reviews and re-labels; the new label transition re-enqueues it.
Staleness is also the first suspect for the ejection itself — #6093 was **354 commits behind**.

```
git merge origin/main --no-edit          # #6093: clean, 0 conflicts, PR diff unchanged
bash tools/prepush.sh                    # gate the merged head
git push fork <branch>
```

**Separate what the merge caused from what main's movement revealed.** `prepush.sh` takes a base
argument, so re-gate the *pristine* head against its *own* merge-base and compare:

```
bash tools/prepush.sh "$(git merge-base <pre-merge-head> origin/main)"   # 11 ok, 4 failed, 1 UNRUN
bash tools/prepush.sh                                                     # 11 ok, 4 failed, 1 UNRUN
```

Identical counts mean the merge introduced nothing, and the failures are pre-existing on a branch the
pipeline had already carried to 10/10 — `decldiff`/`nsjump`/`rootsurplus`/`slice` are the
body-answerable kind. Without this comparison the post-merge gate looks like four fresh breakages.

The cost is a certain re-review of a green PR. r678 declined to pay it against an *uncertain*
failure and was right to; r679 paid it once the failure was certain. **That ordering is the rule:
refresh a green PR only once `queuepos.py` says `STRANDED`.**
