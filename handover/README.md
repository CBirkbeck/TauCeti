# Handover — the Chebotarev / ArithmeticDirichletSeries lane (TauCeti)

**Written 2026-09-13 by the outgoing worker (pr-worker-4).**
**Everything below was verified against live GitHub state on 2026-09-13T16:10Z.**

---

## 0. Read this first — why the lane is stalled

The loop stopped running on **2026-09-10 ~16:20Z**. It is now three days later. In those
three days the review pipeline came back to life and **reviewed every open PR in this lane**,
and nobody acted on the findings. So:

* **Six open PRs, five of them awaiting author action on live findings.**
* **One (#6269) has a RED build** introduced by a commit that is not mine (see §2).
* Nothing is blocked on anyone else. **All six are blocked on us.**

This is not a review backlog or an infrastructure problem. It is three days of no work.
The first job is to clear the five fix-ups, not to author anything new.

---

## 1. What this lane is for

Two roadmap areas in [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap):

* **`Chebotarev`** — the Chebotarev density theorem, built in fourteen layers.
  We are working **Layer 8.2, the cyclic fixed-field fibre**.
* **`ArithmeticDirichletSeries`** — Dirichlet series and Tauberian methods.
  We have just finished **Layer 3.4** and **Layer 2.3**.

### Landed while this worker held the lane
`#6205`, `#6174`, `#6201`, **`#6233` (ADS Layer 3.4 — merged 2026-09-11)**.

### Where the two targets stand

**ADS Layer 2.3 is mathematically complete** and sitting in `#6274`. Its blocker `#6233`
has merged, so `#6274` should be rebased onto `main` and taken out of draft (§2).

**Chebotarev 8.2 has three of its four parts done or in flight:**

| §8.2 asks for | status |
|---|---|
| `#C · f ∣ #G` as a separate statement | **already on `main`** — `ConjClasses.card_carrier_mul_orderOf_dvd` |
| the closed-form quotient | **already on `main`** — same file, `TauCeti/Algebra/Group/Conj.lean` |
| residue degree = least `n` with `Frob^n ∈ ⟨σ⟩` | `#6241` + `#6250`, both open with findings |
| the fibre count itself | **not written.** `#6269` + `#6277` are its two halves; see §3 |

---

## 2. The six open PRs, and the exact next action for each

Ordered by the cascade: **fix the red build first, then the findings, then author.**

### `#6269` — how many primes carry a given Frobenius element — **RED BUILD, do this first**

`https://github.com/TauCetiProject/TauCeti/pull/6269` · head `8c85fae355`

**Another worker pushed `8c85fae355` on 09-11 and it broke the build.** They were addressing
the same `proof-quality` finding I was (the `rfl`s crossing the `Subgroup.centralizer` action
wrapper), and their `rw [Subgroup.smul_def] at hP` does not fire:

```
FiberCount.lean:85:8: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?g • ?m
in the target expression
  (fun m => m • Q) ⟨τ, hτ⟩ = P
```

The membership is stated through an un-beta-reduced lambda, so `Subgroup.smul_def`'s pattern
is not syntactically present. **`simp only [Subgroup.smul_def] at hP` instead of `rw`** should
fix it (`simp only` beta-reduces first). Reproduce with:

```bash
lake build TauCeti.NumberTheory.NumberField.Frobenius.FiberCount
```

⚠ **Coordinate before pushing.** That commit is under the shared `CBirkbeck` account, so I
cannot tell whether another worker is still actively on this PR. Check the commit timestamps
before force-pushing over them.

### `#6277` — contracting a Frobenius fibre to the fixed field — 5 findings

`https://github.com/TauCetiProject/TauCeti/pull/6277` · head `dd5425e511` · green

| rubric | fix |
|---|---|
| `generality` | `under_fixedField_injOn` takes `𝔭`, `LiesOver`, `≠ ⊥` and Frobenius witnesses it never uses. State injectivity for primes **fixed by `σ`**, derive the fibre version. |
| `naming` | `Q` must precede `σ` in both `exists_isArithFrobAt_restrictScalars_eq` and `isArithFrobAt_of_restrictScalars_eq` so `Ideal` dot-notation works. |
| `placement` | Move to `Frobenius/FixedField/Fibre.lean` **and** `Frobenius/FixedField/Inertia.lean` — i.e. this touches `#6241`'s file too. Sequence them. |
| `attribution` | Add `TauCetiRoadmap/Chebotarev/README.md` §8.2 to References. |
| `documentation` | Strip "Layer 8.1" and the proof narration from the docstrings. |

### `#6241` — residue degree below the fixed field — 3 findings

`https://github.com/TauCetiProject/TauCeti/pull/6241` · head `a7d3801e31` · green

`api-design` (export the ideal-action lemma and the stabilizer comap equality, canonically in
`FixedField.lean`), `placement` (move `card_stabilizer_fixedField_eq_card_inf` to
`FixedField.lean` — it has no Galois/prime/unramified hypotheses), `documentation` (the heading
claims the decomposition group *is* the intersection; the theorem only proves `Nat.card`
equality — say so).

**Note:** `#6241` and `#6277` both end up moving things into `FixedField.lean` / a new
`FixedField/` directory. Do them in one sitting or they will fight.

### `#6273` — index the prime-power ideals by a prime and an exponent — 4 findings

`https://github.com/TauCetiProject/TauCeti/pull/6273` · head `da89e98eb7` · green

`api-design` (drop both `@[expose]`; add a `simp` lemma for `idealPrimePowerEquiv.symm`),
`naming` (put `idealPrimePowerOf` and its lemmas in the `HeightOneSpectrum` namespace, not
`TauCeti`), `placement` (`Mathlib.NumberTheory.EulerProduct.Basic` is topically wrong — import
the specific `Mathlib.Topology.Algebra.InfiniteSum` module instead), `documentation`
("absolutely convergent" → "summable"; the theorem only assumes `Summable`).

⚠ `#6274` is stacked on this. Fix `#6273` first, then rebase `#6274`.

### `#6250` — the least exponent landing in `H` — 1 finding

`https://github.com/TauCetiProject/TauCeti/pull/6250` · head `5f7ea72b0b` · green

Only `documentation` is live: the sentence describing the theorem as *"transported"* into
`⟨g⟩` documents the proof mechanism rather than the result. Replace or delete it. **This is
the closest PR to merging — one sentence.**

### `#6274` — the logarithmic derivative as a von Mangoldt Dirichlet series — DRAFT

`https://github.com/TauCetiProject/TauCeti/pull/6274` · head `ee01a4a39e` · green, no review

This is **ADS Layer 2.3, complete**. It was drafted as stacked on `#6233` and `#6273`.
**`#6233` has now merged**, so:

1. rebase onto `origin/main` — the diff shrinks to `VonMangoldt.lean` + `VonMangoldtCoeff.lean`
   (+ `PrimePowerIndex.lean` until `#6273` lands);
2. once `#6273` merges too, it is parent-free → **take it out of draft** and it will be reviewed.

It carries the target marker `ArithmeticDirichletSeries/README.md:Layer-2.3`.

### Parked (not on the cascade — check their conditions, do not let them rot)

* **`#5572`** — *divergence of `log(1/(s-1))`*. **ITS CONDITION IS NOW MET.** It was parked
  until `logDeriv_LSeries_eq_tsum_prime_pow` was on `main`; `#6233` merged it on 09-11.
  **Un-park it, rebase, and drive it.**
* **`#5594`** — counting cyclic-group elements of order divisible by `f`. Still parked: it
  unparks when Layer 7.2's conclusion is actually *used* by a consumer.

---

## 3. Work in preparation — verified, not yet shipped

`handover/verified/` in this branch. **Every file here compiled against the pinned Mathlib**
on 2026-09-13 or earlier. They are proof bodies, not PR-ready files: they need docstrings,
placement decisions, and the `/cleanup` pass.

The valuable ones:

* **`chebotarev-82-fibre-injective-verified.lean`** and
  **`chebotarev-82-surjectivity-verified.lean`** — the two halves of the §8.2 fibre bijection.
  Both are **already in `#6277`**; kept here as the standalone proofs.
* **`ads-layer23-*-verified.lean`** — Layer 2.3's summand identity, summability, and the
  complete file. All in `#6274`.
* `chebotarev-82-fibercount-verified.lean`, `chebotarev-82-leastn-verified.lean`,
  `chebotarev-82-complete-verified.lean`, `chebotarev-82-relative-frobenius-verified.lean` —
  earlier verified pieces, mostly superseded by the open PRs but useful as references.

**The one genuinely unwritten thing is the fibre count itself**:

```text
#{𝔓 of E above 𝔭 : f(𝔓/𝔭) = 1, relative Frobenius = σ} · orderOf σ = #Centralizer_G(σ)
```

It is now **one step**: `#6277` gives the bijection, `#6269` gives the L-side cardinality, so
the E-side count is those two composed. Do it after both merge.

`handover/notes/` has the Layer 2.3 scoping file, a map of the Chebotarev subtree, and the
**full round-by-round worklog** (`full-worklog.md`, ~21k lines) — the worklog is the real
record of what was tried and why.

---

## 4. The workflow

The lane runs the **`/taupr`** skill (`mathlib-quality:taupr`). One unit of work per round,
first that applies:

```
R1 REBASE   a PR has a genuine TauCeti/ conflict
R2 FIX-CI   a PR's build is red          ← outranks R3; a red PR cannot be reviewed
R3 FIX      a PR has adverse findings at its CURRENT head → fix, or contest in-thread
R4 REVIEW   green ≥1h with no scoreboard at that head → tauceti-review --post
R5 AUTHOR   otherwise open a new PR
```

Run it on a ten-minute loop:

```
/loop 10m /taupr --max-open 3
```

**The `--max-open 3` cap does not bind for this lane** — the operator's standing instruction is
*"have as many open as you can handle, don't sit idle"*. But see §6: the reason this handover
exists is that nine open PRs with no one working them is worse than three.

### Reading the board correctly — this is where the traps are

* **A scoreboard applies only to the `head_sha` it names.** Stale boards look identical to live
  ones in the GitHub UI. Always parse `<!--tauceti-meta:v1 {...}-->` and compare `head_sha`.
  At one point all three of my PRs showed adverse rubrics and **none of them was live**.
* **`error` is not a verdict.** A rubric that errored (≈6s, $0.00) means the reviewer CLI died,
  not that anything is wrong. There is nothing to fix and nothing to contest.
* **An `error` still claims the head**, so R4 will never fire on that PR and CI will not
  re-review without a new commit. Two of my PRs were wedged this way for three days.
  ⚠ **Do not run R4 while the reviewer is broken** — posting an all-error board claims the head
  and suppresses the real review when credit returns.
* **`submitted_by` tells you whose rig ran it.** Reviews arrive from several rigs
  (`kim-em`, `ldct`, `utensil`, `CBirkbeck`), so a dead local reviewer does not mean no reviews.

---

## 5. Standing rules — non-negotiable

Carried from the operator. Breaking these has real consequences for other workers.

**Worktree and the shared rig**
* Work **only** in your own worktree. **Never** work in `~/GitHub/TauCeti` itself, and never
  create another worktree.
* `.lake/packages` is a **symlink to a shared Mathlib cache**. **Never run `lake exe cache get`,
  `lake update`, or a bare `lake build`.** Build only your own modules:
  `env LEAN4_GUARDRAILS_BYPASS=1 lake build TauCeti.Path.Module`.
  If Lake ever starts compiling `Mathlib.*`, **stop it immediately**.
* A mathlib bump on `main` is refreshed **once, from the rig root, by one person**:
  `cd ~/GitHub/TauCeti && git pull && lake exe cache get`. Tell the operator; do not do it
  from a worktree.
* **Never kill processes you did not start.**
* The **git stash stack is shared**. Never bare `git stash` / `git stash pop`. Use
  `git stash push -u -m "<unique-tag>"`, capture the SHA, `apply` (not `pop`), then drop by tag.
* **Branch names on the fork are shared too.** See §6.

**Git and PRs**
* `git fetch origin fork` and `git rebase origin/main` before the first build on any branch.
* **Push with `--force-with-lease`**, always, using the *observed* oid.
* Draft first → `/cleanup` on **every** changed `.lean` file → `/decompose-proof` anything over
  30 lines (50 is the hard cap) → then mark ready.
* Stacked PRs are allowed **as drafts with a parent line**.
* **Search TauCeti *and* Mathlib before writing any declaration.** An absence in one is not
  evidence about the other.
* PR body carries `Roadmap: <CanonicalAreaName>`, a `tauceti-target` marker **only** when the PR
  authors a roadmap target, and a `Provenance:` line for adapted code.
  ⚠ **Two PRs must never carry the same target id** — the duplicate sweeper closes the newer one.
* No `sorry`, no `native_decide`, no `maxHeartbeats` overrides. CI enforces all three.
* `scripts/`, `.github/` and the lakefile are **human-owned**. Never `--admin`-merge. Never open
  a PR or issue in TauCetiRoadmap.
* Re-drive a review only with
  `uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review <PR> --reviewer codex --post`
  and only after a green build has sat an hour with no scoreboard at that head.
* **Contest only genuine contradictions**, in the rubric's own thread (a top-level `gh pr comment`
  is never read as a contest). Otherwise implement the finding.
* **Never abandon a PR.** If it is blocked, comment on it saying *what unblocks it*.

---

## 6. Things that cost me real time — read before you repeat them

1. **A rejected push does not stop `gh pr create`.** I batched them; the push was rejected
   (`stale info`, the branch already belonged to another worker), and `gh pr create` ran anyway
   and opened a PR **over that worker's diff under my title**. I closed it (#6276) and re-pushed
   elsewhere. *Check the branch name is free with `git ls-remote --exit-code` first, never batch
   push and create, and verify the created PR's `headRefOid` matches your local HEAD.*
2. **Defeq crossings are the single most common finding against this lane** — three in one day
   (`relIndex`, a `set` wrapper, a restricted subgroup action). Wherever a subgroup coercion, a
   `set` binding, or a `def` wrapper sits between two expressions, **name the equality even when
   Lean does not ask**. Every time, the explicit version was the same length or shorter.
3. **A dependency recorded once is a claim with an expiry date.** I carried "the fibre count
   needs #6241" for twenty rounds. It did not — the `H = ⟨σ⟩` case had been on `main` since
   #6164 the whole time. **Re-check blockers against `main`, not against the PR you remember.**
4. **Read the destination file's prose before grepping.** `VonMangoldt.lean` said in its own
   module docstring exactly what was missing and why it had been deferred. Twice this saved a
   whole PR's worth of duplicated work.
5. **`--rubrics <one>` rewrites the entire scoreboard**, it does not patch one row. I turned a
   ten-row board into a one-row board and lost the record that nine rubrics had approved.
6. **The module system bites:** a `rfl` lemma about a `def` fails with *"all definitions that
   need to be unfolded must be exposed"* unless the `def` is `@[expose]`. Narrow `@[expose]` to
   the specific definitions, not the whole section (`#6273`'s `api-design` finding says even that
   was too broad).
7. `omit [Foo] in` goes **before** the docstring, not between docstring and `theorem`.
8. **`gh pr create` needs `--head <owner>:<branch>`** when pushing to a fork.

---

## 7. Environment for a new machine

* TauCeti checkout with a **built, pinned Mathlib**, plus a clone of TauCetiRoadmap.
* `gh` authenticated; `uvx` on PATH.
* `codex` logged into a ChatGPT subscription — **this is the R4 reviewer**.
  ⚠ **As of 2026-09-13 the shared account is over its usage limit until `Sep 15 02:23`.**
  A second account exists (`CODEX_HOME=~/.codex2`) and works, but **switching to it is the
  operator's call — do not do it unilaterally.** R4 is only a fallback; CI and other rigs
  review normally, so the lane works without it.
* Known broken, harmless, **do not fix without being asked**: the review tool's archive sync
  (`~/.cache/tauceti-review/data/TauCetiData` is thousands of commits behind and its checkout
  aborts on two untracked blobs). Records queue in the outbox. Shared state.

---

## 8. Suggested first session

1. **`#6269`** — fix the red build (`simp only` for `rw`), after checking nobody else is on it.
2. **`#6250`** — one documentation sentence. Ship it.
3. **`#6241` + `#6277` together** — they both restructure into `Frobenius/FixedField/`.
4. **`#6273`**, then rebase **`#6274`** onto `main` and undraft it.
5. **`#5572`** — un-park, rebase, drive. Its blocker merged.
6. Only then author: the **§8.2 fibre count**, which is `#6277` ∘ `#6269`.

Then start the loop: `/loop 10m /taupr --max-open 3`.
