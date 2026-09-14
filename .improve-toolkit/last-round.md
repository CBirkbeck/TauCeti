# Last round — r727 (2026-09-14T18:06Z)

## PR rotation (user directive, 2026-09-14) — read this first

The PRs this role opens now **alternate between three kinds, in order 1 → 2 → 3 → 1**:

1. **Mathlib catch-up** — work that has landed in pinned Mathlib and duplicates TauCeti: refactor TauCeti
   onto the Mathlib version and delete the local copy (no aliases, per `.claude/CLAUDE.md`).
2. **File pass** — pick one file, run `/cleanup` and `/mathlibable` (mathlib-quality plugin) on it, with
   ChatGPT `gpt-6-astra` helping.
3. **What this role has been doing** — rooting, dedup, hypothesis weakening, docstrings, relocation.

Every PR so far is kind 3. **Kinds 1, 2 and 3 are all staged** (below): open them in that order, one per freed
slot. Record each PR's kind in
the ledger. Step 5's cap still holds (fewer than 3 open `improve/*` PRs, #5950 excluded); research for
the due kind runs while it is shut.

**ChatGPT access:** no `chatgpt-math` MCP server is configured (only `lean-lsp`). The model is reachable
through the local codex CLI that MCP wraps:
`codex exec -m gpt-6-astra -c model_reasoning_effort="high" -o <answer-file> "$(cat <question-file>)" < /dev/null`
(the form the plugin's voyager skill uses).

## Board

| PR | head | CI | state | whose move |
|---|---|---|---|---|
| **#6093** | `18e85bea2` | green | 10/10, `ready-to-merge`, **QUEUED pos 12/39** | nobody — act only if `queuepos.py` says `EJECTED` |
| **#6796** | `06e8f7fdf` | green | 10/10, `ready-to-merge`, **QUEUED pos 13** | nobody |
| **#6800** | `716cf35ee` | green | **10/10** (driven, board 13:16:34Z, $0.98), `ready-to-merge`, **QUEUED pos 14** | nobody |
| **#5950** | `a64ba63667` | green | `ready-to-merge`, **NEVER-QUEUED** | **Chris** — do not refresh |

**Three `improve/*` PRs of mine are open → step 5 does not fire** until one merges (~30 min per merge,
11 ahead of #6093, unchanged from 17:56Z to 18:06Z; main is `c37f31f12`).

## What to expect next

1. **Queue:** `queuepos.py` each round; act only on `EJECTED`. If main moves a lot, re-run r702's
   merge-group simulation (cheap, read-only; r726: all three clean against `c37f31f12`). Staged branches:
   `git merge-tree --write-tree --name-only origin/main <branch>` checks them without a checkout (r726: all three
   clean against `c37f31f12`, none of their files touched on main).
2. **When a slot opens, open kind 1: `improve/levi-civita-mathlib`** (`4d0dfadf1` on `fork`). At that moment:
   merge `origin/main`, re-gate (expect 15 ok / 2 failed / 0 UNRUN: `decldiff` and `nsjump`, both answered in
   the body), push, then
   `gh pr create --draft --repo TauCetiProject/TauCeti --base main --head CBirkbeck:improve/levi-civita-mathlib --title "refactor(Geometry/Manifold): use Mathlib's Levi-Civita connection" --body-file pending/levi-civita-mathlib-body.md`.
   **CI is the first elaborator this branch meets** — iterate as a draft; `gh pr ready` only when green.
   (r709: the fork `CBirkbeck/TauCeti` has Actions enabled but has never run a workflow, so pushing there gives
   no early build.)
3. **At the second free slot, open kind 2: `improve/quadratic-separable-ring`** (`89205ce8d` on `fork`). Same
   recipe: merge `origin/main`, re-gate (expect 12 ok / 0 failed / 0 UNRUN), push, then
   `gh pr create --draft --repo TauCetiProject/TauCeti --base main --head CBirkbeck:improve/quadratic-separable-ring --title "refactor(Algebra/Polynomial): separability of a quadratic from a unit discriminant" --body-file pending/quadratic-separable-ring-body.md`.
4. **At the third free slot, open kind 3: `improve/exchangeable-contractable-dedup`** (`73227e02e` on `fork`).
   Same recipe (expect 12 ok / 0 failed / 0 UNRUN), title
   "refactor(Probability/Exchangeability): drop the duplicate `contractable_of_exchangeable`", body
   `pending/exchangeable-contractable-dedup-body.md`.
5. **After those:** kind 1 again (the deck group, mathlib4#40135 — large), then kind 2 (a new file), then kind 3
   (next candidate: the `StronglyContinuousSemigroup.norm_resolvent_integrand_le` weakening; see ledger r706).

## Kind-1 prospects (r703 first pass)

Method: `$SP/mlcatchup.py` indexes pinned Mathlib `30a58f7` (243230 names) and TauCeti main (58119):
same-name collisions, stale "Mathlib has no `X`" notes, and cited Mathlib PRs whose squash commit is in
the pin. Outputs: `$SP/mlcatchup.out`, `$SP/idx-*.tsv`.

* **Not duplicates:** all 13 same-name collisions are deliberate generalisations (ContMDiff
  `subtypeVal_comp_iff` at every `n`; Dedekind/Noetherian integral closure without separability;
  `descPochhammer` over any ring; `exp` in noncommutative Banach algebras). No stale "Mathlib has no" note.
* **STAGED in r704 — Levi-Civita — mathlib4#36845 (landed 2026-08-22, in the pin).** Mathlib has
  `CovariantDerivative.IsLeviCivitaConnection`, `.apply_eq` (Koszul), `.apply_eq_extend`, `.uniqueness`,
  `leviCivitaConnection I M`, `leviCivitaConnection_apply_inner(_right)`,
  `isLeviCivitaConnection_leviCivitaConnection` — the instance set of TauCeti's `Existence.lean`.
  TauCeti duplicates: `IsLeviCivita`, `.unique`, `leviCivita`, `isLeviCivita_leviCivita`,
  `exists_isLeviCivita`. Outside the LeviCivita directory only Geodesic files use them (`leviCivita` 39
  lines in 4 files; `isLeviCivita_leviCivita` 1). `Regularity.lean` (smoothness) has no Mathlib
  counterpart and sits on TauCeti's Koszul API.
* **Next kind-1 candidate — deck group — mathlib4#40135 (landed 2026-08-27).** Mathlib `deck p : Subgroup (E ≃ₜ E)`, carrier
  `p ∘ h = p`; TauCeti `TauCeti.Deck p`, carrier `∀ e, p (φ e) = p e` — equal, **not defeq**. 36 files /
  837 lines name `Deck`, but few sites depend on the carrier (`.2 e` ≤ 14, `∈ Deck` 3, `mem_iff` 3).
  TauCeti's extras (`fiberHomeomorph`, `mapsTo_fiber`, `smul_eq_apply`, `deck_comp_of_injective`) have
  no Mathlib counterpart.
* **Checked, nothing to do:** mathlib4#40303 (`xRep`) is consumed, not duplicated; the #38813 hit was
  #38909, whose lemmas `GradedRing.lean` already consumes.

## Kind-2 pass notes (r705)

`/cleanup` and `/mathlibable` (in `~/.claude/plugins/marketplaces/mathlib-quality-plugins/commands/`) both start
with `lake build` and gate every edit on `lean_diagnostic_messages` — **forbidden here**. Run their static phases only
(audit, literature, Mathlib search, generality, composition, verdict); CI compiles. Mathlib search without a local
build: the lean-lsp **remote** tools `lean_loogle`, `lean_leansearch` and `lean_leanfinder` (confirm every hit at the
pin), plus grep. Never the file-based lean-lsp tools. ChatGPT: `codex exec -m gpt-6-astra` (see the rotation section).
Full artifact: `pending/quadratic-discriminant-report.md`. Reference docs:
`~/.claude/plugins/marketplaces/mathlib-quality-plugins/skills/mathlib-quality/references/`.

## What r703–r727 did

* `decldiff`/`rootsurplus` learned `open` (ROOTED-VIA-OPEN, still blocking; FLAGGED-VIA-OPEN) — 152/0.
* #6800's scheduled drive: 10/10, $0.98, queued.
* Recorded the user's PR rotation; first kind-1 prospecting pass (above).
* r704: staged kind 1 (Levi-Civita); prepush/stalequal/decldiff learned deleted files — 158/0.
* r705: staged kind 2 (`QuadraticDiscriminant.lean`: separable from a unit discriminant, over any `CommRing`).
* r706: re-simulated the three merge groups (clean); staged kind 3 (the `Exchangeable.contractable` dedup).
* r707: no-op board; the three staged branches still merge clean.
* r708: no-op board (queue 24/25/26); staged branches re-checked against main (ledger r708).
* r709: no-op board; the fork has never run a workflow, so staged branches get no build before they open.
* r710: no-op board; queue head #6641 mid `sandboxed-build` (slow, not stuck).
* r711: no-op board; queue and main unmoved for 30+ minutes.
* r712: main moved (#6641, #6692); queued merge groups and staged branches re-checked, all clean.
* r713: no-op board.
* r714: no-op board.
* r715: main moved (#6680, #6634); queued merge groups and staged branches re-checked, all clean.
* r716: no-op board.
* r717: main moved (#6655, #6710); queued merge groups and staged branches re-checked, all clean.
* r718: no-op board.
* r719: no-op board.
* r720: no-op board; queue head recorded (ledger r720).
* r721: main moved (#6736, #6734); queued merge groups and staged branches re-checked, all clean.
* r722: sweep crashed on a rate-limited API; sweep/queuepos now refuse error payloads — 166/0.
* r723: main moved (#6675, #6730); queued merge groups and staged branches re-checked, all clean.
* r724: no-op board.
* r725: main moved (#6691); queued merge groups and staged branches re-checked, all clean.
* r726: main moved (#6742); queued merge groups and staged branches re-checked, all clean.
* r727: no-op board.

## Candidates for a later step 5

**r706:** every WHOLE `nscand` target is taken or a trap, and `ClassGroup` is partial (ledger r706). `dupsig` has no public duplicate left once kind 3 lands.

Re-run `nscand.py` first. Skip `TauCeti.LinearEquiv.toLinearEquiv_generalLinearEquiv_symm` and
`TauCeti.FDRep.intCharacter_def` (both `private`). The r681 trap namespaces still apply
(`Probability.Kernel`, `PDE.Continuous(On)`, `Probability.AEStronglyMeasurable`,
`Probability.MeasurableSet`, `BilinForm.IsAlt` do not exist in Mathlib). The partial namespaces in
`Lattice.lean` (`TauCeti.Submodule.IsLattice` 3/4, `TauCeti.Submodule` 5/20) are not whole — do not cut.

## Settled

* **Merged this watch:** #6406, #6426, #6412, #6418, #6432, #6188, #6482.
* **#6093** — `scope`, `naming`, `documentation` green; `api-design` answered. Deferred laws on
  `handover/fiber-compfiberequiv-laws-deferred`.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile — **including the dot-notation baseline**, which is
why renaming a flagged declaration is red unless it is rooted in the same commit.
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
**Backticks inside `-m "…"` are COMMAND SUBSTITUTION** — `git commit -m "…\`stale\`…"` silently
drops the word. Escape them (`\\\``) or pass the message with `-F file` (r687 lost one word this
way; every PR-branch commit survived only because they were escaped).
Every PR body needs a standalone `Roadmap: none`.
**PRs here are CROSS-REPO** — head on `CBirkbeck/TauCeti`, base `TauCetiProject/TauCeti`. Always
`gh pr create --repo TauCetiProject/TauCeti --base main --head CBirkbeck:<branch>`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`, then **re-read to verify**.
**Pass an explicit `--limit` to every `gh` listing** — the defaults are 30 rows and truncate silently.
`sweep.py` had it too (r691), at `--limit 100` repo-wide: 213 open PRs pushed both old `improve/*`
rows past the cut and the sweep printed **nothing**, exit 0. **An empty sweep is not an empty board.**
**A draft draws no review** however its label reads — `gh pr ready` the moment CI is green (r650).
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
**COMMIT BEFORE GATING** — prepush reads HEAD and refuses a dirty tree.
**`prepush.sh` takes a base argument.** To tell "my change broke it" from "main moved", re-gate the
pristine head against its **own** merge-base: `prepush.sh $(git merge-base <head> origin/main)`.
**Identical gate counts across a `main` merge prove the merge introduced nothing — they do NOT make
the standing findings safe.** A latent `nsjump`/`decldiff` finding is one waiting for a caller, and
merging `main` is what supplies callers.
**A removed declaration whose namespace is also a TERM does not announce its absence** — it re-reads
as generalized field notation and fails somewhere else entirely (#6093).
**A board finding dated before the current head may be `absent`, not live.** `threadread.py` now
classifies this: answer **LIVE** only; **NOT-RUN** is deferred behind the block.
**Control rows go to plain `grep`** — a bracketed pattern is a character class, and a negative
control asserting one passes for the wrong reason.
**Refresh a scouted branch AT the moment it is opened, not speculatively** — it drifts ~4–6 commits
an hour, so an early refresh is churn and a stale open is #6093's failure mode.
**Verify a staged artefact against something real before trusting it** (r685: the staged
`gh pr create` was wrong and only a real PR's `head.repo` showed it).
A rubric that went green can go 🟡 again; clearing a ⛔ reveals rubrics that never ran; and
**a 🟡 behind a ⛔ may not survive the next board — do not chase it**.
**When a rubric has no satisfiable head, removing the subject is an answer** — provided the work
lands somewhere, and you say where. Twice: #6188 (r675) and #6093 (r681).
**Deleting a declaration means deleting what advertises it** — docstring bullets, overview prose, and
any `variable` only it used.
**A green PR is not a place to apply a lesson** — but an *ejected* one is not green, whatever its
four sweep fields say. Act only on `queuepos.py` saying **`EJECTED`**; `NEVER-QUEUED` (#5950) is not
this role's to fix.
**`queuepos.py` judges EJECTED against the LATEST `ready-to-merge` transition** (r700) — an enqueue from an
earlier transition is not this one's; before r700 it told a freshly 10/10 #6093 to merge main and push.
**Replace an exact block, never a range between two anchors** — r700's range deleted `pr_list_cmd`.
**Self-posted 10/10 boards enqueue like the pipeline's own** (r700); today's label→enqueue gap is 17–53 s.
**A `private` declaration is not a rooting target** — no one outside can use the dot notation it
would enable (r691 skipped two). **`open Module` makes `Basis` mean `Module.Basis`** — check the
receiver's real head constant before trusting `mathlibns`'s count for the short name.
**`decldiff` and `rootsurplus` see `open` since r703**: re-namespacing to the receiver's real head,
e.g. `TauCeti.Basis` → `Module.Basis` under `open Module`, prints `ROOTED-VIA-OPEN` (still blocking --
say in the body that `M.X` is the receiver's real head) and `FLAGGED-VIA-OPEN` instead of `SURPLUS`.
**A proof can be changed without an elaborator when the design is read off exact signatures** -- #6093's
`@[expose]` removal went green first try because `monodromy_eq_of_map_eq`'s `Γ : Quotient ex.1 ey`
was read, not guessed, and every cross-module consumer was read before the push.
Verify a rooting target with `mathlibns.py`, never a grep; then **gate it**. **A WHOLE ratio does not
settle a target.**
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form —
**nor whether `to_additive` can derive a name it was given** (`toaddname.py` asks; only CI answers).
**A rooting can break an attribute whose own text never changed** (#6482).
**`stale` on a board means approved-earlier/re-run-pending, not a finding**; `absent` means not yet
judged on this head. `threadread.py` classifies both as NOT ACTIONABLE — answer **LIVE** only.
**166 controls, 0 failed** (r722) — the round prompt still says 129; the prompt is stale, not the suite.
**An API error is not an empty answer** (r722). The `gh` login is shared with other sessions, so the hourly quota
can run out mid-round. `sweep.py` now prints `API-ERROR` and exits 1, and `queuepos.py` prints `UNRUN` (exit 2) or
`UNKNOWN` — **rerun; never act on those rows**. Before r722 an unreadable merge queue could print `EJECTED`.
`gh api rate_limit` shows the remaining quota and the reset time.
**`awk length` counts BYTES** — `≤`, `σ`, `γ`, `ℝ` are multibyte. Measure line width in codepoints (Python)
before rewrapping anything (r704: 3 of 14 reported overflows were not).
**A PR that deletes a file** is screened since r704 (`deleted:` in the header; `--deleted` for stalequal and
decldiff). **`deadpath` only resolves names inside `_root_.` declarations** — a catch-up PR's Mathlib names
need a read of Mathlib's source, and a `public` check: a non-`public` declaration in a `module` file is
invisible to Tau Ceti.
**HANDOVER.md §11–13 carry this watch's rules** — read them before re-deriving one.
