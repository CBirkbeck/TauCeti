# Last round — r1040 (2026-09-24T11:49Z)

## PR rotation (user directive, 2026-09-14) — read this first

The PRs this role opens now **alternate between three kinds, in order 1 → 2 → 3 → 1**:

1. **Mathlib catch-up** — work that has landed in pinned Mathlib and duplicates TauCeti: refactor TauCeti
   onto the Mathlib version and delete the local copy (no aliases, per `.claude/CLAUDE.md`).
2. **File pass** — pick one file, run `/cleanup` and `/mathlibable` (mathlib-quality plugin) on it, with
   ChatGPT `gpt-6-astra` helping.
3. **What this role has been doing** — rooting, dedup, hypothesis weakening, docstrings, relocation.

**Second cycle, kind 1 open:** kind 3 **#6855 merged** (05:43:53Z, r798). Kind 1 **#6851** and kind 2 **#6854** are 10/10
but were flushed from the queue for the bot's Mathlib bump (r798). The freed slot went to kind 1 again: **#6875** (ready since r801),
Mathlib's deck group (r798), which needs a **human merge** because it updates `web/examples/Examples.lean`. Kind 2 opened as **#6896** (r843) and kind 3 as **#6899** (r844); both are now `ready-to-merge`. Kind 1 had no target at
pin `30a58f795a` (r845), so kind 2 went again as **#6902** (PseudoHyperbolic cleanup). Then came kind 3 as **#6910** (r847,
Vandermonde dedup), kind 2 as **#6911** (r848, Resolvent/Basic.lean style pass, now `ready-to-merge`), kind 3 as
**#6915** (r853, three private strict hypotheses), and kind 2 again as draft **#6923** (r857, `Winding/Number/Segment/Jump.lean`
style pass, since kind 1 is still dry at `30a58f795a`). Kind 3 then opened as draft **#6933** (r861, the `Subcomodule/Comap.lean` dedup), and kind 2 went again in kind 1's slot as draft **#6941**
(r865, `Residue/Theorem.lean` style pass; the pin is still `30a58f795a`). Kind 3 then opened as draft **#6945** (r869, the `ExchangeableAt.of_lt` dedup), and kind 2 went again in kind 1's slot as draft **#6947** (r873,
`Arrays/ZeroOne.lean` style pass; the pin is still `30a58f795a`). Kind 3 then opened as draft **#6950** (r874, two dead `have`s in `Recut/Pairing.lean`), and kind 2 went again in kind 1's slot as draft
**#6952** (r878, `Winding/Number/Segment/Formula.lean` style pass; the pin is still `30a58f795a`). Kind 3 then opened as draft **#6953** (r879, two dead `have`s in the Weierstrass equation differential). Both merged
2026-09-22. Kind 2 went in kind 1's slot as **#8101** (r881, `Cesaro/Convergence.lean`, now `ready-to-merge`), kind 3 as draft
**#8224** (r882, `norm_resolvent_integrand_le` to `0 ≤ t`), and kind 2 again in kind 1's slot as draft **#8233** (r882,
`Residue/Basic.lean` style pass; the pin is still `dc4b8d60d5`). **The next opening is kind 3.** Record each PR's kind in the ledger. **Step 5's cap counts only PRs still in progress** (user directive, 2026-09-15 ~15:00Z): drafts and
`awaiting-review`, `awaiting-author` or `ci-failed` PRs count. `ready-to-merge` and queued PRs do not, and neither
does #5950. Do not idle waiting for merges: open the next kind whenever fewer than 3 are in progress.

**Open question to Chris (asked after r732, unanswered at r856):** `/cleanup` has not run in full on any staged
PR. Kind 2 had a static partial pass (report in `pending/`), kinds 1 and 3 none, because `/cleanup`'s Phase 0
`lake build` and its diagnostics gate are forbidden here. Asked whether a local build is now allowed, and whether
kinds 1 and 3 get a pass scoped to the declarations they change. Kind 1 (#6851) opened at r746 under the announced
no-build default, and so did kinds 2 (#6854, r749) and 3 (#6855, r750) and kind 1 again (#6875, r798). **If he
answers:** #6851 and #6854 are 10/10, so a push to either would cost the board. Give them a separate follow-up PR
instead. #6875 is mid-review (fixes pushed at r803), so a scoped pass can still go into it directly.

**ChatGPT access:** no `chatgpt-math` MCP server is configured (only `lean-lsp`). The model is reachable
through the local codex CLI that MCP wraps:
`codex exec --skip-git-repo-check -m gpt-6-astra -c model_reasoning_effort="high" -o <answer-file> "$(cat <question-file>)" < /dev/null`
(the form the plugin's voyager skill uses). Run it from the scratchpad, where it cannot build anything. Outside a git repository the
flag is required: without it codex prints `Not inside a trusted directory` and exits with no answer (r857).

## Board

| PR | head | CI | state | whose move |
|---|---|---|---|---|
| **#8570** | `ee586dc07` | green | kind 2 (`DenseGraphLimits/Representability/Moebius.lean`: 43 `↦`). **Approved** by the pipeline (11:42:48Z, 8 min after ready); `ready-to-merge` | **queue** |
| **#8577** | `e6b34bcb5` | green (11:39:06Z) | kind 2 (`Wishart/Transforms.lean`: 36 `↦`; `Roadmap: StandardDistributions`). Astra cleared it; **marked ready 11:40Z** (r1039) | **external reviewers** |
| **#8578** | `64f6f0612` | green (11:38:27Z) | kind 2 (`Induction/Mackey/Decomposition.lean`: 38 `↦`; `Roadmap: RepresentationTheory`). Astra cleared it; **marked ready 11:40Z** (r1039) | **external reviewers** |
| **#8586** | `fb68ebd34` | queued | kind 2 (`Contour/Chord/QuotientAsymptotics.lean`: 38 `↦`, the first calc step's chain split; gate 12/0/0; `Roadmap: ContourIntegration`). **Draft**; **astra cleared it** (r1039); base `9889e2022` | **CI** — mark ready when green |

**In progress (cap full): #8577 and #8578 (ready 11:40Z; 12:40Z) and the draft #8586 (QuotientAsymptotics; astra ✓; build queued).** #8570 is `ready-to-merge`; **#8563 merged 11:36:11Z** (r1040), the forty-fifth.
**Staged:** nothing (QuotientAsymptotics went as #8586 at r1040). Next kind 2: `Arrays/Extreme.lean` (38, 2), `MixedIID/Const.lean` (38, 2), `WorkedExamples/HalfDisc/Basic.lean` (37, 3), `Kostant/Form.lean` (36, 1), `ProbabilityMeasure/Ext.lean` (36, 1); or re-score.
**#8426 merged 23:47:10Z** (r970), #8413 at 23:37:48Z (r969) and #8402 at 23:06:21Z (r966). Twenty of this session's PRs merged on 2026-09-23. Skip `VanishingMoments.lean` as a kind-2 target (roadmap text is woven through its docstrings).

**The staged kind-2 branch was opened as #8273 (r902), and kind 3 as #8275 (r903, `RelNorm.lean`).** The next opening is kind 1 if the pin
has moved; otherwise kind 3 again while astra is out (until 2026-09-27T15:04Z). The staged GlobalTurning branch went as #8286 (r908). The r843 `not_mem_maxAvoid` rename went as #8291 (r910).
Remaining kind-3 target: the private `integral_Ioi_eq_Ioc_add_Ioi` in `Resolvent/Basic.lean` (`0 < h` → `0 ≤ h`, cosmetic); re-run the scanners for more. Remaining kind-3 targets: the `GlobalTurning.lean` `i ≤ j` weakening (item 5), and the private `integral_Ioi_eq_Ioc_add_Ioi` in `Resolvent/Basic.lean` (`0 < h` → `0 ≤ h`, only `hh.le` used), now unblocked since #8224 merged. #6952 and #6953 merged on 2026-09-22 (15:27:14Z and 18:02:40Z). Main is `cdd847a11`, the Mathlib pin
`dc4b8d60d5`, and the toolchain `leanprover/lean4:v4.34.0-rc2`. **Cron `4b5d0e55`** fires this round every 10 minutes (at
:03/:13/…/:53); it is session-only and expires 2026-09-30. **Handover:** `fork handover/improve-toolkit` tip is `5c20c37ec`
(r902); sync each round from the tip recorded here, with a lease on it.

## What to expect next

**The r889 hard stop was LIFTED at r931 (17:25Z):** `gpt-6-astra` and `gpt-5.6-sol` both answer again, days before the stated reset.
Step 4 drives and kind-2 astra passes are back. Before any drive or astra run, probe with a one-line `codex exec -m <model> "Reply ok"`;
a usage-limit error means the stop applies again (a drive then posts an all-⚠️ error board, as at r889).


0. **Now (r1014):** #8525 got `documentation` changes requested (provenance sentence); fixed at `e5b5676d1`, body updated. #8521
   driven 07:29Z. #8526 ready 06:45Z (07:45Z). **New `documentation` reading (r1014): proof-provenance sentences ("adapted from
   split-branch commit …") also count as dated text; keep the mathematical reference in the docstring and put provenance in the PR body.** VariableLp is staged (above). Next kind 2: the read
   roadmap-bearing r976 hits [`Integrated/Basic.lean` staged], [`JHolomorphic/Prod/Basic.lean` #8526], [`VariableLp.lean` staged]
   (status/motivation roadmap text), or re-score. Drives cost ~$1 each, not ~$16, but the process then hangs ~15–20 min in its archive push to `TauCetiData` (403 retries) after
   posting: run drives in the background and read the board, not the exit. Probe the codex quota
   before any drive. **Next kind 2**, from the r976 re-score (`snap-main11`, main
   `e697269a7`; arrow-only files with ≥45 `fun … =>`, excluding open-PR and ledger-named files; columns arrows/roadmap/chains), roadmap-free first:
   [`CondExp.lean` #8497], [`CutNormLimit.lean` #8491], [`DifferenceQuotient.lean` #8499],
   [`PDE/Spectrum.lean` #8492], [`Wishart/Basic.lean` #8503], [`DriftMaximumPrinciple.lean` #8510],
   [`HopfLemma.lean` #8508]. The biggest is `PDE/EnergyForm/Integrated/Basic.lean` (156/2/0); read its 2 roadmap lines first. **Declined `ClassicalGroups/Rational.lean`** (r975): the roadmap is its cited design source (References
   section and four prose mentions), so removing it invites an `attribution` finding and keeping it a `documentation` one, the #8332 conflict.
   Roadmap mentions in docstrings are deleted outright (r939 rule), or replaced by a plain scope statement.
1. **Queue:** `queuepos.py` each round; act only on `EJECTED`, and first read the removal reason (GraphQL
   `RemovedFromMergeQueueEvent.reason`): a bot Mathlib-bump flush reads `manual`, is not a failure, and
   `merge-sweep` re-enqueues a green TauCeti/-only PR afterwards (r798–r799). A `MERGING` PR's group build is the check-runs of
   `git ls-remote origin 'refs/heads/gh-readonly-queue/main/pr-<n>-*'` (r739), the earliest sign of an ejection. If main moves a lot, re-run r702's
   merge-group simulation (cheap, read-only; r878: all fourteen open heads (#6875, #6896, #6899, #6902, #6910, #6911, #6915, #6923, #6933, #6941, #6945, #6947, #6950 and #6952) clean against `e0103897b`; #6953 (r879) was branched from that same commit). Staged branches:
   `git merge-tree --write-tree --name-only origin/main <branch>` checks them without a checkout (r750: none
   left; kind 3 opened as #6855). A merge-tree check sees conflicts, not new
   callers: also grep main's new lines for the names each staged branch removes, and when main DELETES declarations,
   grep every branch's added lines for them (r738: #6601 removed `sum_binomial_weight(_mul)`; 0 uses). Print a firing
   control: r738's first try was a crashed `sed` whose empty result read as "none".
2. **Everything from the 2026-09-15 batch has merged**, as have #6952 and #6953 (2026-09-22) and Chris's #5950. None of it
   needs watching.

3. **A draft nobody marks ready gets parked.** `tauceti-review-bot` swapped `awaiting-review` → **`on-hold`** on #6952 and #6953 at
   2026-09-16T07:33Z, six days before this round. The label means "Draft PR or explicitly held by a keep/hold/wip/human/do-not-close
   label" — it is automatic, not a human hold, and the pipeline stops looking at the PR until it leaves draft.

4. **A green build ages out at a pin bump.** Both PRs still showed CI green from 2026-09-15, but Mathlib's pin had moved twice since.
   r881 rebased both onto fresh main and re-gated before marking them ready, so the builds that matter ran against `dc4b8d60d5`.


5. **Next kind-3 turn — ready target (r891 scans):** (a) ~~`RelNorm.lean` dead `hJ'`~~ TAKEN by #8275 (r903); (b) `SchwarzChristoffel/GlobalTurning.lean:94`: weaken
   `schwarzChristoffelEdgeAngle_sub_eq_neg_pi_mul_sum_Ioc`'s `i < j` to `i ≤ j` (only `hij.le` is used; one caller, line 120). Check each file
   against a fresh open-PR list first. Older kind-3 notes follow. Kind 3 went as #8235 (ConvexSubgroup `mabs_mem_iff`). Queued kind-3 candidates for later: `not_mem_maxAvoid` →
   `notMem_maxAvoid` (a rename: the file's other names already say `notMem`; update every caller, with no alias), plus the following, of which the first is TAKEN by #8235:
   * the r843 `Algebra/Order/Group/ConvexSubgroup.lean` leftovers (#6896 merged, and no open PR touches the file):
     `mem_of_mabs_le_mabs` and `mem_closure_singleton` rebuild `|h|ₘ ∈ H` by cases where Mathlib's `mabs_mem_iff` gives it. Check
     that `mabs_mem_iff` is still at the pin and fits the statement before cutting.
   * ~~`gammaPDFReal_of_pos`~~ — **gone from main (r887)**, dropped.
   Re-run the scanners on fresh main as well (`strictscan`, `deadhave`, `unusedscan`). The private `integral_Ioi_eq_Ioc_add_Ioi`
   in `Resolvent/Basic.lean` also uses only `hh.le`, but it shares a file with #8224: wait for #8224 to merge. The kind-1 scan is dry at
   `dc4b8d60d5`; re-run it after the next pin bump.

## Kind-1 prospects (r703 first pass, r798 re-run, r881 re-run at pin `dc4b8d60d5`)

**r881 re-run: dry.** Between pins `30a58f795a` and `dc4b8d60d5` Mathlib changed 383 files and added 255 declaration headers.
Sixteen of those names are also declared in TauCeti, and all but one family are generic category-theory spellings (`of`, `lift`,
`pi`, `image`, `dim`, `proj`, `limit`, `coe_of`, `prodFst`, `prodSnd`, `I`, `H0π`). The `wordProd` family looked promising and is
**a false positive**: Mathlib's new `Group.Generators.wordProd` (`Mathlib/Geometry/Group/WordProd.lean`) evaluates *signed* words
`List (ι × Bool)` over a generating family via `P.lift (FreeGroup.mk l)`, while `TauCeti.wordProd` multiplies an *unsigned*
`List b.support` of simple reflections into `P.weylGroup`. Same name, different notion — Mathlib's own docstring says it is
modelled on the separate unsigned `CoxeterSystem.wordProd`, which TauCeti's `GroupTheory/Coxeter/*` files already use. Adopting it
would mean a `Group.Generators` instance and signed words through 18 files: a redesign, not a catch-up. Re-run after the next bump.

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
* **OPENED in r798 as draft #6875 — deck group — mathlib4#40135 (landed 2026-08-27).** Mathlib `deck p : Subgroup (E ≃ₜ E)`, carrier
  `p ∘ h = p`; TauCeti `TauCeti.Deck p`, carrier `∀ e, p (φ e) = p e` — equal, **not defeq**. 36 files /
  837 lines name `Deck`, but few sites depend on the carrier (`.2 e` ≤ 14, `∈ Deck` 3, `mem_iff` 3).
  TauCeti's extras (`fiberHomeomorph`, `mapsTo_fiber`, `smul_eq_apply`, `deck_comp_of_injective`) have
  no Mathlib counterpart.
* **Checked, nothing to do:** mathlib4#40303 (`xRep`) is consumed, not duplicated; the #38813 hit was
  #38909, whose lemmas `GradedRing.lean` already consumes.
* **r798 re-run on `d7ac608e0`:** the same 13 collisions. Of the 36 cited Mathlib PRs only #36845, #40135 and #39722 have
  merged (bors: read `closedAt`), and #39722 landed after the pin.

## Kind-2 pass notes (r705)

`/cleanup` and `/mathlibable` (in `~/.claude/plugins/marketplaces/mathlib-quality-plugins/commands/`) both start
with `lake build` and gate every edit on `lean_diagnostic_messages` — **forbidden here**. Run their static phases only
(audit, literature, Mathlib search, generality, composition, verdict); CI compiles. Mathlib search without a local
build: the lean-lsp **remote** tools `lean_loogle`, `lean_leansearch` and `lean_leanfinder` (confirm every hit at the
pin), plus grep. Never the file-based lean-lsp tools. ChatGPT: `codex exec -m gpt-6-astra` (see the rotation section).
Full artifact: `pending/quadratic-discriminant-report.md`. Reference docs:
`~/.claude/plugins/marketplaces/mathlib-quality-plugins/skills/mathlib-quality/references/`.

## What r703–r965 did

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
* r728: quota exhausted again at :16 (API-ERROR rows, nothing acted on); rerun clean; main moved, all still clean.
* r729: no-op board.
* r730: main moved (#6689); queued merge groups and staged branches re-checked, all clean.
* r731: main moved (#6658, beside #6796's Clifford files); re-checked, all clean.
* r732: main moved (Krull dimension merge); queued merge groups and staged branches re-checked, all clean.
* r733: main moved (#6773, ModularForms); queued merge groups and staged branches re-checked, all clean.
* r734: REST quota ran out at 19:16 (the third :16 round); rerun after the :17 reset clean; no-op board.
* r735: main moved (#6514, renames a module); queued merge groups and staged branches re-checked, all clean.
* r736: main moved (#6738); queued merge groups and staged branches re-checked, all clean.
* r737: main moved (#6681); queued merge groups and staged branches re-checked, all clean.
* r738: #6093 MERGING; main moved (#6601 deletes two lemmas, which no branch uses); all re-checked, all clean.
* r739: no merges; #6093's merge-group build in progress (read off the queue ref's check-runs); no-op board.
* r740: REST quota ran out at 20:16 (the fourth :16 round); rerun clean; #6093's merge-group build passed.
* r741: no merges for 36 min; the queue's top two groups built green and wait on a queued publish job.
* r742: still no merges (46 min): 427 queued Actions runs saturate the hosted runners the publish job needs.
* r743: backlog draining (413 queued runs); queue head #6744's publish started after 39 min; no merges yet.
* r744: both top groups published; each waits on a queued finalize job (386 queued runs); no merges for 66 min.
* r745: both finalize jobs still queued (20 and 15 min); backlog down to 331 runs; no merges for 76 min.
* r746: #6744 then #6093 merged (21:07, 21:09); all re-checked clean; step 5 fired, and kind 1 opened as draft **#6851**.
* r747: quota at 21:16 again; rerun clean; #6851's first build running; staged branches clean against #6093's merge.
* r748: #6796's merge-group build passed; #6851's first build still running (12 min); no merges.
* r749: #6796 and #6800 merged; #6851 green and marked ready; step 5 opened kind 2 as draft **#6854**.
* r750: step 5 opened kind 3 as draft **#6855**; #6851 awaits its board; #6854's first build running.
* r751: main moved (#6746, additive); my three open PRs still merge clean; both drafts building; #6851 no board yet.
* r752: #6854 green and marked ready; main moved (#6733, restated a lemma none of mine uses); #6855 still building.
* r753: quota at 22:16 again; #6855 green and marked ready; all three kinds now ready and awaiting boards.
* r754: main moved (#6702 beside #6851's geodesic files; #6731 renames a module); #6851 re-simulated clean; no boards yet.
* r755: #6851 and #6855 went 10/10 on their first boards and queued; #6855's merge group simulated clean; #6854 awaits its board.
* r756: main moved (#6763); #6851 and #6855 re-simulated clean (queue 32/30); #6854 still awaits its board.
* r757: main moved (#6765); #6851 and #6855 re-simulated clean (queue 31/29); #6854 still awaits its board (49 min).
* r758: no merges; #6854 at its drive window with no board (59 min); held one round, and the 23:16 round drives if still none.
* r759: quota at 23:16 again; main moved (#6769, #6636), all clean; #6854 driven at 71 min, blocked `scope` (an
  unrelated golf), fixed in `217fecb81`.
* r760: no merges; #6854's fix building (board BEHIND, so no re-fix); #6851 and #6855 still queued (29/27).
* r761: main moved (#6775, additive); queued PRs re-simulated clean (28/26); #6854's fix still building.
* r762: no merges; #6854's fix green (23:39Z), re-review pending (drive clock 00:39Z); queued PRs unchanged (28/26).
* r763: main moved (#6709; #6741 restated `exists_common_X_pow_factor`, which none of mine uses); queued PRs
  re-simulated clean (26/24); #6854's re-review pending.
* r764: no merges; #6854 relabelled `awaiting-review`, no new board 27 min after CI-green; queued PRs unchanged (26/24).
* r765: quota at 00:16 again; main moved (#6829, additive); queued PRs re-simulated clean (24/22); #6854 still not re-reviewed.
* r766: main moved (#6652 removes `polarBilin_isSymm`, which none of mine uses); queued PRs re-simulated clean (24/22);
  #6854 still not re-reviewed.
* r767: no merges; #6854 at 57 min after CI-green with no re-review (window opens 00:39:06Z; the 00:46 round drives
  if still none).
* r768: #6854 driven at 67 min → **10/10** ($0.91); main moved (#6635); queued PRs re-simulated clean (23/21).
* r769: #6854's board is ON-HEAD but its label is stuck in the Actions backlog; main moved (#6597); queued PRs clean (21/19).
* r770: #6854 relabelled and QUEUED (32), so all three kinds are queued; main moved (#6718, a Lie refactor removing 14
  declarations, none used by mine); all re-simulated clean.
* r771–r772: lost to a full `/tmp` (ENOSPC; every command failed, and nothing was read, recorded or changed).
* r773: space back (another session held 24G of `/tmp/claude-1001`); board unchanged; queue slow again (195 queued runs).
* r774: queue moving (14/16/28); main moved (#6665, #6822, additive); all three re-simulated clean.
* r775: no merges; board unchanged; `/tmp` at 28G and climbing (the other session's scratchpad is 27G); flagged again.
* r776: main moved (#6843 renames a module; #6686); module-rename grep and all three simulations clean; queue 12/14/26;
  `/tmp` steady at 45%.
* r777: quota at 02:16 again (reset 02:19:08Z); rerun clean; no merges; queue unchanged (12/14/26).
* r778: no merges for 20 min; the queue head's group has built, and its publish job waits on runners (166 queued); board unchanged.
* r779: no merges for 30 min; board and queue unchanged.
* r780: main moved (#6735 generalizes `tendsto_nsmul_apply_div_of_hasDerivAt`, unused by mine); all three re-simulated clean (11/13/25).
* r781: main moved (#6834, additive; the kind-3 candidate `norm_resolvent_integrand_le` untouched); all three re-simulated
  clean (10/12/24).
* r782: no merges; board and queue unchanged (10/12/24).
* r783: quota at 03:16 again; no merges; queue unchanged; `/tmp` at 52% (the other session is at 32G, with a new 4.4G
  `wt-center`); flagged again.
* r784: no merges for 32 min; board and queue unchanged (10/12/24 of 41); `/tmp` steady at 52%.
* r785: main moved (#6821, additive, in optimal transport); all three re-simulated clean (9/11/23 of 40).
* r786: main moved (#6685: the Monge problem, plus a `Probability/HasLaw.lean` edit unused by #6855); all three re-simulated
  clean (8/10/22 of 41).
* r787: main moved (#6868, CI only: review pins now carry approvals across an unchanged patch); no Lean change, so r786's
  simulations stand.
* r788: no merges; board and queue unchanged (8/10/22 of 45).
* r789: quota at 04:16 again; main moved (#6621, additive); all three re-simulated clean (7/9/21 of 44); `/tmp` at 58%
  (the other session is at 35G, with a new `wt-countable`).
* r790: main moved (#6640, additive); all three re-simulated clean (6/8/20 of 43).
* r791: no merges; board and queue unchanged (6/8/20 of 43).
* r792: no merges for 29 min; board and queue unchanged (6/8/20 of 43).
* r793: no merges for 39 min; the queue's top two groups have built and published, and their finalize jobs wait on
  runners (204 queued); board unchanged.
* r794: the queue moved (#6847 and #6637 merged); all three re-simulated clean (4/6/18 of 45).
* r795: no merges; board and queue unchanged (4/6/18 of 46); the REST quota held through the :16 round.
* r796: main moved twice (#6643, #6611; nothing removed; the one grep hit was a docstring word); all re-simulated clean; #6855 MERGING at 2 of 44.
* r797: no merges; queue unchanged (2/4/16 of 44); both top groups still in `sandboxed-build` at 05:37Z.
* r798: #6855 merged (05:43:53Z), so step 5 fired and kind 1 opened as draft #6875 (Mathlib's deck group; human merge for `web/examples`). The bot flushed the queue for its bump #6852, so #6851 and #6854 read `EJECTED`.
* r799: REST out until 06:24:59Z; corrected `queuepos.py`'s stale EJECTED advice (the merge sweep re-enqueues flushed green PRs; controls 166/0); #6875's first build running; #6852 still alone in the queue.
* r800: no merges; #6875's first build and #6852's group build still running; the merge sweep has not re-run (last 05:18:46Z).
* r801: #6875's first build went green (06:38:24Z), so I marked it ready at 06:46:57Z; no merges; #6852's group build still running (31 min).
* r802: no merges; #6875 has no board yet (clock to 07:47Z); #6852's group build at 41 min of an expected 83–95.
* r803: #6875's first board went 7/10 (changes requested: naming, placement, documentation). I fixed all three in `462ed9705` (24 declarations into `deck`, one import dropped, 33 docstrings trimmed), pushed it, and updated the body; no merges.
* r804: #6875's fix head is building (its board is behind, so nothing to re-fix); #6852's group build at 77 min; no merges.
* r805: no change 3.5 min after r804; #6852's group build at 81 min.
* r806: no merges; #6875's fix head at 15 min of CI; #6852's group build at 91 min.
* r807: #6875's fix head went green (07:49:13Z) and awaits re-review (clock to 08:49Z); #6852's group build at 101 min, its hold lapsing at 09:12:38Z; no merges.
* r808: #6852's group build failed after 102 min and the queue evicted it (`failed_checks`, 07:57:43Z); #6826, #6808 and #6871 queued; #6851/#6854 still wait for the merge sweep; no merges.
* r809: REST out 08:16–08:27; #6875 still has no board for its fix head (clock to 08:49Z); no merges.
* r810: no change; queue depth 5, none mine; #6851/#6854 still wait for the merge sweep; no merges.
* r811: no change; queue depth 6, none mine; #6875's re-drive clock runs to 08:49Z; no merges.
* r812: no change; #6875 still has no board or live marker for its fix head, 2.5 min short of the clock; no merges.
* r813: #6875 went 10/10 on its re-review (08:54:23Z), so no drive; it waits for Chris's merge. Main moved to `43d510787` (#6826, which renames `CandidateGenusField/Real.lean`); all three PRs re-simulated clean, and no branch names the renamed module.
* r814: main moved to `4ea08bc2f` (#6808, one new file); all three PRs re-simulated clean; #6875's label still lags its 10/10 board.
* r815: no merges; #6875's label still `awaiting-review` 22 min after its 10/10 board; queue depth 5, none mine.
* r816: REST out 09:26–09:27; the low-memory watchdog killed the background wait for the reset, so the sweep reran in the foreground; no change, no merges.
* r817: #6875's label moved to `ready-to-merge` (~09:28Z) and it reads NEVER-QUEUED, as a PR auto-merge refuses; no merges.
* r818: Actions backlog at 361 queued runs; #6875's only pending check is a runnerless `zulip-pr` job (build green); no merges for 48 min.
* r819: no change; backlog 336 queued runs; queue depth 12, none mine; no merges for 58 min.
* r820: main moved to `8c4c13530` (#6871, #6849, which deletes 27 points-functor names); all three PRs re-simulated clean; #6875 fully green; backlog down to 217.
* r821: no change on my PRs; the backlog cleared to 40 queued runs and the queue refilled to 25; no merges.
* r822: the merge sweep finally ran (10:24:54Z) and failed after 14 s (exit 1; log unread, REST out until 11:27:41Z); main moved to `31fc2e21e` (#6659, #6717); all three PRs re-simulated clean.
* r823: the sweep failure was transient (it could not read queue entry #6751's files, and it fails closed; the call reads cleanly now); REST came back before its stated reset; no change on my PRs; no merges.
* r824: eight queued round prompts coalesced; main moved 8 commits to `62cfc4d65` (2 module renames, 2 deletions); all three PRs re-simulated clean; three grep hits read and false; no merge sweep since the 10:24Z failure.
* r825: no change, 3 minutes after r824; no merges.
* r826: no change; no merges since #6727; backlog up to 66 queued runs.
* r827: main moved to `f7a8984cb` (#6693 Riemannian path length, #6876); nothing removed; all three PRs re-simulated clean.
* r828: no change; no merges since #6876; queue depth 35, none mine.
* r829: main moved to `7cae20a91` (#6626, quantile functions); nothing removed; all three PRs re-simulated clean.
* r830: main moved to `a9313057f` (#6809, one new quaternion file); nothing removed; all three PRs re-simulated clean.
* r831: main moved to `c38794df8` (#6747, Schwarz–Christoffel polygon boundary; one module moved, nothing removed); all three PRs re-simulated clean.
* r832: main moved to `82f5e9ac2` (#6770 DG right modules, #6795 circle Peter–Weyl; nothing removed); all three PRs re-simulated clean.
* r833: REST out at 13:26Z (back by 13:28:48Z); a GraphQL read (new `sweep-gql.py`) and the rerun agree: no change, no merges. The quota probe had used `rate_limit`'s own headers; probe a real call.
* r834: main moved to `581339e13` (#6781 smooth link isotopy, one module moved; #6698 natural density; nothing removed); all three PRs re-simulated clean.
* r835: no change; no merges since #6698 (main still `581339e13`); REST held (4959 left).
* r836: main moved to `6f51dd839` (#6732, the quaternion symbol (a, -a); prose and one `variable` line removed, no declaration); all three PRs re-simulated clean.
* r837: main moved to `a62443626` (#6704, Frobenius orbit sizes over a finite field; nothing removed); all three PRs re-simulated clean.
* r838: main moved to `6550e8186` (#6776, the universal resolvent at a polynomial; its one removed line is an import re-added in re-sorted order); all three PRs re-simulated clean.
* r839: main moved to `46c3b38ac` (#6840, induction on representation-ring modules; `Induction/FiniteDimensional.lean` moved to `FiniteDimensional/Basic.lean`, no declaration removed); all three PRs re-simulated clean; the grep's one hit (`function`) was prose on both sides.
* r840: main moved to `40c612666` (#6874, rational refinements of covers of the adic spectrum; nothing removed); all three PRs re-simulated clean.
* r841: main moved to `fc7a5c329` (#6842, Chevalley generators from a minuscule weight table; an E6/E7 refactor that removes 19 declarations, none used by my PRs); all three PRs re-simulated clean.
* r842: no change; no merges since #6842 (main still `fc7a5c329`); queue depth 35, none mine.
* r843: user directive — `ready-to-merge` and queued PRs no longer count toward the cap. Kind 2 pass on `ConvexSubgroup.lean` opened as draft **#6896** (non-strict exclusion lemmas; gate 12/0/0).
* r844: kind 3 opened as draft **#6899** (`chafaiRescaling_coe_of_pos` → `chafaiRescaling_coe_of_nonneg`; gate 12/0/0). `unusedscan.py` now treats `split_ifs` as context-consuming (controls 166/0).
* r845: kind 1 found no target at pin `30a58f795a` (the 13 name collisions are TauCeti generalisations; the checked "Mathlib has no X" notes hold). #6896 green and marked ready. Kind 2 again as draft **#6902** (PseudoHyperbolic cleanup; gate 12/0/0; gpt-6-astra reviewed the edits).
* r846: the merge sweep ran clean (15:15:27Z) and re-queued #6851 (38/72) and #6854 (35/72). Main moved to `591746fa6` (4 merges, one module moved); #6851, #6854, #6875, #6896 and #6899 all re-simulated clean. #6899 and #6902 are still on their first builds.
* r847: #6902's first build failed on a term `rfl` (module export check). The same fix landed from Chris's account (`f8294ed14`) before mine, and my lease push was correctly rejected; #6902 is now green and ready. #6899 got a clean board (`ready-to-merge`). #6896 had no board after 92 min, so its review was driven. Main moved to `edcf25b9a` (7 merges), and all six PRs re-simulated clean. Kind 3 opened as draft **#6910** (Vandermonde dedup; gate 12/0/0).
* r848: #6896's driven review approved all 10 rubrics, so it is `ready-to-merge` (the `TauCetiData` sync 403 after posting is harmless). Kind 2 again as draft **#6911** (Resolvent/Basic.lean style pass; gpt-6-astra reviewed the edits; gate 12/0/0).
* r849: main moved to `c0295f4a9` (#6700; #6880 removes 48 points-functor declarations, none used by my PRs), and all seven re-simulated clean. #6910 and #6911 are still building; #6896 and #6899 await the merge sweep.
* r850: #6910 went green (17:32:21Z) and was marked ready. No merges; #6911 is still building; #6896 and #6899 still await the merge sweep.
* r851: main moved to `a30a47ee7` (#6726; one private declaration removed), and all eight re-simulated clean. #6911 went green (17:43:41Z) and was marked ready, so all three in-progress PRs await boards.
* r852: main moved to `102eadf1e` (#6677, additive), and all eight re-simulated clean. There are no boards yet for #6902, #6910 and #6911, and #6896 and #6899 still await the merge sweep.
* r853: #6911 approved (`ready-to-merge`). #6902's review, driven after its hour, approved 9/10, but `attribution` asked to keep the upstream credit, so `3282c9611` adds a `## References` entry (gate 12/0/0). Kind 3 opened as draft **#6915** (three private strict hypotheses). Main moved to `c3c47a5d8` (#5594, additive), and all eight re-simulated clean.
* r854: main moved to `3cbd4f4ca` (#6877, additive), and all nine re-simulated clean. #6902's fix and #6915 are building. #6896, #6899 and #6911 await the merge sweep, which has not run since 15:15:27Z.
* r855: main moved to `b3e8ec19b` (#6678, additive), and all nine re-simulated clean. #6902's fix and #6915 are still building; #6910 cannot be driven before 18:37Z.
* r856: #6902's fix went green (18:32:05Z). #6915 went green and was marked ready (18:37:18Z). #6910 had no board after its hour, so its review was driven (18:37:56Z). No merges.
* r857: #6910's driven review approved all 10 rubrics (18:41:05Z, $0.87), and it queued (54/55). Main moved twice, to `871fb6d9f` (#6623, #6707) and `6f93392bd` (#6714), both times additively, and every PR re-simulated clean. The freed slot went to kind 2 again (kind 1 still dry): draft **#6923**, a style pass on `Winding/Number/Segment/Jump.lean` (gpt-6-astra reviewed; gate 12/0/0).
* r858: the merge sweep fired again (19:11:04Z, the first run since 15:15:27Z) and queued #6896, #6899 and #6911. Main moved to `906b08e84` (#6673, additive), and all ten PRs plus the staged branch simulated clean. With the cap full, kind-3 research staged `improve/subcomodule-comap-dedup` (`4d33cc423`, local only), which drops Comap.lean's duplicate private `comap_coact_mem`.
* r859: no change 3 minutes after r858. #6902 and #6915 were not yet due for a drive, #6923 was still building, and there were no merges.
* r860: #6923 went green (19:21:52Z) and was marked ready (19:28:01Z). Main moved to `a67007d22` (#6794, the Hecke tiling, which removed only prose), and all eleven heads re-simulated clean. No drive was due yet: #6902's window opens at 19:32Z and #6915's at 19:37Z.
* r861: both drives ran. #6902's re-review approved 10/10 (19:41:02Z, $0.91), and it queued. #6915's first board went 9/10 (19:41:46Z, $0.95): `api-design` asked for `one_add_sq_div_eq` to become a public lemma in a general module, and `08b8138bc` does that as `Real.inv_sqrt_mul_sq` in the new `TauCeti/Analysis/Real/Sqrt.lean`. The freed slot opened the staged kind-3 branch as draft **#6933** (gate 12/0/0). Main moved twice, to `2e0c1a0b2` (#6660) and `d791db95c` (#6619), and every head re-simulated clean.
* r862: no change 4 minutes after r861. #6915's fix and #6933 were still building, #6923 was not yet due for a drive, and there were no merges.
* r863: #6933's first build went green (20:05:45Z), and it was marked ready (20:07:08Z). #6915's fix was still building, #6923 was not yet due for a drive, and there were no merges.
* r864: #6915's fix went green (20:13:06Z) and awaits its board (drive not before 21:13Z). Main moved to `9cd85f80e` (#6883, #6881), which renamed one module, `RamificationInertia/DoubleCoset.lean` → `DoubleCoset/Basic.lean`; no branch names it. All eleven heads re-simulated clean.
* r865: #6923 had no board after its hour, so its review was driven (20:28:06Z) and approved 10/10 ($1.21); it queued. That freed a slot, and with kind 1 still dry at `30a58f795a`, kind 2 opened as draft **#6941**, a style pass on `Contour/Residue/Theorem.lean` (gpt-6-astra: no risk; gate 12/0/0). Main moved to `f7443c964` (#6706, #6782), which moved `VectorBundle/SectionAlongCurve.lean` to `SectionAlongCurve/Basic.lean`. The grep hits on #6851's along-curve API were read and false (main only added uses), and all twelve heads re-simulated clean.
* r866: no change 3 minutes after r865. #6941 was still building, no drive was due (#6933 at 21:07Z, #6915 at 21:13Z), and there were no merges.
* r867: no change 7 minutes after r866. #6941 was still building, no drive was due, and there were no merges.
* r868: #6941 went green (20:49:35Z) and was marked ready (20:58:05Z). Main moved to `be6dbc1cb` (#6720, #6612; #6720 edits a universal-cover file beside #6875's but names no `Deck`), and all twelve heads re-simulated clean.
* r869: both due drives ran. #6933's approved 10/10 (21:10:20Z, $0.81), and it turned `ready-to-merge`. #6915's round-2 re-review ran only `api-design`, which asked for `Real.inv_sqrt_mul_sq` to be `@[simp]`; `4f9c8d7cd` does it (pushed 21:18:40Z). The freed slot opened kind 3 as draft **#6945** (`ExchangeableAt.of_lt`, gate 12/0/0). Main moved to `c743c210c` (#6848, additive), and all thirteen heads re-simulated clean.
* r870: no change 2 minutes after r869. #6915's fix and #6945 were still building, #6941 was not yet due for a drive (21:58Z), #6933 queued at 73, and there were no merges.
* r871: #6915's `@[simp]` fix went green (21:36:18Z; drive not before 22:36Z). #6854 is MERGING at 2, its group build running since 21:31:44Z behind #6860. Main moved to `dc381d667` (#6857, a `/cleanup` pass that re-roots `commutatorCongr` as `MulEquiv.commutatorCongr` and removes 8 names no branch uses). The `lift` and `congr` grep hits were prose and a tactic, and all thirteen heads re-simulated clean.
* r872: #6945 went green (21:37:02Z) and was marked ready (21:47:11Z; drive not before 22:47Z). #6854 was still MERGING at 2, #6941 was not yet due for a drive (21:58Z), and there were no merges.
* r873: **#6854 merged** (21:52:04Z, with #6860), and #6851 is MERGING at 2. #6941's review, driven after its hour (21:58:10Z), approved 10/10 ($1.22), and it queued. That freed a slot, and with kind 1 still dry at `30a58f795a`, kind 2 opened as draft **#6947**, a style pass on `Arrays/ZeroOne.lean` (gpt-6-astra: no risk; gate 12/0/0). Main moved to `689c8bf27` (#6860, #6854, additive), and all twelve open heads re-simulated clean.
* r874: **#6851 merged** (22:11:28Z, with #6853). The local worker approved #6915's `@[simp]` fix 10/10 (22:06:19Z), and it queued, freeing a slot. Fresh scans on `689c8bf27` found no new strict, implied, unused-binder or duplicate-signature target, so kind 3 opened as draft **#6950**, dropping two `deadhave`-flagged unused `have`s in `Recut/Pairing.lean` (gate 12/0/0). Main moved to `14754a1d1` (#6853, and #6851, which deletes 24 Levi-Civita declarations and `Existence.lean`). #6875's `unique` hit was prose, and all thirteen open heads re-simulated clean.
* r875: no change 6 minutes after r874. #6947 and #6950 were still on their first builds, #6945 was not yet due for a drive (22:47Z), and there were no merges.
* r876: #6947 went green (22:20:35Z) and was marked ready (22:27:09Z; drive not before 23:27Z). #6950 was still building, #6945 was not yet due for a drive, and there were no merges.
* r877: #6950 went green (22:32:19Z) and was marked ready (22:37:55Z; drive not before 23:38Z). Main moved to `72f21ba26` (#6850, #6846, additive), and all thirteen open heads re-simulated clean. #6945 was not yet due for a drive (22:47Z).
* r878: #6945's review, driven after its hour (22:47:13Z), approved 10/10 ($0.84), and the local worker approved #6947 10/10 (22:56:19Z); both queued (75, 76). Two slots freed, and with kind 1 still dry, kind 2 opened as draft **#6952**, a style pass on `Winding/Number/Segment/Formula.lean` (gpt-6-astra: no risk; gate 12/0/0). Main moved to `e0103897b` (#6845, #6841, additive), and all fourteen heads re-simulated clean. One slot is still free, and the next opening is kind 3.
* r879: kind 3 opened as draft **#6953**, dropping the unused `h2` and `h3` in the Weierstrass equation differential (gate 12/0/0; `deadhave` flagged `h3`, and `h2` is dead the same way). No merges since #6845 and #6841, main still `e0103897b`, and #6950 was not yet due for a drive (23:38Z).
* r880: **#6952's first build failed** on the `simpa only [mul_one]` golf (instance paths). The job log gave the exact mismatch, `f2f4f9666` restores the explicit `have`/`simp only`/`exact`, and the body was corrected. #6953 was still building, #6950 still had no board, and there were no merges.
* r881 (2026-09-22, after a six-day gap): every queued PR had merged — thirteen of mine plus #5950. The two survivors, #6952 and #6953, were drafts the bot had parked `on-hold`; both were rebased onto `c6b94ee7a`, re-gated 12/0/0, pushed and marked ready. The kind-1 re-run at pin `dc4b8d60d5` was dry (the `wordProd` collision is a false positive), so kind 2 opened as draft **#8101**, a style pass on `Cesaro/Convergence.lean` (gpt-6-astra: no risk; gate 12/0/0).
* r882 (2026-09-23): no cron had been set, so a 10-minute job (`4b5d0e55`) now drives rounds. #6952 and #6953 had merged. #8101 was still a draft, parked `on-hold` again; with the pin unchanged, it was marked ready, approved within 8 minutes and merged at 09:19:24Z. Kind 3 opened as draft **#8224** (`norm_resolvent_integrand_le` to `0 ≤ t`; ready 09:18:43Z), kind 2 in kind 1's slot as draft **#8233** (`Residue/Basic.lean` style pass), and kind 3 as draft **#8235** (`ConvexSubgroup.lean` uses Mathlib's `mabs_mem_iff`). All three gated 12/0/0.
* r883: #8233 went green (09:24:57Z) and was marked ready (09:26:40Z) with the pin unchanged. #8235 was still on its first build; the cap is full.
* r884: #8235 went green (09:35:30Z) and was marked ready (09:36:14Z); all three PRs are now `awaiting-review`.
* r885: no change; drive clocks open at 10:18Z (#8224), 10:26Z (#8233) and 10:36Z (#8235).
* r886: board unchanged. Kind 2 is staged locally as `improve/condindep-conditional-style` @ `dddfd9f96` (`Independence/Conditional.lean`: 82 `↦`, 12 chains split; gate 12/0/0), with astra running.
* r887: board unchanged; the `gammaPDFReal_of_pos` candidate is gone from main (dropped).
* r888: no change; #8224's drive clock opens at 10:18Z.
* r889: drove #8224 (10:24:54Z; 66 min without a board). **Every rubric errored**: codex is out of quota until 2026-09-27T15:04Z, and astra is too. The drive left an error board (5793153420). Step 4 is hard-stopped until the reset.
* r890: no change; #8233 is past its hour, but step 4 is hard-stopped. Review boards come from contributors' own runs (distributed), and #8232 (another lane on this account) also got an error board.
* r891: no change. The kind-3 queue is refilled: the `RelNorm.lean` dead `hJ'` and the `GlobalTurning.lean` `i < j` → `i ≤ j` weakening, both free.
* r892–r894: no change. At r894 external reviewers were active (21 boards in 45 min).
* r895: no change; main moved to `7d24ccc8a` (pin unchanged), and all three heads plus the staged branch merge-tree clean.
* r896: reviewers are **passing over** #8233 and #8235 (they boarded #8230–#8252, all numbered above them); other contributors do review CBirkbeck PRs, and the cause is not visible locally. Reported to the user.
* r897–r901: no change (main `90ff820df` at r901; every branch merge-tree clean).
* r902: **#8233 approved 10/10** (`Robertboy18`) and MERGING. In the freed slot, kind 2 opened as draft **#8273** (the staged `Conditional.lean` pass, rebased to `0f704c040`, gate 12/0/0).
* r903: **#8233 merged**. **#8224 approved 10/10** by `sqrt-of-2`, despite my error board, and is MERGING. Kind 3 opened as draft **#8275** (`RelNorm.lean` dead `hJ'`; gate 12/0/0).
* r904: no new change; #8273 marked ready (12:50:19Z, via the r903 waiter), and #8275 is still building.
* r905: **#8224 merged** (12:55:04Z). #8235, #8273 and #8275 are all `awaiting-review`; the cap is full.
* r906: no change. With astra out, the next slot goes to kind 3; the `GlobalTurning.lean` `i ≤ j` weakening is staged locally (`26b23a436`, gate 12/0/0).
* r907: #8235 is `review-in-progress` (an external reviewer, 228 min after ready).
* r908: **#8235 approved 10/10** (`sqrt-of-2`) and MERGING. Kind 3 opened as draft **#8286** (the `GlobalTurning.lean` `i ≤ j` weakening, `d099adbd2`, gate 12/0/0).
* r909: #8273 is `review-in-progress`; #8286 is building.
* r910: **#8235 merged**; **#8273 approved 10/10** (`roed-math`) and MERGING. Kind 3 opened as draft **#8291** (rename `not_mem_maxAvoid` → `notMem_maxAvoid`; gate 12/0/0).
* r911: no board change. The scanner refill found nothing new for kind 3 (the new `deadprivate` hits are worked examples).
* r912: **#8273 merged**, the fifth today. The `nscand` rooting lane is dry (8 WHOLE, all known traps or skips), so the next kind 3 is the `integral_Ioi_eq_Ioc_add_Ioi` weakening.
* r913: **#8275 and #8286 approved 10/10** (`sqrt-of-2`), MERGING. Kind 3 opened as draft **#8295** (two private resolvent lemmas to `0 ≤ h`). The third slot is left empty: every kind is dry or blocked, and `docghost` had no real hit.
* r914: **#8275 and #8286 merged** (the sixth and seventh today); #8295 is building. Trap: `queuepos` shows a just-merged PR as EJECTED, so check `merged` before acting on an ejection.
* r915: no change; #8295 was marked ready (14:40:03Z).
* r916: #8291 and #8295 are both `review-in-progress`.
* r917: **#8291 approved**. **#8295 got one `api-design` finding** (the private Ioi-split helper is general infrastructure). Fixed by deleting it in favour of Mathlib's `intervalIntegral.integral_interval_add_Ioi` (`08d0a50ca`, gate 12/0/0, body v2).
* r918: #8295 is rebuilding on the fix (its board is BEHIND the head, as expected); #8291 is `ready-to-merge`.
* r919: **#8291 merged** (the eighth today). `misplaced.py` ∩ Mathlib names found two private exact duplicates of Mathlib lemmas, opened as drafts **#8304** (`invOf_two_add_invOf_two`) and **#8305** (`norm_sub_le_of_mem_segment`); six more are queued for vetting.
* r920: **#8295 approved on the fix**. The rest of the `misplaced` × Mathlib list was vetted: no more duplicates. The HilbertTheory overlap with Mathlib is a design question, not a catch-up.
* r921: no change; #8304 and #8305 are building.
* r922: **#8295 merged**, the ninth today. #8304 and #8305 were marked ready (15:48Z); #8305 is under review.
* r923: **#8304 approved**. **#8305 got one `placement` finding** (an import left unused by the deletion). Fixed by dropping it (`4f4ff931e`, closure unchanged, gate 12/0/0).
* r924–r925: no change; #8305's fix went green (16:24:15Z) and awaits re-review.
* r926: **#8304 merged**, the tenth today. #8305 is under re-review.
* r927: **#8305 approved on its fix**. Nothing is in progress, and every kind is blocked or dry. The `LevelRaise` `hmod` was declined as a probable `deadhave` false positive (`simp` discharger).
* r928–r929: no change.
* r930: **#8305 merged**, the eleventh today; no `improve/*` PR is open. A scanner re-run on fresh main found no new target.
* r931: **the quota is back** (astra and sol probes ok), so the hard stop is lifted. Kind 2 opened as draft **#8332** (`ProductKernel.lean` style pass; gate 12/0/0; astra pending).
* r932: kind 2 again as draft **#8339** (`ViaKoopman/Decoupling.lean` style pass; gate 12/0/0; astra pending).
* r933: #8332 was marked ready after astra cleared it (it accepted everything). Kind 2 opened as draft **#8344** (`Slice/Density.lean`; gate 12/0/0; astra pending). The cap is full.
* r934: **#8332 got an `attribution` finding** (keep the roadmap credit). Fixed, and the same fix applied to #8339 and #8344. All three are rebuilding.
* r935: the rebuilds are running. Found that r934's proactive push on #8339 superseded a 10/10 approval on its old head, so it now needs a re-review. New trap: read the board before any speculative push.
* r936: #8332's rebuild is done (`awaiting-review`); #8339 and #8344 are still building.
* r937: #8332 round 2 — `documentation` contradicted `attribution` round 1 over the roadmap sentence. Reconciled with provenance wording (`ccc663cf3`), and body v3 links both threads.
* r938: #8344 marked ready (its rebuild went green). #8339 is green and awaiting review; #8332 is rebuilding.
* r939: **#8339 and #8344 got `documentation` (+ `attribution` on #8344) findings: remove the roadmap bullet.** Done on both. This corrects r934: roadmap credit goes only in the PR description.
* r940: **#8332 round 3: `documentation` rejected the provenance wording too.** The roadmap reference is removed (`a32a2f72e`), leaving the credit only in the PR body.
* r941: all three are rebuilding on their fixes.
* r942: **#8339 approved**. Kind 2 opened as draft **#8381** (`OnCurve.lean`: 70 `↦`, 3 chains split, and roadmap framing dropped per the r939 rule; gate 12/0/0).
* r943: no action; #8332 is green and awaiting review, #8344 is under review, and #8381 is building.
* r944: **#8332 and #8344 approved** (with #8339, all three roadmap-rework PRs are `ready-to-merge`). Kind 2 opened as draft **#8388** (`Arrays/JointLaw.lean`; gate 12/0/0).
* r945: CI is congested (32 queued). #8381 was cleared by astra, but its build is still queued. Kind 2 opened as draft **#8389** (`ConditionallyIID/Moments.lean`; gate 12/0/0). The cap is full.
* r946: **#8339 merged**, the twelfth today. The drafts are still waiting on the CI queue.
* r947: #8381 went green after about 44 min queued and was marked ready.
* r948: **#8381 approved**. Kind 2 opened as draft **#8402** (`RowExchangeable.lean`, 83 `↦`; the astra question uses the three-dot diff).
* r949: **#8344 merged**, the thirteenth today. The drafts are still waiting on the CI queue.
* r950: **#8332 merged**, the fourteenth today. #8388 and #8389 were marked ready (they went green at 20:28Z and 20:30Z).
* r951: **#8388 and #8389 approved**; #8402 was cleared by astra. Kind 2 opened as draft **#8413** (`KnotTheory/Grid/Unknot/Basic.lean`, 62 `↦`).
* r952: kind 2 opened as draft **#8426** (`Arrays/ConditionalLaw.lean`, 64 `↦`). The cap is full.
* r953: **#8381 merged**, the fifteenth today.
* r954: CI backlog (114 queued, 4 running). The three drafts' builds have not started. The sweep marks each green draft ready when it lands.
* r955–r959: the backlog is still growing (124 → 141 queued, about 5 running, for about 2 h). Reported to the user as a probable runner-capacity problem. All three drafts are cleared by astra and waiting for builds.
* r960: **#8388 and #8389 merged** (the sixteenth and seventeenth today). The drafts are still waiting for builds.
* r961–r962: CI is recovering (16 running, the queue down to 128); the drafts are still queued.
* r963: #8402 was marked ready (it went green at 22:38Z); #8413 and #8426 are still queued.
* r964: **#8402 approved**. `VanishingMoments.lean` was declined (roadmap text throughout). Kind 2 opened as draft **#8469** (`Arrays/Block.lean`, 61 `↦`).
* r965: #8413 went green and was marked ready; astra cleared #8469.
* r966: **#8402 merged** (23:06:21Z). #8426's build started at 23:13Z; #8469 is still queued. The cap is full.
* r967: **#8413 approved**; #8426 went green and was marked ready. Kind 2 opened as draft **#8473** (`Arrays/RowCoding.lean`, 65 `↦` plus the roadmap sentence), cleared by astra.
* r968: **#8426 approved**. Kind 2 opened as draft **#8476** (`Exchangeability/Contractability.lean`, 63 `↦`, two chains, the "Layer 0 home" clause), cleared by astra.
* r969: **#8413 merged** (23:37:48Z). All three drafts are still queued for CI (103 queued repo-wide). The cap is full.
* r970: **#8426 merged** (23:47:10Z). The three drafts are still queued for CI.
* r971: #8469's build started at 00:02Z (waiter armed); #8473 and #8476 are still queued.
* r973: #8473's build started at 00:23Z (waiter armed); #8476 is still queued; #8469 awaits its board.
* r974: #8473 went green (00:34:19Z) and was marked ready; #8476's build started at 00:31Z, went green at 00:43:16Z, and it was marked ready too.
* r975: all three `awaiting-review`. Declined `Rational.lean`; staged `improve/monodromy-style` (astra ✓, gate 12/0/0).
* r976: all three still `awaiting-review` (no board; #8469 at 39 min). Re-scored kind-2 candidates on `snap-main11`.
* r977: no change (#8469 at 49 min). The staged Monodromy branch still merges cleanly.
* r978: **#8469 approved**. The staged Monodromy branch was rebased onto `53ab872de`, re-gated (12/0/0) and opened as draft **#8487**.
* r979: **#8469 merged** (01:20:26Z). #8487's build started at 01:18Z, went green at 01:27:42Z, and it was marked ready.
* r980: no boards yet; #8473 at 59m45s since ready (not driven; next round it and #8476 pass the hour).
* r981: **#8473 driven** (70 min, no board; quota probe ok). #8476 (60m22s) gets one more round inside the pipeline's 46–64 min window. The drive approved #8473 10/10 ($0.94). Kind 2 opened as draft **#8491** (`Graphon/CutNormLimit.lean`), cleared by astra.
* r982: **#8476 driven** (70 min, no board) and **approved 10/10** ($1.17). #8491 went green and was marked ready. Kind 2 opened as draft **#8492** (`PDE/Spectrum.lean`, 47 `↦`), cleared by astra.
* r983: **#8473 merged** (02:01:52Z). #8492 went green at 02:12:47Z and was marked ready.
* r984: **#8476 merged** (02:11:49Z). Staged `improve/condexp-contractable-style` (astra ✓, gate 12/0/0).
* r985: no change; #8487 at 57 min (drive next round if still boardless).
* r986: **#8487 driven** (67 min) → **approved 10/10** ($1.15) → **merged 03:05:55Z**. CondExp opened as draft **#8497**. **#8491 driven** (65 min).
* r987: queued prompt right after r986; #8491 shows `review-in-progress` (the drive); nothing else changed.
* r988: **#8491 approved 10/10** by the drive. Kind 2 opened as draft **#8499** (`Sobolev/W1p/DifferenceQuotient.lean`), cleared by astra.
* r989: queued prompt; #8492 at 63 min (drive next round). #8497 went green at 03:16:23Z and was marked ready; #8499 went green at 03:24:11Z and was marked ready. **#8492 driven** at 71 min.
* r990: **#8491 merged** (03:24:45Z). #8492's drive **approved it 10/10** ($1.02). Kind 2 opened as draft **#8503** (`Wishart/Basic.lean`, 45 `↦`), cleared by astra.
* r991: #8492 `ready-to-merge`; #8503 went green at 03:42:10Z and was marked ready; #8497/#8499 at 17/10 min.
* r992: **#8492 merged** (03:40:27Z). Staged `improve/hopf-lemma-style` (astra ✓, gate 12/0/0).
* r993: no change (#8497/#8499/#8503 at 37/30/12 min).
* r994: no change (47/40/22 min); main still `5832ba2dd`, so the staged HopfLemma branch is current.
* r995: no change (57/50/32 min). Main `a34466e9c`; HopfLemma still merges cleanly.
* r996: **#8497 driven** (67 min, no board; quota probe ok). #8499 (60 min) held one round. The drive **approved #8497 10/10** ($0.78); HopfLemma rebased onto `a0749c0b4`, re-gated, opened as draft **#8508**.
* r997: #8497 `ready-to-merge`. **#8499 driven** (70 min) → **approved 10/10** ($1.07). #8508 went green and was marked ready. Kind 2 opened as draft **#8510** (`DriftMaximumPrinciple.lean`), cleared by astra.
* r998: **#8497 merged** (04:40:40Z). #8510 went green (04:53:58Z) and was marked ready. **#8503 driven** at 71 min.
* r999: **#8499 merged** (04:50:46Z). The drive **approved #8503 10/10** ($0.90). Kind 2 opened as draft **#8513** (`AlmostSplit/Basic.lean`), cleared by astra.
* r1000: #8503 `ready-to-merge`; #8513 went green (05:12:39Z) and was marked ready. Staged `improve/arrays-basic-style` (astra ✓, gate 12/0/0).
* r1001: **#8503 merged** (05:10:13Z). #8508/#8510/#8513 at 32/20/2 min.
* r1002: no change (42/30/12 min); the staged Arrays/Basic branch still merges cleanly.
* r1003: no change (52/40/22 min).
* r1004: no change (62/50/32 min); #8508 held one round (drive next round if still boardless).
* r1005: **#8508 driven** (72 min; quota probe ok) → **approved 10/10** ($0.84). #8510 (60 min) held one round. Arrays/Basic rebased onto `a3fbe61a2`, re-gated, opened as draft **#8521**.
* r1006: #8508 `ready-to-merge`. **#8510 driven** (70 min) → **approved 10/10** ($0.96). Kind 2 opened as draft **#8525** (`Grid/Grading/Parity.lean`), cleared by astra. #8521 went green and was marked ready. #8513 at 62 min (held).
* r1007: **#8508 merged** (06:11:47Z). #8525 building. #8513 at 63 min (drive next round).
* r1008: **#8510 merged** (06:23:34Z). #8525 went green (06:24:34Z) and was marked ready. **#8513 driven** (72 min) → **approved 10/10** ($0.88). Kind 2 opened as draft **#8526** (`JHolomorphic/Prod/Basic.lean`), cleared by astra.
* r1009: #8513 `ready-to-merge`; #8526 building. Staged `improve/energyform-variablelp-style` (astra ✓, gate 12/0/0).
* r1010: **#8513 merged** (06:38:11Z). #8526 went green (06:44:12Z) and was marked ready.
* r1011: no change (39/30/10 min); VariableLp still merges cleanly.
* r1012: no change (49/40/20 min). Staged a second branch, `improve/energyform-integrated-style` (astra ✓, gate 12/0/0).
* r1013: #8525 `review-in-progress` (the pipeline picked it up); #8521 at 59 min; #8526 at 30 min.
* r1014: **#8525 `awaiting-author`**: `documentation` asked to move the split-branch provenance sentence to the PR description; done at `e5b5676d1`. **#8521 driven** (73 min) → **approved 10/10** ($1.06). VariableLp rebased onto `b8003b8c2`, re-gated, opened as draft **#8530**.
* r1015: queued prompt; #8521 `ready-to-merge`; #8525 `awaiting-CI` on the fix (board behind the head, as expected); #8530 queued.
* r1016: #8525 fix green, awaiting re-review; #8526 at 60 min (drive next round if boardless); #8530 building.
  Later: #8530 went green (07:51:21Z) and was marked ready; **#8526 driven** at 67 min.
* r1017: **#8521 merged** (07:50:55Z). #8525's re-review and #8526's drive are both `review-in-progress`.
  Later: the drive **approved #8526 10/10** ($0.92); Integrated/Basic rebased onto `9979a4b21`, re-gated, opened as draft **#8531**.
* r1018: **#8525 round 2**: documentation ✅, `attribution` asked to keep the proof credit in the docstring (the #8332 conflict again). Fix 2 `8ae84de0c`: credit as a plain source citation, no dated wording. #8526 `ready-to-merge`.
* r1019: **#8526 merged** (08:06:09Z). #8525 fix 2 building. Staged `improve/hyperbolic-length-style` (astra ✓, gate 12/0/0); declined four roadmap-sourced files.
* r1020: no change (#8525 awaiting re-review of fix 2; #8530/#8531 at 33/15 min).
* r1021: **#8525 approved 10/10** on fix 2 (the source-citation wording satisfied both `documentation` and `attribution`). Hyperbolic/Length rebased onto `2d6f52f7d`, re-gated, opened as draft **#8534**.
* r1022: **#8525 merged** (08:43:36Z). #8534 went green and was marked ready. Re-scored main (`snap-main12`) and staged `improve/specht-standardbasis-style` (astra ✓, gate 12/0/0).
* r1023: no change; #8530 at 63 min (held one round; drive next round if boardless).
* r1024: **#8530 driven** (73 min; quota probe ok) → **approved 10/10** ($0.88). Specht rebased onto `bed3bd6bb`, re-gated, opened as draft **#8538**.
* r1025: #8530 `ready-to-merge`. **#8531 driven** (65 min) → **approved 10/10** ($1.31). Kind 2 opened as draft **#8541** (`DenseGraphLimits/Applications.lean`), cleared by astra. #8538 went green and was marked ready.
* r1026: **#8530 merged** (09:18:13Z). #8541 went green (09:31:28Z) and was marked ready.
* r1027: **#8531 merged** (09:31:17Z). Staged `improve/pdcode-kauffman-style` (astra ✓, gate 12/0/0).
* r1028: no change (#8534/#8538/#8541 at 56/22/12 min).
* r1029: **#8541 approved** by the pipeline (22 min). **#8534 driven** (66 min) → **approved 10/10** ($1.17). Two slots opened: Kauffman rebased onto `0c20df3de` and opened as draft **#8548**; Complexification staged, cleared by astra and opened as draft **#8549**.
* r1030: #8534 and #8541 `ready-to-merge`. #8548 (10:08:16Z) and #8549 (10:13:06Z) went green and were marked ready; #8538 at 42 min.
* r1031: no change (#8538 at 52 min). Staged `improve/wirtinger-w1p-style` (astra ✓, gate 12/0/0).
* r1032: #8538 at 62 min (held one round; drive next round if boardless). #8534/#8541 still queued.
* r1033: the pipeline **approved #8538, #8548 and #8549** (10:28–10:29Z); **#8541 merged**. All three slots opened: Wirtinger rebased and opened as draft **#8563**; `Wishart/Inverse/Moments.lean` (**#8565**) and `Contour/Crossing/PVAggregation.lean` (**#8566**) prepared, gated, cleared by astra and opened as drafts.
* r1034: **#8534 merged** (10:38:16Z). The three drafts are building.
* r1035: #8563 (10:48:13Z) and #8565 (10:54:41Z) went green and were marked ready; #8566 (10:56:17Z) too. No drafts.
* r1036: **#8538 and #8549 merged**. #8563/#8565/#8566 `review-in-progress`. Staged `improve/dgl-moebius-style` (astra ✓, gate 12/0/0).
* r1037: the pipeline **approved #8563, #8565 and #8566** (11:06–11:07Z); **#8548 merged**. All three slots opened: Moebius rebased and opened as **#8570**; `Wishart/Transforms.lean` (**#8577**) and `Induction/Mackey/Decomposition.lean` (**#8578**) prepared, gated, cleared by astra and opened.
* r1038: queued prompt right behind r1037; no change (#8570 building, #8577/#8578 queued).
* r1039: **#8566 and #8565 merged**. #8570, #8577 and #8578 went green and were marked ready. Staged `improve/quotient-asymptotics-style` (astra ✓, gate 12/0/0).
* r1040: **#8563 merged**; the pipeline **approved #8570** (8 min). QuotientAsymptotics rebased onto `9889e2022` and opened as draft **#8586**.
* r972: #8469 went green (00:14:42Z) and was marked ready; #8473 and #8476 are still queued.

## Candidates for a later step 5

**Kind 3, OPENED as #6933 (r861):** `improve/subcomodule-comap-dedup` @ `311f6a427` (rebased onto `2e0c1a0b2`; gate 12/0/0). It deletes
`TauCeti.Subcomodule.comap_coact_mem`, a private restatement of `coact_mem_range_comap_toLinearMap` proved by it, so `comap` calls
the lemma directly. It also turns the module docstring's roadmap sentence into the motivation it carried: +4/−13,
`Roadmap: ReductiveGroups`.

**Later kind-3 candidates (r858 scans):**

* `ExchangeableAt.of_lt`: taken by #6945 (r869).
* Two unused private `rfl` lemmas in `RingTheory/Polynomial/SymmetricPower.lean`: `coe_degreeLTEquiv_toEquiv_symm_apply` and
  `coe_monicEquivDegreeLT_symm_apply`. Risky (r869): they are component lemmas for Mathlib's `degreeLTEquiv` and
  `monicEquivDegreeLT`, and `api-design` asked #6915 to export such general lemmas rather than hide them, so deleting them may
  draw the same request.
* Private `jetField_add_ae` in `PDE/EnergyForm/Sobolev.lean`. It is unused, but its `jetField_zero_ae` and `jetField_smul_ae`
  siblings are used, so deleting only it may draw an API-completeness comment.
* `deadhave`: `Recut/Pairing.lean`'s two went as #6950 (r874), and `Derivation.lean`'s `h2`/`h3` as #6953 (r879). What is left is
  `LevelRaise/Commute.lean:269`'s `have hmod`, which strands `w`, so deleting it needs a replacement binder.

**Not candidates:**

* `deadprivate`'s regressions, counterexamples and worked examples in `UnitIntervalMap.lean`, `Disintegration/Countable.lean`,
  `MapRestrictDensity.lean` and `SquareClass/Rational.lean`. They exist to be elaborated.
* `dupsig`'s 53 `private …_aux` + public pairs, the module-system `rfl` idiom.

**Kind 3, TAKEN by #8224 (r882); was ready (r848):** `StronglyContinuousSemigroup.norm_resolvent_integrand_le` (`Analysis/Semigroups/Resolvent/Basic.lean`)
takes `ht : 0 < t` but passes only `ht.le` on. Weaken it to `0 ≤ t`: no rename is needed, and its one caller, in the same
file, gains `.le`. Wait for #6911 (same file) to merge first. Also blocked (r853): `gammaPDFReal_of_pos` in `Distributions/Gamma/Basic.lean`,
because open PR #6580 touches that file, and the weakening would need an `_of_nonneg` rename.

**Kind 3 (r845), taken by #6910 (r847):** `LinearAlgebra/Vandermonde.lean` kept private `monic_descPochhammer'` and
`descPochhammer_natDegree'` (over a `CommRing`). They duplicate the public, more general `TauCeti.monic_descPochhammer`
and `TauCeti.descPochhammer_natDegree` in `RingTheory/Polynomial/Pochhammer.lean`, which `Vandermonde.lean` does not
import yet. **Kind 1 is dry at pin `30a58f795a`** (r845): re-run `mlcatchup.py` (session scratchpad) after the next
Mathlib bump.

**r843 leftovers from the `ConvexSubgroup.lean` pass** (not bundled into #6896, one topic per PR; wait for #6896 to
merge before touching the file again): `mem_of_mabs_le_mabs` and `mem_closure_singleton` rebuild `|h|ₘ ∈ H` by cases
where Mathlib's `mabs_mem_iff` gives it; the private declarations carry docstrings; `not_mem_maxAvoid` keeps the old
spelling. **Scanner hits on `f29016218` outside open PRs:** `strictscan` PUBLIC `one_sub_conj_mul_ne_zero_of_norm_lt_one`
(PseudoHyperbolic, 16 sites in 7 files), `StronglyContinuousSemigroup.norm_resolvent_integrand_le` (1 caller, same file);
`chafaiRescaling_coe_of_pos` is taken by #6899. `unusedscan`'s `descendIndexGL_smul_infty_of_eq_zero` hit was a false
positive: `split_ifs` uses `hc`, and the tool learned that at r844.

**r706:** every WHOLE `nscand` target is taken or a trap, and `ClassGroup` is partial (ledger r706). `dupsig` has no public duplicate left once kind 3 lands.

Re-run `nscand.py` first. Skip `TauCeti.LinearEquiv.toLinearEquiv_generalLinearEquiv_symm` and
`TauCeti.FDRep.intCharacter_def` (both `private`). The r681 trap namespaces still apply
(`Probability.Kernel`, `PDE.Continuous(On)`, `Probability.AEStronglyMeasurable`,
`Probability.MeasurableSet`, `BilinForm.IsAlt` do not exist in Mathlib). The partial namespaces in
`Lattice.lean` (`TauCeti.Submodule.IsLattice` 3/4, `TauCeti.Submodule` 5/20) are not whole — do not cut.

## Settled

* **Merged this watch:** #6406, #6426, #6412, #6418, #6432, #6188, #6482, **#6093** (2026-09-14T21:09:02Z), **#6796**
  (21:29:41Z), **#6800** (21:31:53Z), **#6855** (2026-09-15T05:43:53Z), **#6854** (2026-09-15T21:52:04Z), **#6851** (2026-09-15T22:11:28Z),
  and then the whole queue on **2026-09-16**: **#6950** (06:59:48Z), **#6947** (07:15:38Z), **#6945** (07:48:23Z), **#6941**
  (08:20:45Z), **#6933** (08:41:30Z), **#6923** (09:14:10Z), **#6915** (09:39:29Z), **#6911** (09:45:57Z), **#6910** (09:54:31Z),
  **#6902** (10:04:56Z), **#6899** (10:10:06Z), **#6896** (10:18:58Z); **#5950** (2026-09-17T15:57:25Z) and **#6875**
  (2026-09-21T05:44:38Z).
* **#6093** — `scope`, `naming`, `documentation` green; `api-design` answered. Deferred laws on
  `handover/fiber-compfiberequiv-laws-deferred`.

## Standing traps

* **Build astra questions from `git diff origin/main...HEAD` (three dots), never `..` (r947).** A two-dot diff is HEAD against the *current*
  tip of `origin/main`. Once main moves past the branch base, every file main added shows up as "deleted", and astra rejected #8388 for
  deleting `Fuchsian/Elliptic.lean`, a file the PR never touched (GitHub's PR diff, from the merge base, was clean).

* **Roadmap credit belongs ONLY in the PR description (r939, replacing the r934/r937 note).** Three rubric runs (#8339 and #8344
  `documentation`, #8344 `attribution`) require removing every roadmap mention from docstrings — stage wording *and* plain credit — and
  keeping only the PR body's `Roadmap:` line. #8332's round-1 `attribution` ask was the outlier. Style passes: delete roadmap
  sentences and bullets outright (the #8101 approach, which merged). Never re-add a credit speculatively; the r934 re-adds cost an
  approval and two review cycles.

* **Read the board before any speculative push (r935).** At r934 a proactive fix went to #8339 minutes after it had been approved 10/10 on
  its old head, and the push threw that approval away for a change no reviewer asked for. Push only to answer a finding on *that* PR, or
  when its current board is not approved. Otherwise apply the lesson to the next PR.

* **A roadmap-stage docstring line is also the file's roadmap credit (r934).** `attribution` asked #8332 to keep "a module-level credit to
  the Exchangeability roadmap; the stage-specific wording can be omitted". Drop "Layer n"/"Milestone"/"Part C" but keep a stage-free
  `TauCetiRoadmap/<Area>` mention. #8101 got through without one, but the rubric enforces it stochastically.

* **Judge an astra run by its log, not by the answer file alone (r882).** An existing `-o` file from an earlier pass printed as
  though it answered the new question, and was overwritten 8 seconds later. The fresh file was then moved aside as "stale" and waited
  on for 12 minutes. Before launching, give the `-o` target a unique name (`astra-<topic>-<UTC time>.txt`). A run is finished when
  its log has `tokens used`, and the answer is the log's final text. **Never wait with `pgrep -f <pattern>`**: the waiter's own command
  line matches, so it never exits. **Nor with `kill -0 $!`** (r886): under `setsid nohup … &`, `$!` is `setsid`'s PID, and `setsid`
  forks and exits at once, so the wait ends in seconds while codex runs on. Wait on files instead:
  `until [ -s "$A" ] || grep -q '^tokens used' "$LOG"; do sleep 15; done`.
* **The round that opens a draft must also be the one that marks it ready (r881 → r882).** r881 recorded the on-hold trap and then
  ended with #8101 still a draft. The bot parked it within the hour. When a round ends with a draft building, say so in item 0 of
  "What to expect next" so the next round's first action is to mark it ready.

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
**Do not trust `gh api rate_limit`** (r734: at 19:16Z it said core 4999 left, reset 19:36Z, while every REST read
failed). Read the quota off a real call: `gh api -i <endpoint>` prints `X-RateLimit-Remaining` and `-Reset`. The
headers of `gh api -i rate_limit` are no better (r833: `used 0` there while `pulls/6851` read `used 18`).
**The hourly window rolls over at about :17–:19** (r722, r728, r734 at 19:17:29Z, r740; r777 at 02:19:08Z), and the :16
round keeps hitting it. Read the exact reset from a failing `gh api -i` call (`X-RateLimit-Reset`, free even on the
403), then rerun in a background until-loop (foreground `sleep` is blocked).
**`gh pr list --state merged --limit 200` is ordered by creation, not merge time** (r728): an old PR such as
#6093 can merge without appearing in it. A merge also shows as the PR vanishing from the sweep's open-PR list.
**`awk length` counts BYTES** — `≤`, `σ`, `γ`, `ℝ` are multibyte. Measure line width in codepoints (Python)
before rewrapping anything (r704: 3 of 14 reported overflows were not).
**A PR that deletes a file** is screened since r704 (`deleted:` in the header; `--deleted` for stalequal and
decldiff). **`deadpath` only resolves names inside `_root_.` declarations** — a catch-up PR's Mathlib names
need a read of Mathlib's source, and a `public` check: a non-`public` declaration in a `module` file is
invisible to Tau Ceti.
**The merge sweep fails closed on any unreadable queue entry** (r823). `queue_entries()` reads every entry's changed
paths, and one failed call (`unexpected end of JSON input` on #6751) aborted the whole run before it evaluated any PR.
Read a failed run's log by job id (`actions/jobs/<id>/logs`), since `gh run view --log-failed` came back empty for this
reusable-workflow job, and re-run the failing call to tell a transient error from a persistent one.
**REST can come back before `X-RateLimit-Reset`** (r823): at 10:36Z, `X-RateLimit-Remaining` read 4180 while the reset
header still said 11:27:41Z. Probe `X-RateLimit-Remaining` before skipping a REST sweep, not the reset time.
**The low-memory watchdog kills even a trivial background task** (r816). A background loop that only probed `gh api`
every 20 seconds, waiting for the REST reset, died seconds after it started, with 10 GiB free and 62 GiB available
(tmpfs and page cache hold the rest). Once `X-RateLimit-Reset` has passed, rerun the sweep in the foreground; a
background wait is not a reliable way to get the post-reset board.
**The naming rubric puts a declaration whose first explicit argument has a Mathlib type in that type's namespace**,
section variables included (r803). Declare it in place as `_root_.<ns>.<name>`: the enclosing namespace still resolves
short names in the body, as `_root_.IsCoveringMap.isRegular_iff_normal_range` shows. `prepush.sh`'s `decldiff` and
`rootsurplus` model a rooting as dropping `TauCeti.`, so a move into a differently cased Mathlib namespace reads as
VANISHED/APPEARED/SURPLUS: pair the rows, and answer `rootsurplus` in the body.
**The documentation rubric (`afb424e`) flags roadmap stages, item numbers and status narrative** in the module
docstring of any file a PR touches, so a wide rename inherits that cleanup (r803).
**Auto-merge needs every changed path under `TauCeti/`** (`auto-merge.yml`). A rename that must also update
`web/examples/Examples.lean`, a separate Lake project that `pages.yml` builds from main, routes the PR to a human
(#5950, #6875). Keep the `web/` edit, because leaving it out breaks the site, and say so in the body (r798).
**A Mathlib bump flushes the merge queue** (r798): `tauceti-review-bot` removes every entry with reason `manual` and
enqueues the bump alone, so `queuepos.py` says `EJECTED` for PRs whose boards are fine. Read the reason first.
Such removals are reservation cleanup, and TauCetiReview's `runner/sweep.py` (`merge-sweep.yml`) re-enqueues green
TauCeti/-only PRs after the bump, with no push and no re-review (r799).
**Bors-merged Mathlib PRs are CLOSED with `mergedAt: null`**: date them by `closedAt` (r798).
**A module rename on main is invisible to `ghostref` and `stalequal`** — they chase declaration names, not import
paths. When main renames or deletes a module, grep each branch's ADDED lines for the old path (r735: #6514's
`GeckLattice/Weyl.lean` → `Weyl/Basic.lean`, no hits).
**A `queued` check with no runner is a capacity stall, not a failure** (r742). Read `actions/runs/<id>/jobs` for
`labels` and `runner_name`, and `actions/runs?status=queued` for the backlog. It is human-owned: report it, never
cancel runs.
**Give check-runs the full head SHA from the sweep** (r747): a mistyped abbreviation returns `422 No commit found`,
which is not a CI state.
**In a `module` file, never golf `by rfl` → `rfl` on a public lemma** (r847, #6902). A bare term `rfl` is exported as a
definitional equality and may unfold only `@[expose]`d definitions (CI: "Not a definitional equality … must be exposed").
gpt-6-astra reviewed that golf as safe; CI was the only thing that caught it.
**The `Review` workflow is `disabled_manually`** (seen r847). Boards come from external review workers (eohjelle posted
#6899's at 16:40:36Z), so Actions shows no review runs. Step 4's hour still applies.
**Someone else pushes fixes to these branches** (r847: Chris's `CDBirbeck` account fixed #6902 at 15:50:06Z). Always push
with a lease on the observed head. If the lease is rejected, compare trees before re-pushing, and drop a duplicate fix.
**A driven review ends in a `TauCetiData` 403 after posting** (r848, #6896). `post.py` posts the scoreboard and threads, and
then its ledger sync to `TauCetiProject/TauCetiData` is denied to CBirkbeck and raises. The board is already live: read the
log's `ROUND … approved` line and the PR comment, not the exit code.
**Keep credit when trimming module docstrings** (r853, #6902). Removing status narrative is right for `documentation`, but
if that narrative carried the file's only credit to upstream work, `attribution` requests changes. Turn the credit into a
`## References` entry instead of deleting it.
**A kind-2 file pass must not bundle an unrelated golf** (r759): #6854 drew ⛔ `scope` for the
`discrim_eq_sq_of_two_eq_zero` golf riding along with the separability lemma. Ship such a golf as its own PR.
**During a REST outage, read a board's `head_sha` from GraphQL** (`pullRequest.comments { updatedAt body }`). A
comment count alone cannot tell a re-review from the old board, because an edited board keeps its id (r765).
`sweep-gql.py [PR ...]`, next to `sweep.py` in the session scratchpad, reads the whole board that way (r833): drafts,
labels, the latest check run per name, boards by `updatedAt`, and merge-queue membership.
**A merged-list entry is not a main merge** (r768: #6757 and #6831 were stacked PRs into CFSG feature branches).
Filter `gh pr list --state merged` by `baseRefName`, or confirm against `git log origin/main`.
**A pushed fix did not re-review itself within the hour** (r768: #6854's two boards were both drives). Keep the
step-4 clock running after a fix.
**A full `/tmp` stops every tool call** (r771–r772: ENOSPC even for `df`, since the harness writes command output
there). Diagnose with `du -sh /tmp/claude-1001/*/*`; at r773 one other session held 24G of the 25G, 27G at r775, 32G at r783 and 35G at r789 (a new Lean worktree every hour
or so), still growing. Never delete
another session's files; tell Chris.
**A generalization can change a signature without touching its header line** (r780: #6735's firing control read 0
removed or added headers). When main generalizes, list the declarations in the changed files and grep the branches'
added lines for them. Short names such as `ext` and `map` false-match, so read any hit before trusting it (r785).
**Approvals now carry across an unchanged patch** (r787: #6868 pins TauCetiReview at `603b28011`). A rubric's approval
moves to a new head when the PR's own change and the rubric text are unchanged, so a `main`-merge refresh of an ejected
PR should keep its 10/10 instead of restarting review. Check the first board after such a push before relying on it.
**HANDOVER.md §11–13 carry this watch's rules** — read them before re-deriving one.
**`codex exec` outside a git repository needs `--skip-git-repo-check`** (r857). Without it, a launch from the scratchpad prints
`Not inside a trusted directory` and exits at once with no answer file. `pgrep -f 'codex exec'` still matches the shell that
launched it, so check for the answer file and read the log instead of trusting a process count.
**The merge sweep's hourly cron fires every 4–6 hours in practice** (r858). `merge-sweep.yml` is scheduled `40 * * * *`, but on
2026-09-15 its runs were created at 05:18:46Z, 10:24:54Z, 15:15:27Z and 19:11:04Z; GitHub drops scheduled runs under load. A green,
10/10, TauCeti/-only PR can sit NEVER-QUEUED for hours. That is not a fault to fix, and the workflow is human-owned.
**`api-design` judges a touched private lemma as hidden infrastructure** (r861, #6915). Weakening `one_add_sq_div_eq`'s hypothesis
made the rubric read the whole lemma, and it asked for a public lemma in a general module. Implementing that meant a new file,
`TauCeti/Analysis/Real/Sqrt.lean`, whose path mirrors Mathlib's; the root `TauCeti.lean` is intentionally empty, so nothing registers
it. `prepush.sh` then reports `movedopens` UNRUN for the new file. Run it by hand on the source file as it was before the move
(`git show <old-head>:<path>` into the scratchpad) with the moved line range.
**Main moves every few minutes while a staged branch is gated** (r861). A strict "main unchanged since the gate" guard refused #6933
once. Gate against freshly fetched main, and if main moves during the gate, open when merge-tree is clean and main did not touch
the branch's files.
**A newly public lemma draws an `@[simp]` review** (r869, #6915). After `api-design` had `one_add_sq_div_eq` exported as
`Real.inv_sqrt_mul_sq`, its next round asked for `@[simp]`, because the lemma is a normal-form rewrite. When exporting a lemma at a
reviewer's request, decide its simp attribute in the same push.
**A merge-group ref can outlive its group** (r871). After the 06:12Z flush, `pr-6854-1d6c77a5…` still existed with 06:14Z
check-runs, beside the live `pr-6854-b40126a7…`. `git ls-remote … | head -1` picked the stale one. List every
`gh-readonly-queue/main/pr-<n>-*` ref, and judge the group by the ref whose check-runs started after the latest enqueue (or by the
`mergeQueue.entries` `headCommit`).
**A draft left unmarked is parked, not reviewed** (r881). `tauceti-review-bot` relabels a draft `on-hold` ("Draft PR or
explicitly held by a keep/hold/wip/human/do-not-close label") once its `awaiting-review` pass finds it still in draft, and then
ignores it. #6952 and #6953 sat that way for six days. Mark a draft ready the same round its build goes green; if a round ends
with a draft still building, the next round's first job is to mark it.

**A green build ages out when the Mathlib pin moves** (r881). CI-green on a head is evidence only against the pin that built it.
After a bump — three landed here in six days — rebase onto fresh main, re-gate, and let CI re-run before marking ready or driving
a review.
**A golf gpt-6-astra approves can still fail CI on instance paths** (r880, #6952). `simpa only [mul_one] using h2.comp t h1`
was rejected with "Type mismatch: After simplification": the composed term carries `(NormedAlgebra.toNormedSpace ℝ).toModule`
where the goal has `Semiring.toModule`, and only the original `exact` bridges that. `simp only … at h` then `exact h` is not
interchangeable with `simpa … using h` when the two sides differ by instance paths. astra reviews source, never a build: it also
passed the term `rfl` that broke #6902 (r847). Read the failing job's log by check-run id
(`gh api repos/<repo>/actions/jobs/<id>/logs`): the summary and text fields of the check run are empty for this workflow.
