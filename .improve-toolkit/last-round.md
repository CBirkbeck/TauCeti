# Last round — r866 (2026-09-15T20:40Z)

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
(r865, `Residue/Theorem.lean` style pass; the pin is still `30a58f795a`). **The next opening is kind 3**, then kind 1 if a Mathlib bump has
opened a catch-up window, otherwise kind 2. Record each PR's kind in the ledger. **Step 5's cap counts only PRs still in progress** (user directive, 2026-09-15 ~15:00Z): drafts and
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
| **#6851** | `fdeaff5cb7` | green | kind 1; **10/10 first board** (22:35:00Z), `ready-to-merge`; re-queued by the 15:15:27Z merge sweep: **QUEUED 12/70** (20:16Z, r864) | nobody — the queue builds its group; on an eject, read the removal reason first |
| **#6854** | `217fecb812` | green | kind 2; **10/10** (r768 driven board, 00:49:59Z), `ready-to-merge`; re-queued by the 15:15:27Z merge sweep: **QUEUED 10/70** (20:16Z, r864) | nobody — the queue builds its group; on an eject, read the removal reason first |
| **#6875** | `462ed9705b` | green (07:49:13Z) | kind 1 (Mathlib's deck group); **10/10 on the re-review** (08:54:23Z, head `462ed97`), `ready-to-merge` since ~09:28Z and NEVER-QUEUED after r803 fixed the first board's naming, placement and documentation findings; cannot auto-merge (`web/examples`) | **Chris** — merge it; until then it holds one of the three step-5 slots |
| **#6896** | `8a6278e95` | green (15:34:55Z) | kind 2 (convex-subgroup exclusion lemmas take `≤`, renamed to `notMem`); **10/10 on the driven board** (codex, posted 17:14:21Z, r847–r848), `ready-to-merge`; **QUEUED 52/70** (enqueued 19:12:32Z by the 19:11:04Z merge sweep; 20:16Z, r864) | nobody — the queue builds its group; on an eject, read the removal reason first |
| **#6899** | `f450e0dcc` | green (15:42:54Z) | kind 3 (`chafaiRescaling_coe_of_nonneg`); ready 15:47:13Z; **board on head at 16:40:36Z (eohjelle), `ready-to-merge`**; **QUEUED 51/70** (enqueued 19:12:24Z by the merge sweep; 20:16Z, r864) | nobody — the queue builds its group; on an eject, read the removal reason first |
| **#6902** | `3282c9611` | green (18:32:05Z) | kind 2 (PseudoHyperbolic cleanup). The first driven review (on `f8294ed14`) went 9/10 on `attribution`, and `3282c9611` answered it with a `## References` entry. **The re-review driven at r861 approved 10/10** (codex, posted 19:41:02Z, $0.91), so it is `ready-to-merge`, **QUEUED 67/70** (20:16Z) | nobody — the queue builds its group; on an eject, read the removal reason first |
| **#6910** | `3548cebb7` | green (17:32:21Z) | kind 3 (`Vandermonde.lean` uses `TauCeti.monic_descPochhammer` and `TauCeti.descPochhammer_natDegree`; private copies deleted); **10/10 on the driven board** (codex, posted 18:41:05Z, $0.87, r856–r857), `ready-to-merge`, **QUEUED 47/70** (20:16Z) | nobody — the queue builds its group; on an eject, read the removal reason first |
| **#6911** | `4a8439956` | green (17:43:41Z) | kind 2 (Resolvent/Basic.lean style pass); **board on head at 18:03:15Z, `ready-to-merge`**; **QUEUED 50/70** (enqueued 19:12:01Z by the merge sweep; 20:16Z, r864) | nobody — the queue builds its group; on an eject, read the removal reason first |
| **#6915** | `08b8138bc` | green (20:13:06Z) | kind 3 (three strict hypotheses weakened). **The review driven at r861 went 9/10** (board 19:41:46Z, on `efbb6423d`, $0.95). Its one blocker, `api-design`, asked for `one_add_sq_div_eq` to become a public lemma in a general module. `08b8138bc` (pushed 19:56:20Z) does that as `Real.inv_sqrt_mul_sq` in the new `TauCeti/Analysis/Real/Sqrt.lean` (gate 12/0/1; the UNRUN `movedopens`, run by hand, is clean). Body v2 and title patched. `awaiting-review`, board behind | **pipeline** — a board for `08b8138bc` is due; step 4 may drive only after 21:13Z |
| **#6923** | `8f846c57b` | green (19:21:52Z) | kind 2 (`Winding/Number/Segment/Jump.lean` style pass: `;` chains split, 38 `↦`, `Icc_subset_uIcc`/`rwa`/`ne'` golfs; gpt-6-astra reviewed; gate 12/0/0). No board came within its hour, so **a review was driven at r865 (20:28:06Z) and approved 10/10** (codex, posted 20:31:04Z, $1.21); `ready-to-merge`, **QUEUED 69/69** (20:35Z) | nobody — the queue builds its group; on an eject, read the removal reason first |
| **#6933** | `311f6a427` | green (20:05:45Z) | kind 3 (drops the duplicate private `comap_coact_mem` in `Subcomodule/Comap.lean` and rephrases the module docstring's roadmap sentence; gate 12/0/0); opened as a draft 19:48:30Z from `2e0c1a0b2`, **marked ready 20:07:08Z**, `awaiting-review`, no board at 20:35Z | **pipeline** — board due; step 4 may drive only after 21:07Z |
| **#6941** | `8c4c5fa79` | first build | kind 2, in kind 1's slot (`Contour/Residue/Theorem.lean` style pass: 14 `;` chains split, 45 `↦`, `.le`/`.ne`, roadmap narrative out of the module docstring; gpt-6-astra reviewed, no risk; gate 12/0/0); **draft**, opened 20:36:04Z from `9cd85f80e` | **CI** — mark ready when `sandboxed-build` is green |
| **#5950** | `a64ba63667` | green | `ready-to-merge`, **NEVER-QUEUED** | **Chris** — do not refresh |

**In progress: #6915 (fix `08b8138bc` green 20:13:06Z, `awaiting-review`), #6933 (`awaiting-review`, ready 20:07:08Z) and #6941 (draft, first build).** The cap is full, so
step 5 is shut until one of them turns `ready-to-merge`. #6851, #6854, #6875, #6896, #6899, #6902, #6910, #6911 and #6923 are `ready-to-merge` and do not count. #6855 merged at 05:43:53Z. #6851 and #6854 were re-queued by the 15:15:27Z merge sweep (r846), #6910 queued on its 10/10 board (r857), the 19:11:04Z merge sweep queued #6896, #6899 and #6911 (r858), #6902 queued on its 10/10 re-review (r861), #6923 queued on its 10/10 driven board (r865), and #6875 is 10/10 and waits for a human merge (r813). Main is `f7443c964`.

## What to expect next

0. **r843–r865:** the cap rule changed (rotation paragraph above). In progress: #6915 (the `api-design` fix `08b8138bc`, green at
   20:13:06Z; drive not before 21:13Z), #6933 (green 20:05:45Z, ready 20:07:08Z; drive not before 21:07Z) and #6941 (draft; mark it
   ready once its first build is green). Pass #6941, #6933, #6923, #6915, #6911, #6910, #6902, #6899, #6896, #6875, #6854 and #6851
   to `queuepos.py`. When a slot frees: kind 3 (candidates below), then kind 1 if a target exists, otherwise kind 2.
1. **Queue:** `queuepos.py` each round; act only on `EJECTED`, and first read the removal reason (GraphQL
   `RemovedFromMergeQueueEvent.reason`): a bot Mathlib-bump flush reads `manual`, is not a failure, and
   `merge-sweep` re-enqueues a green TauCeti/-only PR afterwards (r798–r799). A `MERGING` PR's group build is the check-runs of
   `git ls-remote origin 'refs/heads/gh-readonly-queue/main/pr-<n>-*'` (r739), the earliest sign of an ejection. If main moves a lot, re-run r702's
   merge-group simulation (cheap, read-only; r865: all twelve (#6851, #6854, #6875, #6896, #6899, #6902, #6910, #6911, #6915 at `08b8138bc`, #6923, #6933 and #6941) clean against `f7443c964`). Staged branches:
   `git merge-tree --write-tree --name-only origin/main <branch>` checks them without a checkout (r750: none
   left; kind 3 opened as #6855). A merge-tree check sees conflicts, not new
   callers: also grep main's new lines for the names each staged branch removes, and when main DELETES declarations,
   grep every branch's added lines for them (r738: #6601 removed `sum_binomial_weight(_mul)`; 0 uses). Print a firing
   control: r738's first try was a crashed `sed` whose empty result read as "none".
2. **#6851 (kind 1, Levi-Civita) is 10/10 on its first board** (22:35:00Z, head `fdeaff5cb7`). It was MERGING at 2 of
   43 when the bot flushed the queue for #6852 (r798). Do not refresh: `merge-sweep` re-enqueues it (green,
   TauCeti/-only) on its next run. #6852 failed its group build and left the queue at 07:57:43Z (r808), so the reservation
   no longer blocks. The first such run, at 10:24:54Z (r822), aborted after 14 s: it could not read queue entry #6751's
   files ("unexpected end of JSON input"), and it fails closed. The same call read cleanly at 10:37:48Z (r823), so the
   failure was transient and the next scheduled sweep should re-enqueue it. If a later run still aborts, tell Chris rather
   than refreshing. Re-simulate its merge group when main moves: it deletes
   24 declarations and `LeviCivita/Existence.lean`, so pass `--deleted` to `stalequal` and the deleted path to `ghostref`.
3. **#6854 (kind 2, quadratic separability) is 10/10** on the r768 driven board (00:49:59Z, head `217fecb812`). It was
   flushed from 14th the same way (r798); handle it like #6851. It removes nothing, so only merge-tree and ghostref's
   firing control matter.
4. **#6875 (kind 1 again, Mathlib's deck group) went 10/10 on its re-review** (r813, 08:54:23Z, head `462ed97`). It now waits for Chris's merge, because `web/examples` keeps it off auto-merge. Its first board went 7/10 at head `e70f761ba`, and commit
   `462ed9705` answers the three findings. Naming: 24 declarations with a deck-transformation first argument became
   `_root_.deck.<name>`. Placement: the `ConstMulAction` import is gone. Documentation: roadmap narrative is out of 33
   module docstrings. Its CI went green at 07:49:13Z (r807), so the dropped import broke nothing;
   the re-review landed at 08:54:23Z, so no drive was needed. `prepush.sh`'s
   `decldiff`/`rootsurplus` FAILs on this move are the rooting-premise mismatch (r803). Expect `prepush.sh`'s `decldiff` FAIL (`VANISHED TauCeti.Deck`), since the deletion is the
   point of the PR. It touches `web/examples/Examples.lean`, so it cannot auto-merge; once it is 10/10, the merge is
   Chris's call, as with #5950.
5. **At the next free slot:** kind 3 (candidates below; the `StronglyContinuousSemigroup.norm_resolvent_integrand_le` weakening still
   waits for #6911 to merge). Kind 2 went as #6941 (r865) in kind 1's slot. No kind-1
   target is left after #6875. #39722 (`Nat.Partition` → `YoungDiagram`, merged 2026-09-14) needs a pin from that date or later,
   and #6852's `8842b50` is from 2026-09-04.

## Kind-1 prospects (r703 first pass, r798 re-run)

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

## What r703–r866 did

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

## Candidates for a later step 5

**Kind 3, OPENED as #6933 (r861):** `improve/subcomodule-comap-dedup` @ `311f6a427` (rebased onto `2e0c1a0b2`; gate 12/0/0). It deletes
`TauCeti.Subcomodule.comap_coact_mem`, a private restatement of `coact_mem_range_comap_toLinearMap` proved by it, so `comap` calls
the lemma directly. It also turns the module docstring's roadmap sentence into the motivation it carried: +4/−13,
`Roadmap: ReductiveGroups`.

**Later kind-3 candidates (r858 scans):**

* `ExchangeableAt.of_lt` (`ExchangeableAtMonotone.lean`): public, no callers, proved as `h.of_le hmn.le hX`.
* Two unused private `rfl` lemmas in `RingTheory/Polynomial/SymmetricPower.lean`: `coe_degreeLTEquiv_toEquiv_symm_apply` and
  `coe_monicEquivDegreeLT_symm_apply`.
* Private `jetField_add_ae` in `PDE/EnergyForm/Sobolev.lean`.

**Not candidates:**

* `deadprivate`'s regressions, counterexamples and worked examples in `UnitIntervalMap.lean`, `Disintegration/Countable.lean`,
  `MapRestrictDensity.lean` and `SquareClass/Rational.lean`. They exist to be elaborated.
* `dupsig`'s 53 `private …_aux` + public pairs, the module-system `rfl` idiom.

**Kind 3, ready (r848):** `StronglyContinuousSemigroup.norm_resolvent_integrand_le` (`Analysis/Semigroups/Resolvent/Basic.lean`)
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
  (21:29:41Z), **#6800** (21:31:53Z).
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
