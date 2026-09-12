# Last round — r653 (2026-09-12 12:45Z) — first round on **AI-DOOM**

## The toolkit arrives broken on a new machine. Run the controls FIRST.

`tools/controls.sh` read **125 passed, 4 failed**, not 129/0. All four in `lintcand`, and the tool
was byte-identical to the handover — the **fixture** was not portable. `base.tsv` held absolute
paths from the old machine; `lintcand.py:79` honours absolute paths, so they resolved to nothing.

**Two inherited controls were passing vacuously on empty output.** r649's rule applies to inherited
controls too: *a control that has never been seen to fail here is not evidence.*

### A mutation that does not reproduce the documented defect is not a mutation test

My first mutation left **all five controls green** — not because they are weak, but because the
flagged declaration sits at `Twin.lean:11` and the decoy at `:17`, so first-match-wins is right by
accident. Only the faithful r439 defect (header must *be* the bare short name, so a dotted header is
skipped) fails them — reporting the decoy at width 52, exactly as the fixture's docstring predicts.

## Machine-change artefacts to expect anywhere

* **No `.lake` in a fresh worktree** → `lint-dot-notation` errors on **both** sides and the gate
  renders that as `FAIL … NEW violations` + `rootsurplus UNRUN`. Symlink `.lake` to the rig root
  (no `lake` is invoked — the prohibition stands). Then: base **761** → head **741**, 0 new.
  **A check that errors on both sides is not a comparison.**
  `.gitignore` says `/.lake/` (directory-only), so the symlink shows untracked → `.git/info/exclude`.
* **Hardcoded absolute paths** — `minecount.py` passed the old machine's worktree as `cwd=`, which
  *raises*. Now derived from `__file__` (`TAUCETI_WT` overrides).

## A superseded run is not a red build

My sweep first read **#6188 as RED**. A commit's check-runs list carries *every* run created for that
SHA; a re-dispatch had left a `cancelled` duplicate `label` job while `sandboxed-build` was green and
nothing had conclusion `failure`. **Judge each check by its LATEST run per name.**
Sweep: `python3 /tmp/claude-1001/-home-chris/0b3b2a65-fff4-42cd-a2ef-093a3324dfa3/scratchpad/sweep.py`

## `gh pr edit` is broken against this repo

It fails on the projects-classic GraphQL deprecation and **leaves the body unchanged without
saying so**. Use `gh api -X PATCH repos/$R/pulls/<n> -F body=@file`, then re-read the body.

## Board (12:45Z — all CI green, every board on its current head)

| PR | head | label | whose move |
|---|---|---|---|
| **#5950** | `a64ba63667` | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `34ac589376` | `awaiting-author` | **me** — `reuse` + `api-design` on `Function.fiberMap` still open; `documentation` contested r653 |
| **#6188** | `36d148a8d9` | `awaiting-author` | **me** — not yet read this session |
| **#6412** | `360cdfc5b9` | `awaiting-author` | reviewer — `api-design` contested r653 |
| **#6418** | `d20b665467` | `awaiting-author` | reviewer — ⛔ `reuse` **fixed** r653, re-review running |
| **#6426** | `54f8eb82b5` | `awaiting-review` | reviewer — ready 12:15Z, inside the 46–64 min window |
| **#6432** | `f9bdb0a8b4` | `awaiting-CI` | reviewer — **marked ready 12:25Z** (r653 first action) |

## Settled — do not re-litigate

* **#6093** — keep `@[expose]` on `Function.fiberMap`; `Equiv.compFiberEquiv` must NOT have it;
  `fundamentalGroupEquivFiber_apply_coe` must NOT be `@[simp]`; `fiberMap_comp_apply` must NOT be
  `@[simp]` (`simpNF` rejects it, tested twice). `naming` and `placement` cleared on scope.
* **#6418** — `parallelns`/`slice` are one fact twice: `intCharacter_def` is `private` and stays;
  `intCharacter_eq_iff`'s `FDRep` args are **implicit**. `FDRep.isIntegral_char` is **deleted**, not
  rooted — it duplicates Mathlib's `FDRep.isIntegral_character` exactly. `decldiff`'s VANISHED row is
  a true positive and is answered in the body.
* **#6412** — the roadmap line the finding wants changed is in **TauCetiRoadmap**, a human-controlled
  repo this role may not open a PR or issue in. Contested, not fixable here.

## Next

1. **#6093** `reuse` + `api-design` — both on the new `TauCeti/Logic/Function/Fiber.lean`, which this
   PR *does* create, so both are in scope and should be implemented, not contested. `reuse` wants
   `fiberMap` built from `Set.MapsTo.restrict` with the laws via `Subtype.map_id`/`Subtype.map_comp`;
   `api-design` wants `@[expose]` gone. §6 records that removing it breaks `fiberMap_monodromy`
   across a module boundary — but the `reuse` restructure may change that, so do `reuse` first and
   re-measure. **No local build: gate on CI.**
2. **#6188** — not yet read this session. Five blocking rubrics per the handover; expect `api-design`
   and `reuse` to have re-fired on the rooting alone, which is expected, not a regression.
3. `handover/congraut-structural-deferred` opens only **after #6188 lands**.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (This machine has no toolchain at
  all, so it enforces itself.)
* No `uv`/`uvx` here — step 4 review drives unavailable until installed. The pipeline self-serves in
  46–64 min, so this is rarely the bottleneck.
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile. No bare `git stash`. Never #5481.
Never open a PR from `handover/improve-toolkit`. Every PR body needs a standalone `Roadmap: none`.
