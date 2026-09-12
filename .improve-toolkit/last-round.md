# Last round — r656 (2026-09-12 13:40Z)

## A green build is not a green CI

#6188 went red on `sandboxed-build`, but the build **succeeded** — 10981 jobs, axioms and
module-system audits clean, 8738/8738 docstrings. `sandboxed-build` bundles build + audits +
`lint-env`, and the failure was one new `simpNF` violation. Reading only "did it compile" would have
sent me hunting an elaboration error that did not exist. **Always open the log and find the actual
`##[error]`.**

The defect was the `@[simp]` r654 added on `api-design`'s instruction:

```
[simpNF] TauCeti.UpperUnitriangular.congrLinearEquiv_pointsAction_eq_toLin
  Left-hand side simplifies … using
  simp only [*, @LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv]
```

That lemma is `@[simp]` and states its subject as `(ofLinearEquiv _).toLinearEquiv`, so ours took it
out of normal form. Attribute dropped, lemma kept — both proofs cite it **by name**, so `simp` never
needed it. Reported to `api-design` **with the CI output**; the lint's own fix (restate the other
lemma) is declined with a reason — unrelated file, statement change, the shape `scope` blocked once.

## `rfl` and the 35-site rename both held

Evidence, not assumption: r654's `rfl` for `toLinearEquiv_ofLinearEquiv` and the
`congrAut → autCongr` rename across three files **compiled**. The Mathlib precedent
(`AlgEquiv.toLinearEquiv_ofLinearEquiv := rfl`) was a sound basis for a proof written with no local
toolchain.

## "Red now" is not evidence about your own diff either

`xsibling` reported `specialOrthogonalToGeneralLinear` breaking at `OrthogonalGroup.lean:390,397`.
False positive, on three independent grounds: it fires identically on the **pristine** head;
**`origin/main` carries the same shape** and is green; and **CI compiled this exact head**. The
branch is **204 commits behind main** (merge-base `dff54ce97`), and main edited that very file.

**Before believing a gate FAIL, run the gate on the pristine head — and check how far main has
moved.**

## Step 4: eligible and still the wrong call

#6432 sat green with no board at **71 min**, past the hour and past the band. Installed `uv`
(0.12.13, `~/.local/bin/uvx`) so drives are now possible — then did **not** drive. Its board arrived
on its own at **13:32:44Z, 67 min in**; a drive would have burned ~$16 reproducing it.

**Measured band is now 32–67 min** (#6426 32, #6412 65, #6432 67). Six minutes past a
three-sample band is not a stalled PR.

## Board (13:40Z)

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `9d13f95872` | building | `awaiting-author` | reviewer — last rubric fixed r655, board BEHIND |
| **#6188** | `94921c53a` | building | `awaiting-CI` | reviewer — simpNF fixed r656, board BEHIND |
| **#6412** | `360cdfc5b9` | green | 10/10 ✅ | nobody |
| **#6418** | `d20b665467` | green | `awaiting-review` | reviewer — board BEHIND |
| **#6426** | `54f8eb82b5` | green | `ready-to-merge` | nobody — 10/10, unmerged at 81 min; **pipeline's call, never mine** |
| **#6432** | `f9bdb0a8b4` | green | `awaiting-review`→author | **me — next unit, see below** |

**Boards on #6093, #6188 and #6418 are BEHIND their heads. Do NOT re-fix.**

## Next unit: contest #6432 on SEQUENCING, not merit

Its board (13:32Z) has two blockers, and **both are already built elsewhere**:

* `naming` — *"move `congrAut`, `congrAut_apply`, `congrAut_symm_apply` to root `LinearEquiv`"*.
  **That is #6188**, which additionally renames them to `autCongr` / `autCongr_apply_apply` /
  `autCongr_symm_apply_apply`.
* `api-design` — *"Add semilinear `congrAut_eq` and `congrAut_symm_eq`, rebasing on the namespace
  relocation first if necessary"*. **That is `handover/congraut-structural-deferred`**, openable
  only after #6188 lands.

If #6432 roots the declarations itself it duplicates an open PR and turns a textual overlap into a
hard conflict. The reviewer's own *"rebasing … first if necessary"* shows it is receptive. Contest
with the sequence: **#6188 lands → #6432 rebases (rooting and rename come free, keeping only the
semilinear generalisation) → deferred branch opens as `autCongr_eq` / `autCongr_symm_eq`.**

## Settled — do not re-litigate

* **#6188** — transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, public,
  `rfl`, phrased via `ofLinearEquiv`, and **deliberately NOT `@[simp]`** (simpNF, CI-confirmed).
  `congrAut` is now `autCongr`.
* **#6093** — keep `@[expose]` on `Function.fiberMap`; `compFiberEquiv` must NOT have it;
  `fundamentalGroupEquivFiber_apply_coe` and `fiberMap_comp_apply` must NOT be `@[simp]`. The
  conjugacy helper assumes **no connectedness** — only `hj : Joined (h e₀) f₀`.
* **#6412** — roadmap line is in TauCetiRoadmap, out of reach. Contest accepted, 10/10.
* **#6418** — `FDRep.isIntegral_char` deleted, not rooted: exact Mathlib duplicate.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.
* **#6188 is 204 commits behind main** — if it ever conflicts, merge main in and re-gate.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile (incl. `lint-baseline.txt` and the nolint
allowlist — the RATCHET message asking to delete 7 stale baseline lines is **not** mine to action).
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is now installed at `~/.local/bin/uvx` for step-4 drives.
