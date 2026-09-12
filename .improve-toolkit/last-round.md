# Last round — r654 (2026-09-12 13:08Z)

## A pairwise contradiction is not a deadlock until the third opinion has been read

#6188's five blocking rubrics were not five problems. `reuse`, `api-design` and `proof-quality` all
pointed at one duplicated four-line transport, and two of their fixes were **mutually exclusive**:

* `reuse`: "keep the `have`s inline so no shared restating declaration reappears"
* `proof-quality`: "restore the single `private theorem …`"

Contesting looked obvious and would have been wrong. **`api-design` had already written the way
out** — state it once, public, phrased through `ofLinearEquiv` so it mentions neither
`generalLinearEquiv` nor `symm`, which is exactly what stops it being a restatement of
`MulEquiv.apply_symm_apply`:

```lean
@[simp]
theorem LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv (f : M ≃ₗ[R] M) :
    (ofLinearEquiv f).toLinearEquiv = f := rfl
```

`generality` (dead `M` binders) dissolved on its own — the lemma is stated over `M`.

**Read the whole set of findings before concluding one has no implementation.**

## Don't guess `rfl` — find the Mathlib precedent

`rfl` here is backed by `AlgEquiv.toLinearEquiv_ofLinearEquiv`, proved exactly that way, plus the
fact that `generalLinearEquiv` is literally `⟨toLinearEquiv, ofLinearEquiv, …⟩`. The old CI failure
recorded in the body ("`MulEquiv.apply_symm_apply` reported unused, unsolved goals") was always about
**`simp` matching syntactically**, never about the fact being hard to prove.

## An `open` does not rescue a name the file declares at root

The gate caught r389 before CI did — `rootedin` *and* `xsibling` both fired on a bare reference to
the new lemma, in a file that has `open LinearMap.GeneralLinearGroup` and already writes bare
`coe_ofLinearEquiv`. Inside `namespace TauCeti` the lookup is `TauCeti.x`, then root `x`. Qualifying
both sites turned three checks green at once.

## Rename longest-first, then residue-check

`congrAut_apply` is a prefix-collision hazard for a naive `congrAut` substitution: one pass yields
`autCongr_apply` where `autCongr_apply_apply` was wanted. 35 sites, three files, residue 0.

## Measure a "too wide" line against HEAD before believing you widened it

Two lines flagged at 196 and 164 chars were pre-existing roadmap URLs, byte-identical before my
change. `width` only judges added lines and stayed green throughout.

## The board latency band is 32–64 min, not 46–64

#6426's first board came **32 min** after `ready_for_review`. Do not treat 46 as a floor when
judging whether a drive is overdue.

## Board (13:08Z)

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `34ac589376` | green | `awaiting-author` | **me** — `reuse` + `api-design` on `Function.fiberMap` |
| **#6188** | `2aaf5e818c` | building | `awaiting-author` | reviewer — **4 rubrics fixed r654**, board BEHIND |
| **#6412** | `360cdfc5b9` | green | `awaiting-author` | reviewer — `api-design` contested r653 |
| **#6418** | `d20b665467` | building | `awaiting-author` | reviewer — ⛔ `reuse` fixed r653, board BEHIND |
| **#6426** | `54f8eb82b5` | green | `awaiting-review` | **nobody — 10/10 green, 0 files outside `TauCeti/`** |
| **#6432** | `f9bdb0a8b4` | green | `awaiting-CI` | reviewer — awaiting first board |

**Boards on #6188 and #6418 are BEHIND their heads. The fixes are already pushed — do NOT re-fix.**

## Settled — do not re-litigate

* **#6188** — the transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, public,
  `rfl`, phrased via `ofLinearEquiv`. `congrAut` is now **`autCongr`**, with
  `autCongr_apply_apply` / `autCongr_symm_apply_apply`, verified against `AlgEquiv.autCongr` and
  `LinearEquiv.conj_apply`/`conj_apply_apply`. Both `have`s keep their syntactic shape because
  `simp` matches syntactically.
* **#6093** — keep `@[expose]` on `Function.fiberMap`; `Equiv.compFiberEquiv` must NOT have it;
  `fundamentalGroupEquivFiber_apply_coe` and `fiberMap_comp_apply` must NOT be `@[simp]`.
  `naming` and `placement` cleared on scope; `documentation` contested r653 (0 roadmap lines touched).
* **#6412** — the roadmap line is in **TauCetiRoadmap**, human-controlled and out of reach.
* **#6418** — `FDRep.isIntegral_char` deleted, not rooted: it duplicates Mathlib's
  `FDRep.isIntegral_character` exactly.

## Next

1. **#6093** `reuse` + `api-design`, both on `TauCeti/Logic/Function/Fiber.lean`, which this PR
   creates — in scope, so implement. `reuse` wants `fiberMap` via `Set.MapsTo.restrict` with the
   laws through `Subtype.map_id`/`Subtype.map_comp`; `api-design` wants `@[expose]` gone and
   `fiberMap_monodromy` rewritten through `fiberMap_apply_coe`/`Subtype.ext`. §6 says removing
   `@[expose]` breaks it across a module boundary — **do `reuse` first, then re-measure**, since the
   restructure may remove the need for the body.
2. Watch #6188 and #6418 CI; their boards are behind, so wait rather than re-fix.
3. `handover/congraut-structural-deferred` opens only **after #6188 lands** — and its
   `congrAut_eq`/`congrAut_symm_eq` must be **renamed to `autCongr_eq`/`autCongr_symm_eq`** first.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* No `uv`/`uvx` — step-4 drives unavailable. The pipeline self-serves in 32–64 min.
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile. No bare `git stash`. Never #5481.
Never open a PR from `handover/improve-toolkit`. Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
