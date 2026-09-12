# Last round — r660 (2026-09-12 14:50Z)

## A finding on one PR can be discharged by a different PR landing

#6188's `generality` asked for `extendOfIsLattice` over a domain `R` and fraction field `K`. That is
**exactly #6426**, which merged at 14:07:54Z — the PR the `scope` block split this work into. The
branch was **209 commits behind**, so it simply did not have it.

Merged `origin/main` in. **One conflict**, the predictable one: `Algebra/Module/Lattice.lean`, the
four declarations #6426 generalised and #6188 roots. Resolved by taking #6426's signatures
(`R`, `K`, `[Module.Free R S]`) and applying the rooting on top. Branch is **0 behind main**,
`MERGEABLE`, `lint-dot-notation` 759 → 751, 0 new.

**Before implementing a `generality` or `reuse` finding, check whether a sibling PR already landed
it.** Re-implementing would have duplicated merged code.

Also corrected a main-declarations bullet that still said *"integral … rational ambient spaces"* —
**stale on `main` itself**: #6426 generalised the declarations and left the prose.

## A `rfl` that works is not automatically a `rfl` that belongs

#6093 hit 9/10 (`reuse` ✅, `api-design` ✅ — the r658 restructure and r659 `mapsTo_fiber` naming
landed). The one new blocker, `proof-quality`, was fair: r658's `compFiberEquiv_refl`/`_trans` closed
with `Subtype.ext rfl`, unfolding `compFiberEquiv`, `Set.equivOfEq` and equivalence composition at
once. Both now read `Equiv.ext fun _ ↦ Subtype.ext (by simp)`, routing through
`compFiberEquiv_apply_coe` where that definitional equality already lives.

## ⚠ `xsibling` has a real defect — the r656 explanation is dead

r656 blamed its `specialOrthogonalToGeneralLinear` rows on the branch being 204 commits behind. The
branch is now **level with main and the rows persist**, at main's own line numbers (392, 399).
`origin/main` itself declares `_root_.TauCeti.QuadraticMap.specialOrthogonalToGeneralLinear` and
references it bare a few lines later, and main is green by construction.

`xsibling` reports a breakage for a wrapper **the PR does not remove** — the file is in the diff only
because the `congrAut → autCongr` rename touched call sites in it. **A standing false positive trains
the operator to skim the gate.** Toolkit task: restrict `xsibling` to wrappers the PR actually
removes, with a control built from this case. Run `tools/controls.sh` after (expect 129 → more).

## Board (14:50Z) — six open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `02175efe6` | building | `awaiting-author` | reviewer — **9/10**, last blocker fixed r660, board BEHIND |
| **#6188** | `3e027a657` | building | `awaiting-CI` | reviewer — main merged r660, board BEHIND |
| **#6412** | `360cdfc5b9` | green | `ready-to-merge` | nobody — 10/10 |
| **#6418** | `5c73d4c54` | green | `ready-to-merge` | nobody — **10/10** |
| **#6432** | `f9bdb0a8b4` | green | `awaiting-author` | **me — both contests rejected, see below** |

**Boards on #6093 and #6188 are BEHIND. Do NOT re-fix.**

## Next unit: #6432, whose contests were rejected

Both r657 contests failed: `naming` still reports the noncanonical namespace, `api-design` still
reports the missing structural lemmas, on `f9bdb0a8b4`. The sequencing argument did not land.

**New information that changes the picture:** #6188's own `api-design` now asks for the *same*
structural lemmas (`autCongr_apply` / `autCongr_symm_apply` as equalities to the composites — the
`handover/congraut-structural-deferred` content). So the two PRs are being asked for the same work
from both ends, and #6188 *is* the rooting, so the lemmas can finally be added there.

Options, in preference order:
1. **Add the structural lemmas to #6188** (where they are now unblocked and explicitly requested),
   then contest #6432 again citing that they exist on the rooting PR.
2. If #6188 lands first, rebase #6432 — rooting and rename come free.
3. Only if both stall: root the declarations in #6432 too, accepting the duplication.

#6188's other two blockers: `api-design` also wants `@[simp]` on `toLinearEquiv_ofLinearEquiv`
(r656 proved via CI that this breaks `simpNF` on
`UpperUnitriangular.congrLinearEquiv_pointsAction_eq_toLin`; the reviewer now explicitly asks to
restate *that* lemma first — an unrelated file, so weigh scope against it), and `naming` wants
`toLinearEquiv_ofLinearEquiv` moved to root `LinearEquiv`. **Check the precedent before implementing
the latter:** Mathlib's own `AlgEquiv.toLinearEquiv_ofLinearEquiv` — the finding's cited precedent —
sits in `AlgEquiv`, the namespace of `ofLinearEquiv`/`toLinearEquiv`, *not* in `LinearEquiv`, despite
its first explicit argument being a `LinearEquiv`. That may be a contest with evidence.

## Settled — do not re-litigate

* **#6093** — keep `@[expose]` on `Function.fiberMap` (reduction path exposed all the way down);
  `compFiberEquiv` must NOT be exposed; `fundamentalGroupEquivFiber_apply_coe`, `fiberMap_comp_apply`
  and `compFiberEquiv_trans` must NOT be `@[simp]`. `movedopens` clean. The conjugacy helper assumes
  **no connectedness**, only `hj : Joined (h e₀) f₀`.
* **#6188** — transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, `rfl`, via
  `ofLinearEquiv`, **NOT `@[simp]`** (simpNF, CI-confirmed). `congrAut` → `autCongr`.
* **#6418** — `isIntegral_char` deleted as an exact Mathlib duplicate; `intCharacter_eq_iff` rooted
  on cohesion; only `private intCharacter_def` stays nested. **10/10.**
* **#6412** — roadmap line is in TauCetiRoadmap, out of reach. Contest accepted. **10/10.**

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile (incl. `lint-baseline.txt` and the nolint
allowlist — the RATCHET message asking to delete 7 stale baseline lines is **not** mine to action).
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
Before believing a gate FAIL is yours, re-run it on the **pristine head** — and remember `xsibling`
currently has a standing false positive on `OrthogonalGroup.lean`.
A rubric that went green can go 🟡 again — re-read the board, never a remembered verdict.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
