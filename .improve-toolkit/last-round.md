# Last round — r667 (2026-09-12 16:37Z)

## When a rubric loop returns to a rejected position, look for a sibling PR where it is approved

#6188's `proof-quality` asked, verbatim, for *"a shared private bridge … using `coe_toLinearEquiv`,
`coeFn_generalLinearEquiv`, and `apply_symm_apply`"* — which is the `private theorem
toLinearEquiv_generalLinearEquiv_symm` this PR **opened with**.

The full circuit: private bridge → (`reuse`) public lemma via `ofLinearEquiv` → (`reuse` ⛔) inline
proof from `apply_symm_apply` → (`proof-quality`) private bridge. Four positions, three rubric
demands, one fact.

Restored it on evidence rather than as a fourth guess: **#6432 carries the identical bridge and its
`reuse` reads ✅**. The same reviewer approving the same declaration on a sibling PR beats any
reading of the rubric text.

Two of my own omissions fixed with it:
* a **second** `## Main statements` section still advertising `toLinearEquiv_ofLinearEquiv`, deleted
  in r665 — **deleting a declaration means deleting what advertises it**;
* `autCongr_symm_apply`'s docstring described its proof; §8 — narrative to a source comment.

## `generality` exposed a convergence; I asked rather than chose

It asks #6188 to state the API semilinearly — **#6432's entire topic**, mirroring #6432 being told
to take #6188's relocation. After r666 both PRs share the relocation, the names and the structural
lemmas, so doing it here makes `GeneralLinearGroup/Congr.lean` **identical in both** and leaves
#6432 with nothing of its own — the arrangement the original `scope` ⛔ existed to prevent.

Genuinely unshared: this PR also roots the four `extendOfIsLattice` declarations in
`Algebra/Module/Lattice.lean` — the half of `TauCeti.LinearEquiv` that #6432's `nsslice` row reports
as still nested.

The thread now carries two options, either implementable immediately: this PR generalises too, or
#6432 keeps the file and this one stands as the `Lattice.lean` rooting. **This is not the deferral
the reviewer twice refused** — that was "another PR will fix this later"; this is which of two open,
green, converged PRs owns a file.

## Board (16:37Z) — five open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `ready-to-merge` | nobody — **10/10** |
| **#6188** | `1e9fddb17` | building | `awaiting-CI` | reviewer — 3 of 4 blockers fixed, board BEHIND |
| **#6418** | `5c73d4c54` | green | `ready-to-merge` | nobody — **10/10** |
| **#6432** | `3d4b240ee` | building | `awaiting-CI` | reviewer — rooted+renamed+semilinear, board BEHIND |

**Both live boards are BEHIND. Do NOT re-fix.**

## Next

1. **Watch #6432 on `3d4b240ee`** — rooting + rename + two new lemmas, none built locally. The
   riskiest piece is `autCongr_symm_apply`'s `rw [MulEquiv.symm_apply_eq, autCongr_apply]; exact
   LinearEquiv.ext fun m ↦ by simp` at the **semilinear** generality.
2. **Watch #6188 on `1e9fddb17`** — the restored bridge is the file's original proof, so low risk;
   the `simp only` sets now cite `toLinearEquiv_generalLinearEquiv_symm` again.
3. **#6188's `generality` thread** — answer pending. Do **not** implement either option until it
   replies; both are written out there and either is a single push.
4. **#6188's `api-design` bullet 1** is still open: no `autCongr_refl` / `autCongr_symm` /
   `autCongr_trans`. Mathlib's `AlgEquiv` versions are all `rfl`, but ours is a composite through
   `generalLinearEquiv` and `congrLinearEquiv`, so `rfl` is unlikely to transfer — expect to need
   `MulEquiv.ext` plus the pointwise lemmas. **Do this in whichever PR ends up owning the file.**
5. Five open, so step 5 does **not** trigger. When it does: `ContRepresentation` 141/184,
   `Representation` 134/189, `AbelianVariety.Hom` 41/54, `WeierstrassCurve` 26/27; avoid
   `IsCoveringMap` / `Deck.IsQuotientCoveringMap`. Measure against a **freshly fetched** `origin/main`.

## Settled — with the conditions attached

* **#6093** — **10/10.** `@[expose]` on `fundamentalGroupEquivFiber` removed, **and that is why**
  `_apply_coe` is not `@[simp]`.
* **#6418** — **10/10.** `isIntegral_char` deleted as an exact Mathlib duplicate.
* **#6188** — the transport is a **`private` bridge proved extensionally**, which is where the file
  began and what `proof-quality` asked for; `reuse` accepts it (✅ on #6432's identical copy).
  Structural lemmas present, not `@[simp]`. Main merged.
* **#6432** — rooted **and** renamed together (name-keyed baseline couples them), semilinear,
  structural lemmas at that generality.

## Still needs Chris

* **No `lake build` / `cache get` / `lake update`.** Gate on CI. (No toolchain here anyway.)
* `cft-fix-6093` holds 13 superseded files + a stray `lake-manifest.json` bump. #5950.

## Standing traps

Never merge/close a PR. Push to `fork`, never `origin` (403). One worktree: `improver-1`.
Never touch `scripts/`, `.github/`, the lakefile — **including the dot-notation baseline**, which is
why renaming a flagged declaration is red unless it is rooted in the same commit.
No bare `git stash`. Never #5481. Never open a PR from `handover/improve-toolkit`.
Every PR body needs a standalone `Roadmap: none`.
`gh pr edit` silently no-ops here — use `gh api -X PATCH … -F body=@file`.
A fresh worktree needs `.lake` symlinked or `lint-dot-notation` errors on both sides.
`uvx` is at `~/.local/bin/uvx`; measured board latency band is **32–67 min**.
**COMMIT BEFORE GATING** — prepush reads HEAD and now refuses a dirty tree.
Before believing a gate FAIL is yours, re-run it on the **pristine head**.
A rubric that went green can go 🟡 again, and **clearing a ⛔ reveals rubrics that never ran**.
**Deleting a declaration means deleting what advertises it** — module docstring included.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**133 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
