# Last round — r666 (2026-09-12 16:30Z)

## The reviewer answered the r664 question, and the answer was "fix the head"

> *"A promised future rebase does not correct the API presented by this PR."*

Third time of asking, unambiguous. r664 had put both routes to the reviewer and said the choice was
theirs; this is the choice. **Asking was not wasted** — it turned a guess into an instruction, and
the instruction is on the record for `scope` to read.

## #6432 took the relocation, in one commit with the rename

r664 proved the halves are coupled — the rename alone adds three `lint-dot-notation` findings
because the baseline grandfathers **by declaration name**, while rooted the declarations are not
flagged at all. So both land together. `lint-dot-notation`: **759 → 756, 0 new.**

Plus the structural `autCongr_apply` / `autCongr_symm_apply` at the **semilinear** generality — what
`handover/congraut-structural-deferred` held all along, legal here now that root `LinearEquiv` (the
"lint-clean canonical namespace" the finding named) arrives in the same commit.

Both branches now carry identical names and statements, so whichever merges second sees its own work
already applied rather than a conflict.

## #6188's ⛔ cleared and the r665 gamble held

`(generalLinearEquiv R M₁).apply_symm_apply f` typechecks as the proof of the `have`, exactly as the
reviewer's *"allowing definitional reduction of `generalLinearEquiv`'s `invFun`"* predicted.
`reuse` ✅, `naming` ✅ (the disputed declaration no longer exists), `scope` ✅.

**Clearing a ⛔ starts the rest of the review, not the merge** — third time this watch, now reliable
enough to plan around.

## Board (16:30Z) — five open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `ready-to-merge` | nobody — **10/10** |
| **#6188** | `587afa02f` | green | `awaiting-author` | **me — four blockers, board ON-HEAD** |
| **#6418** | `5c73d4c54` | green | `ready-to-merge` | nobody — **10/10** |
| **#6432** | `3d4b240ee` | building | `awaiting-CI` | reviewer — rooted+renamed r666, board BEHIND |

**#6432's board is BEHIND. Do NOT re-fix.**

## Next unit: #6188's four blockers — read them together, they point at each other

1. **`proof-quality`** — *"The two pointwise conjugation proofs rely on an implementation-level
   definitional equality across `generalLinearEquiv` and `toLinearEquiv`."* That is **precisely the
   proof `reuse` demanded** in the ⛔ one round earlier, and the third lap of this loop
   (private bridge → public lemma → inline definitional proof). Do **not** simply move to a fourth
   spelling. The shared reading across all three rounds is *state the transport once, somewhere
   legitimate*; read `reuse`'s ✅ text and `proof-quality`'s full finding side by side before
   touching it, and if no single form satisfies both, that is the contest — with all three CI
   results quoted.
2. **`generality`** — *"the conjugation API remains unnecessarily restricted to linear equivalences
   over one semiring"*: that is **#6432's entire topic**, now asked of #6188, mirroring #6432 being
   asked for #6188's relocation. Both branches now share names and statements, so whichever lands
   first leaves the other very little. Say so rather than duplicating a third time.
3. **`api-design`** — lacks the functorial API (`refl`/`trans`/`symm` laws), and *"the module
   documentation advertises a nonexistent declaration"*. Check the module docstring in
   `GeneralLinearGroup/Congr.lean` against what survived r665's deletion of
   `toLinearEquiv_ofLinearEquiv`.
4. **`documentation`** — stale and proof-oriented text in the congruence module. Likely the same
   docstring; §8 applies (review argument belongs in the PR body, not the file).

Also: watch #6432's CI on `3d4b240ee` — a rooting plus rename plus two new lemmas, none built
locally.

Five open, so step 5 does **not** trigger. When it does: `ContRepresentation` 141/184,
`Representation` 134/189, `AbelianVariety.Hom` 41/54, `WeierstrassCurve` 26/27; avoid
`IsCoveringMap` / `Deck.IsQuotientCoveringMap`. Measure against a **freshly fetched** `origin/main`.

## Settled — with the conditions attached

* **#6093** — **10/10.** `@[expose]` on `fundamentalGroupEquivFiber` is removed, **and that is why**
  `_apply_coe` is not `@[simp]` — coupled, accepted as such.
* **#6418** — **10/10.** `isIntegral_char` deleted as an exact Mathlib duplicate;
  `intCharacter_eq_iff` rooted on cohesion.
* **#6188** — no `toLinearEquiv_ofLinearEquiv`; transport proved inline from
  `(generalLinearEquiv R M).apply_symm_apply`, which works as a **proof term** though not as a simp
  lemma. Structural lemmas present, not `@[simp]`. Main merged.
* **#6432** — rooted **and** renamed together, because the name-keyed baseline couples them.
  Structural lemmas added at the semilinear generality. `nsslice`'s remaining four are the
  `extendOfIsLattice` family, which #6188 roots.

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
Re-read a finding's text, and **record the position a failed attempt was tried in**.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**133 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
