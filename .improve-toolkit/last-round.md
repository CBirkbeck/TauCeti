# Last round — r668 (2026-09-12 17:05Z)

## 🎉 #6418 MERGED 16:58:30Z — third landing of this watch

`root the TauCeti.FDRep character API`. Its path: ⛔ `reuse` (an exact Mathlib duplicate) → four
rubrics arriving when the block lifted → 10/10 → the bot. **Every finding on it was implemented,
none contested.**

## An answer can arrive as a finding rather than as a reply

r667 asked, on #6188's `generality` thread, which of two converged PRs should own
`GeneralLinearGroup/Congr.lean`. No reply came — a **⛔ `scope` block** answered instead:

> *"Keep this PR to rooting and renaming the existing declarations; move both structural lemmas
> **and the corresponding call-site rewrites** to a follow-up PR."*

The follow-up already exists: **#6432 carries both lemmas at the semilinear generality with
`api-design` ✅**. So #6188 is now the relocation alone, and the structural lemmas plus their
call-site rewrites are removed (the `Main statements` section went with them).

**Asking was still right.** The question named the two options precisely and the block picked one. Had
r667 chosen unilaterally and generalised #6188, this ⛔ would have landed on a PR carrying even more
of #6432's topic.

`api-design` asked for those lemmas here; `scope` removed them. Both were satisfiable — just not in
the same PR, which is what `scope` is for.

## Port a fix the moment it is accepted anywhere

#6432 came back 7/10 (`naming`, `api-design`, `generality`, `scope` all ✅ — the r666 work landed).
Its three remaining findings were **verbatim the ones #6188 had already taken**: the two `show`/`ext`
blocks in `map_specialOrthogonalGroup` (`reuse` + `proof-quality`, same site) and
`autCongr_symm_apply`'s proof-narrative docstring (`documentation`). Ported in one commit.

## Do not chase a 🟡 that sits behind a ⛔

#6188's `reuse` now wants the private bridge deleted again — position **three of three** on the same
fact (private bridge → public lemma → inline → private bridge → delete). Not acted on: `scope` is a
⛔, the rest of the board is *not yet run*, and the next board judges a PR that no longer contains
the structural lemmas. If it returns, the evidence to quote is that **#6432 holds the identical
private bridge with `reuse` ✅**.

## Board (17:05Z) — four open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `ready-to-merge` | nobody — **10/10** |
| **#6188** | `da705df62` | building | `awaiting-author` | reviewer — scope-split r668, board BEHIND |
| **#6432** | `98bb7e78f` | building | `awaiting-author` | reviewer — three fixes ported r668, board BEHIND |

**Both live boards are BEHIND. Do NOT re-fix.**

## Next

1. **Watch both builds.** #6188 `da705df62` (removal only, low risk); #6432 `98bb7e78f` (two `rw`s
   replacing `show` blocks — the same edit #6188 built green, so also low risk).
2. **#6188's next board judges a smaller PR.** Expect the rubrics that were *not yet run* behind the
   ⛔ to appear fresh. `generality` may re-fire asking for semilinearity — the answer is now on the
   record: **#6432 is the PR that does that**, and `scope` said so. Quote the block.
3. **#6432 is the one to push toward green** — it now owns the structural lemmas, the semilinear
   generality, and the call-site rewrites. It is 7/10 with three fixes just pushed.
4. **`api-design`'s functorial API** (`autCongr_refl`/`symm`/`trans`) belongs in **#6432**, not
   #6188. Mathlib's `AlgEquiv` versions are `rfl` on a structure literal; ours is a composite through
   `generalLinearEquiv` and `congrLinearEquiv`, so expect `MulEquiv.ext` plus the pointwise lemmas.
5. **Four open** — one more merge and step 5 triggers. Prospect candidates:
   `ContRepresentation` 141/184, `Representation` 134/189, `AbelianVariety.Hom` 41/54,
   `WeierstrassCurve` 26/27; avoid `IsCoveringMap` / `Deck.IsQuotientCoveringMap` (they overlapped
   #6093, now merged-adjacent — re-check against a **freshly fetched** `origin/main` before ranking).

## Settled — with the conditions attached

* **#6093** — **10/10.** `@[expose]` on `fundamentalGroupEquivFiber` removed, **and that is why**
  `_apply_coe` is not `@[simp]`.
* **#6418** — **MERGED.**
* **#6188** — the relocation alone: `TauCeti.LinearEquiv` → root, four `extendOfIsLattice` plus three
  conjugation declarations, and the rename. **No structural lemmas** (`scope` ⛔). Transport is the
  `private` bridge; `reuse` disputes it but sits behind the ⛔.
* **#6432** — semilinear, rooted, renamed, **owns** the structural lemmas and the call-site rewrites.

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
A rubric that went green can go 🟡 again; **clearing a ⛔ reveals rubrics that never ran**; and
**a 🟡 behind a ⛔ may not survive the next board — do not chase it**.
**Deleting a declaration means deleting what advertises it.**
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**133 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
