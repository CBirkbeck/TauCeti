# Last round — r665 (2026-09-12 16:00Z)

## 🎉 #6093 is 10/10 `ready-to-merge`

The coupled-annotation contest was accepted. **It worked because it enumerated the states rather
than arguing**: `main` carries `@[expose]` *and* `@[simp]` together; this PR removes `@[expose]` at
`api-design`'s own earlier request; the third combination is CI-proven red. Two of three
configurations are green and the request was the third.

## "Tried and failed" is scoped to the form it was tried in

#6188 took a ⛔ `reuse` block, and it was right:

> Delete `toLinearEquiv_ofLinearEquiv` and prove each local `h` with
> `(generalLinearEquiv R M₁).apply_symm_apply f`, allowing definitional reduction of
> `generalLinearEquiv`'s `invFun`.

r654 reasoned this *could* work and did not test it. The PR body carried, from an earlier CI cycle,
that `MulEquiv.apply_symm_apply` "does not work" — but **that failure was about the `simp only` set**,
where it never fires because `simp` matches syntactically. As the *proof of the `have`* it needs no
matching at all, only definitional reduction. Different position, different question; the body
recorded the verdict without the position and hid the distinction.

Deleting the declaration retires two further findings: `naming` wanted it moved to root
`LinearEquiv` (contested r662), `api-design` wanted it `@[simp]` (r656, CI-proven red). **The
cheapest way to settle a disputed declaration can be not to have it.**

`reuse` had been consistent every round — no shared declaration, prove the transport where it is
needed. r654 read that as irreconcilable with `api-design` and reached for a third option; the
reconciliation existed and was one line.

## The reviewer found the consumers that justify last round's lemmas

`OrthogonalGroup.lean` was re-proving `autCongr_apply`/`autCongr_symm_apply` inline as
`show … by ext m; exact autCongr_apply_apply …`. Now `rw [LinearEquiv.autCongr_apply]` and
`rw [LinearEquiv.autCongr_symm_apply]`, eight lines shorter. The call sites were there all along,
written the long way.

## Board (16:00Z) — five open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | **`ready-to-merge`** | nobody — **10/10** |
| **#6188** | `587afa02f` | building | `awaiting-CI` | reviewer — ⛔ cleared r665, board BEHIND |
| **#6418** | `5c73d4c54` | green | `ready-to-merge` | nobody — 10/10 |
| **#6432** | `ba59a9318` | building | `awaiting-CI` | reviewer — question outstanding on `naming` |

**#6188's and #6432's boards are BEHIND. Do NOT re-fix.**

## Next

1. **Watch #6188 on `587afa02f`.** The risk is the `have` proof: `(generalLinearEquiv R M₁).apply_symm_apply f`
   against a `have` stated as `((generalLinearEquiv R M₁).symm f).toLinearEquiv = f`. It typechecks
   only if `invFun` reduces definitionally — which is the reviewer's own stated premise, but is
   untested. If it fails, the error will name the mismatch; report it on the `reuse` thread and
   restore a named lemma phrased through `ofLinearEquiv`.
2. **Watch #6432 on `ba59a9318`** — should return to green (the revert restores `f9bdb0a8b4`'s state
   plus a clean `main` merge).
3. **#6432's `naming` thread has an open question**: rebase onto #6188, or root-and-rename here.
   Both routes are on the table; the choice is the reviewer's. **Do nothing there until it answers.**
4. With #6093 clearing the ⛔ chain, the deferred structural work is fully discharged: the
   `handover/congraut-structural-deferred` branch content now lives on #6188 as `autCongr_apply` /
   `autCongr_symm_apply`. That branch can be considered spent.
5. Five open, so step 5 does **not** trigger. When it does: `ContRepresentation` 141/184,
   `Representation` 134/189, `AbelianVariety.Hom` 41/54, `WeierstrassCurve` 26/27; avoid
   `IsCoveringMap` / `Deck.IsQuotientCoveringMap`. Measure against a **freshly fetched** `origin/main`.

## Settled — with the conditions attached

* **#6093** — **10/10.** `@[expose]` on `Function.fiberMap` stays; on `fundamentalGroupEquivFiber`
  it is removed, **and that is why** `_apply_coe` is not `@[simp]` — coupled, and accepted as such.
* **#6188** — there is **no** `toLinearEquiv_ofLinearEquiv`; the transport is proved inline from
  `(generalLinearEquiv R M).apply_symm_apply`, which works as a *proof term* though not as a simp
  lemma. `congrAut` → `autCongr`. Structural `autCongr_apply` / `autCongr_symm_apply` exist and are
  **not** `@[simp]`; their call sites in `OrthogonalGroup.lean` use them. Main merged.
* **#6418** — `isIntegral_char` deleted as an exact Mathlib duplicate; `intCharacter_eq_iff` rooted
  on cohesion. **10/10.**
* **#6432** — rename reverted; it is coupled to the relocation by the name-keyed baseline.

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
A rubric that went green can go 🟡 again — re-read the board, never a remembered verdict.
Re-read a finding's text too, and **record the position a failed attempt was tried in** — "tried and
failed" for a simp lemma says nothing about the same term used as a proof.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**133 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
