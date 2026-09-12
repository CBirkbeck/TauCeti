# Last round — r661 (2026-09-12 15:05Z)

## The gate had a false positive, and reasoning past it twice was the real error

`xsibling`'s `specialOrthogonalToGeneralLinear` rows were explained away in r656 ("main moved") and
correctly doubted in r660. The cause, found by running the tool's own `gone` computation on the real
file instead of theorising:

A declaration written `_root_.TauCeti.Foo.bar` gives `ns = 'TauCeti.Foo'`, so the guard asked
`'TauCeti.TauCeti' not in h` — **vacuously true for every file**. `TauCeti` entered `wrappers`, and
every bare use of any `TauCeti.*` name in that file became a BREAK.

Fixed by skipping `ns == 'TauCeti'` / `ns.startswith('TauCeti.')`: rooting *into* TauCeti lands a
declaration exactly where the enclosing wrapper already puts it. The legitimate path
(`_root_.QuadraticMap.IsometryEquiv.*` → tests `'TauCeti.QuadraticMap' in h`) was never broken.

**Controls 129 → 131**, mutation-tested:

```
MUTATION (original guard restored):
  FAIL  xsibling: rooting INTO TauCeti is not a lost wrapper (r661)
  PASS  xsibling: still finds the real breakage with that case present
  130 passed, 1 failed
```

The paired positive is the point — it proves the fix **narrows** the check rather than blinding it.
#6188's gate went **11 ok / 4 failed → 12 ok / 3 failed**.

**A check that cries wolf is a check the operator learns to skim.**

## A goal printed unchanged means the lemma never fired

#6093 went red on r660's `Subtype.ext (by simp)`:

```
Fiber.lean:117:33: unsolved goals
⊢ ↑(((Equiv.refl X).compFiberEquiv y) x✝) = ↑((Equiv.refl ↑(p ⁻¹' {y})) x✝)
```

`simp` made **no progress**; the `@[simp]` characteristic lemma never matched. Naming it
(`Subtype.ext (compFiberEquiv_apply_coe (p := p) … e)`) removes the question and is what
`proof-quality` asked for. **"`simp` closes it" is a guess until CI says so.**

## Board (15:05Z) — six open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | building | `ci-failed`¹ | reviewer — 9/10, last blocker re-fixed r661 |
| **#6188** | `3e027a657` | building | `awaiting-CI` | reviewer — main merged r660, board BEHIND |
| **#6412** | `360cdfc5b9` | green | `ready-to-merge` | nobody — 10/10 |
| **#6418** | `5c73d4c54` | green | `ready-to-merge` | nobody — 10/10 |
| **#6432** | `f9bdb0a8b4` | green | `awaiting-author` | **me — contests rejected** |

¹ stale label, describes the superseded head. **Read CI from the check-runs API for the CURRENT head.**

## Next

1. **Watch #6093 on `370dad05e`.** If `Subtype.ext (compFiberEquiv_apply_coe …)` still fails, the
   defeq on the RHS (`Equiv.refl`/`Equiv.trans` application) is the suspect — fall back to
   `Equiv.ext fun e ↦ Subtype.ext <| by rw [compFiberEquiv_apply_coe]` and report the CI output.
2. **Watch #6188 on the merge `3e027a657`** — it validates the #6426 conflict resolution. Do not
   push on top until it lands, or a failure cannot be attributed to the merge.
3. **Then #6188's three blockers**, in this order:
   * `api-design` bullet 2 — add structural `autCongr_apply` / `autCongr_symm_apply` (equalities to
     the composites). These exist on `handover/congraut-structural-deferred`, already
     `_root_`-anchored **and already semilinear**; #6188 *is* the rooting, so they are unblocked
     here. Verified verbatim in r657.
   * `naming` — wants `toLinearEquiv_ofLinearEquiv` under root `LinearEquiv`. **Check the precedent
     first:** Mathlib's `AlgEquiv.toLinearEquiv_ofLinearEquiv`, which the finding itself cites, sits
     in `AlgEquiv` — the namespace of `ofLinearEquiv`/`toLinearEquiv` — *not* in `LinearEquiv`,
     despite its first explicit argument being a `LinearEquiv`. Likely a contest with evidence.
   * `api-design` bullet 1 — `@[simp]` on `toLinearEquiv_ofLinearEquiv`. r656 proved via CI this
     breaks `simpNF` on `UpperUnitriangular.congrLinearEquiv_pointsAction_eq_toLin`; the reviewer now
     asks to restate *that* lemma first, in a file this PR does not touch. Weigh scope.
4. **#6432**: prefer landing #6188 first (rooting + rename come free on rebase). Only if both stall,
   root in #6432 too and accept the duplication.
5. Six PRs open, so step 5 does **not** trigger. When it does: `ContRepresentation` 141/184,
   `Representation` 134/189, `AbelianVariety.Hom` 41/54, `WeierstrassCurve` 26/27; avoid
   `IsCoveringMap` / `Deck.IsQuotientCoveringMap`. Measure against a **freshly fetched** `origin/main`.

## Settled — do not re-litigate

* **#6093** — keep `@[expose]` on `Function.fiberMap`; `compFiberEquiv` must NOT be exposed;
  `fundamentalGroupEquivFiber_apply_coe`, `fiberMap_comp_apply`, `compFiberEquiv_trans` must NOT be
  `@[simp]`. `movedopens` clean. Conjugacy helper assumes **no connectedness**.
* **#6188** — transport is `LinearMap.GeneralLinearGroup.toLinearEquiv_ofLinearEquiv`, `rfl`, via
  `ofLinearEquiv`, **NOT `@[simp]`**. `congrAut` → `autCongr`. Main merged; 0 behind.
* **#6418** — `isIntegral_char` deleted as an exact Mathlib duplicate; `intCharacter_eq_iff` rooted
  on cohesion. **10/10.**
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
Before believing a gate FAIL is yours, re-run it on the **pristine head**.
A rubric that went green can go 🟡 again — re-read the board, never a remembered verdict.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**131 controls, 0 failed.** Run them after any toolkit edit, and mutation-test every new control.
