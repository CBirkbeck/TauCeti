# Last round — r669 (2026-09-12 17:35Z)

## A 🟡 behind a ⛔ is a prediction about a PR that will not exist

r668 declined to act on #6188's `reuse` "delete the private bridge", because it sat behind a ⛔.
It did not survive: `scope` cleared to ♻️, `reuse` went ♻️ with it, and **`proof-quality` approved
the bridge outright**. Acting would have deleted a declaration the next board accepted and reopened a
loop that has already run private → public → inline → private.

## #6432 is 10/10 `ready-to-merge`

The three fixes ported from #6188 in r668 cleared `reuse`, `documentation` and `proof-quality`
together. `api-design` approved **without** asking for the functorial lemmas — that item was never
owed there.

## #6188: two findings answered by quoting the block that created them

`api-design` wants `autCongr_refl`/`_symm`/`_trans`; `generality` wants the semilinear statement.
Both answered on their threads, citing #6188's own `scope` ⛔ — *"Keep this PR to rooting and renaming
… move both structural lemmas and the corresponding call-site rewrites to a follow-up PR."* Three new
bundled equalities are the same category the block refused; the semilinear statement is #6432's
topic, now 10/10 and carrying both. **Each reply says plainly what I will do if the reviewer wants it
here anyway**, since either reverses the block.

`documentation` fixed (`cc5b861ca`): the private bridge's docstring stated coercion mechanics; it now
states the equality, rest as a source comment. #6432 has the same docstring but is 10/10 with
`documentation` ✅ — **not touched: a green PR is not a place to apply a lesson.**

## Prospect lane re-measured — one verified target, not yet opened

Main is at **739 flagged** (was 759). `nscand.py`: 52 flagged namespaces, **12 WHOLE**. Ten are
accounted for — `BialgHom` = #5950, `LinearEquiv` = #6188/#6432, six ABSENT traps, `FDRep` 1/1 is the
`private intCharacter_def` #6418 left, `Basis` is Mathlib's `Module.Basis`.

**The twelfth is new and verified: `TauCeti.Submonoid` 1/1.**

* `mathlibns.py`: `ROOT 517 Submonoid` — real root namespace, not a grep (r511).
* Mathlib has **no** `Submonoid.continuousConstSMul` / `AddSubmonoid.continuousConstVAdd` — not the
  #6418 duplicate trap.
* Mathlib's own `Topology/Algebra/ConstMulAction.lean` has the identical sibling pattern
  (`Units.`, `Prod.`, `MulOpposite.continuousConstSMul`), so the rooted name matches convention.

Target: `TauCeti/Topology/Algebra/ConstMulAction.lean:37`, an `instance` with
`@[to_additive AddSubmonoid.continuousConstVAdd]`, referenced once by
`TauCeti.Subgroup.continuousConstSMul` in the same file. Rooting it enables no dot notation (it is an
instance) — the value is emptying the namespace and matching Mathlib's placement. It is flagged, so
`rootsurplus` will not fire. Removing the wrapper leaves `namespace Submonoid` empty: delete it.

**Not opened — four PRs are open and step 5 needs fewer than three.** Note the arithmetic: #6093 and
#6432 merging leaves #5950 + #6188 = two, and step 5 then triggers.

## Board (17:35Z) — four open

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `ready-to-merge` | nobody — **10/10** |
| **#6188** | `cc5b861ca` | building | `awaiting-author` | reviewer — 1 fixed, 2 contested, board BEHIND |
| **#6432** | `98bb7e78f` | green | `ready-to-merge` | nobody — **10/10** |

## Next

1. **Watch #6188 on `cc5b861ca`** (docstring only, low risk) and its next board — the two contests
   are the live question.
2. If `generality` or `api-design` re-fires on #6188 **with the reviewer explicitly asking for it
   there despite the block**, implement it: both replies committed to that. Otherwise hold.
3. **When step 5 triggers, `TauCeti.Submonoid` is scouted and verified** — see above. Branch
   `improve/submonoid-constsmul-root` from a freshly fetched `origin/main`, root the instance, drop
   the empty wrapper, update the one reference, gate, open as a DRAFT, mark ready when CI is green.
4. Re-run `nscand.py` after each merge: main moved 759 → 739 during this watch and the WHOLE list
   changes with it.

## Settled — with the conditions attached

* **#6093** — **10/10.** `@[expose]` on `fundamentalGroupEquivFiber` removed, **and that is why**
  `_apply_coe` is not `@[simp]`.
* **#6418** — **MERGED.**
* **#6188** — the relocation alone. Transport is the **`private` extensional bridge**, now
  `proof-quality` ✅. No structural lemmas, no functorial lemmas, not semilinear — all of that is
  #6432's, per the `scope` ⛔.
* **#6432** — **10/10**: semilinear, rooted, renamed, owns the structural lemmas and call-site
  rewrites.

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
A rubric that went green can go 🟡 again; clearing a ⛔ reveals rubrics that never ran; and
**a 🟡 behind a ⛔ may not survive the next board — do not chase it**.
**Deleting a declaration means deleting what advertises it.**
**A green PR is not a place to apply a lesson** — port fixes to PRs that asked for them.
Verify a rooting target against Mathlib with `mathlibns.py`, never a grep, and check the name is not
already there.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**133 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
