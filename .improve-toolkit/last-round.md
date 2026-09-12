# Last round — r671 (2026-09-12 18:05Z)

## A scouted target is not a verified one

Step 5 still does not trigger (four open), so `TauCeti.Submonoid` was built and gated but **not
opened**. The gate's first answer was 12 ok / 3 failed, and one was real:

```
FAIL  stalequal: a dead path survives
      STALE  TauCeti.Submonoid.continuousConstSMul
             TauCeti/Topology/Algebra/ConstMulAction.lean:21
```

The module docstring still named the path the rooting destroyed — **r491's exact defect class**.
r670's scouting checked the namespace was real and the name free; it could not have found this,
because that needs the change made and the gate run.

Fixed: **13 ok / 2 failed**, both remaining being the documented *questions* (`parallelns`
rooted-beside-nested; `slice` 1 of 2 flagged — the other is `TauCeti.Subgroup.continuousConstSMul`,
a different namespace at 39/62). `lint-dot-notation` 739 → 738, 0 new; `decldiff` and `rootsurplus`
clean, which is what a pure rooting should look like.

**Branch `improve/submonoid-constsmul-root` is pushed and gate-clean. No PR opened**; open count
still 4. When step 5 triggers it is `gh pr create --draft` and a body answering the two questions.

## #6188: both r669 contests rejected, and the knot is explicit

Seven green — `reuse` ✅ (the private bridge, settled), `scope` ✅ **on the split diff**,
`documentation` ✅ (r669's fix), plus `proof-quality`, `naming`, `placement`, `attribution`.

Two 🟡, and they want back exactly what `scope` ⛔'d out one round ago:

* `api-design` — add `autCongr_apply` / `autCongr_symm_apply`.
* `generality` — state the conjugation API semilinearly. (Its subject *moved*:
  `extendOfIsLattice` is now approved at fraction-ring generality.)

**No head satisfies all three at once.** Put the content back and it is the diff `scope` blocked;
leave it out and `api-design`/`generality` block. Each rubric judges the current head, and the
reviewer has three times refused "another PR does it".

## Next — the structural move, deliberately deferred one round

The resolution is not another contest. **#6188 should stop touching `Congr.lean` entirely** and stand
as the `Algebra/Module/Lattice.lean` rooting; then `api-design` and `generality` have no subject in
it, `scope` stays single-topic, and **#6432 — 10/10, semilinear, owning the structural lemmas —**
owns the conjugation API outright. That was option 2 of the question r667 put on the `generality`
thread; the findings have since picked it by elimination.

**Cheapest route to the same place: let #6432 merge first, then rebase #6188** — its `Congr.lean`
hunks become no-ops because the same rooting, rename and lemmas are already on main. #6432 is
`ready-to-merge` at 10/10, so this may need no edit at all.

So, in order:
1. **Check whether #6432 merged.** If yes: rebase #6188 onto fresh `origin/main`, confirm its
   `Congr.lean` changes have evaporated, re-gate, push. That is the whole fix.
2. **If #6432 is still unmerged and #6188's board re-fires the same two**, do it by hand: drop the
   `Congr.lean` hunks from #6188, retitle/rebody it as the `Lattice.lean` rooting, and say on both
   threads that the conjugation API is #6432's — citing `scope`'s block and #6432's 10/10.
3. **When step 5 triggers** (two more merges): open `improve/submonoid-constsmul-root` as a **DRAFT**
   — already pushed and gate-clean. Body must answer `parallelns` (the `Subgroup` instance stays
   nested; it is a different namespace, 39/62 partial) and `slice` (1 of 2 flagged, same reason).
   Mark ready when CI is green.
4. **Re-run `nscand.py` after each merge** — main moved 759 → 738 across this watch.

## Board (18:05Z) — four open, all green

| PR | head | CI | label | whose move |
|---|---|---|---|---|
| **#5950** | `a64ba63667` | green | `ready-to-merge` | **Chris** — human-owned `web/examples/Examples.lean` |
| **#6093** | `370dad05e` | green | `ready-to-merge` | nobody — **10/10** |
| **#6188** | `cc5b861ca` | green | `awaiting-author` | **me — 7/10, see Next** |
| **#6432** | `98bb7e78f` | green | `ready-to-merge` | nobody — **10/10** |

## Settled — with the conditions attached

* **#6093** — **10/10.** `@[expose]` on `fundamentalGroupEquivFiber` removed, **and that is why**
  `_apply_coe` is not `@[simp]`.
* **#6418** — **MERGED.**
* **#6188** — transport is the **`private` extensional bridge**, `reuse` ✅ and `proof-quality` ✅;
  do not touch it again. `scope` ✅ **only while `Congr.lean`'s API expansion stays out.**
* **#6432** — **10/10**: semilinear, rooted, renamed, owns the structural lemmas and call-site
  rewrites. **Do not edit it** — it is green and waiting on the bot.
* **`improve/submonoid-constsmul-root`** — pushed, gate-clean at 13 ok / 2 questions, **no PR**.

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
**Deleting a declaration means deleting what advertises it** — and a rooting destroys the old path
everywhere, docstrings included (`stalequal` is the check that catches it).
**A green PR is not a place to apply a lesson.**
Verify a rooting target with `mathlibns.py`, never a grep; then **gate it**, because scouting cannot
see a stale docstring.
The gate is pure Python: it cannot see docstring attachment, elaboration, or simp normal form.
**133 controls, 0 failed** — the round prompt still says 129; the prompt is stale, not the suite.
**HANDOVER.md §11 carries this watch's rules** — read it before re-deriving one.
