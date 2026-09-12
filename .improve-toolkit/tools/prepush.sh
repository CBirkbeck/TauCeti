#!/usr/bin/env bash
# prepush.sh [base-ref] -- run every applicable pre-push screen against HEAD.
#
# WHY THIS EXISTS.  Every blocking finding this session came from a check that EXISTED and was not
# RUN, or was run with the wrong root:
#
#   r491  #5953  three rubrics blocked on two PROSE references to a path a rooting destroyed.
#                `lintcand` had counted those since r457; the namespace-at-a-time lane never
#                picked the check up.  *A check inside one lane's tool is not a check the other
#                lane has.*
#   r493  #5950  the same class again -- `stalequal` was run over `git archive <rev> TauCeti`, so
#                `web/examples/Examples.lean` was outside the scan root entirely.
#   r498  #5959  `Basis` unbound after a move, because `open Module` did not travel with it.
#                Three CI cycles and two wrong diagnoses.
#   r499  #5950  a parallel API left nested beside a rooted one -- invisible to the gate.
#   r503  #5959  an import the move made redundant, in BOTH files.
#
# So: one entry point, run from the worktree, that decides for itself which screens apply.  It
# fails loudly rather than skipping: a check it cannot run is reported as UNRUN, never as a pass.
set -u
T="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(git rev-parse --show-toplevel)"
BASE="${1:-origin/main}"
cd "$ROOT" || exit 2
[ -d TauCeti ] || { echo "prepush: no TauCeti/ here -- run from the worktree root, not a subtree." >&2; exit 2; }

# THE GATE READS `HEAD`, NOT THE WORKING TREE (r664).  Every screen below is driven by
# `git diff "$BASE"...HEAD` or `git archive HEAD`, so uncommitted work is INVISIBLE to all of them:
# the run describes the previous commit and calls it green.  That is exactly how #6432 went red on
# a rename this gate had just passed -- `lint-dot-notation` measured the archived HEAD, which still
# held the OLD names, while the new ones sat unstaged.  The renamed declarations were no longer
# grandfathered by `scripts/lint-dot-notation-baseline.txt`, which keys on declaration name, so CI
# reported `3 new` against a local `0 new`.
# A stale pass is worse than no pass, so refuse rather than report (the same rule as UNRUN).
DIRTY=$(git status --porcelain -- '*.lean' 2>/dev/null | grep -v '^??' || true)
if [ -n "$DIRTY" ]; then
  {
    echo "prepush: UNCOMMITTED .lean changes -- every screen here reads HEAD, so this run would"
    echo "         describe the previous commit, not your work.  Commit (or amend) first."
    echo "$DIRTY" | sed 's/^/         /'
  } >&2
  exit 2
fi

RES="$(mktemp)"; trap 'rm -f "$RES"' EXIT
ok()   { printf '  ok    %s\n' "$1"; echo P >> "$RES"; }
bad()  { printf '  FAIL  %s\n' "$1"; echo F >> "$RES"; }
unrun(){ printf '  UNRUN %s\n' "$1"; echo U >> "$RES"; }
# A ROW WHOSE PREMISE DOES NOT HOLD IS NOT A RESULT (r620).  Five of these checks presuppose a
# ROOTING PR: `parallelns`, `nsslice`, `decldiff`, `rootsurplus` and `slice` all ask a question of
# the form "given that this PR roots declarations, ...".  Run them on a naming or dead-code branch
# and they emit rows that are category errors, not defects -- r616 gated five recovered branches and
# `riemann-roch-mul-pow-membership` came back 12 ok / 1 because `decldiff` objected to a NEW named
# lemma, which is exactly what that branch exists to add.  With the rooting lane nearly exhausted
# (r603), most future work is other lanes, so this would misreport by default.
# `n/a` records NOTHING -- it neither passes nor fails, so the summary counts only real answers.
na()   { printf '  n/a   %s\n' "$1"; }

CHANGED=$(git diff --name-only "$BASE"...HEAD -- '*.lean' 2>/dev/null)
ADDED=$(git diff --name-only --diff-filter=A "$BASE"...HEAD -- '*.lean' 2>/dev/null)
[ -z "$CHANGED" ] && { echo "prepush: no .lean files changed against $BASE -- nothing to screen."; exit 0; }
echo "prepush: $BASE...HEAD  ($(echo "$CHANGED" | wc -l | tr -d ' ') .lean file(s) changed)"

# Is this a ROOTING PR at all?  Conservative: yes if the diff ADDS a `_root_.`-anchored declaration
# or REMOVES a `namespace` line.  Anything else is treated as another lane, and the five
# rooting-specific checks report `n/a` instead of a verdict they have no basis for.
_RA=$(git diff "$BASE"...HEAD -- '*.lean' | grep -cE '^\+[[:space:]]*(@\[[^]]*\][[:space:]]*)?(public |private |protected |noncomputable |nonrec |scoped |partial |unsafe )*(theorem|lemma|def|abbrev|instance|structure|class|inductive)[[:space:]]+_root_\.' || true)
_NR=$(git diff "$BASE"...HEAD -- '*.lean' | grep -cE '^-namespace ' || true)
if [ "${_RA:-0}" -gt 0 ] || [ "${_NR:-0}" -gt 0 ]; then IS_ROOTING=1; else IS_ROOTING=0; fi
[ "$IS_ROOTING" -eq 1 ] || printf '  ----  not a rooting PR (%s rooted declaration(s) added, %s namespace line(s) removed):\n        parallelns, nsslice, decldiff, rootsurplus and slice report n/a\n' "${_RA:-0}" "${_NR:-0}"

# 0. Do `namespace`/`section` and `end` still match? FIRST, because it is the cheapest check here
# and the most catastrophic failure: #6056 shipped twice with a wrapper conversion that renamed the
# `end` of the section INSIDE it, and Lean's five follow-on errors (overlapping instance
# parameters, unused section variables) look like real findings and are not. Reported as a delta:
# green `main` produces 4600 "anonymous section never closed" rows, because `public section` is
# normally never closed at all.
nsb=$(python3 "$T/nsbalance.py" "$(git merge-base "$BASE" HEAD)" $CHANGED 2>/dev/null)
case "$?" in
  0) ok "nsbalance: every \`end\` still matches its \`namespace\`/\`section\`" ;;
  1) bad "nsbalance: this PR leaves a scope closed by the wrong \`end\`"
     echo "$nsb" | sed 's/^/        /' ;;
  *) unrun "nsbalance on $CHANGED" ;;
esac

# 1. Dead `TauCeti.` paths left by a rooting or a move -- PROSE included, whole repository.
# ONE walk for every changed file that roots something (r540).  Per-file walks made this the
# slowest step of the round on a 13-file PR -- ~4,600 files scanned thirteen times.
# EVERY changed file, not just the ones that root something (r564).  With `--base` the question
# is "did a declaration disappear from this file", and a file can lose one without gaining a
# `_root_.` line -- #6093 renamed `HomotopyGroup.map_injective` out of existence that way.  The old
# `_root_.` filter answered a narrower question and would have skipped exactly that case.
EXISTING=""
for f in $CHANGED; do [ -f "$f" ] && EXISTING="$EXISTING $f"; done
if [ -z "$EXISTING" ]; then
  ok "stalequal: no changed .lean file to check"
else
  out=$(python3 "$T/stalequal.py" --base "$(git merge-base "$BASE" HEAD)" . $EXISTING 2>&1)
  case $? in
    0) ok   "stalequal: every name these files stopped declaring is unreferenced" ;;
    1) bad  "stalequal: a dead path survives"; echo "$out" | grep -A2 '^STALE' | sed 's/^/        /' ;;
    *) unrun "stalequal -- $(echo "$out" | head -1)" ;;
  esac
fi

# 2. A move only carries the declarations; `open` commands stay behind (r498).
if [ -n "$ADDED" ]; then
  for f in $ADDED; do
    unrun "movedopens for the NEW file $f -- rerun by hand naming the SOURCE file and line range:
          python3 $T/movedopens.py <mathlib>/Mathlib <source.lean> <first> <last>
          (r498: \`Basis\` was unbound because \`open Module\` did not travel. \`?m.5\` in a build
          error means AUTO-BOUND -- look at \`open\`, not at imports.)"
  done
fi

# 3. One interface split across two namespaces (r499).
# `--mathlib` drops nested namespaces Mathlib declares nothing into -- Tau Ceti's own notions, which
# belong nested (r529).  Tree-wide that is 44 rows down to 31, and the #5950 defect still fires
# because `BialgHomClass` IS a Mathlib namespace.  Without a checkout the tool reports every nested
# namespace, which is noisier but never less safe.
MLIB0="${TAUCETI_MATHLIB:-$HOME/GitHub/TauCeti/.lake/packages/mathlib/Mathlib}"
if [ "$IS_ROOTING" -eq 0 ]; then na "parallelns: n/a -- not a rooting PR"; else
PNBASE="$(git merge-base "$BASE" HEAD)"
if [ -d "$MLIB0" ]; then pn=$(python3 "$T/parallelns.py" . --mathlib "$MLIB0" --base "$PNBASE" 2>/dev/null)
else pn=$(python3 "$T/parallelns.py" . --base "$PNBASE" 2>/dev/null); fi
hit=""
for f in $CHANGED; do echo "$pn" | grep -q "^\[.*\] $f\$" && hit="$hit $f"; done
[ -z "$hit" ] && ok "parallelns: no changed file roots beside a nested sibling" \
              || { bad "parallelns: rooted and nested in one file --$hit"
                   echo "$pn" | grep -A2 "^\[.*\]$hit\$" | sed 's/^/        /'
                   echo "        (a QUESTION, not a defect: the remainder may belong nested. With"
                   echo "         --mathlib, namespaces absent from Mathlib are already dropped, so"
                   echo "         what is left is a real Mathlib namespace -- ANSWER IT IN THE BODY,"
                   echo "         as #6022 does, or root it too.)"; }
fi

# 2b. A wrapper this PR removes may be LOAD-BEARING (r389, learned from a RED BUILD; #5854 shipped
# five such blocks without the test and CI rejected three).  Inside `namespace Foo`, a declaration
# written `_root_.Foo.bar` is reachable from a later sibling as bare `bar`; delete the wrapper and
# that stops resolving.  Triggered by a `namespace` line the diff REMOVES.
# THE REMOVAL IS PER FILE, AND SO IS THE BREAKAGE (r609).  Collecting removed `namespace` lines
# across the WHOLE diff and then scanning every changed file for each of them reports a wrapper as
# gone from files that still have it.  #6148 retires `namespace IsCompactOperator` in `Basic.lean`
# and KEEPS it in `Eigenspace.lean` and `RieszTheory.lean` -- where six unflagged private helpers
# still live inside it -- and the check called both of those broken. Inside a surviving wrapper a
# short reference resolves exactly as before (r389), so there was nothing to fix.
any_removed=0; found=0
for f in $CHANGED; do
  [ -f "$f" ] || continue
  fns=$(git diff "$BASE"...HEAD -- "$f" | grep -E '^-namespace ' | sed 's/^-namespace //' | sort -u)
  # A wrapper the file removes and then re-adds is not removed at all.
  kept=$(git diff "$BASE"...HEAD -- "$f" | grep -E '^\+namespace ' | sed 's/^+namespace //' | sort -u)
  for ns in $fns; do
    case " $kept " in *" $ns "*) continue ;; esac
    grep -qxF "namespace $ns" "$f" && continue          # still present at HEAD: not removed
    any_removed=1
    short="${ns##*.}"
    out=$(python3 "$T/siblingscan.py" "$f" "$short" 2>/dev/null)
    case $? in
      0) : ;;
      1) found=1; bad "siblingscan: removing \`namespace $ns\` breaks a short reference in $f"
         echo "$out" | sed 's/^/        /' ;;
      *) unrun "siblingscan on $f for $ns" ;;
    esac
  done
done
if [ "$any_removed" -eq 0 ]; then ok "siblingscan: this PR removes no \`namespace\` wrapper"
elif [ "$found" -eq 0 ]; then ok "siblingscan: no short sibling reference under any removed wrapper"; fi

# 2c. The DUAL of 2b: a wrapper this PR KEEPS, with a declaration rooted OUT of it (r625, from the
# r609 red build). `siblingscan` and `xsibling` both model a wrapper being REMOVED; #6148 kept
# `namespace IsCompactOperator` for six unflagged private helpers, rooted the flagged ones out to
# `_root_.IsCompactOperator.x`, and a bare `x` inside the surviving wrapper stopped resolving --
# `TauCeti.IsCompactOperator.x`, `TauCeti.x` and root `x` are tried; `IsCompactOperator.x` is not.
# Until this check the only detector was a 13-minute build.
if [ -n "$EXISTING" ]; then
  ri=$(python3 "$T/rootedin.py" $EXISTING 2>/dev/null)
  case "$?" in
    0) ok   "rootedin: no bare reference is stranded by a surviving wrapper" ;;
    1) bad  "rootedin: a bare reference cannot reach a declaration rooted out of its wrapper"
       echo "$ri" | sed 's/^/        /'
       echo "        (r389 applies to \`namespace Foo\` AT ROOT. A wrapper opening \`TauCeti.Foo\`"
       echo "         does not open \`Foo\`, so qualify each reference before pushing.)" ;;
    *) unrun "rootedin -- $(python3 "$T/rootedin.py" $EXISTING 2>&1 >/dev/null | head -1)" ;;
  esac
else
  ok "rootedin: no changed .lean file to check"
fi

# 3b. Imports another import already covers (r503, `placement` on #5959).
# ONLY rows this PR INTRODUCED.  `CentralSimple/TensorProduct.lean` carries three such rows on main
# that predate the branch, and a screen that reports them is proposing work the PR did not cause --
# the same principle as checking width on ADDED lines (r495).  And redundancy is not automatically a
# defect: `importnarrow.py`'s r218/r222 criteria exist because "a file that visibly leans on the
# module can keep the direct import as a statement of intent, and a reviewer is right to say so."
MLIB="${TAUCETI_MATHLIB:-$HOME/GitHub/TauCeti/.lake/packages/mathlib/Mathlib}"
if [ -d "$MLIB" ]; then
  WORK=$(mktemp -d); git archive "$BASE" 2>/dev/null | tar -x -C "$WORK"
  newrows=""
  for f in $CHANGED; do
    [ -f "$f" ] || continue
    head_rows=$(python3 "$T/importcover.py" "$MLIB" TauCeti "$f" 2>/dev/null | grep '^REDUNDANT' | sort)
    base_rows=""
    [ -f "$WORK/$f" ] && base_rows=$(cd "$WORK" && python3 "$T/importcover.py" "$MLIB" TauCeti "$f" 2>/dev/null | grep '^REDUNDANT' | sort)
    d=$(comm -13 <(echo "$base_rows") <(echo "$head_rows") | grep '^REDUNDANT' || true)
    [ -n "$d" ] && newrows="$newrows
      $f
$(echo "$d" | sed 's/^/        /')"
  done
  rm -rf "$WORK"
  [ -z "$newrows" ] && ok "importcover: this PR introduces no covered import" \
                    || { bad "importcover: imports this PR made redundant"; echo "$newrows"; }
else
  unrun "importcover -- no Mathlib checkout at $MLIB (set TAUCETI_MATHLIB)"
fi

# 3c. Does this PR root only PART of a namespace that lives in other files? (r527)
# `slice` and `parallelns` are both FILE-LOCAL and neither can see this. A probe that rooted 9 of
# `IsCoveringMap`'s 67 declarations passed both while leaving 58 in eight other files.
if [ "$IS_ROOTING" -eq 0 ]; then na "nsslice: n/a -- not a rooting PR"; else
nsl=$(python3 "$T/nsslice.py" --base "$(git merge-base "$BASE" HEAD)" TauCeti $CHANGED 2>/dev/null)
if [ -z "$nsl" ]; then ok "nsslice: no namespace left half-rooted in other files"
else bad "nsslice: this PR roots part of a namespace that lives elsewhere"; echo "$nsl" | sed 's/^/        /'; fi
fi

# 3d. Does this PR break a short reference held together by a wrapper it removes? (r550)
# `siblingscan` above is FILE-LOCAL ON BOTH ENDS -- it pairs one file's `_root_.X.` declarations
# with bare uses in THAT file. #6056 passed it, and CI answered with `Unknown identifier
# root_mem_of_pairing_ne_zero`: declared in InvariantSubmodule.lean, used bare in Irreducible.lean.
# This screen pairs every rooted name in the TREE with bare uses in the changed files, and searches
# every component-boundary suffix (`Equiv.indexHom` as well as `indexHom`), which is the second
# half of the same red build.
xs=$(python3 "$T/xsibling.py" TauCeti "$(git merge-base "$BASE" HEAD)" $CHANGED 2>/dev/null)
xsrc=$?
case "$xsrc" in
  0) ok "xsibling: no short reference breaks when these wrappers go" ;;
  1) bad "xsibling: removing a wrapper breaks a short reference in ANOTHER file"
     echo "$xs" | grep '^BREAKS' | sed 's/^/        /' ;;
  *) unrun "xsibling on $CHANGED" ;;
esac
echo "$xs" | grep -E '^(ATTRIBUTE|TACTIC)' | sed 's/^/        note: /'

# 3d-bis. Did this PR change the declaration set in a way no rooting explains? (r565)
# `stalequal` catches a reference left pointing at an old name; this catches the CAUSE, and also a
# rename that nothing happens to reference. Pair every removed `TauCeti.X.y` with the added `X.y`;
# a clean rooting leaves no residue. r563 would have shown one of each.
if [ "$IS_ROOTING" -eq 0 ]; then na "decldiff: n/a -- not a rooting PR"; else
dd=$(python3 "$T/decldiff.py" "$(git merge-base "$BASE" HEAD)" $CHANGED 2>/dev/null)
case "$?" in
  0) ok "decldiff: every declaration change is a rooting" ;;
  1) bad "decldiff: the declaration set changed by more than a rooting"
     echo "$dd" | sed 's/^/        /' ;;
  *) unrun "decldiff on $CHANGED" ;;
esac
fi

# 3e. Does this PR write a qualified name that does not exist? (r552)
# Two shapes `xsibling` is blind to by construction, because it hunts BARE references and its
# search refuses a name preceded by a dot: a name over-qualified with the WRAPPER's name
# (`WeierstrassCurve.conj` for `WeierstrassCurve.Affine.CoordinateRing.conj`), and an `open` of the
# namespace the PR has just emptied. The second half walks the WHOLE TREE: six of #6065's nine such
# files were not in its diff at all.
ML=""
for c in "$(dirname "$(cd "$(git rev-parse --git-common-dir)" && pwd)")/.lake/packages/mathlib/Mathlib" \
         "$(git rev-parse --show-toplevel)/.lake/packages/mathlib/Mathlib"; do
  [ -d "$c" ] && { ML="$c"; break; }
done
if [ -z "$ML" ]; then unrun "deadpath (no Mathlib checkout found)"; else
  dp=$(python3 "$T/deadpath.py" --base "$(git merge-base "$BASE" HEAD)" TauCeti "$ML" $CHANGED 2>/dev/null)
  case "$?" in
    0) ok "deadpath: every qualified name this PR writes resolves" ;;
    1) bad "deadpath: this PR writes a name that does not exist"
       echo "$dp" | sed 's/^/        /' ;;
    *) unrun "deadpath on $CHANGED" ;;
  esac
fi

# 3e2. Does main still SHORT-spell a name this PR removed? (r679, from #6093's red build)
# `stalequal` matches the FULL dead path and prefilters on `TauCeti`, so a reference spelled `A.b`
# -- which the r389 rule resolves from inside `namespace TauCeti.*` -- never reaches its regex.
# `deadpath` resolves properly but only inside the files THIS PR changed. #6093's caller was in
# `FiberFunctor.lean`, untouched by the PR and newly arrived on main, and because `IsCoveringMap`
# is itself a TERM the dead reference became generalized field notation rather than an error.
if [ -z "$ML" ]; then unrun "ghostref (no Mathlib checkout found)"; else
  gr=$(python3 "$T/ghostref.py" --base "$(git merge-base "$BASE" HEAD)" . "$ML" $CHANGED 2>/dev/null)
  case "$?" in
    0) ok "ghostref: nothing still short-spells a name this PR removed" ;;
    1) bad "ghostref: a file this PR does not touch still names a removed declaration"
       echo "$gr" | sed 's/^/        /'
       echo "        (r679: it may not say 'unknown identifier' -- if the namespace is also a term"
       echo "         the reference re-reads as field notation and fails elsewhere. Update the"
       echo "         call site; that is part of the rename, not a scope expansion.)" ;;
    *) unrun "ghostref on $CHANGED" ;;
  esac
fi

# 3e3. Did the rooting make a `to_additive` target redundant? (r687, from #6482's red build)
# Nested, the attribute needed the explicit name; at root `to_additive` derives it, and naming a
# target it can autogenerate is an ERROR. A rooting can break an attribute it never touched.
ta=$(python3 "$T/toaddname.py" --base "$(git merge-base "$BASE" HEAD)" $CHANGED 2>/dev/null)
case "$?" in
  0) ok "toaddname: no rooted declaration names a \`to_additive\` target" ;;
  1) bad "toaddname: a rooted declaration still names a \`to_additive\` target"
     echo "$ta" | sed 's/^/        /' ;;
  *) unrun "toaddname on $CHANGED" ;;
esac

# 3f. Did a fixer move a REFERENCE to an unrelated namespace? (r622, from #6188)
# `xqualify`/`deadfix` pick a candidate by matching the TAIL of a name (r556). On #6188 that turned
# `Submodule.rationalizationEquiv` into `LieSubalgebra.rationalizationEquiv` and
# `LinearEquiv.restrictScalars_apply` into `AlgHom.restrictScalars_apply` -- a branch that passed six
# gate runs over 29 rounds and failed its FIRST build. `deadpath` cannot catch it: those names exist
# elsewhere in the index, and existence is not resolution. NOT gated on IS_ROOTING -- any lane that
# rewrites references can suffer it.
if [ -n "$EXISTING" ]; then
  nj=$(python3 "$T/nsjump.py" "$(git merge-base "$BASE" HEAD)" $EXISTING 2>/dev/null)
  case "$?" in
    0) ok   "nsjump: no reference changed namespace family" ;;
    1) bad  "nsjump: a reference moved to an unrelated namespace"
       echo "$nj" | sed 's/^/        /'
       echo "        (r556: a fixer matching on the tail alone. Check each against \`main\` before"
       echo "         pushing -- this is what #6188 shipped to CI.)" ;;
    *) unrun "nsjump -- $(python3 "$T/nsjump.py" "$(git merge-base "$BASE" HEAD)" $EXISTING 2>&1 >/dev/null | head -1)" ;;
  esac
else
  ok "nsjump: no changed .lean file to check"
fi

# 4. Width, on the ADDED LINES ONLY (r495: a whole-file check flags pre-existing 155-char URLs).
long=$(git diff "$BASE"...HEAD -- '*.lean' | grep '^+' | grep -v '^+++' | python3 -c '
import sys
n=0
for l in sys.stdin:
    s=l.rstrip("\n")[1:]
    if len(s) > 100:
        n+=1; print(f"        {len(s)}: {s[:80]}")
print(f"__COUNT__{n}")')
if echo "$long" | grep -q '^__COUNT__0$'; then ok "width: every added line <= 100 characters"
else bad "width: added lines over 100 characters"; echo "$long" | grep -v '^__COUNT__'; fi

# 5. The gate's own count, base vs head. `0 new` is the bar; a drop is the point.
# Compare against the MERGE BASE, not the tip of `$BASE` (r518).  A branch that is behind main
# reports a base snapshot NEWER than its own work, and the delta comes out backwards: the parked
# `LinearIndependent` branch showed `base 983 -> head 984` and looked like it ADDED a violation,
# when it removes one.  The `0 new` verdict was right throughout; only the numbers misled — which
# is why they are printed. `git diff "$BASE"...HEAD` already uses the merge base; this makes the
# lint snapshots agree with it.
MB=$(git merge-base "$BASE" HEAD)
SNAPB=$(mktemp -d); SNAPH=$(mktemp -d)
git archive "$MB" TauCeti 2>/dev/null | tar -x -C "$SNAPB" && git archive HEAD TauCeti | tar -x -C "$SNAPH"
EMPTY=$(mktemp); : > "$EMPTY"
BASEROWS=$(python3 scripts/lint-dot-notation.py --source-root "$SNAPB/TauCeti" --baseline "$EMPTY" 2>&1 | grep -E '\.lean:[0-9]+: TauCeti\.' || true)
HEADROWS=$(python3 scripts/lint-dot-notation.py --source-root "$SNAPH/TauCeti" --baseline "$EMPTY" 2>&1 | grep -E '\.lean:[0-9]+: TauCeti\.' || true)
b=$(python3 scripts/lint-dot-notation.py --source-root "$SNAPB/TauCeti" 2>&1 | head -1)
h=$(python3 scripts/lint-dot-notation.py --source-root "$SNAPH/TauCeti" 2>&1 | head -1)
echo "        base: $b"
echo "        head: $h"
case "$h" in *", 0 new,"*) ok "lint-dot-notation: 0 new" ;; *) bad "lint-dot-notation: NEW violations" ;; esac

# 5a2. Does this PR root MORE than the linter asked for? (r605, from #6148)
# `rootns` moves a whole `namespace` block, so a PR roots every member of the wrapper rather than
# the subset the linter flagged. #6148 rooted 17 where 11 were flagged; `api-design` blocked the
# six-declaration surplus -- all private, all general, none flagged -- and NONE of the other twelve
# checks asks this. `slice` asks whether a file's flagged set was rooted in full, `decldiff` whether
# each change is a rooting, `nsslice` whether a namespace is left half-rooted: all three pass when a
# PR roots too much. A surplus may be legitimate (a private helper cannot stay behind when its
# wrapper is retired) but it is a claim made on the PR's own authority, so it must be deliberate.
if [ "$IS_ROOTING" -eq 0 ]; then na "rootsurplus: n/a -- not a rooting PR"; else
FLAGGED=$(mktemp); printf '%s\n' "$BASEROWS" > "$FLAGGED"
if [ -n "$EXISTING" ]; then
  rs=$(python3 "$T/rootsurplus.py" --base "$MB" "$FLAGGED" $EXISTING 2>/dev/null)
  case "$?" in
    0) ok   "rootsurplus: every rooted declaration was flagged" ;;
    1) bad  "rootsurplus: this PR roots declarations the linter never flagged"
       echo "$rs" | sed 's/^/        /'
       echo "        (answer it in the body or drop them: rooting an unflagged declaration asserts a"
       echo "         receiver on your own authority, which is what \`generality\` blocked #6093 on.)" ;;
    *) unrun "rootsurplus -- $(python3 "$T/rootsurplus.py" --base "$MB" "$FLAGGED" $EXISTING 2>&1 >/dev/null | head -1)" ;;
  esac
else
  ok "rootsurplus: no changed .lean file to check"
fi
rm -f "$FLAGGED"
fi
rm -rf "$SNAPB" "$SNAPH" "$EMPTY"

# 5b. Did this PR root SOME of a file's flagged declarations but not all? (r512)
# r490 gives the ratio within a namespace; this is its file-level twin, and it is the one that
# rejected an already-written `RootPairing.Equiv` PR -- 2 flagged rooted, 30 left in the same file.
# Rooting a slice is the arbitrary boundary that cost #5905 three blocks. A file may legitimately
# keep flagged declarations (a namespace that is not root in Mathlib -- check with mathlibns.py),
# so the row names the numbers and asks for that justification in the PR body.
if [ "$IS_ROOTING" -eq 0 ]; then na "slice: n/a -- not a rooting PR"; else
: > "$RES.slice"
for f in $CHANGED; do
  [ -f "$f" ] || continue
  nb=$(echo "$BASEROWS" | grep -c "/$f:" || true)
  nh=$(echo "$HEADROWS" | grep -c "/$f:" || true)
  [ "$nb" -eq 0 ] && continue
  [ "$nh" -eq 0 ] && continue
  [ "$nb" -eq "$nh" ] && continue
  echo "        $f: rooted $((nb - nh)) of $nb flagged, $nh left" >> "$RES.slice"
done
if [ -s "$RES.slice" ]; then
  bad "slice: this PR roots some of a file's flagged declarations, not all"
  cat "$RES.slice"
  echo "        (r512: 2 of 32 in one file was the #5905 boundary. If the remainder belongs where"
  echo "         it is, say so in the body — check the namespace with tools/mathlibns.py.)"
else
  ok "slice: no changed file is left partly rooted"
fi
rm -f "$RES.slice"
fi

p=$(grep -c P "$RES" || true); f=$(grep -c F "$RES" || true); u=$(grep -c U "$RES" || true)
printf '\n  %d ok, %d failed, %d UNRUN\n' "$p" "$f" "$u"
printf '  PR body still needs a standalone `Roadmap: none` line and the session trailer.\n'
[ "$f" -eq 0 ]
