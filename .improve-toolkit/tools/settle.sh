#!/usr/bin/env bash
# settle.sh [base] -- run the three rooting screens and their fixers to a FIXED POINT.
#
# WHY THIS EXISTS.  Rounds 550, 551 and 552 each opened with a red build, and all three defects came
# out of the same hand-rolled extraction pass:
#
#   r550  a reference the removed wrapper had been resolving      -> xsibling  / xqualify
#   r551  the `end` of the section INSIDE the converted wrapper   -> nsbalance / endfix
#   r552  a name qualified with the WRAPPER's name, and an `open`
#         of the namespace the PR had just emptied                -> deadpath  / deadfix
#
# Each was found a round after the last, and each was then found AGAIN sitting in branches already
# parked -- 40+ breaks across four branches, every one a red build waiting to happen.  The screens
# and the fixers already existed by the end of r552; what did not exist was the discipline of
# running all of them, in a loop, until none of them has anything left to say.
#
# ITERATION IS THE POINT, not a convenience.  The three fixes interact: qualifying a reference can
# expose a dead path, and repairing an `end` changes which namespace a declaration sits in, which
# changes what counts as a bare reference.  A single pass of each is not enough, which is the same
# lesson the width pass taught in r549 (101 wraps, then 5 more).
#
# WIDTH IS DELIBERATELY NOT FIXED HERE.  Qualifying lengthens lines and wrapping Lean needs a
# judgement about where the break goes; it is reported and left to a person.
set -u
T="$(cd "$(dirname "$0")" && pwd)"
BASE="${1:-origin/main}"
MB="$(git merge-base "$BASE" HEAD)"
ML=""
for c in "$(dirname "$(cd "$(git rev-parse --git-common-dir)" && pwd)")/.lake/packages/mathlib/Mathlib" \
         "$(git rev-parse --show-toplevel)/.lake/packages/mathlib/Mathlib"; do
  [ -d "$c" ] && { ML="$c"; break; }
done
[ -n "$ML" ] || { echo "settle: no Mathlib checkout found -- refusing to run deadpath blind" >&2; exit 2; }

files() { git diff --name-only "$MB" -- 'TauCeti/*.lean'; }

for round in 1 2 3 4 5; do
  changed=0
  mapfile -t FL < <(files)
  [ "${#FL[@]}" -gt 0 ] || { echo "settle: no changed .lean files"; exit 0; }

  out=$(python3 "$T/nsbalance.py" "$MB" "${FL[@]}" 2>/dev/null); rc=$?
  [ "$rc" -gt 1 ] && { echo "settle: nsbalance UNRUN"; exit 2; }
  [ "$rc" -eq 1 ] && { echo "$out" | python3 "$T/endfix.py" || exit 2; changed=1; }

  mapfile -t FL < <(files)
  out=$(python3 "$T/xsibling.py" TauCeti "$MB" "${FL[@]}" 2>/dev/null); rc=$?
  [ "$rc" -gt 1 ] && { echo "settle: xsibling UNRUN"; exit 2; }
  [ "$rc" -eq 1 ] && { echo "$out" | python3 "$T/xqualify.py" || exit 2; changed=1; }

  mapfile -t FL < <(files)
  out=$(python3 "$T/deadpath.py" TauCeti "$ML" "${FL[@]}" 2>/dev/null); rc=$?
  [ "$rc" -gt 1 ] && { echo "settle: deadpath UNRUN"; exit 2; }
  [ "$rc" -eq 1 ] && { echo "$out" | python3 "$T/deadfix.py" || exit 2; changed=1; }

  if [ "$changed" -eq 0 ]; then
    echo "settle: fixed point after $((round - 1)) round(s) of edits -- nsbalance, xsibling and deadpath all clean"
    python3 - "$MB" <<'PY'
import subprocess, sys
mb = sys.argv[1]
fs = subprocess.run(['git','diff','--name-only',mb,'--','TauCeti/*.lean'],
                    capture_output=True, text=True).stdout.split()
n = 0
for f in fs:
    try: base = set(subprocess.run(['git','show',f'{mb}:{f}'], capture_output=True, text=True,
                                   check=True).stdout.split('\n'))
    except subprocess.CalledProcessError: base = set()
    for i, L in enumerate(open(f, encoding='utf-8').read().split('\n'), 1):
        if len(L) > 100 and L not in base:
            n += 1; print(f"  WIDE {f}:{i} ({len(L)}) -- wrap by hand, then re-run")
print(f"settle: {len(fs)} changed file(s), {n} over-width added line(s) left for a person")
PY
    exit 0
  fi
  echo "settle: round $round made edits; re-screening"
done
echo "settle: still changing after 5 rounds -- something is oscillating, look by hand" >&2
exit 1
