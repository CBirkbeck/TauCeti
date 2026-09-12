#!/usr/bin/env bash
# snapshot.sh <ref> <destdir>
# Build a prospecting snapshot and REFUSE to hand it over unless it is complete.
# Round 104: a killed `git archive | tar -x` left 3220 of 4250 .lean files for two rounds,
# hiding 9 prime candidates. A printed file count is not a control; this is.
set -uo pipefail
REF="${1:-origin/main}"; DEST="${2:?usage: snapshot.sh <ref> <destdir>}"
rm -rf "$DEST"; mkdir -p "$DEST"
git archive "$REF" | tar -x -C "$DEST"
rc=$?
EXP=$(git ls-tree -r --name-only "$REF" -- TauCeti | grep -c '\.lean$')
GOT=$(find "$DEST/TauCeti" -name '*.lean' 2>/dev/null | wc -l | tr -d ' ')
echo "ref=$REF expected=$EXP got=$GOT (archive rc=$rc)"
if [ "$EXP" != "$GOT" ] || [ "$rc" -ne 0 ]; then
  echo "snapshot.sh: INCOMPLETE — refusing. Do NOT profile this tree." >&2
  exit 1
fi
echo "snapshot.sh: COMPLETE"
