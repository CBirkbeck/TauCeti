#!/usr/bin/env bash
# branchscreen.sh <path>...  — which remote refs changed <path> relative to their merge-base
# with origin/main?  Prefilter: drop every ref whose blob for <path> is one that origin/main's
# history has ever held (such a ref is merely behind/at main for this file).  Then three-dot
# diff the survivors.  Prints "CHANGED <tipdate> <ref>" lines.  Run from the rig root.
set -u
cd "$(git rev-parse --show-toplevel)"
git for-each-ref --format='%(refname)' refs/remotes/ > /tmp/bs-refs.$$
for P in "$@"; do
  git log --format=%H origin/main -- "$P" | while read -r c; do git rev-parse "$c:$P" 2>/dev/null; done | sort -u > /tmp/bs-hist.$$
  echo "## $P  (main history blobs: $(wc -l < /tmp/bs-hist.$$); refs: $(wc -l < /tmp/bs-refs.$$))"
  sed "s|^\(.*\)$|\1:$P \1|" /tmp/bs-refs.$$ \
    | git cat-file --batch-check='%(objectname) %(rest)' 2>/dev/null \
    | awk -v hist="/tmp/bs-hist.$$" 'BEGIN{while((getline l < hist)>0) h[l]=1}
           !($1 in h) && $2!="missing" {print $2}' \
    | sort -u > /tmp/bs-cand.$$
  echo "   prefilter survivors: $(wc -l < /tmp/bs-cand.$$)"
  while read -r ref; do
    [ -z "$ref" ] && continue
    ch=$(git diff --name-only "origin/main...$ref" -- "$P" 2>/dev/null | head -1)
    d=$(git log -1 --format=%cI "$ref" 2>/dev/null)
    if [ -n "$ch" ]; then echo "   CHANGED  $d  $ref"; fi
  done < /tmp/bs-cand.$$
done
rm -f /tmp/bs-refs.$$ /tmp/bs-cand.$$ /tmp/bs-hist.$$
echo "BRANCHSCREEN_DONE"
