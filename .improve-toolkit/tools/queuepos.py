#!/usr/bin/env python3
"""queuepos.py -- the fifth field the sweep cannot see: merge-queue membership.

WHY.  r679 lost a PR in plain sight.  #6093 was enqueued at 15:43:28Z, sat 3h11m without ever
receiving a `merge_group` run, and was dropped by `github-merge-queue[bot]` at 18:54:20Z -- the
instant the PR ahead of it merged.  No comment was posted.  Afterwards it still read:

    label=ready-to-merge   CI=GREEN   board=ON-HEAD   isDraft=false   mergeable=MERGEABLE

Every field `sweep.py` reads said healthy.  The PR was stranded, because `tauceti-review-bot`
enqueues on the `ready-to-merge` LABEL TRANSITION, which had already happened -- so nothing was
ever going to put it back.  Only queue membership distinguished it from a PR merely waiting.

AND IT IS USUALLY JUST WAITING.  The queue is one serialised worker at ~25-30 min per merge, 30
deep in r679; merges are strictly FIFO by enqueue time.  A label->merge latency of 2.5-3.5h is
NORMAL.  r676 read that wait as a "jam" on an unrelated PR and was wrong; r679 then read it as
`improve/*` discrimination and was wrong again.  Both theories came from reasoning over run lists
and merge timestamps.  The queue's own state was one API call away.  *Query the queue; do not
model it.*

TWO WAYS TO BE OUT OF THE QUEUE, AND ONLY ONE IS MINE (found by running this tool, r679).  Its
first run flagged #5950 alongside #6093.  But #5950 has **no `merge_queue` timeline events at all**
-- the bot never managed to enqueue it, because it needs a human review on a human-owned file.
#6093 had `added_to_merge_queue` and then `removed_from_merge_queue`.  Same "labelled but absent",
opposite causes, and refreshing the branch is the fix for exactly one of them:

    EJECTED       enqueued, then dropped   -> mine: refresh against main and re-gate
    NEVER-QUEUED  no queue events ever     -> NOT mine: the bot could not enqueue it at all

So the enqueue history, not queue membership alone, is what makes the verdict actionable.
QUEUED at position 18 is not a problem, however long it has been there.
"""
import json, subprocess, sys

REPO = "TauCetiProject/TauCeti"

_Q = """{repository(owner:"%s",name:"%s"){mergeQueue(branch:"%s"){entries(first:100){
  totalCount nodes{position state enqueuedAt pullRequest{number}}}}}}"""


def queue_verdict(label, in_queue, position=None, state=None, ever_enqueued=False):
    """EJECTED / NEVER-QUEUED / QUEUED:… / MERGING:… / NOT-READY.

    Pure so the controls can exercise it on fixture data without touching the network.

    EJECTED is the ONLY verdict this role acts on: the bot enqueues on the label transition, so a
    PR that WAS enqueued and is now out will never be re-enqueued on its own.  The fix is to
    refresh the branch against `main` and re-gate (r679) -- the bot re-reviews, re-labels, and the
    new transition re-enqueues it.

    NEVER-QUEUED is the other shape and is NOT actionable here: the bot never got it into the
    queue, so the branch is not what is wrong.  #5950 is the standing example -- it needs a human
    review on a human-owned file, and refreshing it would achieve nothing.
    """
    if label != "ready-to-merge":
        return "NOT-READY"
    if not in_queue:
        return "EJECTED" if ever_enqueued else "NEVER-QUEUED"
    if state in ("AWAITING_CHECKS", "MERGEABLE"):
        return "MERGING:pos=%s" % position
    return "QUEUED:pos=%s" % position


def fetch(owner_repo=REPO, branch="main"):
    owner, name = owner_repo.split("/")
    out = subprocess.run(
        ["gh", "api", "graphql", "-f", "query=" + _Q % (owner, name, branch)],
        capture_output=True, text=True).stdout
    try:
        q = json.loads(out)["data"]["repository"]["mergeQueue"]
    except Exception:
        return None, {}
    if not q:
        return None, {}
    e = q["entries"]
    return e.get("totalCount"), {n["pullRequest"]["number"]: n for n in e["nodes"]}


def ever_enqueued(n, owner_repo=REPO):
    """Did this PR ever reach the queue?  EJECTED vs NEVER-QUEUED turns on this."""
    out = subprocess.run(
        ["gh", "api", "repos/%s/issues/%d/timeline" % (owner_repo, n), "--paginate",
         "-q", '.[]|select(.event=="added_to_merge_queue")|.created_at'],
        capture_output=True, text=True).stdout
    return bool(out.strip())


def main(argv):
    prs = [int(a.lstrip("#")) for a in argv[1:]]
    if not prs:
        out = subprocess.run(["gh", "pr", "list", "--author", "CBirkbeck", "--state", "open",
                              "--json", "number,headRefName"], capture_output=True, text=True).stdout
        prs = [p["number"] for p in json.loads(out or "[]")
               if p["headRefName"].startswith("improve/")]
    depth, entries = fetch()
    print("merge queue depth: %s" % (depth if depth is not None else "unavailable"))
    ejected = []
    for n in prs:
        out = subprocess.run(["gh", "pr", "view", str(n), "--json", "labels"],
                             capture_output=True, text=True).stdout
        labels = [l["name"] for l in json.loads(out or '{"labels":[]}')["labels"]]
        label = "ready-to-merge" if "ready-to-merge" in labels else ",".join(labels)
        e = entries.get(n)
        v = queue_verdict(label, e is not None,
                          e["position"] if e else None, e["state"] if e else None,
                          ever_enqueued(n) if e is None else True)
        if v == "EJECTED":
            ejected.append(n)
        print("  #%-6s %-22s %s" % (n, label, v))
    if ejected:
        print("\nEJECTED: %s" % ", ".join("#%d" % n for n in ejected))
        print("  The bot enqueues on the label transition, so these will NOT return on their own.")
        print("  Merge origin/main into each, re-gate, push (r679).")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
