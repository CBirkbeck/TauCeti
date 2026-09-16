#!/usr/bin/env python3
"""Select PRs to reconsider when a Lake-pin queue reservation ends.

This only selects candidates. The pinned merge-only workflow rechecks current-head
reviews, CI, paths, and any new reservation before it can enqueue anything.
"""

import json
import os
import subprocess


PIN_PATHS = {"lake-manifest.json", "lean-toolchain"}
HOLD_LABELS = {"keep", "hold", "wip", "human", "do-not-close"}


def gh_json(*args):
    return json.loads(subprocess.check_output(["gh", *args], text=True))


def candidates(prs, released_pr):
    result = []
    for pr in prs:
        labels = {label["name"].lower() for label in pr.get("labels", [])}
        if (pr["number"] != released_pr and pr["state"] == "open"
                and pr["base"]["ref"] == "main" and not pr["draft"]
                and "ready-to-merge" in labels and not labels & HOLD_LABELS):
            result.append(str(pr["number"]))
    return result


def select(repo, released_pr):
    # A delayed release event may arrive after the same bump has been re-enqueued.
    owner, name = repo.split("/")
    response = gh_json("api", "graphql", "-f", "query=" + """
        query($owner: String!, $name: String!, $pr: Int!) {
          repository(owner: $owner, name: $name) {
            pullRequest(number: $pr) { baseRefName isInMergeQueue }
          }
        }
        """, "-f", f"owner={owner}", "-f", f"name={name}", "-F", f"pr={released_pr}")
    if response.get("errors"):
        raise RuntimeError(f"Cannot read reservation state: {response['errors']}")
    current = response["data"]["repository"]["pullRequest"]
    if current["baseRefName"] != "main" or current["isInMergeQueue"]:
        return []
    pages = gh_json("api", "--paginate", "--slurp",
                    f"repos/{repo}/pulls/{released_pr}/files?per_page=100")
    if not any(f["filename"] in PIN_PATHS for page in pages for f in page):
        return []
    pages = gh_json("api", "--paginate", "--slurp",
                    f"repos/{repo}/pulls?state=open&base=main&per_page=100")
    prs = candidates([pr for page in pages for pr in page], released_pr)
    # GitHub limits a matrix to 256 jobs. Fail visibly rather than silently omit PRs.
    if len(prs) > 256:
        raise RuntimeError(f"{len(prs)} candidates exceeds the 256-job matrix limit")
    return prs


def main():
    repo = os.environ["REPO"]
    released_pr = int(os.environ["RELEASED_PR"])
    prs = select(repo, released_pr)
    print(f"Queue release for #{released_pr}: {len(prs)} PR(s) to reconsider")
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write("prs=" + json.dumps(prs) + "\n")


if __name__ == "__main__":
    main()
