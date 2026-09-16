"""Run with python3 scripts/test_queue_release.py."""

import subprocess
import unittest
from unittest.mock import patch

import queue_release as release


def pr(number, **overrides):
    return dict(number=number, state="open", draft=False, base={"ref": "main"},
                labels=[{"name": "ready-to-merge"}], **overrides)


def state(queued=False, base="main"):
    return {"data": {"repository": {"pullRequest": {
        "isInMergeQueue": queued, "baseRefName": base}}}}


class QueueRelease(unittest.TestCase):
    def test_only_waiting_main_prs_without_holds(self):
        prs = [pr(i) for i in range(1, 11)]
        prs[2]["draft"] = True
        prs[3]["state"] = "closed"
        prs[4]["base"] = {"ref": "stack-parent"}
        prs[5]["labels"] = []
        for item, label in zip(prs[6:], ["hold", "HUMAN", "keep", "wip"]):
            item["labels"].append({"name": label})
        self.assertEqual(release.candidates(prs, released_pr=1), ["2"])
        self.assertEqual(release.candidates([
            dict(pr(20), labels=[{"name": "ready-to-merge"},
                                 {"name": "do-not-close"}])], 1), [])

    @patch.object(release, "gh_json")
    def test_pin_and_candidates_on_later_pages(self, gh):
        gh.side_effect = [state(), [[{"filename": "TauCeti/X.lean"}],
                                    [{"filename": "lake-manifest.json"}]],
                          [[pr(1), pr(2)], [pr(3)]]]
        self.assertEqual(release.select("o/r", 1), ["2", "3"])
        for call in gh.call_args_list[1:]:
            self.assertIn("--paginate", call.args)
            self.assertIn("--slurp", call.args)

    @patch.object(release, "gh_json")
    def test_toolchain_also_releases(self, gh):
        gh.side_effect = [state(), [[{"filename": "lean-toolchain"}]], [[pr(2)]]]
        self.assertEqual(release.select("o/r", 1), ["2"])

    @patch.object(release, "gh_json")
    def test_stale_event_does_not_retry_requeued_bump(self, gh):
        gh.return_value = state(queued=True)
        self.assertEqual(release.select("o/r", 1), [])
        gh.assert_called_once()

    @patch.object(release, "gh_json")
    def test_non_main_release_does_nothing(self, gh):
        gh.return_value = state(base="stack-parent")
        self.assertEqual(release.select("o/r", 1), [])
        gh.assert_called_once()

    @patch.object(release, "gh_json")
    def test_ordinary_removal_does_not_fan_out(self, gh):
        gh.side_effect = [state(), [[{"filename": "TauCeti/X.lean"}]]]
        self.assertEqual(release.select("o/r", 1), [])
        self.assertEqual(gh.call_count, 2)

    @patch.object(release, "gh_json")
    def test_api_failure_does_not_mean_unreserved(self, gh):
        gh.side_effect = subprocess.CalledProcessError(1, ["gh"])
        with self.assertRaises(subprocess.CalledProcessError):
            release.select("o/r", 1)
        gh.side_effect = None
        gh.return_value = dict(state(), errors=[{"message": "partial response"}])
        with self.assertRaises(RuntimeError):
            release.select("o/r", 1)

    @patch.object(release, "gh_json")
    def test_matrix_overflow_is_visible(self, gh):
        gh.side_effect = [state(), [[{"filename": "lean-toolchain"}]],
                          [[pr(i) for i in range(2, 259)]]]
        with self.assertRaisesRegex(RuntimeError, "256-job"):
            release.select("o/r", 1)


if __name__ == "__main__":
    unittest.main()
