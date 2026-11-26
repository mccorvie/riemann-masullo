"""Which claims count as stale."""
import datetime
import io
import subprocess
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

import stale_claims
from stale_claims import is_stale, last_claim, referenced


class StaleClaimsTest(unittest.TestCase):
    def test_last_claim_reads_first_lines_only(self):
        comments = [
            {"body": "Claiming", "created_at": "2026-11-21T01:00:00Z"},
            {"body": "A note.\nClaiming this later", "created_at": "2026-11-21T05:00:00Z"},
            {"body": "Claimed by a prover agent (codex)", "created_at": "2026-11-21T03:00:00Z"},
            {"body": "claims are fun", "created_at": "2026-11-21T06:00:00Z"},
        ]
        self.assertEqual(last_claim(comments), "2026-11-21T03:00:00Z")
        self.assertIsNone(last_claim([{"body": "Released.", "created_at": "2026-11-21T01:00:00Z"}]))

    def test_age(self):
        now = datetime.datetime(2026, 11, 21, 12, 0, tzinfo=datetime.timezone.utc)
        self.assertTrue(is_stale("2026-11-21T03:59:00Z", now))
        self.assertFalse(is_stale("2026-11-21T04:01:00Z", now))

    def test_open_pull_requests_keep_a_claim_alive(self):
        pulls = [
            {"title": "Prove x", "body": "Closes #12\n\nfixes: #13", "ref": "my-branch"},
            {"title": "Prove y", "body": "see #99", "ref": "prover/14"},
        ]
        self.assertEqual(referenced(pulls), {12, 13, 14})


class ReleaseStaleClaimsTest(unittest.TestCase):
    def setUp(self):
        self.issue = {"number": 42, "assignees": ["holder"]}
        responses = [[], [self.issue],
                     [{"body": "Claiming", "created_at": "2000-01-01T00:00:00Z"}]]
        api = patch.object(stale_claims, "api", side_effect=responses)
        api.start()
        self.addCleanup(api.stop)
        self.failed_command = None
        run = patch.object(stale_claims.subprocess, "run", side_effect=self.run_command)
        self.run = run.start()
        self.addCleanup(run.stop)
        self.output = io.StringIO()

    def run_command(self, cmd, **kwargs):
        result = subprocess.CompletedProcess(
            cmd, int(cmd[2] == self.failed_command), stderr="GitHub write failed")
        if kwargs.get("check"):
            result.check_returncode()
        return result

    def invoke(self, argv):
        with redirect_stdout(self.output):
            stale_claims.main(argv)

    def test_release_updates_issue_before_announcing(self):
        self.invoke(["--apply"])
        commands = [call.args[0] for call in self.run.call_args_list]
        self.assertEqual(commands[0], ["gh", "issue", "edit", "42", "--remove-label", "claimed",
                                       "--remove-assignee", "holder"])
        self.assertEqual(commands[1][:4], ["gh", "issue", "comment", "42"])
        self.assertEqual(len(commands), 2)
        self.assertIn("1 stale claim(s) of 1 claimed issues", self.output.getvalue())

    def test_failed_edit_does_not_announce_release(self):
        self.failed_command = "edit"
        with self.assertRaises(subprocess.CalledProcessError):
            self.invoke(["--apply"])
        self.assertEqual([call.args[0][2] for call in self.run.call_args_list], ["edit"])
        self.assertNotIn("stale claim(s)", self.output.getvalue())

    def test_failed_notice_fails_the_job(self):
        self.failed_command = "comment"
        with self.assertRaises(subprocess.CalledProcessError):
            self.invoke(["--apply"])
        self.assertEqual([call.args[0][2] for call in self.run.call_args_list], ["edit", "comment"])
        self.assertNotIn("stale claim(s)", self.output.getvalue())

    def test_release_without_assignees(self):
        self.issue["assignees"] = []
        self.invoke(["--apply"])
        self.assertEqual(self.run.call_args_list[0].args[0],
                         ["gh", "issue", "edit", "42", "--remove-label", "claimed"])

    def test_dry_run_does_not_write(self):
        self.invoke([])
        self.run.assert_not_called()
        self.assertIn("1 stale claim(s) of 1 claimed issues; dry run", self.output.getvalue())


if __name__ == "__main__":
    unittest.main()
