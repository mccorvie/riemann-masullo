"""Which claims count as stale."""
import datetime
import unittest

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


if __name__ == "__main__":
    unittest.main()
