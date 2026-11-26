#!/usr/bin/env python3
"""Tests for history-ranked base_state.py and staggered Main state slots."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import base_state

ROOT = Path(__file__).resolve().parent.parent.parent
REPO_ID = 7


def make_artifact(sha, ident=55, **overrides):
    run = dict(
        repository_id=REPO_ID,
        head_repository_id=REPO_ID,
        head_branch="main",
        head_sha=sha,
    )
    run.update(overrides.pop("workflow_run", {}))
    art = dict(
        id=ident,
        name="main-state",
        expired=False,
        size_in_bytes=1000,
        created_at="2026-01-01T00:00:00Z",
        workflow_run=run,
    )
    art.update(overrides)
    return art


class BaseStateTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.dir = Path(temp.name)
        self.env = dict(
            os.environ,
            GIT_AUTHOR_NAME="t",
            GIT_AUTHOR_EMAIL="t@invalid",
            GIT_COMMITTER_NAME="t",
            GIT_COMMITTER_EMAIL="t@invalid",
            GIT_CONFIG_GLOBAL="/dev/null",
            GIT_CONFIG_NOSYSTEM="1",
        )
        self.git("init", "-q", "-b", "main")
        self.c1 = self.commit("a\n")
        self.c2 = self.commit("b\n")
        self.c3 = self.commit("c\n")

    def git(self, *args):
        return subprocess.run(
            ["git", *args], cwd=self.dir, env=self.env, check=True,
            capture_output=True, text=True,
        ).stdout.strip()

    def commit(self, text):
        (self.dir / "f.txt").write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "c")
        return self.git("rev-parse", "HEAD")

    def test_usable_rejects_untrusted_or_expired_artifacts(self):
        self.assertEqual(base_state.usable(make_artifact(self.c1), REPO_ID), self.c1)
        self.assertIsNone(base_state.usable(make_artifact(self.c1, expired=True), REPO_ID))
        self.assertIsNone(base_state.usable(make_artifact(self.c1, name="other"), REPO_ID))
        self.assertIsNone(base_state.usable(make_artifact(self.c1, size_in_bytes=base_state.MAX_BYTES + 1), REPO_ID))
        self.assertIsNone(base_state.usable(make_artifact(self.c1, workflow_run={"head_branch": "pr"}), REPO_ID))
        self.assertIsNone(base_state.usable(make_artifact(self.c1, workflow_run={"head_repository_id": 99}), REPO_ID))
        self.assertIsNone(base_state.usable(make_artifact("not-a-sha"), REPO_ID))

    def test_newest_picks_newest_by_history_not_upload_order(self):
        # Older commit c1 uploaded after newer commit c2: history must still prefer c2.
        a_c1_late = make_artifact(self.c1, ident=102, created_at="2026-01-01T02:00:00Z")
        a_c2 = make_artifact(self.c2, ident=101, created_at="2026-01-01T01:00:00Z")
        saved = [(a_c1_late, self.c1), (a_c2, self.c2)]
        self.assertEqual(base_state.newest(self.dir, saved, self.c3), (a_c2, self.c2))

        # Among multiple uploads for the same newest commit, newest upload (first in `saved`) wins.
        a_c2_newer = make_artifact(self.c2, ident=103, created_at="2026-01-01T03:00:00Z")
        saved2 = [(a_c2_newer, self.c2), (a_c1_late, self.c1), (a_c2, self.c2)]
        self.assertEqual(base_state.newest(self.dir, saved2, self.c3), (a_c2_newer, self.c2))

    def test_has_exact_flag(self):
        artifacts = [make_artifact(self.c2, ident=77)]

        def fake_run(cmd, *args, **kwargs):
            self.assertEqual(cmd[:2], ["gh", "api"])
            return subprocess.CompletedProcess(cmd, 0, stdout=json.dumps({"artifacts": artifacts}).encode())

        with mock.patch.dict(os.environ, {"GH_REPO": "o/r", "REPO_ID": str(REPO_ID)}), \
                mock.patch.object(base_state.subprocess, "run", fake_run):
            with mock.patch("sys.argv", ["base_state.py", "--has-exact", "--base", self.c2]), \
                    contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(base_state.main(), 0)
            self.assertIn("saved: 77", out.getvalue())

            with mock.patch("sys.argv", ["base_state.py", "--has-exact", "--base", self.c3]), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(base_state.main(), 1)


class MainStateWorkflowTest(unittest.TestCase):
    text = (ROOT / ".github/workflows/main_state.yml").read_text()

    def test_staggered_slots_and_early_skip(self):
        for cron in ("17 10 * * *", "0 * * * *", "15 * * * *", "30 * * * *", "45 * * * *"):
            self.assertIn(cron, self.text)
        for slot in ("'full'", "'slot-0'", "'slot-1'", "'slot-2'", "'slot-3'"):
            self.assertIn(slot, self.text)
        self.assertLess(self.text.index("id: check"), self.text.index("Install Lean"))
        self.assertLess(self.text.index("id: check"), self.text.index("lake exe cache get"))
        self.assertIn("steps.check.outputs.skip != 'true'", self.text)
        self.assertIn("github.event.schedule == '17 10 * * *'", self.text)
        self.assertNotIn("contents: write", self.text)
        self.assertNotIn("actions: write", self.text)


if __name__ == "__main__":
    unittest.main()
