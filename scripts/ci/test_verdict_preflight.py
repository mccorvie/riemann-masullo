#!/usr/bin/env python3
"""Tests for verdict.py --preflight and pr_check.yml fast-fail wiring."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent.parent
VERDICT = Path(__file__).resolve().parent / "verdict.py"
LIB = "RiemannMasullo/AppA/Sec1.lean"


class PreflightRepo(unittest.TestCase):
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
        self.base = self.commit({
            LIB: "theorem t : True := by\n  sorry\n",
            "README.md": "hello\n",
        })

    def git(self, *args):
        return subprocess.run(
            ["git", *args], cwd=self.dir, env=self.env, check=True,
            capture_output=True, text=True,
        ).stdout.strip()

    def commit(self, files):
        for path, text in files.items():
            target = self.dir / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "c")
        return self.git("rev-parse", "HEAD")

    def branch(self, start, files):
        here = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "--detach", start)
        sha = self.commit(files)
        self.git("checkout", "-q", "--detach", here)
        return sha

    def run_preflight(self, base, head):
        out = self.dir / ".out"
        res = subprocess.run(
            [sys.executable, str(VERDICT), "--preflight", "--work", str(self.dir),
             "--base", base, "--head", head, "--pr", "1", "--out", str(out)],
            capture_output=True, text=True,
        )
        vfile = out / "verdict.json"
        data = json.loads(vfile.read_text()) if vfile.exists() else None
        return res.returncode, res.stdout, data

    def test_clean_library_pr_passes_without_verdict_file(self):
        head = self.branch(self.base, {LIB: "theorem t : True := by\n  trivial\n"})
        rc, out, data = self.run_preflight(self.base, head)
        self.assertEqual(rc, 0)
        self.assertIn("preflight: ok", out)
        self.assertIsNone(data)
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_non_library_pr_stops_with_read(self):
        head = self.branch(self.base, {"README.md": "updated\n"})
        rc, _out, data = self.run_preflight(self.base, head)
        self.assertEqual(rc, 0)
        self.assertEqual(data["verdict"], "read")

    def test_lint_failure_stops_with_fail(self):
        head = self.branch(self.base, {LIB: "theorem t : True := by\n  native_decide\n"})
        rc, _out, data = self.run_preflight(self.base, head)
        self.assertEqual(rc, 1)
        self.assertEqual(data["verdict"], "fail")
        self.assertTrue(any("lint" in r for r in data["reasons"]))

    def test_merge_conflict_stops_with_fail(self):
        tip = self.commit({LIB: "theorem t : True := by\n  exact True.intro\n"})
        head = self.branch(self.base, {LIB: "theorem t : True := by\n  trivial\n"})
        rc, _out, data = self.run_preflight(tip, head)
        self.assertEqual(rc, 1)
        self.assertEqual(data["verdict"], "fail")
        self.assertTrue(any("merge cleanly" in r for r in data["reasons"]))


class WorkflowOrder(unittest.TestCase):
    text = (ROOT / ".github/workflows/pr_check.yml").read_text()

    def test_preflight_runs_before_lean_install_and_gates_heavy_steps(self):
        self.assertIn("verdict.py --preflight", self.text)
        self.assertLess(self.text.index("id: preflight"), self.text.index("Install Lean"))
        self.assertLess(self.text.index("id: preflight"), self.text.index("lake exe cache get"))
        self.assertGreaterEqual(self.text.count("if: steps.preflight.outputs.verdict == ''"), 5)
        self.assertIn("steps.preflight.outputs.verdict || steps.check.outputs.verdict", self.text)


if __name__ == "__main__":
    unittest.main()
