"""Local report reuse across real Git commits, including a PR branched from older main."""

from pathlib import Path
import subprocess
import tempfile
import unittest

CHECK = Path(__file__).resolve().parents[1] / "triage_report.py"


class TriageReportTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "test@example.org")
        self.git("config", "user.name", "Test")
        self.proof = "RiemannMasullo/Proof.lean"
        self.commit(self.proof, "original")
        self.git("switch", "-qc", "proof")
        self.head = self.commit(self.proof, "proved")
        self.git("switch", "-q", "main")
        self.base = self.commit("RiemannMasullo/Other.lean", "already on main")
        self.report = self.repo / "report.txt"
        self.report.write_text(f"checking {self.head} against {self.base}\nexit=0\n")

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.repo, text=True).strip()

    def commit(self, name, content):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        self.git("add", "--", name)
        self.git("commit", "-qm", "change " + name)
        return self.git("rev-parse", "HEAD")

    def check(self, tip, head=None):
        return subprocess.run(["python3", CHECK, self.report, head or self.head, tip],
                              cwd=self.repo, capture_output=True, text=True)

    def test_only_relevant_changes_require_another_build(self):
        self.assertEqual(self.check(self.base).returncode, 0)
        unrelated = self.commit("RiemannMasullo/Other.lean", "new proof")
        self.assertEqual(self.check(unrelated).returncode, 0)
        self.git("mv", self.proof, "RiemannMasullo/Renamed.lean")
        self.git("commit", "-qm", "rename")
        stale = self.check(self.git("rev-parse", "HEAD"))
        self.assertNotEqual(stale.returncode, 0)
        self.assertIn(self.proof, stale.stdout)

    def test_checker_inputs_and_report_identity(self):
        for name in ("scripts/lint.sh", "scripts/check_pr.sh"):
            with self.subTest(name=name):
                self.git("switch", "-q", "--detach", self.base)
                tip = self.commit(name, "changed checker")
                result = self.check(tip)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(name, result.stdout)
        self.assertNotEqual(self.check(self.head).returncode, 0)  # diverged from the checked base
        self.assertNotEqual(self.check(self.base, head=self.base).returncode, 0)
        self.report.write_text("old report without a base\nexit=0\n")
        self.assertNotEqual(self.check(self.base).returncode, 0)
