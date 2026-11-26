"""How verdict.py checks command_keywords.txt against the built library."""

from pathlib import Path
import importlib.util
import tempfile
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location("verdict", Path(__file__).resolve().parent / "verdict.py")
verdict = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verdict)


class KeywordsCurrentTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.tools = Path(temp.name)
        (self.tools / "scripts" / "ci").mkdir(parents=True)
        self.keywords_file = self.tools / "scripts" / "ci" / "command_keywords.txt"
        self.check = verdict.Check(temp.name, "0" * 40, "1" * 40)

    def run_check(self, listed_text, lake_status, lake_out):
        self.keywords_file.write_text(listed_text, encoding="utf-8")
        with (
            mock.patch.object(verdict, "TOOLS", self.tools),
            mock.patch.object(self.check, "modules", return_value=["RiemannMasullo.AppA.Sec1"]),
            mock.patch.object(self.check, "lake", return_value=(lake_status, lake_out)),
        ):
            return self.check.keywords_current()

    def test_exact_match_passes(self):
        listed = "# comment\ncommand def\ncommand theorem\ntail def\n"
        ok, _ = self.run_check(listed, 0, "command def\ncommand theorem\ntail def\n")
        self.assertTrue(ok)

    def test_superset_with_extra_unused_tokens_passes(self):
        listed = "# comment\ncommand #instances\ncommand assert_no_sorry\ncommand def\ntail instances\n"
        ok, _ = self.run_check(listed, 0, "command def\n")
        self.assertTrue(ok)

    def test_missing_token_fails_and_reports_missing(self):
        listed = "command def\n"
        ok, out = self.run_check(listed, 0, "command #new_cmd\ncommand def\n")
        self.assertFalse(ok)
        self.assertEqual(out, "command #new_cmd\n")

    def test_nonzero_exit_fails(self):
        ok, out = self.run_check("command def\n", 1, "CommandKeywords error\n")
        self.assertFalse(ok)
        self.assertEqual(out, "CommandKeywords error\n")

    def test_empty_output_fails(self):
        ok, out = self.run_check("command def\n", 0, "")
        self.assertFalse(ok)
        self.assertEqual(out, "")


if __name__ == "__main__":
    unittest.main()
