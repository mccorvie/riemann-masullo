"""Invalid signature baselines are checker errors, before the PR is merged or built."""
import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import verdict


BASE = "theorem Example.a 123\ntheorem Example.b 456\n"
MALFORMED = "theorem Example.a broken\n"


class BaselineTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.check = verdict.Check(temp.name, "0" * 40, "1" * 40)
        self.patches = contextlib.ExitStack()
        self.addCleanup(self.patches.close)
        self.run = self.patch(verdict, "run", return_value=mock.Mock(returncode=0, stdout=""))
        self.patch(self.check, "changed_files", return_value=[])
        self.patch(self.check, "held_back", return_value=[])
        self.patch(self.check, "lint_text")
        self.patch(self.check, "git", return_value=mock.Mock(
            returncode=0, stdout="2" * 40, stderr=""))
        self.patch(self.check, "docstrings_inert", return_value=True)
        self.build = self.patch(self.check, "build", return_value=(0, "build log"))
        self.patch(self.check, "keywords_current", return_value=(True, ""))
        self.patch(self.check, "synonym_sizes", return_value={})
        self.signatures = self.patch(self.check, "signatures", return_value=(BASE, BASE))
        self.merge = self.patch(self.check, "merge")
        self.patch(self.check, "held_back_after_merge", return_value=[])

    def patch(self, obj, name, **kwargs):
        return self.patches.enter_context(mock.patch.object(obj, name, **kwargs))

    def decision(self, supplied):
        with self.assertRaises(verdict.Stop) as stopped:
            verdict.decide(self.check, supplied)
        return stopped.exception

    def assert_baseline_error(self, supplied):
        stopped = self.decision(supplied)
        self.assertEqual(stopped.verdict, "error")
        self.assertIn("signature dump of main", " ".join(stopped.reasons))
        self.merge.assert_not_called()
        return stopped

    def test_malformed_supplied_baseline_cannot_hide_change_or_removal(self):
        for head in ("theorem Example.a 999\n", ""):
            with self.subTest(head=head):
                self.signatures.return_value = (head, head)
                stopped = self.assert_baseline_error(MALFORMED)
                self.assertEqual(stopped.log, MALFORMED)
                self.build.assert_not_called()
                self.signatures.assert_not_called()

    def test_mixed_supplied_baseline_is_not_partially_trusted(self):
        self.assert_baseline_error(BASE + MALFORMED)
        self.build.assert_not_called()
        self.signatures.assert_not_called()

    def test_nonempty_blank_supplied_baseline_does_not_regenerate(self):
        for supplied in ("\n", "\n\n", " \t\n"):
            with self.subTest(supplied=supplied):
                self.assert_baseline_error(supplied)
                self.build.assert_not_called()
                self.signatures.assert_not_called()

    def test_invalid_generated_baseline_stops_before_candidate_build(self):
        for dump in (MALFORMED, BASE + MALFORMED, "", "\n", " \t\n"):
            with self.subTest(dump=dump):
                self.build.reset_mock()
                self.signatures.reset_mock()
                self.signatures.return_value = (dump, dump)
                stopped = self.assert_baseline_error(None)
                self.assertEqual(stopped.log, dump)
                self.build.assert_called_once_with(sandboxed=False)
                self.signatures.assert_called_once_with()

    def test_valid_supplied_baseline_retains_main_checks_and_exact_text(self):
        supplied = "\n" + BASE + "\n"
        self.assertEqual(self.check.base_state(supplied), (supplied, "build log", {}))
        self.build.assert_called_once_with(sandboxed=False)
        self.check.keywords_current.assert_called_once_with()
        self.check.synonym_sizes.assert_called_once_with()
        self.signatures.assert_not_called()

    def test_empty_or_absent_supplied_baseline_regenerates(self):
        for supplied in ("", None):
            with self.subTest(supplied=supplied):
                self.signatures.reset_mock()
                self.assertEqual(self.check.base_state(supplied), (BASE, "build log", {}))
                self.signatures.assert_called_once_with()

    def test_failed_generation_retains_existing_error_and_log(self):
        self.signatures.return_value = (None, "generation failed")
        stopped = self.assert_baseline_error(None)
        self.assertEqual(stopped.reasons, ["the signature dump of main failed"])
        self.assertEqual(stopped.log, "generation failed")

    def test_valid_baseline_still_rejects_public_changes_and_removals(self):
        for head in ("theorem Example.a 999\ntheorem Example.b 456\n",
                     "theorem Example.b 456\n"):
            with self.subTest(head=head):
                self.signatures.return_value = (head, head)
                self.assertEqual(self.decision(BASE).verdict, "fail")

    def test_valid_baseline_with_unchanged_head_merges(self):
        self.assertEqual(self.decision(BASE).verdict, "merge")

    def test_malformed_head_keeps_existing_read_behavior(self):
        self.signatures.return_value = (BASE + "unrecognized output\n", "")
        stopped = self.decision(BASE)
        self.assertEqual(stopped.verdict, "read")
        self.assertIn("the signature dump has lines that could not be read", stopped.reasons)

    def test_candidate_build_failure_remains_a_failure(self):
        self.build.side_effect = [(0, "main log"), (1, "candidate log")]
        stopped = self.decision(BASE)
        self.assertEqual(stopped.verdict, "fail")
        self.assertEqual(stopped.reasons, ["it does not build on top of main"])

    def test_earlier_read_conflict_and_import_results_keep_their_order(self):
        cases = [(self.check.changed_files, verdict.Stop("read", ["outside library"]), "read"),
                 (self.check.git, mock.Mock(returncode=1, stdout="", stderr=""), "fail"),
                 (self.run, mock.Mock(returncode=3, stdout="import all"), "fail")]
        for call, outcome, expected in cases:
            with self.subTest(expected=expected, outcome=str(outcome)):
                if isinstance(outcome, Exception):
                    call.side_effect = outcome
                else:
                    call.return_value = outcome
                try:
                    self.assertEqual(self.decision(MALFORMED).verdict, expected)
                    self.build.assert_not_called()
                    self.signatures.assert_not_called()
                    self.merge.assert_not_called()
                finally:
                    call.side_effect = None
                    call.return_value = (mock.Mock(returncode=0, stdout="2" * 40, stderr="")
                                         if call is self.check.git else
                                         mock.Mock(returncode=0, stdout="") if call is self.run else [])

    def test_invalid_baseline_reports_error_artifact_and_exit_two(self):
        saved = self.root / "baseline.txt"
        saved.write_text(MALFORMED)
        args = ["verdict.py", "--work", str(self.root), "--base", "0" * 40,
                "--head", "1" * 40, "--base-signatures", str(saved)]
        with mock.patch.object(sys, "argv", args), mock.patch.object(verdict, "Check",
                                                                    return_value=self.check):
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(verdict.main(), 2)
        report = json.loads((self.root / ".agent/verdict/verdict.json").read_text())
        self.assertEqual(report["verdict"], "error")
        self.merge.assert_not_called()


if __name__ == "__main__":
    unittest.main()
