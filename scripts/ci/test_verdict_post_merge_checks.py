"""How verdict.py checks command_keywords.txt and doc.verso on the merged PR."""

from pathlib import Path
import importlib.util
import tempfile
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location("verdict", Path(__file__).resolve().parent / "verdict.py")
verdict = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verdict)


class VerdictPostMergeChecksTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.check = verdict.Check(temp.name, "0" * 40, "1" * 40)

    def run_decide(self, *, docstrings_inert=True, keywords_current=(True, "")):
        entry = {"path": "RiemannMasullo/Ch02_AdelicTheta/Sec1.lean"}
        with (
            mock.patch.object(self.check, "changed_files", return_value=[entry]),
            mock.patch.object(self.check, "held_back", return_value=[]),
            mock.patch.object(self.check, "lint_text"),
            mock.patch.object(self.check, "git", return_value=mock.Mock(returncode=0, stdout="2" * 40 + "\n")),
            mock.patch.object(verdict, "run", return_value=mock.Mock(returncode=0, stdout="", stderr="")),
            mock.patch.object(self.check, "base_state", return_value=("", "", {})),
            mock.patch.object(self.check, "merge"),
            mock.patch.object(self.check, "held_back_after_merge", return_value=[]),
            mock.patch.object(self.check, "build", return_value=(0, "build log")),
            mock.patch.object(self.check, "signatures", return_value=("", "")),
            mock.patch.object(self.check, "docstrings_inert", return_value=docstrings_inert) as mock_inert,
            mock.patch.object(self.check, "keywords_current", return_value=keywords_current) as mock_kw,
            mock.patch.object(self.check, "synonym_sizes", return_value={}),
        ):
            with self.assertRaises(verdict.Stop) as stopped:
                verdict.decide(self.check, None)
            return stopped.exception, mock_inert, mock_kw

    def test_stale_keywords_after_merge_fails_pr(self):
        stop, mock_inert, mock_kw = self.run_decide(keywords_current=(False, "command #new_cmd\n"))
        self.assertEqual(stop.verdict, "fail")
        self.assertIn("command_keywords.txt", " ".join(stop.reasons))
        self.assertEqual(stop.log, "command #new_cmd\n")
        mock_inert.assert_called_once_with()
        mock_kw.assert_called_once_with()

    def test_doc_verso_after_merge_fails_pr(self):
        stop, mock_inert, mock_kw = self.run_decide(docstrings_inert=False)
        self.assertEqual(stop.verdict, "fail")
        self.assertIn("doc.verso", " ".join(stop.reasons))
        mock_inert.assert_called_once_with()
        mock_kw.assert_not_called()

    def test_inert_docstrings_and_current_keywords_allow_merge(self):
        stop, mock_inert, mock_kw = self.run_decide()
        self.assertEqual(stop.verdict, "merge")
        mock_inert.assert_called_once_with()
        mock_kw.assert_called_once_with()


if __name__ == "__main__":
    unittest.main()
