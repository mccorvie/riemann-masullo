"""Build times are parsed from Lake's output and reported without affecting the verdict."""
import json
import tempfile
import types
import unittest
from pathlib import Path

import verdict

LOG = """\
✔ [5/62] Built Cache.Cli (290ms)
✔ [18784/18928] Built RiemannMasullo.ForMathlib.Analysis.Complex.Liouville (1.8s)
⚠ [18824/18928] Built RiemannMasullo.AppB_AnalyticNT.Sec1 (12s)
✔ [18900/18928] Built RiemannMasullo.AppD_SchwartzBruhat.Sec1c (2.1m)
warning: RiemannMasullo/AppB_AnalyticNT/Sec1.lean:3:1: declaration uses `sorry`
"""


class TimingTest(unittest.TestCase):
    def tearDown(self):
        verdict.TIMINGS.clear()

    def test_parse(self):
        t = verdict.build_timing(LOG, 99.6)
        self.assertEqual(t["modules"], 3)                     # Cache.* is not a library module
        self.assertEqual(t["slowest"][0], ["RiemannMasullo.AppD_SchwartzBruhat.Sec1c", 126.0])
        self.assertEqual(t["compile_seconds"], 140)
        self.assertEqual(t["wall_seconds"], 100)

    def test_empty_or_missing_log(self):
        self.assertEqual(verdict.build_timing(None, None)["modules"], 0)

    def test_report_keeps_verdict_and_shows_times(self):
        verdict.TIMINGS["main"] = verdict.build_timing("", 10)
        verdict.TIMINGS["pr"] = verdict.build_timing(LOG, 200)
        with tempfile.TemporaryDirectory() as out:
            args = types.SimpleNamespace(out=out, pr=1, head="a" * 40, base="b" * 40)
            verdict.report(args, "merge", [], "")
            data = json.loads((Path(out) / "verdict.json").read_text())
            self.assertEqual(data["verdict"], "merge")
            self.assertEqual(data["timings"]["pr"]["modules"], 3)
            summary = (Path(out) / "summary.md").read_text()
            self.assertIn("Build time", summary)
            self.assertIn("RiemannMasullo.AppD_SchwartzBruhat.Sec1c", summary)


if __name__ == "__main__":
    unittest.main()
