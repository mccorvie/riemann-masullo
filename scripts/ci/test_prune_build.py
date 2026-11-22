"""Only build outputs without a source file are deleted."""
import tempfile
import unittest
from pathlib import Path

from prune_build import orphans, prune


class PruneBuildTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        for src in ("RiemannMasullo/AppA/Sec1.lean", "RiemannMasullo/ForMathlib/A/B.lean"):
            (self.root / src).parent.mkdir(parents=True, exist_ok=True)
            (self.root / src).write_text("")
        self.out = self.root / ".lake/build/lib/lean/RiemannMasullo"
        self.ir = self.root / ".lake/build/ir/RiemannMasullo"
        for rel in ("AppA/Sec1.olean", "AppA/Sec1.olean.private.hash", "AppA/Sec1.trace", "ForMathlib/A/B.ilean",
                    "AppA/Gone.olean", "AppA/Gone.olean.server", "Old/Sec9.trace"):
            (self.out / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.out / rel).write_text("")
        for rel in ("AppA/Sec1.c", "AppA/Gone.c"):
            (self.ir / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.ir / rel).write_text("")
        other = self.root / ".lake/build/lib/lean/Main.olean"      # another library: never touched
        other.write_text("")

    def names(self):
        return sorted(str(p.relative_to(self.root / ".lake/build")) for p in (self.root / ".lake/build").rglob("*")
                      if p.is_file())

    def test_orphans_only(self):
        self.assertEqual(len(orphans(self.root)), 4)
        self.assertEqual(prune(self.root, dry=True), 4)
        self.assertEqual(len(self.names()), 10)
        self.assertEqual(prune(self.root), 4)
        self.assertEqual(self.names(), [
            "ir/RiemannMasullo/AppA/Sec1.c", "lib/lean/Main.olean",
            "lib/lean/RiemannMasullo/AppA/Sec1.olean", "lib/lean/RiemannMasullo/AppA/Sec1.olean.private.hash",
            "lib/lean/RiemannMasullo/AppA/Sec1.trace", "lib/lean/RiemannMasullo/ForMathlib/A/B.ilean"])
        self.assertFalse((self.out / "Old").exists())
        self.assertEqual(prune(self.root), 0)


if __name__ == "__main__":
    unittest.main()
