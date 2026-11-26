"""A pull request that makes existing statements of at least LARGE_STATEMENT nodes more than
STATEMENT_GROWTH times larger has that among its reasons to fail; a new statement of at least
NEW_LARGE_STATEMENT nodes gets a note. Statements already that large on main hold nothing up."""
import unittest

from verdict import (LARGE_STATEMENT, LISTED_STATEMENT, NEW_LARGE_STATEMENT, declared_names,
                     grown_statements, large_new_statements, parse_statement_sizes)

BIG = LARGE_STATEMENT


class StatementSizesTest(unittest.TestCase):
    def test_parse(self):
        text = ("RiemannMasullo.a\tRiemannMasullo.Ch10.Sec1\t32361984597301\t20263\tSubgroup.map/4 87000×1900\n"
                "RiemannMasullo.b\tRiemannMasullo.Ch01.Sec2\t2000000\t900\t-\n"
                "\n"
                "not a line of the script\n")
        self.assertEqual(parse_statement_sizes(text), {
            "RiemannMasullo.a": (32361984597301, "Subgroup.map/4 87000×1900"),
            "RiemannMasullo.b": (2000000, "-")})

    def test_declared_names(self):
        dump = "theorem RiemannMasullo.a 123\ndef RiemannMasullo.b 4 5\nnot a line\n"
        self.assertEqual(declared_names(dump), {"RiemannMasullo.a", "RiemannMasullo.b"})

    def test_statement_that_grows_tenfold_is_named(self):
        grown = grown_statements({"X": (BIG, "-")}, {"X": (20 * BIG, "Subgroup.map/4 9×9")}, {"X"})
        self.assertEqual(len(grown), 1)
        self.assertIn("X", grown[0])
        self.assertIn("Subgroup.map/4", grown[0])

    def test_statement_that_grows_less_is_not(self):
        self.assertEqual(grown_statements({"X": (BIG, "-")}, {"X": (5 * BIG, "-")}, {"X"}), [])

    def test_statement_that_stays_small_is_not(self):
        self.assertEqual(grown_statements({}, {"X": (BIG - 1, "-")}, {"X"}), [])

    def test_statement_absent_from_main_listing_counts_as_listed_size(self):
        # main lists only statements of LISTED_STATEMENT nodes or more
        self.assertEqual(len(grown_statements({}, {"X": (20 * LISTED_STATEMENT * 100, "-")}, {"X"})), 1)

    def test_statement_that_shrinks_is_not(self):
        self.assertEqual(grown_statements({"X": (100 * BIG, "-")}, {"X": (2 * BIG, "-")}, {"X"}), [])

    def test_new_statement_is_not_counted_as_grown(self):
        self.assertEqual(grown_statements({}, {"Y": (100 * BIG, "-")}, {"X"}), [])

    def test_large_new_statement_gets_a_note(self):
        new = large_new_statements({"Y": (NEW_LARGE_STATEMENT, "-"), "Z": (NEW_LARGE_STATEMENT - 1, "-"),
                                    "X": (10 * NEW_LARGE_STATEMENT, "-")}, {"X"})
        self.assertEqual(len(new), 1)
        self.assertIn("Y", new[0])


if __name__ == "__main__":
    unittest.main()
