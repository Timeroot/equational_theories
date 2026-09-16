"""Independent small-table checks for the linear-count search, not proof seeds."""
import unittest

from definability_linear_counts import find_obstructions, linear_models
from spectrum_generate import load_equations, satisfies


class LinearCountsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.equations = load_equations()

    def test_matches_full_table_check(self):
        for n in (2, 3, 4, 5):
            for law in (3, 43, 467, 680, 704, 1276, 1279, 4405):
                lhs, rhs = self.equations[law - 1]
                expected = [(a, b) for a in range(n) for b in range(n)
                            if satisfies(lhs, rhs,
                                         [(a*x+b*y) % n for x in range(n) for y in range(n)], n)]
                self.assertEqual(linear_models((lhs, rhs), n), expected, (law, n))

    def test_equation_without_univariate_constraint(self):
        # E4405's scalar-linear condition is just a=b: no spurious empty count.
        self.assertEqual(linear_models(self.equations[4404], 5), [(i, i) for i in range(5)])

    def test_small_certificate(self):
        results = list(find_obstructions(self.equations, [(1276, 680)], 5))
        self.assertEqual(results, [dict(source=1276, target=680, modulus=5,
                                       source_count=2, target_count=1,
                                       factors=[(1, 3), (4, 4)])])

    def test_larger_certificates(self):
        for source, target, modulus in ((704, 504, 47), (1279, 3548, 17), (704, 870, 83)):
            self.assertGreater(len(linear_models(self.equations[source-1], modulus)),
                               len(linear_models(self.equations[target-1], modulus)))

    def test_bad_modulus(self):
        with self.assertRaises(ValueError):
            linear_models(self.equations[0], 1)


if __name__ == '__main__':
    unittest.main()
