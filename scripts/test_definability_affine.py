"""Compare coefficient counting with direct evaluation on small finite rings."""

import itertools
import unittest

from definability_affine_counts import affine_models, affine_model_count
from spectrum_generate import load_equations, variables


class AffineCountsTest(unittest.TestCase):
    def test_full_assignment_evaluation(self):
        equations = load_equations()
        laws = [
            3,
            47,
            75,
            104,
            411,
            420,
            429,
            473,
            477,
            481,
            562,
            623,
            640,
            669,
            846,
            1036,
            1049,
            1083,
            1122,
            1276,
            1279,
            1489,
            3253,
        ]
        for n in (2, 3):
            for law in laws:
                lhs, rhs = equations[law - 1]
                names = sorted(variables(lhs) | variables(rhs))
                expected = []
                for a, b, c in itertools.product(range(n), repeat=3):

                    def evaluate(term, env):
                        if isinstance(term, str):
                            return env[term]
                        return (
                            a * evaluate(term[0], env) + b * evaluate(term[1], env) + c
                        ) % n

                    if all(
                        evaluate(lhs, env) == evaluate(rhs, env)
                        for values in itertools.product(range(n), repeat=len(names))
                        for env in [dict(zip(names, values))]
                    ):
                        expected.append((a, b, c))
                self.assertEqual(affine_models((lhs, rhs), n), expected, (law, n))
                self.assertEqual(affine_model_count((lhs, rhs), n), len(expected))

    def test_composite_shift_counts(self):
        # A constant discrepancy can annihilate several nonzero shifts over a ring.
        equation = load_equations()[419]
        for n in (4, 6, 9):
            models = affine_models(equation, n)
            self.assertEqual(affine_model_count(equation, n), len(models))
            lhs, rhs = equation
            names = sorted(variables(lhs) | variables(rhs))
            direct = []
            for a, b, c in itertools.product(range(n), repeat=3):

                def ev(term, env):
                    return (
                        env[term]
                        if isinstance(term, str)
                        else (a * ev(term[0], env) + b * ev(term[1], env) + c) % n
                    )

                if all(
                    ev(lhs, env) == ev(rhs, env)
                    for vals in itertools.product(range(n), repeat=len(names))
                    for env in [dict(zip(names, vals))]
                ):
                    direct.append((a, b, c))
            self.assertEqual(models, direct)


if __name__ == "__main__":
    unittest.main()
