import unittest

from parastrophe_e872_compression import (
    BASE, Model, candidates, load_countermodels, refuting_model, right_depth, unit,
)


class CountermodelDirectionTests(unittest.TestCase):
    def test_failing_a_bad_model_retains_candidate(self):
        # Right unary swap fails E614; it cannot refute E614 as a candidate.
        bad = load_countermodels([[[1, 0], [1, 0]]])
        self.assertIsNone(refuting_model(unit(0), bad))

    def test_holding_in_a_bad_model_rejects_candidate(self):
        # Left zero satisfies E614 but fails the second image identity.
        bad = load_countermodels([[[0, 0], [1, 1]]])
        self.assertEqual(refuting_model(unit(0), bad), 0)
        self.assertFalse(bad[0].holds(BASE))

    def test_image_model_cannot_enter_bad_pool(self):
        with self.assertRaises(ValueError):
            load_countermodels([[[0, 1], [0, 1]]])

    def test_cyclic_depth_obstruction(self):
        term = unit(unit(unit(0)))
        self.assertEqual(right_depth(term), 9)
        cycle = Model([[(y + 1) % 9 for y in range(9)] for _ in range(9)])
        self.assertTrue(cycle.holds(term))
        self.assertFalse(cycle.is_image())

    def test_reproduce_archived_campaigns(self):
        self.assertEqual(len(candidates(3, False, False)), 364)
        self.assertEqual(len(candidates(2, True, False, 65)), 931)
        self.assertEqual(len(candidates(2, True, True, 65)), 1180)


if __name__ == "__main__":
    unittest.main()
