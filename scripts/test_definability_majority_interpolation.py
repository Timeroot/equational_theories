"""Independent replay and boundary checks for the marked-case refinements."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import numpy as np

from definability_majority_interpolation import (
    boolean_majority, check_interpolation, closure, evaluate, interpolate, is_majority)
from definability_small_model_refine import lattice_majority, run_search
from definability_small_model_sweep import (
    EQUATIONS, guided_term_search, holds, small_bank, term_screen)


SOURCE = [[0, 0, 1, 3], [2, 3, 1, 2], [0, 3, 2, 0], [2, 1, 3, 1]]
TARGET = [[0, 2, 2, 3], [1, 3, 0, 0], [3, 1, 2, 2], [1, 3, 0, 3]]


class MajorityTests(unittest.TestCase):
    def test_construct_and_expand_interpolation(self):
        majority = boolean_majority(SOURCE, seconds=30)
        self.assertIsNotNone(majority)
        self.assertTrue(is_majority(evaluate(SOURCE, majority, 3)))
        self.assertTrue(holds(EQUATIONS[1481], np.array(TARGET)))
        check_interpolation(SOURCE, majority, TARGET)
        term = interpolate(SOURCE, majority, TARGET)
        np.testing.assert_array_equal(evaluate(SOURCE, term, 2), TARGET)

    def test_bad_pair_and_bad_majority_are_rejected(self):
        majority = boolean_majority(SOURCE, seconds=30)
        target = [row.copy() for row in TARGET]
        target[0][0] = 1  # Every source term fixes the idempotent 0.
        with self.assertRaises(AssertionError):
            check_interpolation(SOURCE, majority, target)
        with self.assertRaises(ValueError):
            interpolate(SOURCE, majority, target)
        with self.assertRaises(AssertionError):
            check_interpolation(SOURCE, dict(nodes=[0, 1, 2], root=0), TARGET)

    def test_duplicate_seeds_preserve_original_variable_indices(self):
        _, nodes, lookup = closure([[0, 1], [1, 0]],
                                   [(0, 0), (0, 0), (0, 1)], goals=[(0, 1)])
        self.assertEqual(nodes[lookup[(0, 1)]], 2)

    def test_guided_search_replays_the_hard_e335_example(self):
        table = np.array([[0, 0, 0, 0, 4], [0, 0, 3, 4, 2], [0, 4, 0, 1, 3],
                          [0, 2, 4, 3, 1], [4, 3, 1, 2, 4]])
        result = guided_term_search(table, 3558, seed=330, seconds=30, steps=10000)
        self.assertIn('3558', result['term_roots'])
        term = dict(nodes=[0, 1]+result['term_nodes'][2:], root=result['term_roots']['3558'])
        self.assertTrue(holds(EQUATIONS[3557], evaluate(table, term, 2)))


@unittest.skipUnless(shutil.which('g++'), 'C++ discovery tools require g++')
class CompiledSearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.binaries = []
        for name in ('definability_small_term_search', 'definability_subpower_search'):
            binary = str(Path(cls.directory.name)/name)
            subprocess.run(['g++', '-O3', '-std=c++17', str(Path(__file__).with_name(name+'.cpp')),
                            '-o', binary], check=True)
            cls.binaries.append(binary)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def test_all_two_element_sources_match_python_enumeration(self):
        targets = [313, 1482, 3272, 3472, 3548, 3558, 4290]
        for table in small_bank(2):
            expected, _, _, _ = term_screen(table, targets, 100)
            result = run_search(self.binaries[0], [2, len(targets), 100, 10,
                                *targets, *[int(v) for v in table.flat]])
            self.assertEqual(set(map(int, result['term_roots'])), set(expected))
            for law, root in result['term_roots'].items():
                term = dict(nodes=[0, 1]+result['term_nodes'][2:], root=root)
                self.assertTrue(holds(EQUATIONS[int(law)-1], evaluate(table, term, 2)))

    def test_five_element_packing_and_three_value_majority(self):
        table = [[0, 0, 1, 1, 2], [3, 1, 2, 4, 1], [2, 0, 2, 4, 3],
                 [0, 1, 0, 4, 4], [3, 3, 4, 2, 3]]
        majority = lattice_majority(table, self.binaries[1], 30)
        self.assertIsNotNone(majority)
        self.assertTrue(is_majority(evaluate(table, majority, 3)))
        table = [[0, 0, 0, 0, 4], [0, 0, 3, 4, 2], [0, 4, 0, 1, 3],
                 [0, 2, 4, 3, 1], [4, 3, 1, 2, 4]]
        result = run_search(self.binaries[0], [5, 1, 2000000, 10, 3558,
                            *[v for row in table for v in row]])
        self.assertIn('3558', result['term_roots'])
        for law, root in result['term_roots'].items():
            term = dict(nodes=[0, 1]+result['term_nodes'][2:], root=root)
            self.assertTrue(holds(EQUATIONS[int(law)-1], evaluate(table, term, 2)))


if __name__ == '__main__':
    unittest.main()
