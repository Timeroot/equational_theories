"""Small independent checks for enumeration and obstruction search correctness."""
import json
from pathlib import Path
import unittest

import numpy as np
import z3

import definability_small_model_sweep as sweep


class SmallModelSweepTests(unittest.TestCase):
    def test_unlabeled_table_counts(self):
        self.assertEqual(len(list(sweep.small_bank(2))), 10)
        self.assertEqual(len(list(sweep.small_bank(3))), 3330)

    def test_both_solver_encodings_match_brute_force(self):
        from itertools import permutations
        n = 3
        for source in (335, 4364):
            expected = {tuple(t.flat) for t in sweep.small_bank(n)
                        if sweep.holds(sweep.EQUATIONS[source-1], t)}
            for symmetry in ('lex', 'orbit'):
                solver, es, cells = sweep.source_solver(source, n, 10000, symmetry)
                found = set()
                while True:
                    status = solver.check()
                    if status == z3.unsat:
                        break
                    self.assertEqual(status, z3.sat)
                    model = solver.model()
                    labels = {str(e): i for i, e in enumerate(es)}
                    table = np.array([labels[str(model.eval(c))] for c in cells]).reshape(n, n)
                    orbit = {tuple(sweep.relabel(table, p).flat) for p in permutations(range(n))}
                    canonical = min(orbit)
                    self.assertNotIn(canonical, found)
                    found.add(canonical)
                    blocks = {tuple(table.flat)} if symmetry == 'lex' else orbit
                    for flat in blocks:
                        solver.add(z3.Or(*[c != es[int(v)] for c, v in zip(cells, flat)]))
                self.assertEqual(found, expected)

    def test_known_relation_obstructions(self):
        path = Path(__file__).resolve().parents[1]/'data/definability_335_five_point.json'
        table = np.array(json.loads(path.read_text())['table'], dtype=np.uint8)
        results = sweep.relation_screen(table, [3352, 3748, 4408], 10000)
        for result in results.values():
            self.assertEqual(result['status'], 'unsat')
            for constraint in result['constraints']:
                cells = constraint['cells']
                relation = {tuple(v) for v in constraint['relation']}
                self.assertIn(tuple(c//5 for c in cells), relation)
                self.assertIn(tuple(c % 5 for c in cells), relation)
                for a in relation:
                    for b in relation:
                        self.assertIn(tuple(int(table[x, y]) for x, y in zip(a, b)), relation)

    def test_diagonal_limit_never_returns_partial_closure(self):
        table = np.array([[1, 0], [1, 0]], dtype=np.uint8)
        self.assertIsNone(sweep.diagonal_relation(table, limit=2))
        relation = sweep.diagonal_relation(table, limit=10)
        self.assertEqual({tuple(r) for r in relation['relation']}, {(0, 1), (1, 0)})

    def test_finding_targets_does_not_claim_clone_exhaustion(self):
        table = np.array([[0, 1], [1, 0]], dtype=np.uint8)
        found, _, complete, _ = sweep.term_screen(table, [1], 100)
        self.assertTrue(found)
        self.assertFalse(complete)


if __name__ == '__main__':
    unittest.main()
