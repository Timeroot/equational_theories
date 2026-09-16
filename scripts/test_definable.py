"""Exact reference tests for closure, import coverage, and entry-point pruning."""
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import numpy as np
import definable
import definability_audit as audit
from spectrum_definability_check import spectrum_closure
from lean_sources import imports, import_graph, minimal_entry_imports


def reference_closure(matrix):
    out = matrix.copy()
    for k in range(len(out)):
        out |= out[:, k, None] & out[None, k, :]
    return out


def reference_negatives(pos, neg):
    p = pos.astype(np.int64)
    return p.T @ neg.astype(np.int64) @ p.T > 0


class ClosureTests(unittest.TestCase):
    def test_hierarchy_and_verified_closure(self):
        pos = {key: np.eye(4, dtype=bool) for key in definable.KEYS}
        neg = {key: np.zeros((4, 4), dtype=bool) for key in definable.KEYS}
        pos['structural', 'all'][2, 1] = True
        neg['definable', 'fin'][2, 3] = True
        definable.close(pos, neg, verify=True)
        self.assertTrue(pos['definable', 'fin'][2, 1])
        self.assertTrue(neg['termStructural', 'all'][1, 3])

    def test_random_preorders_and_refutations(self):
        rng = np.random.default_rng(20260914)
        for size in (0, 1, 2, 7, 8, 9, 16, 31):
            for _ in range(15):
                matrix = rng.random((size, size)) < 0.12
                np.fill_diagonal(matrix, True)
                expected = reference_closure(matrix)
                actual = definable.transitive_closure(matrix)
                np.testing.assert_array_equal(actual, expected)
                negative = rng.random((size, size)) < 0.08
                np.testing.assert_array_equal(definable.compose_negatives(actual, negative),
                                              reference_negatives(expected, negative))

    def test_nonrepresentative_negative_is_not_lost(self):
        pos = np.eye(6, dtype=bool)
        pos[1:3, 1:3] = True
        pos[3:5, 3:5] = True
        pos[5, 1:3] = True
        neg = np.zeros_like(pos)
        neg[2, 4] = True  # Neither index is the first representative of its class.
        out = definable.compose_negatives(pos, neg)
        np.testing.assert_array_equal(out, reference_negatives(pos, neg))
        self.assertTrue(out[1:3, 3:5].all())
        self.assertFalse(out[0].any())
        self.assertFalse(out[:, 0].any())


class ImportTests(unittest.TestCase):
    def test_header_comments_and_multiple_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Example.lean'
            path.write_text('/- outer /- import Bogus -/ still comment -/\n'
                            'module\npublic import Foo/- split -/Bar\n'
                            'import Baz -- import Bogus\n'
                            'def text := "import Bogus"\n')
            self.assertEqual(list(imports(path)), ['Foo', 'Bar', 'Baz'])

    def test_pruning_preserves_diamond(self):
        graph = {'Root': ('A', 'B', 'C', 'A'), 'A': ('C',), 'B': ('C',), 'C': ()}
        self.assertEqual(minimal_entry_imports(graph, 'Root'), ['A', 'B'])

    def test_unimported_board_fact_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            lean = root / 'equational_theories/Definability'
            lean.mkdir(parents=True)
            entry = root / 'equational_theories/Definability.lean'
            entry.write_text('-- Empty entry point\n')
            cell = lean / 'Cell.lean'
            cell.write_text('theorem cell : Law3.StructuralFrom Law4 := by assumption\n')
            with patch.object(definable, 'ROOT', root), patch.object(definable, 'LEAN', lean):
                with self.assertRaisesRegex(RuntimeError, 'Unimported board declarations'):
                    definable.parse_lean()
                entry.write_text('import equational_theories.Definability.Cell\n')
                positives, *_ = definable.parse_lean()
                self.assertEqual(positives, [(4, 3, 'structural', False)])
            self.assertEqual(len(import_graph(root)), 2)

    def test_unimported_certificate_halves_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            lean = root / 'equational_theories/Definability'
            lean.mkdir(parents=True)
            (root / 'equational_theories/Definability.lean').write_text('-- Empty\n')
            cell = lean / 'Certificate.lean'
            for declaration in (
                'theorem demo_satisfies_0 : Satisfies Magma.demo [3] := by assumption\n',
                'theorem demo_refutes : FamilyRefutes Magma.demo [4] := by assumption\n',
            ):
                cell.write_text(declaration)
                with patch.object(definable, 'ROOT', root), patch.object(definable, 'LEAN', lean):
                    with self.assertRaisesRegex(RuntimeError, 'Unimported board declarations'):
                        definable.parse_lean()


class AuditTests(unittest.TestCase):
    def test_spectrum_transport_direction(self):
        inclusion = np.eye(5, dtype=bool)
        inclusion[1, 2] = inclusion[3, 4] = True
        present = np.array([False, True, False, False, False])
        absent = np.array([False, False, False, False, True])
        models, exclusions = spectrum_closure(present, absent, inclusion)
        np.testing.assert_array_equal(models, [False, True, True, False, False])
        np.testing.assert_array_equal(exclusions, [False, False, False, True, True])
        with self.assertRaises(AssertionError):
            spectrum_closure(present, models, inclusion)

    def test_completely_open_endpoints_and_strongest_quotient(self):
        pos = {key: np.eye(6, dtype=bool) for key in definable.KEYS}
        neg = {key: np.zeros((6, 6), dtype=bool) for key in definable.KEYS}
        pos['termStructural', 'all'][1:3, 1:3] = True
        pos['definable', 'fin'][3, 4] = True
        pos['definable', 'fin'][4, 3] = True
        neg['termStructural', 'all'][1:3, 3] = True
        definable.close(pos, neg)
        entry = audit.summarize_completely_open(pos, neg)
        recovered = {(s, t) for a, b in entry['pairs'] for s in entry['classes'][a]
                     for t in entry['classes'][b]}
        expected = {(s, t) for s in range(1, 6) for t in range(1, 6)
                    if all(not (pos[key][s, t] or neg[key][s, t])
                           for key in definable.KEYS if key[0] != 'implies')}
        self.assertEqual(recovered, expected)
        self.assertEqual(entry['raw_pairs'], len(expected))
        self.assertEqual(entry['classes'][1], [1, 2])
        # A weaker equivalence does not preserve strongest negative statuses.
        self.assertNotIn((1, 3), recovered)
        self.assertIn((1, 4), recovered)
        pos['structural', 'all'][1, 4] = True  # Break hierarchy deliberately.
        with self.assertRaises(AssertionError):
            audit.summarize_completely_open(pos, neg)

    def test_committing_does_not_stale_unchanged_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            snapshot = folder / 'snapshot.json'
            snapshot.write_text(audit.snapshot_json({'head': 'historical-head'}))
            (folder / 'audit.md').write_text('unchanged report\n')
            with patch.object(audit, 'OUT', folder), patch.object(audit, 'SNAPSHOT', snapshot), \
                    patch.object(audit, 'collect', return_value={'head': 'new-commit'}) as collect, \
                    patch.object(audit, 'artifacts', return_value={'audit.md': 'unchanged report\n'}), \
                    patch('sys.argv', ['definability_audit.py', '--check', '--date', '2026-09-15']):
                audit.main()
                collect.assert_called_once_with('2026-09-15', False)

    def test_lossless_quotient_and_nonuniform_other_relation_profiles(self):
        pos = np.eye(5, dtype=bool)
        pos[1:3, 1:3] = True
        neg = np.zeros_like(pos)
        neg[3, 1:3] = True
        codes = np.zeros((5, 5), dtype=np.uint16)
        # A different relation can distinguish members of this relation's class.
        codes[1, 3], codes[2, 3] = 3, 6
        entry = audit.summarize_relation(pos, neg, codes)
        self.assertEqual(entry['classes'], {1: [1, 2], 3: [3], 4: [4]})
        recovered = set()
        for s, groups in entry['open_rows'].items():
            for targets in groups.values():
                for t in targets:
                    recovered.update((a, b) for a in entry['classes'][s]
                                     for b in entry['classes'][t])
        expected = {(s, t) for s in range(1, 5) for t in range(1, 5)
                    if not (pos[s, t] or neg[s, t])}
        self.assertEqual(recovered, expected)
        self.assertEqual(entry['counts']['raw_open'], len(expected))
        self.assertIn(audit.profile(6), entry['raw_profiles'])
        self.assertNotIn(audit.profile(6), entry['reduced_profiles'])
        neg[3, 2] = False  # A nonuniform rectangle must fail the audit.
        with self.assertRaises(AssertionError):
            audit.summarize_relation(pos, neg, codes)

    def test_ranges_and_profile_order(self):
        self.assertEqual(audit.ranges([]), '')
        self.assertEqual(audit.ranges([8, 2, 1, 3, 7, 10, 11]), '1–3, 7, 8, 10, 11')
        self.assertEqual(audit.profile(1 + 2 * 3**9), 'POOOOOOOON')


if __name__ == '__main__':
    unittest.main()
