"""Check symbolic pruning against every small affine multiplication table."""
import itertools
import unittest

from parastrophe_affine_image_scan import scan
from parastrophe_e872_compression import BASE, Model, core


class AffineScanTest(unittest.TestCase):
    def check_family(self, triangular):
        terms = [0, 1, (0, 1), (0, core(0)), BASE, (1, (0, (1, 0)))]
        record = {"rewrite_replay": {"unresolved": [
            {"index": i, "term": t} for i, t in enumerate(terms)]}}
        result = scan(record, 2, 2, triangular=triangular)
        actual = {h["index"] for h in result["hits"]}
        expected = set()
        vectors = list(itertools.product(range(2), repeat=2))
        matrices = [m for m in itertools.product(range(2), repeat=4) if not triangular or m[2] == 0]
        for A, B, offset in itertools.product(matrices, matrices, vectors):
            table = []
            for x in vectors:
                row = []
                for y in vectors:
                    z = tuple((A[2*i]*x[0] + A[2*i+1]*x[1] +
                               B[2*i]*y[0] + B[2*i+1]*y[1] + offset[i]) % 2
                              for i in range(2))
                    row.append(vectors.index(z))
                table.append(row)
            model = Model(table)
            if not model.is_image():
                expected.update(i for i, t in enumerate(terms) if model.holds(t))
        self.assertEqual(actual, expected)
        self.assertIn(0, actual)
        self.assertNotIn(1, actual)
        self.assertEqual(result["coefficient_pairs"], 64 if triangular else 256)

    def test_complete_small_matrix_family(self):
        self.check_family(False)

    def test_complete_small_triangular_family(self):
        self.check_family(True)


if __name__ == "__main__":
    unittest.main()
