"""Compare symbolic elimination with a complete small-table search."""
import itertools
import unittest

from parastrophe_e872_compression import Model, core, BASE
from parastrophe_partitioned_affine_scan import nullspace, scan


class PartitionedScanTest(unittest.TestCase):
    def test_all_binary_fibres(self):
        terms = [0, 1, (0, core(0)), BASE, (1, (0, (1, 0)))]
        record = {"rewrite_replay": {"unresolved": [
            {"index": i, "term": t} for i, t in enumerate(terms)]}}
        for kind in ("projection", "xor"):
            expected = set()
            for params in itertools.product(range(2), repeat=8):
                table = []
                for x in range(4):
                    a, u = divmod(x, 2)
                    row = []
                    for y in range(4):
                        b, v = divmod(y, 2)
                        colour = b if kind == "projection" else a ^ b
                        value = (params[2*a+b]*u + v + params[4+2*a+b]) % 2
                        row.append(2*colour+value)
                    table.append(row)
                model = Model(table)
                if not model.is_image():
                    expected.update(i for i, t in enumerate(terms) if model.holds(t))
            actual = {h["index"] for h in scan(record, 2, kind)["hits"]}
            self.assertEqual(expected, actual)

    def test_nullspace_over_three_elements(self):
        for rows in ([], [[1,2,0,1]], [[1,2,0,1],[2,1,0,2]],
                     [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]):
            basis = list(nullspace(rows, 3))
            span = {tuple(sum(a*v[i] for a,v in zip(coeffs,basis)) % 3 for i in range(4))
                    for coeffs in itertools.product(range(3), repeat=len(basis))}
            expected = {v for v in itertools.product(range(3), repeat=4)
                        if all(sum(a*b for a,b in zip(r,v)) % 3 == 0 for r in rows)}
            self.assertEqual(span, expected)


if __name__ == "__main__":
    unittest.main()
