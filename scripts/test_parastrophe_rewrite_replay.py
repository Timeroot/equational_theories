"""Compare affine replay, including offsets, with exhaustive small magma tables."""
import itertools
import unittest

from parastrophe_e872_compression import BASE, Model, core
from parastrophe_rewrite_replay import affine_holds


class AffineReplayTest(unittest.TestCase):
    terms = [0, 1, (0, 1), (0, core(0)), BASE, (1, (0, (1, 0)))]

    def test_scalar_offsets(self):
        # Composite moduli work too: no field inverses are used.
        for n in (2, 3, 4, 5):
            for a, b, c in itertools.product(range(n), repeat=3):
                model = Model([[(a*x+b*y+c) % n for y in range(n)] for x in range(n)])
                spec = {"p": n, "a": a, "b": b, "c": c}
                if model.is_image():
                    with self.assertRaises(ValueError):
                        affine_holds([spec])
                else:
                    holds = affine_holds([spec])
                    for t in self.terms:
                        self.assertEqual(bool(holds(t)[0]), model.holds(t), (spec, t))
                    if c == 0:
                        del spec["c"]
                        old = affine_holds([spec])
                        self.assertEqual(old(BASE).tolist(), holds(BASE).tolist())

    def test_quadratic_offsets(self):
        # Exhaust all 64 affine operations over F2[i]/(i²+1), including nonunits.
        elements = list(itertools.product(range(2), repeat=2))
        def mul(x, y):
            return ((x[0]*y[0]-x[1]*y[1]) % 2, (x[0]*y[1]+x[1]*y[0]) % 2)
        for a, b, c in itertools.product(elements, repeat=3):
            table = [[elements.index(tuple((u+v+w) % 2 for u,v,w in
                                           zip(mul(a,x), mul(b,y), c)))
                      for y in elements] for x in elements]
            model = Model(table)
            spec = {"p": 2, "a": a, "b": b, "c": c}
            if model.is_image():
                with self.assertRaises(ValueError):
                    affine_holds([], [spec])
            else:
                holds = affine_holds([], [spec])
                for t in self.terms:
                    self.assertEqual(bool(holds(t)[0]), model.holds(t), (spec, t))

    def test_empty_and_invalid(self):
        self.assertEqual(affine_holds([])(BASE).tolist(), [])
        with self.assertRaises(ValueError):
            affine_holds([{"p": 1, "a": 1, "b": 0}])


if __name__ == "__main__":
    unittest.main()
