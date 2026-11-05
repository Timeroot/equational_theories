"""Compare the bitset calculation with direct multiplication-table checks."""
import unittest

from parastrophe_e872_block_search import bit_columns, parameter_masks, table
from parastrophe_e872_compression import BASE, Model, core


class BlockSearchTest(unittest.TestCase):
    def test_bit_order(self):
        for bits in (2, 8):
            for i, column in enumerate(bit_columns(bits)):
                for parameter in range(1 << bits):
                    self.assertEqual((column >> parameter) & 1, (parameter >> i) & 1)

    def test_masks_against_all_small_tables(self):
        # Includes a tautology and a false identity to check both pruning directions.
        terms = [0, 1, (0, core(0)), BASE]
        for quotient in ([[0, 1], [0, 1]], [[0, 1], [1, 0]]):
            good, valid = parameter_masks(quotient, terms)
            for parameter in range(256):
                model = Model(table(quotient, parameter))
                self.assertEqual(bool((good >> parameter) & 1), model.is_image())
                for term, mask in zip(terms, valid):
                    self.assertEqual(bool((mask >> parameter) & 1), model.holds(term))
            self.assertGreater((valid[0] & ~good).bit_count(), 0)
            self.assertEqual(valid[1], 0)


if __name__ == "__main__":
    unittest.main()
