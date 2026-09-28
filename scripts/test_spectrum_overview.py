"""Semantic checks for the spectrum presentation layer and its proof boundaries."""

import unittest

from spectrum_note import EXCLUDED, TAILS, lower
from spectrum_overview import NOTES, formula_orders, overview, parse_formula


def row(law, *, pending=(), formula=None):
    record = {
        "equation": law, "pdf_representative": law, "mathematical_status": "UNKNOWN",
        "lower_bound_formula": lower(law) if formula is None else formula,
        "lower_bound_proof_status": "PROVED", "included_examples": [],
        "exclusions": [{"order": n, "status": "PROOF_AVAILABLE" if n in pending else "PROVED",
                        "theorem": f"Spectrum.Catalogue.exclude_{law}_{n}"}
                       for n in EXCLUDED[law]],
    }
    if law in TAILS:
        record.update(cofinite_cutoff=TAILS[law], cofinite_proof_status="PROVED")
    return record


class SpectrumOverviewTest(unittest.TestCase):
    def test_e63_separates_seven_open_and_two_pending(self):
        result = overview(row(63, pending=(10, 14)))
        self.assertTrue(result["finite"])
        self.assertEqual(result["through"], 158)
        self.assertEqual(result["open_orders"], [18, 26, 30, 38, 42, 90, 158])
        self.assertEqual(result["pending_orders"], [10, 14])
        self.assertEqual(result["excluded_orders"], [2, 6])
        self.assertNotIn(10, result["included_orders"])

    def test_complete_finite_lists(self):
        for law, expected_count in [(667, 29), (883, 36)]:
            with self.subTest(law=law):
                result = overview(row(law))
                self.assertTrue(result["finite"])
                self.assertEqual(result["through"], 1227)
                self.assertEqual(len(result["open_orders"]), expected_count)
                self.assertEqual(result["open_orders"][0], 12)
                self.assertEqual(result["open_orders"][-1], 1227)
                self.assertEqual(result["pending_orders"], [])

    def test_explicit_quartic_tails(self):
        for law in (1076, 1313):
            result = overview(row(law))
            self.assertTrue(result["finite"])
            self.assertEqual(result["through"], 107772)
            self.assertIn("every order ≥ 107773", result["included_summary"])
            self.assertIn(8, result["open_orders"])
        self.assertEqual(formula_orders(parse_formula("{1} ∪ Set.Ici 10"), 12), {1, 10, 11, 12})
        with self.assertRaises(ValueError):
            parse_formula("Set.Ici 0")

    def test_e1486_full_six_element_gap_list(self):
        result = overview(row(1486))
        self.assertEqual(result["open_orders"], [10, 12, 14, 15, 17, 26])
        self.assertEqual(result["through"], 26)
        self.assertIn(64, result["included_orders"])
        self.assertIn("every order ≥ 27", result["included_summary"])

    def test_e677_fourth_powers_and_new_exclusions(self):
        result = overview(row(677))
        self.assertFalse(result["finite"])
        self.assertEqual(result["through"], 64)
        self.assertEqual(result["excluded_orders"], [2, 3, 4])
        self.assertIn(16, result["included_orders"])
        self.assertIn("Fourth powers", result["family_labels"])
        self.assertIn(6, result["open_orders"])
        self.assertIn("full cofiniteness still has a proof gap", result["note"])
        self.assertIn(256, formula_orders(parse_formula("fourthPowers"), 300))

    def test_e704_tail_and_cubes(self):
        result = overview(row(704, pending=(9,)))
        self.assertTrue(result["finite"])
        self.assertEqual(result["through"], 1227)
        self.assertIn("every order ≥ 1228", result["included_summary"])
        self.assertIn("Cubes", result["family_labels"])
        self.assertIn(27, result["included_orders"])
        self.assertIn(64, result["included_orders"])
        self.assertEqual(result["pending_orders"], [9])

    def test_product_closure_is_iterated_and_uses_proved_examples(self):
        record = row(1483, formula="{1, 2}")
        record["exclusions"] = []
        record["included_examples"] = [{"order": 3, "status": "PROOF_AVAILABLE"}]
        result = overview(record)
        self.assertEqual(result["included_orders"], [1, 2, 4, 8, 16, 32, 64])
        self.assertIn(6, result["open_orders"])
        record["included_examples"].append({"order": 3, "status": "PROVED"})
        result = overview(record)
        for n in (6, 12, 18, 24, 27, 36, 48, 54, 64):
            self.assertIn(n, result["included_orders"])

    def test_paper_lower_bound_and_tail_do_not_become_proved(self):
        record = row(670, formula="positiveExcept {2, 3}")
        record.update(lower_bound_proof_status="PROOF_AVAILABLE", cofinite_cutoff=4,
                      cofinite_proof_status="PROOF_AVAILABLE", included_examples=[5])
        result = overview(record)
        self.assertFalse(result["finite"])
        self.assertEqual(result["included_orders"], [1, 5, 25])
        self.assertIn(8, result["open_orders"])

    def test_tail_without_evidence_does_not_become_proved(self):
        record = row(670, formula="{1, 5}")
        record["cofinite_cutoff"] = 8
        self.assertFalse(overview(record)["finite"])

    def test_e1483_external_exclusion_is_pending(self):
        result = overview(row(1483, pending=(11,)))
        self.assertEqual(result["pending_orders"], [11])
        self.assertNotIn(11, result["open_orders"])
        self.assertNotIn(11, result["excluded_orders"])

    def test_alias_uses_family_note_and_bound(self):
        record = row(883)
        record.update(equation=1323, pdf_representative=1323)
        self.assertEqual(overview(record)["note"], NOTES[883])
        self.assertEqual(len(overview(record)["open_orders"]), 36)

    def test_all_seventeen_notes_distinguish_paper_arguments(self):
        self.assertEqual(len(NOTES), 17)
        for law in (670, 677, 907, 1083, 1286):
            self.assertIn("paper", NOTES[law])
        for law in (1076, 1313):
            self.assertIn("in Lean", NOTES[law])
        self.assertIn("proof gap", NOTES[677])

    def test_named_families_and_residue_exceptions(self):
        values = formula_orders(parse_formula("quarticTailSeeds"), 300)
        self.assertIn(273, values)
        self.assertNotIn(0, values)
        self.assertNotIn(273, overview(row(1076))["open_orders"])
        values = formula_orders(parse_formula("residues 3 {0, 1} {6}"), 12)
        self.assertEqual(values, {1, 3, 4, 7, 9, 10, 12})
        values = formula_orders(parse_formula("(({2} : Set ℕ) ∪ (squares ∪ twiceSquares))"), 20)
        self.assertEqual(values, {1, 2, 4, 8, 9, 16, 18})
        self.assertEqual(formula_orders(parse_formula("shiftedSquares"), 30), {11, 18, 27})
        self.assertIn(41, formula_orders(parse_formula("oddSumTwoSquares"), 64))
        self.assertNotIn(2, formula_orders(parse_formula("oddSumTwoSquares"), 64))

    def test_unsupported_or_executable_syntax_fails_closed(self):
        for text in ("__import__('os')", "squares | cubes", "fourthPowers + 1",
                     "{x : ℕ | x > 3}", "mysteryFamily", "residues 0 {0} ∅",
                     "positiveExcept {2, -3}", "({1} : Set ℕ))"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_formula(text)

    def test_contradictory_evidence_is_an_export_error(self):
        record = row(677, formula="{1, 3}")
        with self.assertRaisesRegex(ValueError, "Inconsistent spectrum evidence"):
            overview(record)


if __name__ == "__main__":
    unittest.main()
