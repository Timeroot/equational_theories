"""Conservative transcription of section 3 of spectrum-note.pdf, with cited supplements.

Question marks are conjectures, never theorem specifications. Bounds at the
contradictory entries E1480 and E1313 are explained explicitly in NOTES.
This module is also used by the catalogue generator and witness search.
"""

EXACT = {
    115: "positiveExcept {2, 6}", 873: "positiveExcept {2, 6}", 880: "positiveExcept {2, 6}",
    481: "positiveExcept {3, 6}", 1496: "positiveExcept {3, 6}",
    2: "{1}", 66: "residues 3 {0, 1} {6}", 167: "residues 4 {0, 1} ∅",
    168: "squares", 474: "positiveExcept {2, 4}", 546: "sumTwoSquares",
    556: "sumTwoSquares", 695: "residues 3 {1, 2} {7}",
    887: "residues 3 {1, 2} {7}", 895: "powersTwo", 898: "powersTwo",
    1485: "squares ∪ twiceSquares", 1685: "positiveExcept {2}",
    1719: "positiveExcept {2}",
    1489: "positiveExcept {2, 4}",
    1480: "positiveExcept {2, 3}",
}

# Equality of *spectra*, not necessarily equivalence of equations.
ALIASES = {73: 63, 118: 63, 125: 63, 1692: 63, 880: 115, 1496: 481,
           1323: 883, 1526: 883, 556: 546, 695: 887}
EQUALITIES = {
    73: "spectrum_63_eq_73.symm",
    118: "(spectrum_63_eq_73.trans spectrum_73_eq_118).symm",
    125: "spectrum_63_eq_125.symm", 1692: "spectrum_63_eq_1692.symm",
    880: "spectrum_115_eq_880.symm", 1496: "spectrum_481_eq_1496.symm",
    1323: "spectrum_883_eq_1323.symm", 1526: "spectrum_883_eq_1526.symm",
    556: "spectrum_546_eq_556.symm", 695: "spectrum_695_eq_887",
}

FINITE = {
    63: [1, 3, 4, 5, 7, 8, 9, 11, 12, 13],
    115: [1, 5], 467: [1, 5, 7, 8], 481: [1, 7, 9, 12, 15],
    501: [1, 4, 5, 8, 9], 667: [1, 7, 9], 670: [1, 4, 5],
    677: [1, 5, 7, 9, 11, 13, 16], 704: [1, 5, 7, 8],
    873: [1, 5], 883: [1, 7], 907: [1, 3, 7, 9, 13],
    1076: [1, 5], 1083: [1, 3, 4, 7, 8, 9], 1110: [1, 4, 5, 7, 8, 9],
    1279: [1, 5, 7, 8], 1286: [1, 7], 1313: [1, 5, 7],
    1480: [1, *range(4, 19)], 1483: [1, 2, 4, 8, 9], 1485: [1],
    1486: [1, 11, 13, 21], 1489: [1, 3, *range(5, 22)],
    1516: [1, 5, 7, 8], 1719: [1, 5, 6, 8],
}
FAMILIES = {
    115: "residues 3 {0, 1} {6}", 467: "oddSumTwoSquares",
    481: "residues 3 {1, 2} {7}", 667: "residues 3 {1, 2} ∅",
    873: "residues 3 {0, 1} {6}", 883: "residues 3 {1, 2} ∅",
    1480: "squares", 1483: "squares", 1485: "squares ∪ twiceSquares",
    1486: "squares ∪ shiftedSquares", 1719: "residues 3 {0, 1} ∅",
}
EXCLUDED = {
    63: [2, 6, 10, 14], 115: [2, 6], 467: [2, 3, 4, 6], 481: [3, 6],
    501: [2], 667: [3], 670: [2, 3, 6, 7], 677: [2],
    704: [2, 3, 4, 6, 9], 873: [2, 6], 883: [3], 907: [2, 4, 5, 6],
    1076: [2, 3, 4, 6, 7], 1083: [2], 1110: [2, 3, 6],
    1279: [2, 3, 4, 6, 9], 1286: [2, 3, 4, 5, 6], 1313: [2, 3, 4, 6],
    # E1485 orders 11/13: now proved by WeakCentralCardinality, beyond the PDF.
    1480: [2, 3], 1483: [3, 5, 6, 7], 1485: [3, 11, 13], 1486: [2],
    1489: [2, 4], 1516: [2, 3, 4, 6], 1719: [2],
}
COFINITE = {63, 467, 670, 677, 704, 883, 1076, 1110, 1279, 1489, 1516}
# E1313: §3.1 says "not known to be cofinite", §3.8 asserts cofiniteness.
# Keep the claim visible as disputed, not as a theorem of the catalogue.
DISPUTED_COFINITE = {1313}
CONJECTURES = {}
NOTES = {
    63: "Constructive Lean lower bound: all positive orders outside {2,6,10,14,18,26,30,38,42,90,158}. The tail starts at 159. Orders 2 and 6 are excluded in Lean; exclusions at 10 and 14 remain explicitly admitted. Bennett (1989) also claims order 90, but its construction has not been reconstructed; it remains unproved here. See docs/63_lean_spectrum.md.",
    1719: "Now proved in Lean: a Bose construction with two shared points gives orders 3m+2 from idempotent Latin squares; Mendelsohn models and checked tables at 6 and 8 cover the rest. The squaring-map argument excludes order 2. See docs/1719_finite_spectrum_theorem.md.",
    873: "Now proved in Lean: transfer the E115 construction and check the six-element exclusion by an exhaustive BV/LRAT certificate.",
    115: "Now proved in Lean: cyclic seeds of orders 7, 13 and 25, products with Z/7, and invariant-subset extensions cover the missing orders. The A×Q entry in formula (12) needs a minus sign before f(y). See docs/quasigroup_spectra.md.",
    481: "Now proved in Lean: partial cyclic seeds of orders 11, 17, 29 and 53 and products with Z/7 cover multiples of three; loop models and checked small tables cover the other orders. See docs/quasigroup_spectra.md.",
    883: "The displayed statement in §3.1 is a lower bound, not an exact formula.",
    1313: "DISPUTED: §3.1 says cofiniteness is unknown; §3.8 asserts it. No cofiniteness theorem is asserted here.",
    1480: "Now proved in Lean: explicit four-point and five-point cores with indexed pairs give orders 4+2m and 5+2m. The existing certificates exclude 2 and 3. This resolves the note's contradictory inclusion of 3 in §3.1 in favor of its exclusion in §3.7. See docs/1480_finite_spectrum_theorem.md.",
    1485: "The note's squares-and-twice-squares conjecture is now proved in Lean by exact degree halving (2026-09-20). See Spectrum/WeakCentralSpectrum.lean and docs/1485_finite_spectrum_theorem.md. No SAT certificates or finite enumeration are used.",
    1486: "Orders 11, 13 and 21: explicit Matthew Bolan tables recovered from Zulip Austin pairs, messages 484348920 and 484345673 (2024-11-25), and checked in Lean.",
    1489: "Now proved in Lean: idempotent models at every order except 2 and 4, using explicit seven-group transversal designs, truncation and gluing, and kernel-checked seeds below 35. See docs/1489_finite_spectrum_theorem.md.",
}


def lean_set(values):
    return "{" + ", ".join(map(str, values)) + "}" if values else "∅"


def lower(i):
    if i == 63:
        return "positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}"
    finite = f"({lean_set(FINITE[i])} : Set ℕ)"
    return finite + (f" ∪ ({FAMILIES[i]})" if i in FAMILIES else "")
