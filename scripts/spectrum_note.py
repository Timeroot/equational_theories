"""Literal, conservative transcription of section 3 of spectrum-note.pdf.

Question marks are conjectures, never theorem specifications. Bounds at the
contradictory entries E1480 and E1313 are explained explicitly in NOTES.
This module is also used by the catalogue generator and witness search.
"""

EXACT = {
    2: "{1}", 66: "residues 3 {0, 1} {6}", 167: "residues 4 {0, 1} ∅",
    168: "squares", 474: "positiveExcept {2, 4}", 546: "sumTwoSquares",
    556: "sumTwoSquares", 695: "residues 3 {1, 2} {7}",
    887: "residues 3 {1, 2} {7}", 895: "powersTwo", 898: "powersTwo",
    1685: "positiveExcept {2}",
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
    115: [1, 5], 467: [1, 5, 7, 8], 481: [1, 7, 9, 12],
    501: [1, 4, 5, 8, 9], 667: [1, 7, 9], 670: [1, 4, 5],
    677: [1, 5, 7, 9, 11, 13, 16], 704: [1, 5, 7, 8],
    873: [1, 5], 883: [1, 7], 907: [1, 3, 7, 9, 13],
    1076: [1, 5], 1083: [1, 3, 4, 7, 8, 9], 1110: [1, 4, 5, 7, 8, 9],
    1279: [1, 5, 7, 8], 1286: [1, 7], 1313: [1, 5, 7],
    1480: [1, *range(4, 19)], 1483: [1, 2, 4, 8, 9], 1485: [1],
    1486: [1, 13, 21], 1489: [1, 3, *range(5, 22)],
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
    63: [2, 6, 10], 115: [2, 6], 467: [2, 3, 4, 6], 481: [3, 6],
    501: [2], 667: [3], 670: [2, 3, 6, 7], 677: [2],
    704: [2, 3, 4, 6, 9], 873: [2, 6], 883: [3], 907: [2, 4, 5, 6],
    1076: [2, 3, 4, 6, 7], 1083: [2], 1110: [2, 3, 6],
    1279: [2, 3, 4, 6, 9], 1286: [2, 3, 4, 5, 6], 1313: [2, 3, 4, 6],
    1480: [2, 3], 1483: [3, 5, 6, 7], 1485: [3], 1486: [2],
    1489: [2, 4], 1516: [2, 3, 4, 6], 1719: [2],
}
COFINITE = {63, 467, 670, 677, 704, 883, 1076, 1110, 1279, 1489, 1516}
# E1313: §3.1 says "not known to be cofinite", §3.8 asserts cofiniteness.
# Keep the claim visible as disputed, not as a theorem of the catalogue.
DISPUTED_COFINITE = {1313}
CONJECTURES = {
    115: "positiveExcept {2, 6}", 481: "positiveExcept {3, 6}",
    873: "positiveExcept {2, 6}", 1480: "positiveExcept {2, 3}",
    1485: "squares ∪ twiceSquares", 1489: "positiveExcept {2, 4}",
    1719: "positiveExcept {2}",
}
NOTES = {
    115: "§3.4.5 leaves the required cyclic partition as a TODO; the question mark in §3.1 is retained.",
    481: "§3.4.6 explicitly calls the proposed exact spectrum a conjecture.",
    883: "The displayed statement in §3.1 is a lower bound, not an exact formula.",
    1313: "DISPUTED: §3.1 says cofiniteness is unknown; §3.8 asserts it. No cofiniteness theorem is asserted here.",
    1480: "ERRATUM: §3.1 includes 3, whereas §3.7 excludes it. Kernel-checked exhaustive search excludes 3; use {1} ∪ [4,18].",
    1485: "Squares and twice-squares are proved lower bounds; equality is conjectural.",
    1489: "§3.8.1 asserts cofiniteness and an ATP check through 21; the exact formula remains conjectural.",
}


def lean_set(values):
    return "{" + ", ".join(map(str, values)) + "}" if values else "∅"


def lower(i):
    finite = f"({lean_set(FINITE[i])} : Set ℕ)"
    return finite + (f" ∪ ({FAMILIES[i]})" if i in FAMILIES else "")
