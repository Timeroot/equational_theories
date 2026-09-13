# Spectrum-note catalogue

Generated from `scripts/spectrum_note.py`; all orders below are positive.
The formulas are Lean-readable: `residues m R X` means residue in R modulo m, excluding X;
`positiveExcept X` means all positive integers except X. The square-set definitions are in
`Spectrum/Shapes.lean`. **Known formula does not mean completed Lean proof**: see the proof column.

| Representative | Exact spectrum / UNKNOWN lower bound | Conjecture | Cofinite claim | Exact proof |
| --- | --- | --- | --- | --- |
| 2 | `{1}` | `—` | — | PROVED |
| 63 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 66 | `residues 3 {0, 1} {6}` | `—` | — | DEFERRED |
| 73 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 115 | `UNKNOWN; contains ({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})` | `positiveExcept {2, 6}` | UNKNOWN | UNKNOWN |
| 118 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 125 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 167 | `residues 4 {0, 1} ∅` | `—` | — | DEFERRED |
| 168 | `squares` | `—` | — | DEFERRED |
| 467 | `UNKNOWN; contains ({1, 5, 7, 8} : Set ℕ) ∪ (oddSumTwoSquares)` | `—` | KNOWN | UNKNOWN |
| 474 | `positiveExcept {2, 4}` | `—` | — | PROVED |
| 481 | `UNKNOWN; contains ({1, 7, 9, 12} : Set ℕ) ∪ (residues 3 {1, 2} {7})` | `positiveExcept {3, 6}` | UNKNOWN | UNKNOWN |
| 501 | `UNKNOWN; contains ({1, 4, 5, 8, 9} : Set ℕ)` | `—` | UNKNOWN | UNKNOWN |
| 546 | `sumTwoSquares` | `—` | — | DEFERRED |
| 556 | `sumTwoSquares` | `—` | — | DEFERRED |
| 667 | `UNKNOWN; contains ({1, 7, 9} : Set ℕ) ∪ (residues 3 {1, 2} ∅)` | `—` | UNKNOWN | UNKNOWN |
| 670 | `UNKNOWN; contains ({1, 4, 5} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 677 | `UNKNOWN; contains ({1, 5, 7, 9, 11, 13, 16} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 695 | `residues 3 {1, 2} {7}` | `—` | — | DEFERRED |
| 704 | `UNKNOWN; contains ({1, 5, 7, 8} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 873 | `UNKNOWN; contains ({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})` | `positiveExcept {2, 6}` | UNKNOWN | UNKNOWN |
| 880 | `UNKNOWN; contains ({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})` | `positiveExcept {2, 6}` | UNKNOWN | UNKNOWN |
| 883 | `UNKNOWN; contains ({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)` | `—` | KNOWN | UNKNOWN |
| 887 | `residues 3 {1, 2} {7}` | `—` | — | DEFERRED |
| 895 | `powersTwo` | `—` | — | DEFERRED |
| 898 | `powersTwo` | `—` | — | DEFERRED |
| 907 | `UNKNOWN; contains ({1, 3, 7, 9, 13} : Set ℕ)` | `—` | UNKNOWN | UNKNOWN |
| 1076 | `UNKNOWN; contains ({1, 5} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1083 | `UNKNOWN; contains ({1, 3, 4, 7, 8, 9} : Set ℕ)` | `—` | UNKNOWN | UNKNOWN |
| 1110 | `UNKNOWN; contains ({1, 4, 5, 7, 8, 9} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1279 | `UNKNOWN; contains ({1, 5, 7, 8} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1286 | `UNKNOWN; contains ({1, 7} : Set ℕ)` | `—` | UNKNOWN | UNKNOWN |
| 1313 | `UNKNOWN; contains ({1, 5, 7} : Set ℕ)` | `—` | DISPUTED | UNKNOWN |
| 1323 | `UNKNOWN; contains ({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)` | `—` | KNOWN | UNKNOWN |
| 1480 | `UNKNOWN; contains ({1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} : Set ℕ) ∪ (squares)` | `positiveExcept {2, 3}` | UNKNOWN | UNKNOWN |
| 1483 | `UNKNOWN; contains ({1, 2, 4, 8, 9} : Set ℕ) ∪ (squares)` | `—` | UNKNOWN | UNKNOWN |
| 1485 | `UNKNOWN; contains ({1} : Set ℕ) ∪ (squares ∪ twiceSquares)` | `squares ∪ twiceSquares` | UNKNOWN | UNKNOWN |
| 1486 | `UNKNOWN; contains ({1, 13, 21} : Set ℕ) ∪ (squares ∪ shiftedSquares)` | `—` | UNKNOWN | UNKNOWN |
| 1489 | `UNKNOWN; contains ({1, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} : Set ℕ)` | `positiveExcept {2, 4}` | KNOWN | UNKNOWN |
| 1496 | `UNKNOWN; contains ({1, 7, 9, 12} : Set ℕ) ∪ (residues 3 {1, 2} {7})` | `positiveExcept {3, 6}` | UNKNOWN | UNKNOWN |
| 1516 | `UNKNOWN; contains ({1, 5, 7, 8} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1526 | `UNKNOWN; contains ({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)` | `—` | KNOWN | UNKNOWN |
| 1685 | `positiveExcept {2}` | `—` | — | PROVED |
| 1692 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1719 | `UNKNOWN; contains ({1, 5, 6, 8} : Set ℕ) ∪ (residues 3 {0, 1} ∅)` | `positiveExcept {2}` | UNKNOWN | UNKNOWN |

## Draft ambiguities

- E115: §3.4.5 leaves the required cyclic partition as a TODO; the question mark in §3.1 is retained.
- E481: §3.4.6 explicitly calls the proposed exact spectrum a conjecture.
- E883: The displayed statement in §3.1 is a lower bound, not an exact formula.
- E1313: DISPUTED: §3.1 says cofiniteness is unknown; §3.8 asserts it. No cofiniteness theorem is asserted here.
- E1480: ERRATUM: §3.1 includes 3, whereas §3.7 excludes it. Kernel-checked exhaustive search excludes 3; use {1} ∪ [4,18].
- E1485: Squares and twice-squares are proved lower bounds; equality is conjectural.
- E1489: §3.8.1 asserts cofiniteness and an ATP check through 21; the exact formula remains conjectural.

The JSON index covers all 4694 laws, not just these representatives. Every non-full law
has a Lean-checked spectrum equality with its representative (or a singleton proof).
No exact-spectrum theorem is emitted for a question-marked or UNKNOWN entry.
