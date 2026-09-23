# Spectrum-note catalogue

Generated from `scripts/spectrum_note.py`; all orders below are positive.
The formulas are Lean-readable: `residues m R X` means residue in R modulo m, excluding X;
`positiveExcept X` means all positive integers except X. The square-set definitions are in
`Spectrum/Shapes.lean`. **A formula stated in the note is not necessarily a completed proof.**

Proof codes (checked against Lean dependencies): PROVED = complete; PROOF_AVAILABLE =
argument/citation/reported ATP result awaiting Lean; NOTE_GAP = a missing step in the note
has not been reconstructed; UNKNOWN = the exact spectrum is left mathematically open.
Reported ATP results do not imply that a certificate is bundled here.

| Representative | Exact spectrum / UNKNOWN lower bound | Conjecture | Cofinite claim | Exact proof |
| --- | --- | --- | --- | --- |
| 2 | `{1}` | `—` | — | PROVED |
| 63 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 66 | `residues 3 {0, 1} {6}` | `—` | — | PROVED |
| 73 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 115 | `positiveExcept {2, 6}` | `—` | — | PROVED |
| 118 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 125 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 167 | `residues 4 {0, 1} ∅` | `—` | — | PROVED |
| 168 | `squares` | `—` | — | PROVED |
| 467 | `UNKNOWN; contains ({1, 5, 7, 8} : Set ℕ) ∪ (oddSumTwoSquares)` | `—` | KNOWN | UNKNOWN |
| 474 | `positiveExcept {2, 4}` | `—` | — | PROVED |
| 481 | `positiveExcept {3, 6}` | `—` | — | PROVED |
| 501 | `UNKNOWN; contains ({1, 4, 5, 8, 9} : Set ℕ)` | `—` | UNKNOWN | UNKNOWN |
| 546 | `sumTwoSquares` | `—` | — | PROVED |
| 556 | `sumTwoSquares` | `—` | — | PROVED |
| 667 | `UNKNOWN; contains ({1, 7, 9} : Set ℕ) ∪ (residues 3 {1, 2} ∅)` | `—` | UNKNOWN | UNKNOWN |
| 670 | `UNKNOWN; contains ({1, 4, 5} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 677 | `UNKNOWN; contains ({1, 5, 7, 9, 11, 13, 16} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 695 | `residues 3 {1, 2} {7}` | `—` | — | PROVED |
| 704 | `UNKNOWN; contains ({1, 5, 7, 8} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 873 | `positiveExcept {2, 6}` | `—` | — | PROVED |
| 880 | `positiveExcept {2, 6}` | `—` | — | PROVED |
| 883 | `UNKNOWN; contains ({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)` | `—` | KNOWN | UNKNOWN |
| 887 | `residues 3 {1, 2} {7}` | `—` | — | PROVED |
| 895 | `powersTwo` | `—` | — | PROVED |
| 898 | `powersTwo` | `—` | — | PROVED |
| 907 | `UNKNOWN; contains ({1, 3, 7, 9, 13} : Set ℕ)` | `—` | UNKNOWN | UNKNOWN |
| 1076 | `UNKNOWN; contains ({1, 5} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1083 | `UNKNOWN; contains ({1, 3, 4, 7, 8, 9} : Set ℕ)` | `—` | UNKNOWN | UNKNOWN |
| 1110 | `UNKNOWN; contains ({1, 4, 5, 7, 8, 9} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1279 | `UNKNOWN; contains ({1, 5, 7, 8} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1286 | `UNKNOWN; contains ({1, 7} : Set ℕ)` | `—` | UNKNOWN | UNKNOWN |
| 1313 | `UNKNOWN; contains ({1, 5, 7} : Set ℕ)` | `—` | DISPUTED | UNKNOWN |
| 1323 | `UNKNOWN; contains ({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)` | `—` | KNOWN | UNKNOWN |
| 1480 | `positiveExcept {2, 3}` | `—` | — | PROVED |
| 1483 | `UNKNOWN; contains ({1, 2, 4, 8, 9} : Set ℕ) ∪ (squares)` | `—` | UNKNOWN | UNKNOWN |
| 1485 | `squares ∪ twiceSquares` | `—` | — | PROVED |
| 1486 | `UNKNOWN; contains ({1, 11, 13, 21} : Set ℕ) ∪ (squares ∪ shiftedSquares)` | `—` | UNKNOWN | UNKNOWN |
| 1489 | `positiveExcept {2, 4}` | `—` | — | PROVED |
| 1496 | `positiveExcept {3, 6}` | `—` | — | PROVED |
| 1516 | `UNKNOWN; contains ({1, 5, 7, 8} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1526 | `UNKNOWN; contains ({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)` | `—` | KNOWN | UNKNOWN |
| 1685 | `positiveExcept {2}` | `—` | — | PROVED |
| 1692 | `UNKNOWN; contains ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)` | `—` | KNOWN | UNKNOWN |
| 1719 | `positiveExcept {2}` | `—` | — | PROVED |

## Draft ambiguities

- E1719: Now proved in Lean: a Bose construction with two shared points gives orders 3m+2 from idempotent Latin squares; Mendelsohn models and checked tables at 6 and 8 cover the rest. The squaring-map argument excludes order 2. See docs/1719_finite_spectrum_theorem.md.
- E873: Now proved in Lean: transfer the E115 construction and check the six-element exclusion by an exhaustive BV/LRAT certificate.
- E115: Now proved in Lean: cyclic seeds of orders 7, 13 and 25, products with Z/7, and invariant-subset extensions cover the missing orders. The A×Q entry in formula (12) needs a minus sign before f(y). See docs/quasigroup_spectra.md.
- E481: Now proved in Lean: partial cyclic seeds of orders 11, 17, 29 and 53 and products with Z/7 cover multiples of three; loop models and checked small tables cover the other orders. See docs/quasigroup_spectra.md.
- E883: The displayed statement in §3.1 is a lower bound, not an exact formula.
- E1313: DISPUTED: §3.1 says cofiniteness is unknown; §3.8 asserts it. No cofiniteness theorem is asserted here.
- E1480: Now proved in Lean: explicit four-point and five-point cores with indexed pairs give orders 4+2m and 5+2m. The existing certificates exclude 2 and 3. This resolves the note's contradictory inclusion of 3 in §3.1 in favor of its exclusion in §3.7. See docs/1480_finite_spectrum_theorem.md.
- E1485: The note's squares-and-twice-squares conjecture is now proved in Lean by exact degree halving (2026-09-20). See Spectrum/WeakCentralSpectrum.lean and docs/1485_finite_spectrum_theorem.md. No SAT certificates or finite enumeration are used.
- E1486: Orders 11, 13 and 21: explicit Matthew Bolan tables recovered from Zulip Austin pairs, messages 484348920 and 484345673 (2024-11-25), and checked in Lean.
- E1489: Now proved in Lean: idempotent models at every order except 2 and 4, using explicit seven-group transversal designs, truncation and gluing, and kernel-checked seeds below 35. See docs/1489_finite_spectrum_theorem.md.

The JSON index covers all 4694 laws, not just these representatives. Every non-full law
has a Lean-checked spectrum equality with its representative (or a singleton proof).
Question-marked source claims require an independent proof before an exact theorem is emitted.
