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
| 63 | `UNKNOWN; contains positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}` | `—` | KNOWN | UNKNOWN |
| 66 | `residues 3 {0, 1} {6}` | `—` | — | PROVED |
| 73 | `UNKNOWN; contains positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}` | `—` | KNOWN | UNKNOWN |
| 115 | `positiveExcept {2, 6}` | `—` | — | PROVED |
| 118 | `UNKNOWN; contains positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}` | `—` | KNOWN | UNKNOWN |
| 125 | `UNKNOWN; contains positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}` | `—` | KNOWN | UNKNOWN |
| 167 | `residues 4 {0, 1} ∅` | `—` | — | PROVED |
| 168 | `squares` | `—` | — | PROVED |
| 467 | `UNKNOWN; contains (({1, 5, 7, 8, 11, 13} : Set ℕ) ∪ (oddSumTwoSquares)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 123, 128, 131, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 299, 300, 303, 339, 340, 346, 349, 355, 356, 358, 377, 387, 422, 426, 439, 443, 487, 499, 508, 516, 520, 534, 538, 542, 543, 548, 559, 587, 611, 615, 674, 688, 717, 723, 755, 807, 811, 843, 863, 867, 895, 923, 927, 933, 1017, 1108, 1203, 1207, 1227}) ∪ cubes` | `—` | KNOWN | UNKNOWN |
| 474 | `positiveExcept {2, 4}` | `—` | — | PROVED |
| 481 | `positiveExcept {3, 6}` | `—` | — | PROVED |
| 501 | `residues 4 {0, 1} ∅` | `—` | — | PROVED |
| 546 | `sumTwoSquares` | `—` | — | PROVED |
| 556 | `sumTwoSquares` | `—` | — | PROVED |
| 667 | `UNKNOWN; contains positiveExcept {3, 6, 12, 15, 24, 30, 39, 48, 51, 60, 75, 87, 96, 102, 123, 159, 174, 195, 219, 303, 339, 543, 615, 717, 723, 807, 843, 867, 933, 1203, 1227}` | `—` | KNOWN | UNKNOWN |
| 670 | `UNKNOWN; contains ({1, 4, 5, 9, 11} : Set ℕ) ∪ (fourthPowers)` | `—` | KNOWN | UNKNOWN |
| 677 | `UNKNOWN; contains ({1, 5, 7, 9, 11, 13, 16, 19, 80, 6487, 6493, 6499} : Set ℕ) ∪ (fourthPowers)` | `—` | KNOWN | UNKNOWN |
| 695 | `residues 3 {1, 2} {7}` | `—` | — | PROVED |
| 704 | `UNKNOWN; contains (({1, 5, 7, 8, 11, 13} : Set ℕ)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 123, 128, 131, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 299, 300, 303, 339, 340, 346, 349, 355, 356, 358, 377, 387, 422, 426, 439, 443, 487, 499, 508, 516, 520, 534, 538, 542, 543, 548, 559, 587, 611, 615, 674, 688, 717, 723, 755, 807, 811, 843, 863, 867, 895, 923, 927, 933, 1017, 1108, 1203, 1207, 1227}) ∪ cubes` | `—` | KNOWN | UNKNOWN |
| 873 | `positiveExcept {2, 6}` | `—` | — | PROVED |
| 880 | `positiveExcept {2, 6}` | `—` | — | PROVED |
| 883 | `UNKNOWN; contains positiveExcept {3, 6, 9, 12, 15, 18, 24, 30, 39, 48, 51, 60, 75, 87, 96, 99, 102, 123, 153, 159, 174, 195, 207, 219, 303, 339, 387, 543, 615, 717, 723, 807, 843, 867, 927, 933, 1017, 1203, 1227}` | `—` | KNOWN | UNKNOWN |
| 887 | `residues 3 {1, 2} {7}` | `—` | — | PROVED |
| 895 | `powersTwo` | `—` | — | PROVED |
| 898 | `powersTwo` | `—` | — | PROVED |
| 907 | `UNKNOWN; contains ({1, 3, 7, 9, 11, 13, 23} : Set ℕ)` | `—` | UNKNOWN | UNKNOWN |
| 1076 | `UNKNOWN; contains (({1, 5, 13, 16, 17, 19, 23, 25, 31, 43, 47, 53, 59, 67, 71, 73, 79, 80, 81} : Set ℕ) ∪ (fourthPowers)) ∪ quarticTailSeeds ∪ Set.Ici 107773` | `—` | KNOWN | UNKNOWN |
| 1083 | `UNKNOWN; contains ({1, 3, 4, 7, 8, 9, 11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 50, 53, 61, 67, 73, 79, 113, 470, 1008, 1009, 1017083} : Set ℕ) ∪ (squares ∪ commonPointSquareOrders ∪ designPairOrders)` | `—` | KNOWN | UNKNOWN |
| 1110 | `UNKNOWN; contains (({1, 4, 5, 7, 8, 9, 11} : Set ℕ) ∪ (squares)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 123, 128, 131, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 299, 300, 303, 339, 340, 346, 349, 355, 356, 358, 377, 387, 422, 426, 439, 443, 487, 499, 508, 516, 520, 534, 538, 542, 543, 548, 559, 587, 611, 615, 674, 688, 717, 723, 755, 807, 811, 843, 863, 867, 895, 923, 927, 933, 1017, 1108, 1203, 1207, 1227}) ∪ cubes` | `—` | KNOWN | UNKNOWN |
| 1279 | `UNKNOWN; contains (({1, 5, 7, 8, 11} : Set ℕ)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 123, 128, 131, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 299, 300, 303, 339, 340, 346, 349, 355, 356, 358, 377, 387, 422, 426, 439, 443, 487, 499, 508, 516, 520, 534, 538, 542, 543, 548, 559, 587, 611, 615, 674, 688, 717, 723, 755, 807, 811, 843, 863, 867, 895, 923, 927, 933, 1017, 1108, 1203, 1207, 1227}) ∪ cubes` | `—` | KNOWN | UNKNOWN |
| 1286 | `UNKNOWN; contains ({1, 7, 9, 11, 13, 17, 19, 23, 29, 31, 32, 37, 43, 47, 53, 59, 67, 71, 73, 79, 113, 218, 1008, 1009, 1898, 1017083} : Set ℕ) ∪ (fourthPowers ∪ commonPointFourthOrders ∪ binaryPointFourthOrders ∪ designPairOrders)` | `—` | KNOWN | UNKNOWN |
| 1313 | `UNKNOWN; contains (({1, 5, 7, 13, 16, 17, 19, 23, 25, 31, 43, 47, 53, 59, 67, 71, 73, 79, 80, 81} : Set ℕ) ∪ (fourthPowers)) ∪ quarticTailSeeds ∪ Set.Ici 107773` | `—` | KNOWN | UNKNOWN |
| 1323 | `UNKNOWN; contains positiveExcept {3, 6, 9, 12, 15, 18, 24, 30, 39, 48, 51, 60, 75, 87, 96, 99, 102, 123, 153, 159, 174, 195, 207, 219, 303, 339, 387, 543, 615, 717, 723, 807, 843, 867, 927, 933, 1017, 1203, 1227}` | `—` | KNOWN | UNKNOWN |
| 1480 | `positiveExcept {2, 3}` | `—` | — | PROVED |
| 1483 | `UNKNOWN; contains ({1, 2, 4, 8, 9} : Set ℕ) ∪ (squares ∪ twiceSquares)` | `—` | UNKNOWN | UNKNOWN |
| 1485 | `squares ∪ twiceSquares` | `—` | — | PROVED |
| 1486 | `UNKNOWN; contains positiveExcept {2, 3, 5, 6, 7, 8, 10, 12, 14, 15, 17, 26}` | `—` | KNOWN | UNKNOWN |
| 1489 | `positiveExcept {2, 4}` | `—` | — | PROVED |
| 1496 | `positiveExcept {3, 6}` | `—` | — | PROVED |
| 1516 | `UNKNOWN; contains (({1, 5, 7, 8, 9, 11, 13} : Set ℕ)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 123, 128, 131, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 299, 300, 303, 339, 340, 346, 349, 355, 356, 358, 377, 387, 422, 426, 439, 443, 487, 499, 508, 516, 520, 534, 538, 542, 543, 548, 559, 587, 611, 615, 674, 688, 717, 723, 755, 807, 811, 843, 863, 867, 895, 923, 927, 933, 1017, 1108, 1203, 1207, 1227}) ∪ cubes` | `—` | KNOWN | UNKNOWN |
| 1526 | `UNKNOWN; contains positiveExcept {3, 6, 9, 12, 15, 18, 24, 30, 39, 48, 51, 60, 75, 87, 96, 99, 102, 123, 153, 159, 174, 195, 207, 219, 303, 339, 387, 543, 615, 717, 723, 807, 843, 867, 927, 933, 1017, 1203, 1227}` | `—` | KNOWN | UNKNOWN |
| 1685 | `positiveExcept {2}` | `—` | — | PROVED |
| 1692 | `UNKNOWN; contains positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}` | `—` | KNOWN | UNKNOWN |
| 1719 | `positiveExcept {2}` | `—` | — | PROVED |

## Draft ambiguities

- E501: Now proved in Lean: squaring the left translations gives a semisymmetric quasigroup, whose pair permutation forces order 0 or 1 modulo 4. Square roots of reflections on Z/(4k+1) and Z/2 × Z/(2k) construct every allowed order. No exceptional orders or finite certificates are needed. See docs/501_finite_spectrum_theorem.md.
- E63: Constructive Lean lower bound: all positive orders outside {2,6,10,14,18,26,30,38,42,90,158}. The tail starts at 159. Orders 2 and 6 are excluded in Lean; exclusions at 10 and 14 remain explicitly admitted. Bennett (1989) claims order 90, but Lean now refutes its stated intermediate construction: the singular 16-model cannot contain a 5-subquasigroup. Existence at 90 remains unresolved; this is not a nonexistence proof. See docs/63_order90.md and docs/63_lean_spectrum.md.
- E1719: Now proved in Lean: a Bose construction with two shared points gives orders 3m+2 from idempotent Latin squares; Mendelsohn models and checked tables at 6 and 8 cover the rest. The squaring-map argument excludes order 2. See docs/1719_finite_spectrum_theorem.md.
- E873: Now proved in Lean: transfer the E115 construction and check the six-element exclusion by an exhaustive BV/LRAT certificate.
- E115: Now proved in Lean: cyclic seeds of orders 7, 13 and 25, products with Z/7, and invariant-subset extensions cover the missing orders. The A×Q entry in formula (12) needs a minus sign before f(y). See docs/quasigroup_spectra.md.
- E481: Now proved in Lean: partial cyclic seeds of orders 11, 17, 29 and 53 and products with Z/7 cover multiples of three; loop models and checked small tables cover the other orders. See docs/quasigroup_spectra.md.
- E667: Constructive cofinite Lean bound with cutoff 1228; finite-field transversal designs, idempotent E63 constructions, loops, and products leave 29 unresolved orders below that cutoff. Orders 3 and 6 are excluded in Lean. See docs/667_883_spectrum_progress.md.
- E883: Constructive cofinite Lean bound with cutoff 1228; finite-field transversal designs, idempotent E63 transfer, loops, and products leave 36 unresolved orders. Orders 3,6,9 are excluded in Lean. The order-9 proof checks all 66 nonidentity canonical row forms after exhaustive permutation normalization. The same bounds transfer to E1323, E1526, and their duals. See docs/667_883_spectrum_progress.md.
- E467: Cofiniteness is now proved in Lean with cutoff 1228, by idempotent E63 transfer. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.
- E704: Cofiniteness is now proved in Lean with cutoff 1228, by idempotent E63 left division. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.
- E1110: All squares are constructed in Lean using the Fibonacci companion operator. Cofiniteness is proved in Lean with cutoff 1228, by idempotent E63 left division. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.
- E1279: Cofiniteness is now proved in Lean with cutoff 1228, by the opposite of idempotent E63 left division. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.
- E1516: Cofiniteness is now proved in Lean with cutoff 1228, by idempotent E63 transfer. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.
- E670: All positive fourth-power orders are constructed in Lean. Cofiniteness has a complete pen-and-paper argument using idempotent finite-field models of orders 9,11,16 and Wilson's PBD theorem; the design theorem is not formalized. See docs/open_spectra_survey_20260927.md.
- E1076: Every order at least 107773 now has an idempotent model in Lean, by explicit finite-field seeds, transversal-design gluing, and an arithmetic induction. The construction uses no Wilson theorem or model tables at large orders. All fourth powers and many smaller orders are also constructed. The exact spectrum below the cutoff remains open. See docs/quartic_cofinite_20260928.md.
- E1313: Every order at least 107773 now has an idempotent model in Lean, by explicit finite-field seeds, transversal-design gluing, and an arithmetic induction. The construction uses no Wilson theorem or model tables at large orders. All fourth powers and many smaller orders are also constructed. The exact spectrum below the cutoff remains open. See docs/quartic_cofinite_20260928.md.
- E907: Finite-field seeds and Wilson's PBD theorem give every sufficiently large odd order, by a pen-and-paper proof. Even-order models remain unresolved beyond the checked exclusions. See docs/open_spectra_survey_20260927.md.
- E1083: Lean constructions include all squares, 119*(30t+2)^2-6 for t>=0 (starting at 470), and 1008*1009^(t+1)+11 (starting at 1017083). Common-point gluing also proves orders 50 and 113. Both new families fill infinitely many orders 2 mod3 and use symbolic proofs. Cofiniteness is proved in Lean, including PBD existence for block sizes 7,9,16, CRT, and gluing. Only finitely many orders remain undecided, but no numerical cutoff has been extracted. See docs/strong_design_cofiniteness_20260928.md.
- E1286: Lean constructions include all fourth powers, 119*(30t+2)^4-6 and 224*(30t+1)^4-6 for t>=0 (starting at 1898 and 218), and 1008*1009^(t+1)+11 (starting at 1017083). These fill infinitely many orders 2 mod3. Order 32 is proved by two 5-by-5 matrix coefficient checks; common-point gluing also gives 113. Cofiniteness is proved in Lean using the shared PBD existence theorem for block sizes 7,9,16 and arbitrary group fillings. Only finitely many orders remain undecided, but no numerical cutoff has been extracted. See docs/strong_design_cofiniteness_20260928.md.
- E677: All fourth powers and models at 6487,6493,6499 have symbolic Lean proofs, with no large tables or exhaustive pair checks. Cofiniteness is proved in Lean, including PBD existence for block sizes 5,11,16 and the extension from residues 0,1 mod5 to all residues. Only finitely many orders remain undecided, but no numerical cutoff has been extracted. See docs/strong_design_cofiniteness_20260928.md.
- E1480: Now proved in Lean: explicit four-point and five-point cores with indexed pairs give orders 4+2m and 5+2m. The existing certificates exclude 2 and 3. This resolves the note's contradictory inclusion of 3 in §3.1 in favor of its exclusion in §3.7. See docs/1480_finite_spectrum_theorem.md.
- E1485: The note's squares-and-twice-squares conjecture is now proved in Lean by exact degree halving (2026-09-20). See Spectrum/WeakCentralSpectrum.lean and docs/1485_finite_spectrum_theorem.md. No SAT certificates or finite enumeration are used.
- E1483: The Lean lower bound includes all squares and twice-squares; the exact spectrum remains open. Orders 3,5,6,7,10 are excluded in Lean. The constant-row subclass has exactly power-of-two orders, proved by cubic untwisting into E1485; a bijective row gives the same restriction. Uniform rank r at order r^2 forces E168. Order 11 remains a separately documented external exclusion with an admitted Lean declaration. See docs/1483_spectrum_progress.md and docs/1483_projector_followup.md.
- E1486: Constructive Lean lower bound: every order at least 27, plus {1,4,9,11,13,16,18,19,20,21,22,23,24,25}. Graph splitting supplies the general tail and checked matching certificates bridge small gaps. Orders 2,3,5,6,7,8 are excluded in Lean; only 10,12,14,15,17,26 remain unresolved. See docs/1486_graph_spectrum.md.
- E1489: Now proved in Lean: idempotent models at every order except 2 and 4, using explicit seven-group transversal designs, truncation and gluing, and kernel-checked seeds below 35. See docs/1489_finite_spectrum_theorem.md.

The JSON index covers all 4694 laws, not just these representatives. Every non-full law
has a Lean-checked spectrum equality with its representative (or a singleton proof).
Question-marked source claims require an independent proof before an exact theorem is emitted.
