"""Conservative transcription of section 3 of spectrum-note.pdf, with cited supplements.

Question marks are conjectures, never theorem specifications. Bounds at the
contradictory entries E1480 and E1313 are explained explicitly in NOTES.
This module is also used by the catalogue generator and witness search.
"""

EXACT = {
    115: "positiveExcept {2, 6}", 873: "positiveExcept {2, 6}", 880: "positiveExcept {2, 6}",
    481: "positiveExcept {3, 6}", 1496: "positiveExcept {3, 6}",
    2: "{1}", 66: "residues 3 {0, 1} {6}", 167: "residues 4 {0, 1} ∅",
    501: "residues 4 {0, 1} ∅",
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
    1480: "squares", 1483: "squares ∪ twiceSquares", 1485: "squares ∪ twiceSquares",
    1486: "squares ∪ shiftedSquares", 1719: "residues 3 {0, 1} ∅",
    1083: "squares ∪ commonPointSquareOrders ∪ designPairOrders", 1110: "squares",
    670: "fourthPowers", 677: "fourthPowers", 1076: "fourthPowers",
    1286: "fourthPowers ∪ commonPointFourthOrders ∪ binaryPointFourthOrders ∪ designPairOrders", 1313: "fourthPowers",
}
SUPPLEMENTAL_MODELS = {
    (1516, 9): "OpenWitnesses.model_1516_9",
    (1286, 9): "OpenWitnesses.model_1286_9",
    (670, 9): "OpenWitnesses.model_670_9",
    (1076, 19): "OpenWitnesses.model_1076_19",
    (1313, 19): "OpenWitnesses.model_1313_19",
    (907, 23): "OpenWitnesses.model_907_23",
    (677, 19): "E677.model19",
    (677, 80): "E677.model80",
    (677, 6487): "E677.model6487",
    (677, 6493): "E677.model6493",
    (677, 6499): "E677.model6499",
    **{(law, n): f"E1083E1286.model_{law}_{n}"
       for law in (1083, 1286) for n in (11, 17, 113, 1008, 1009, 1017083)},
    (1083, 50): "E1083E1286.model_1083_50",
    (1083, 470): "E1083E1286.model_1083_470",
    (1286, 1898): "E1083E1286.model_1286_1898",
    (1286, 32): "E1083E1286.BinarySeed.model32",
    (1286, 218): "E1083E1286.BinarySeed.model218",
}
SUPPLEMENTAL_MODELS.update({
    (law, n): f"E1083E1286.PrimeSeeds.model_{law}_{n}"
    for law, orders in {
        1083: (19, 23, 29, 31, 37, 43, 47, 53, 61, 67, 73, 79),
        1286: (19, 23, 29, 31, 37, 43, 47, 53, 59, 67, 71, 73, 79),
    }.items() for n in orders
})
SUPPLEMENTAL_MODELS.update({
    (law, n): f"QuarticTail.small_{law}_{n}"
    for law in (1076, 1313)
    for n in (13, 16, 17, 23, 25, 31, 43, 47, 53, 59, 67, 71, 73, 79, 80, 81)
})
# These existing external claims are linked directly, outside the small-order basis.
EXTERNAL_EXCLUSIONS = {(1483, 11)}
DIRECT_EXCLUSIONS = {(677, 3), (677, 4), (907, 8), (1083, 5), (1083, 6)} | EXTERNAL_EXCLUSIONS

# Complete computer-assisted arguments whose finite certificates await Lean.
# Keep these separate from TAILS, which generates numerical Lean theorems.
REPORTED_TAILS = {
    677: {
        "cutoff": 42239519,
        "status": "PROVED_UNFORMALIZED",
        "kind": "Computer-assisted construction",
        "proof_sketch": (
            "Linear operations over finite rings provide small seed models. Products and "
            "transversal designs (blocks that connect different groups of points) combine "
            "them into larger models. Checked construction certificates cover every order "
            "from 42,239,519 through 500,000,000. Beyond this interval, a weighted integer "
            "sieve chooses a suitable group size q and a certified hole size r so that "
            "n = 80q + r. Gluing with idempotent block models of sizes 80 and 81 then "
            "completes a strong induction. The general sieve and induction are in Lean; "
            "the concrete construction and weight certificates await Lean verification."
        ),
        "source": {"file": "docs/e677_effective_bound_20260929.md", "line": 1,
                   "name": "Effective bound and certificate"},
    },
    **{law: {
        "cutoff": cutoff,
        "status": "PROVED_UNFORMALIZED",
        "kind": "Computer-assisted construction",
        "proof_sketch": (
            "Linear operations over finite rings provide seed models; products and "
            "transversal designs combine them into larger ones. Compressed construction "
            f"certificates cover every order from {cutoff:,} through {endpoint:,}. "
            "An exact integer sieve shows that every interval of 22,000 integers contains "
            "a suitable group size q for a transversal design. Every larger order can "
            "then be written as 1008q + r, with a certified hole size r and q smaller than "
            "the target order. Gluing with idempotent block models of sizes 1008 and 1009 "
            "completes a strong induction. The general induction is in Lean; the finite "
            "construction certificates and numerical sieve counts await Lean verification."
        ),
        "source": {"file": "docs/1083_1286_effective_tails_20260930.md", "line": 1,
                   "name": "Effective tail and construction certificate"},
    } for law, cutoff, endpoint in ((1083, 246119111, 280000000000),
                                   (1286, 4222119949, 5000000000000))},
}
DUPONT_FAMILIES = {467, 704, 1110, 1279, 1516}
TAILS = {63: 159, 667: 1228, 883: 1228, 1486: 27, 1076: 107773, 1313: 107773,
         **{i: 1228 for i in DUPONT_FAMILIES}}
EXCLUDED = {
    63: [2, 6, 10, 14], 115: [2, 6], 467: [2, 3, 4, 6], 481: [3, 6],
    501: [2], 667: [3, 6], 670: [2, 3, 6, 7], 677: [2, 3, 4],
    704: [2, 3, 4, 6, 9], 873: [2, 6], 883: [3, 6, 9], 907: [2, 4, 5, 6, 8],
    1076: [2, 3, 4, 6, 7], 1083: [2, 5, 6], 1110: [2, 3, 6],
    1279: [2, 3, 4, 6, 9], 1286: [2, 3, 4, 5, 6], 1313: [2, 3, 4, 6],
    # E1485 orders 11/13: now proved by WeakCentralCardinality, beyond the PDF.
    1480: [2, 3], 1483: [3, 5, 6, 7, 10, 11], 1485: [3, 11, 13], 1486: [2, 3, 5, 6, 7, 8],
    1489: [2, 4], 1516: [2, 3, 4, 6], 1719: [2],
}
COFINITE = {63, 467, 667, 670, 677, 704, 883, 1076, 1083, 1110, 1279, 1286, 1313, 1486, 1489, 1516}
# E1313's source conflict is resolved by the explicit quartic cofinite construction.
DISPUTED_COFINITE = set()
CONJECTURES = {}
NOTES = {
    501: "Now proved in Lean: squaring the left translations gives a semisymmetric quasigroup, whose pair permutation forces order 0 or 1 modulo 4. Square roots of reflections on Z/(4k+1) and Z/2 × Z/(2k) construct every allowed order. No exceptional orders or finite certificates are needed. See docs/501_finite_spectrum_theorem.md.",
    63: "Constructive Lean lower bound: all positive orders outside {2,6,10,14,18,26,30,38,42,90,158}. The tail starts at 159. Orders 2 and 6 are excluded in Lean; exclusions at 10 and 14 remain explicitly admitted. Bennett (1989) claims order 90, but Lean now refutes its stated intermediate construction: the singular 16-model cannot contain a 5-subquasigroup. Existence at 90 remains unresolved; this is not a nonexistence proof. See docs/63_order90.md and docs/63_lean_spectrum.md.",
    1719: "Now proved in Lean: a Bose construction with two shared points gives orders 3m+2 from idempotent Latin squares; Mendelsohn models and checked tables at 6 and 8 cover the rest. The squaring-map argument excludes order 2. See docs/1719_finite_spectrum_theorem.md.",
    873: "Now proved in Lean: transfer the E115 construction and check the six-element exclusion by an exhaustive BV/LRAT certificate.",
    115: "Now proved in Lean: cyclic seeds of orders 7, 13 and 25, products with Z/7, and invariant-subset extensions cover the missing orders. The A×Q entry in formula (12) needs a minus sign before f(y). See docs/quasigroup_spectra.md.",
    481: "Now proved in Lean: partial cyclic seeds of orders 11, 17, 29 and 53 and products with Z/7 cover multiples of three; loop models and checked small tables cover the other orders. See docs/quasigroup_spectra.md.",
    667: "Constructive cofinite Lean bound with cutoff 1228; finite-field transversal designs, idempotent E63 constructions, loops, and products leave 29 unresolved orders below that cutoff. Orders 3 and 6 are excluded in Lean. See docs/667_883_spectrum_progress.md.",
    883: "Constructive cofinite Lean bound with cutoff 1228; finite-field transversal designs, idempotent E63 transfer, loops, and products leave 36 unresolved orders. Orders 3,6,9 are excluded in Lean. The order-9 proof checks all 66 nonidentity canonical row forms after exhaustive permutation normalization. The same bounds transfer to E1323, E1526, and their duals. See docs/667_883_spectrum_progress.md.",
    467: "Cofiniteness is now proved in Lean with cutoff 1228, by idempotent E63 transfer. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.",
    704: "Cofiniteness is now proved in Lean with cutoff 1228, by idempotent E63 left division. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.",
    1110: "All squares are constructed in Lean using the Fibonacci companion operator. Cofiniteness is proved in Lean with cutoff 1228, by idempotent E63 left division. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.",
    1279: "Cofiniteness is now proved in Lean with cutoff 1228, by the opposite of idempotent E63 left division. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.",
    1516: "Cofiniteness is now proved in Lean with cutoff 1228, by idempotent E63 transfer. The exact spectrum remains open. See docs/open_spectra_survey_20260927.md.",
    670: "Cofiniteness is now proved in Lean, with idempotent models at every sufficiently large order. Seeds 9,11,16 give design periods 72,110,240 with gcd 2; the singleton and the 16-point seed cover both parity classes. The required design existence is proved constructively, without assuming Wilson's general theorem. No numerical cutoff has been extracted. See docs/670_907_spectrum_progress_20260930.md.",
    1076: "Every order at least 107773 now has an idempotent model in Lean, by explicit finite-field seeds, transversal-design gluing, and an arithmetic induction. The construction uses no Wilson theorem or model tables at large orders. All fourth powers and many smaller orders are also constructed. The exact spectrum below the cutoff remains open. See docs/quartic_cofinite_20260928.md.",
    1313: "Every order at least 107773 now has an idempotent model in Lean, by explicit finite-field seeds, transversal-design gluing, and an arithmetic induction. The construction uses no Wilson theorem or model tables at large orders. All fourth powers and many smaller orders are also constructed. The exact spectrum below the cutoff remains open. See docs/quartic_cofinite_20260928.md.",
    907: "Every sufficiently large odd order now has an idempotent model in Lean. Only seeds 3 and 23 are needed: their design periods 6 and 506 have gcd 2, and the singleton completes the odd residue class. Order 8 is now excluded in Lean by checking all 45 canonical first-row forms. The general even-order question remains open. Every finite group-affine model, including group endomorphisms and arbitrary constants, is now proved to have odd order in Lean. No numerical odd-order cutoff has been extracted. See docs/e907_even_order_research_20260930.md.",
    1083: "Lean constructions include all squares, 119*(30t+2)^2-6 for t>=0 (starting at 470), and 1008*1009^(t+1)+11 (starting at 1017083). Common-point gluing also proves orders 50 and 113. Both new families fill infinitely many orders 2 mod3 and use symbolic proofs. Cofiniteness is proved in Lean, including PBD existence for block sizes 7,9,16, CRT, and gluing. A reproducible computer-assisted construction now gives every order at least 246,119,111; its finite certificates and numerical sieve counts await Lean checking. See docs/1083_1286_effective_tails_20260930.md.",
    1286: "Lean constructions include all fourth powers, 119*(30t+2)^4-6 and 224*(30t+1)^4-6 for t>=0 (starting at 1898 and 218), and 1008*1009^(t+1)+11 (starting at 1017083). These fill infinitely many orders 2 mod3. Order 32 is proved by two 5-by-5 matrix coefficient checks; common-point gluing also gives 113. Cofiniteness is proved in Lean using the shared PBD existence theorem for block sizes 7,9,16 and arbitrary group fillings. A reproducible computer-assisted construction now gives every order at least 4,222,119,949; its finite certificates and numerical sieve counts await Lean checking. See docs/1083_1286_effective_tails_20260930.md.",
    677: "All fourth powers and models at 6487,6493,6499 have symbolic Lean proofs, with no large tables or exhaustive pair checks. Cofiniteness is proved in Lean, including PBD existence for block sizes 5,11,16 and the extension from residues 0,1 mod5 to all residues. Only finitely many orders remain undecided. A checked computer-assisted construction supplies every order at least 42,239,519; its finite certificates await Lean verification. See docs/e677_effective_bound_20260929.md.",
    1480: "Now proved in Lean: explicit four-point and five-point cores with indexed pairs give orders 4+2m and 5+2m. The existing certificates exclude 2 and 3. This resolves the note's contradictory inclusion of 3 in §3.1 in favor of its exclusion in §3.7. See docs/1480_finite_spectrum_theorem.md.",
    1485: "The note's squares-and-twice-squares conjecture is now proved in Lean by exact degree halving (2026-09-20). See Spectrum/WeakCentralSpectrum.lean and docs/1485_finite_spectrum_theorem.md. No SAT certificates or finite enumeration are used.",
    1483: "The Lean lower bound includes all squares and twice-squares; the exact spectrum remains open. Orders 3,5,6,7,10 are excluded in Lean. The constant-row subclass has exactly power-of-two orders, proved by cubic untwisting into E1485; a bijective row gives the same restriction. Uniform rank r at order r^2 forces E168. Order 11 remains a separately documented external exclusion with an admitted Lean declaration. See docs/1483_spectrum_progress.md and docs/1483_projector_followup.md.",
    1486: "Constructive Lean lower bound: every order at least 27, plus {1,4,9,11,13,16,18,19,20,21,22,23,24,25}. Graph splitting supplies the general tail and checked matching certificates bridge small gaps. Orders 2,3,5,6,7,8 are excluded in Lean; only 10,12,14,15,17,26 remain unresolved. See docs/1486_graph_spectrum.md.",
    1489: "Now proved in Lean: idempotent models at every order except 2 and 4, using explicit seven-group transversal designs, truncation and gluing, and kernel-checked seeds below 35. See docs/1489_finite_spectrum_theorem.md.",
}


def lean_set(values):
    return "{" + ", ".join(map(str, values)) + "}" if values else "∅"


def dupont_exceptions():
    """Read the explicit seed sets; NoteBounds checks the resulting equality in Lean."""
    from pathlib import Path
    import re
    root = Path(__file__).resolve().parent.parent / "equational_theories/Spectrum/Equation63"
    def entries(file, name):
        text = (root / file).read_text()
        return set(map(int, re.search(rf'def {name}[^=]*:=\s*\{{([^}}]+)', text)[1].split(',')))
    return sorted(entries("IdempotentFiniteBasis.lean", "exceptions") -
                  entries("FieldBounds.lean", "extraOrders"))


def lower(i, finite_orders=None):
    if i == 63:
        return "positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}"
    if i in (667, 883):
        from pathlib import Path
        import re
        source = (Path(__file__).resolve().parent.parent /
                  "equational_theories/Spectrum/Equation667883FieldBounds.lean").read_text()
        section = source.split(f"namespace E{i}.FieldBounds", 1)[1]
        values = list(map(int, re.search(r"def remaining[^=]*:=\s*\{([^}]+)", section)[1].split(',')))
        return "positiveExcept " + lean_set(values)
    if i == 1486:
        return "positiveExcept {2, 3, 5, 6, 7, 8, 10, 12, 14, 15, 17, 26}"
    finite = f"({lean_set(FINITE[i] if finite_orders is None else finite_orders)} : Set ℕ)"
    result = finite + (f" ∪ ({FAMILIES[i]})" if i in FAMILIES else "")
    if i in DUPONT_FAMILIES:
        result = f"({result}) ∪ (positiveExcept {lean_set(dupont_exceptions())}) ∪ cubes"
    if i in (1076, 1313):
        result = f"({result}) ∪ quarticTailSeeds ∪ Set.Ici 107773"
    return result
