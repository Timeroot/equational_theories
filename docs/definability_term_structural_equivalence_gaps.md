# Remaining term-structural equivalence questions

Date: 2026-09-21. Computed from the same source fingerprint as the verified table audit.

An unresolved pair is an unordered pair of distinct currently proved classes for which neither direction is refuted. Thus either both directions are open, or one is proved and the reverse is open. Open arrows whose reverse is refuted do not appear here.

| Variant | Currently proved classes | Both directions open | One proved, reverse open | Total unresolved class pairs | Raw unordered equation pairs |
|---|---:|---:|---:|---:|---:|
| Arbitrary carriers | 739 | 15 | 19 | 34 | 160 |
| Finite carriers | 716 | 0 | 0 | 0 | 0 |

Representatives are the least equation numbers in their currently proved classes. The two directions in the tables use the variant named in the heading. Class-pair counts are not counts of independent possible reductions in the number of classes.

The finite equivalence classes are completely determined: there are exactly **716**. Every two distinct classes have at least one refuted direction.

All remaining unrestricted questions concern pairs already proved equivalent on finite carriers.

The [strict-implication counting proof](definability_spectrum_priority_pass.md) refutes E629 → E52 and E854 → E433. The [27-element product obstruction](definability_cube_focus.md) refutes E3342 → E3545. All three separations hold for both variants. E3545 → E3342 remains open.

The [unary-permutation obstruction](definability_equivalence_priority_pass.md) additionally refutes E1133 → E1096 and E1167 → E1096 on arbitrary carriers. Their finite equivalences remain proved.

## Finite carriers: complete list

No unresolved equivalence pairs.

## Arbitrary carriers: complete list

| A | B | A → B | B → A |
|---:|---:|---|---|
| 63 | 73 | open | open |
| 63 | 118 | proved | open |
| 63 | 125 | open | proved |
| 63 | 1692 | open | open |
| 65 | 1491 | open | proved |
| 73 | 118 | open | open |
| 73 | 125 | open | proved |
| 73 | 1692 | open | proved |
| 115 | 880 | open | proved |
| 118 | 125 | open | proved |
| 118 | 1692 | open | open |
| 124 | 1648 | open | open |
| 125 | 1692 | proved | open |
| 464 | 511 | open | open |
| 464 | 714 | open | proved |
| 464 | 1289 | open | open |
| 476 | 503 | open | open |
| 477 | 1492 | open | proved |
| 481 | 1496 | open | proved |
| 504 | 910 | open | proved |
| 504 | 1722 | open | open |
| 511 | 714 | open | proved |
| 511 | 1289 | open | open |
| 680 | 1695 | open | proved |
| 707 | 1316 | open | proved |
| 714 | 1289 | proved | open |
| 883 | 1323 | open | open |
| 883 | 1526 | open | open |
| 910 | 1722 | proved | open |
| 917 | 1086 | open | open |
| 917 | 1729 | open | open |
| 1086 | 1729 | open | proved |
| 1133 | 1167 | open | open |
| 1323 | 1526 | proved | open |

### Participating class memberships

| Representative | Equations in the class |
|---:|---|
| 63 | 63, 271 |
| 65 | 65, 261 |
| 73 | 73, 274 |
| 115 | 115, 219 |
| 118 | 118, 229 |
| 124 | 124, 206 |
| 125 | 125, 222 |
| 464 | 464, 3103 |
| 476 | 476, 3076 |
| 477 | 477, 3150 |
| 481 | 481, 3161 |
| 503 | 503, 3069 |
| 504 | 504, 3143 |
| 511 | 511, 3116 |
| 680 | 680, 2947 |
| 707 | 707, 2940 |
| 714 | 714, 1120, 2507, 2913 |
| 880 | 880, 2707 |
| 883 | 883, 2744 |
| 910 | 910, 2737 |
| 917 | 917, 2710 |
| 1086 | 1086, 2541 |
| 1133 | 1133, 1661, 1979, 2481 |
| 1167 | 1167, 1659, 2000, 2473 |
| 1289 | 1289, 2338 |
| 1316 | 1316, 2331 |
| 1323 | 1323, 2304 |
| 1491 | 1491, 2061 |
| 1492 | 1492, 2135 |
| 1496 | 1496, 2146 |
| 1526 | 1526, 2101 |
| 1648 | 1648, 1924 |
| 1692 | 1692, 1895 |
| 1695 | 1695, 1932 |
| 1722 | 1722, 1925 |
| 1729 | 1729, 1898 |

## Validation

The positive and negative matrices were rebuilt from the current sources. The source fingerprint matches the audited snapshot and did not change during the computation. Weighted class-pair counts were independently checked against the predicate on every raw unordered equation pair.

Source SHA-256: `d71384ba900d1638ae4407e1d42530cef1a0e570aa5ab73d4826e2475e920bf7`.

Regenerate after the table audit with `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_term_structural_equivalence_gaps.py --write`.

[Machine-readable pairs and class memberships](../data/definability_term_structural_equivalence_gaps.json).
