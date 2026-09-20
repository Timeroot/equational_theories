# Full core at minimum translation degree three

Research theorem, 19 September 2026. This is a finite E1485 proof
combining analytic arguments with explicitly identified finite profile
checks. **It is not yet a Lean theorem.** No SAT, ATP answer, or
enumeration of full magma tables is a premise.

Here the translation degree of `a` is
`d(a)=|{a*x:x∈M}|=|{x*a:x∈M}|`; the equality of the two image
sizes is part of the established finite structure. The minimum is
`r=min_a d(a)`.

**Theorem.** Every finite E1485 magma with minimum translation degree
three has exactly nine central vertices and order

\[
\boxed{n=9\,2^j\quad\text{for some }j\ge0.}
\]

Conversely every such order is realized at minimum degree three:
take the direct product of the nine-element rectangle magma and a
Boolean NAND magma of order `2^j`. Thus this is the exact order
classification **at minimum degree three**, not the full spectrum
classification without a minimum-degree restriction.

Together with the earlier minimum-degree-one and two theorems, any
counterexample to the square-or-double-square spectrum conjecture
must now have **minimum translation degree at least four**.

## 1. Reduce the central count

Write `Z,T` for the central and top classes. The
[central-defect gap](1485_boundary_central_defect.md) implies that
a non-full core at this minimum has three, four, or five central
vertices. The five-central case is
[excluded analytically](1485_five_central_binary_blocks.md).

For four central vertices, the possible top counts are eight, nine,
or ten. The eight-top case has an
[analytic exclusion](1485_four_central_eight_top.md); the ten-top
case is [excluded analytically by central-block packing](1485_four_central_ten_top_exclusion.md).
With nine tops, the least noncentral degree is four or five:
the [first-output bound](1485_first_top_output_fibers.md)
supplies a noncentral top product of degree at most five at this
minimum. Both possibilities are excluded by the explicit finite
lemmas listed below. No separate degree-six or degree-seven
classification is now needed for this step.

Thus only the three-central case needs further work.

## 2. Exclude three central vertices

The [minimal-central-count theorem](1485_minimal_central_count.md)
gives nine top vertices and three top neighbors in each direction
at every vertex. The
[first-output theorem](1485_first_top_output_fibers.md)
forces a nonempty degree-four class `A`. The
[degree-five necessity theorem](1485_three_central_requires_five.md)
forces degree five as well, and hence `60|n`.

The [mixed-profile theorem](1485_three_central_five_profiles.md)
bounds `|A|≤6`. Every possible size is now excluded:

| `|A|` | Exclusion | Proof status |
| ---: | --- | --- |
| 1 | [Companion outputs and good-pair matchings](1485_three_central_singleton_exclusion.md) | Analytic |
| 2 | [Degree-four/five coverage of central triples](1485_three_central_two_degree_four_exclusion.md) | Explicit finite profile check |
| 3 | [Coverage plus mixed sharp fibers](1485_three_central_three_degree_four_exclusion.md) | Explicit finite profile check |
| 4 | [Mixed sharp-fiber exclusion](1485_three_central_four_five_degree_four_exclusion.md) | Explicit finite profile check |
| 5 | [Two exceptional sharp fibers intersect twice](1485_three_central_five_four_exclusion.md) | Analytic; also independently checked by finite enumeration |
| 6 | [Incompatible bounds on the degree-five class](1485_three_central_six_four_exclusion.md) | Analytic |

There is no remaining size for `A`. This excludes three central
vertices and finishes the non-full-core exclusion.

## 3. From full core to the order

We have proved `|Z|=9`. The already established
[full-core quotient theorem](1485_full_core_quotient.md) gives
`n=r²·2^j`, with no extra congruence assumption. Substituting
`r=3` gives `n=9·2^j`, which is a square if `j` is even and
twice a square if `j` is odd.

## 4. Exact computational premises

The proofs above use five finite profile lemmas. Their exhaustive
domains, necessary conditions, and counting logic are documented
in the linked proofs, and the following commands check them:

```text
python3 -Werror scripts/1485_m4h9_degree_four_exclusion.py
python3 -Werror scripts/1485_m4h9_incidence_check.py --degree-five
python3 -Werror scripts/1485_m3_two_degree_four_check.py
python3 -Werror scripts/1485_m3_three_degree_four_check.py
python3 -Werror scripts/1485_m3_sharp_fiber_check.py --size 4
```

The first two cover all 285 normalized four-central/nine-top
incidence diagrams, with the degree-four argument reducing to
24 diagrams. The remaining three cover respectively 414 disjoint
profile pairs, 1,956 triples, and 4,140 four-element collections.
The sharp-map refinements check 720 fully labeled cases for triples
and 14,004 codomain-normalized cases for four-element collections.
The latter normalization relabels the common codomain of both sharp
maps simultaneously; the proof of completeness is explicit.

All five commands passed. Two additional checks are useful but are
not further premises:

```text
python3 -Werror scripts/1485_m3_sharp_fiber_check.py --size 3
python3 -Werror scripts/1485_m3_sharp_fiber_check.py --size 5
```

The first reproduces the triple exclusion with 216 normalized
sharp-map cases. The second independently excludes the five-element
case in 321,948 normalized cases; the analytic proof above does
not depend on that computation.

These finite verifications are different from model-table regression
tests. The latter, in `scripts/1485_structure_check.py`, check
formulas on examples and do not prove an exclusion.

## 5. What this does not settle

Full core at minimum degree four or greater remains open. In
particular, this theorem must not be read as a proof that every
finite E1485 model has square or twice-square order. The
[current frontier](1485_proof_status.md) records the separate general
packing and divisor-gap results and the still-open targets.
