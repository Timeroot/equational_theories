# Checking stronger negatives after the counting passes

19 September 2026. **None of the latest 234 counting pairs can become a
one-way term-definability negative.** Every target law accepts a projection:
122 accept only the left projection, 31 only the right projection, and 81
accept both. These operations are defined by the terms `x` and `y` in every
source magma, on finite and infinite carriers alike. This is a mathematical
obstruction to the proposed upgrade, not a limitation of the search.

The existing general projection proofs are in
[Simple.lean](../equational_theories/Definability/Simple.lean).
The [checker](../scripts/definability_counting_upgrades_check.py) independently
verifies each target by following the leftmost and rightmost leaves of its two
equation terms.

**Rechecked, 20 September 2026:** all status counts below remain unchanged after
the [finite-symmetry pass](definability_finite_symmetry.md). That pass upgrades
E1076 → E1313 to a one-way FO negative, but this pair is outside the two counting
batches audited here.

## Which FO questions remain open

A fresh computation from the Lean declarations gives the following statuses
for those same 234 pairs:

| Relation | Positive | Open | Negative |
|---|---:|---:|---:|
| Term-definable, finite | 234 | 0 | 0 |
| Term-definable, arbitrary | 234 | 0 | 0 |
| FO-structural, finite | 31 | 203 | 0 |
| FO-structural, arbitrary | 8 | 226 | 0 |

These counts retain the candidate representatives from the TS/fin counting
pass. They are not counts after quotienting again by S or TD equivalence.
The 23 pairs positive for finite FO structurality but open for arbitrary
carriers would require infinite counterexamples for a negative upgrade.

The counting proof needs the forward operation to be a term, so that it acts
coordinatewise on the product. It also needs a recovery term: otherwise
different source coordinates may collapse to the same target operation.
First-order definitions need not act coordinatewise, and the projections
illustrate exactly the collapse allowed by one-way term definability.

## Automorphism searches

On a finite carrier, mutual parameter-free FO definability is equivalent to
equality of the two operations' automorphism groups. The relevant obstruction
is formalized in
[Structural.lean](../equational_theories/Definability/Structural.lean).
The search compares exact permutation subgroups on the same labeled carrier,
not just group orders or abstract group isomorphism types.

No stronger negative was found in the following checks:

- All `3^9 = 19,683` three-element operations, for all 203 pairs open in S/fin.
- The four selected permutation families on four and five elements, and the
  cyclic-translation families on four through seven elements, for their
  corresponding counting pairs.
- The 36 additional product-action and affine permutation-group scans recorded
  in the [saved results](../data/definability_counting_upgrades.json), on selected
  carriers of orders up to 31.

For each permutation family, the enumeration contains **every** binary
operation commuting with its generators. A target with the same automorphism
group as a source in that family must belong to the family too. Finding a
matching target excludes that source as an FO-structural counterexample;
it does not settle the general cell. In particular, this is not an exhaustive
search of all operations on the larger carriers, nor a test of all the large
products used in the counting proofs.

The small searches enumerate every permutation directly. The extended searches
use a colored graph encoding of the operation and compute automorphism
generators with pynauty. Group equality is tested by generator containment in
both directions. Every source model is classified; target enumeration can stop
once all required source groups have matches. Families exceeding 150,000
operations are explicitly listed as skipped. Six of the largest planned affine
scans were deferred when the effort shifted to other high-value cells; the
order-31 multiplier-index-three scan was interrupted without a result. The
extended `exact_groups` counts concern examined tables, since target searches
stop once every required source group has a match. These are exploratory calculations,
not new Lean certificates or negative board seeds.

A separate coefficient scan over every prime from 5 through 2,000 found no
nonprojection affine-source versus projection-only affine-target obstruction
among either counting batch. Testing the same obstruction against all 408,790
open raw S/fin pairs also found no new candidate. This is a check of this
specific affine family, not an exclusion of arbitrary finite counterexamples.

## The preceding 191 pairs

The preceding linear/table counting pass has a different TD status: 182 pairs
are positive on both boards, nine are open on the finite board, and four of
those remain open on the arbitrary-carrier board. The other five already have
infinite TD counterexamples.

For the four TD/all-open pairs, the saved mod-5 linear product witnesses all
have a common forward term. Here `*` denotes the source operation:

| Pair | A term working in every mod-5 linear source factor |
|---|---|
| E167 → E1482 | `(x*x)*(y*y)` |
| E477 → E680 | `(x*(x*x))*((y*y)*y)` |
| E477 → E1073 | `(x*y)*((x*x)*(y*y))` |
| E481 → E680 | `(x*(x*x))*((x*x)*y)` |

The checker evaluates the source and derived target laws on every assignment
in every factor. Thus these particular product witnesses cannot give TD
negatives. **These terms are not claimed to work in arbitrary source models**;
the four general TD questions remain open.

## Reproduction

```sh
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_counting_upgrades_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_counting_upgrades_check.py --extended
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_counting_upgrades_check.py --verify-board
```

The default run checks projections, the four earlier product terms, and the
nine small automorphism searches. `--extended` also needs pynauty and sympy;
`--verify-board` rebuilds the source-derived relation matrices and checks both
passes' status counts against the saved source fingerprint. No Lean declarations
or board statuses were changed by this investigation.
