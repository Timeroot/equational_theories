# Counting with noninvertible endomorphisms

These certificates add seven finite term-structural negatives. They use finite
groups together with noninvertible endomorphisms, and count complete families
of binary operations preserved by those maps and all left translations.

| Carrier and maps | Family size | Source | Target | Source count | Target count |
|---|---:|---:|---:|---:|---:|
| Dihedral group of order 8, two endomorphisms | 64 | E1055 | E3458 | 47 | 41 |
| Cyclic group of order 9, multiplication by 3 | 6,561 | E418 | E422 | 849 | 838 |
| Same | 6,561 | E418 | E618 | 849 | 837 |
| Cyclic group of order 16, multiplication by 4 and all units | 128 | E1233 | E1026 | 20 | 16 |
| Same | 128 | E1235 | E828 | 20 | 17 |
| Same | 128 | E1235 | E1026 | 20 | 16 |
| Same | 128 | E1236 | E1026 | 20 | 16 |

Write the group operation additively, including for the dihedral group. Every
binary operation preserved by all left translations has the unique form

\[
x\mathbin{\star_f}y=x+f(-x+y).
\]

For a group endomorphism \(h\), this operation preserves \(h\) precisely when
\(h\circ f=f\circ h\). The implication from preservation follows by evaluating
at \((0,y)\); the converse follows from the homomorphism laws. These complete
families contain both projections and are closed under composition of binary
terms. Apply the claimed mutual term recovery to the finite product of all
source-law models in the family. Its forward term produces target operations
on the factors; its backward term forces distinct source factors to produce
distinct target operations. This gives an injection contradicting the counts
in the table.

The [general Lean proof](../equational_theories/Definability/EndomorphismFamilyCounting.lean)
also reduces coverage to values on a small set of coordinates. Each carrier
element is the image of one coordinate under a saved endomorphism. A commuting
function is consequently determined by its values on those coordinates.
The certificates check all coordinate assignments that satisfy the commutation
constraints and recover the corresponding row from the saved complete family.

| Carrier | Coordinates | Coordinate assignments checked | Commuting functions |
|---|---:|---:|---:|
| Dihedral group of order 8 | 4 | 4,096 | 64 |
| Cyclic group of order 9 | 6 | 531,441 | 6,561 |
| Cyclic group of order 16 | 2 | 256 | 128 |

The independent Python checker reconstructs the complete families, checks the
group and endomorphism tables, and tests every variable assignment for each
law. Lean proves the coverage and counting implications, with explicit axiom
guards on every resulting negative. The general coverage lemmas use ordinary
Lean axioms; the finite table checks and counts use guarded native computation.

These witnesses do not yield FO-structural upgrades. Exact automorphism
comparisons found matching target groups for all the source models in the first
two families. The third family was enlarged to all 2,048 operations compatible
with the chosen source's full automorphism group; matching target groups again
exist. This does not exclude stronger obstructions from other witnesses.

Reproduce the data and proofs with:

```sh
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_endomorphism_counts_check.py
lake build equational_theories.Definability.Generated.MonoidDihedral8 \
  equational_theories.Definability.Generated.MonoidCyclic9Times3 \
  equational_theories.Definability.Generated.MonoidCyclic16Times4Units
```

The current integration checkpoint is recorded in
[the twelve-hour pass log](definability_twelve_hour_pass.md).
