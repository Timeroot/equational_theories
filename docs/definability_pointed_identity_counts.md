# Pointed right-identity blocks: 13 October 2026

This extends the [regular-block counting method](definability_block_symmetry_counting.md)
from one-variable equations to laws of the form `x = x * t(y)`. The new
[Lean catalogue](../equational_theories/Definability/PointedIdentityCountingCatalogue.lean)
contains 139 independent FO-structural negatives on arbitrary carriers.
They were selected from 321 count gaps between classes that were open in the
starting snapshot. Every discarded gap follows from one of the selected
negatives using already proved positive arrows.

These are **unrestricted FO-structural** results. They do not establish finite
FO-structural negatives or one-way FO-definability negatives. The finite groups
below serve as local counting devices, not as finite counterexample carriers.

## A small example: E11 cannot structurally recover E108

The equations are E11: `x = x * (y*y)` and E108: `x = x * ((y*y)*y)`.
Take a root `o` and `m` disjoint two-element blocks. Require independently
swapping either pair to be an automorphism. Outputs must belong to an input
block or be the root; in particular, the root together with one block is a
submagma. Products between two different blocks have five choices per ordered
pair of blocks: the root, or either of the two points in either input block.

For E11, make the root a right identity and make every square the root. There
are nine choices on each block: three choices for its mixed product and three
for the product with the root on the left. All inter-block products are free,
so this constructs `9^m * 5^(m*(m-1))` invariant E11 operations.

An invariant E108 operation restricts to one of only seven possibilities on
each three-element root-plus-block carrier. Six make the left cube equal the
root; the seventh is left projection. Consequently, even allowing every
possible inter-block product, there are at most
`7^m * 5^(m*(m-1))` invariant E108 operations.

FO definitions preserve the swaps. A definable recovery for every E11 magma,
including infinite magmas, would by compactness give a finite menu of recovery
formulas. If its size is `K`, each E108 operation can recover at most `K` E11
operations. The counts would force `9^m ≤ K*7^m` for every `m`, a contradiction.
This also allows formulas to be chosen separately for different input magmas.

## General construction

Replace each pair by a regular orbit of a nontrivial finite group `H` of order
`h`, still sharing a single fixed root. Local operations are parametrized by
`(p,u,v)`, where `p : H → Option H`, and `u,v : Option H`. Equivariance transports
the product at a base point to all other points. There are `(h+1)^(h+2)` local
parameter choices, and `2h+1` choices for each ordered pair of distinct orbits.

For a source `x = x*t(y)`, restrict to `u = 1` and `t(1) = o`. The first condition
makes the root a right identity. The second, by equivariance, makes `t` return
the root everywhere on the free orbit; it also returns the root at the root.
Thus these choices can be assembled with completely arbitrary inter-orbit
products. If their number is `a`, they give a source lower bound
`a^m * (2h+1)^(m*(m-1))`.

For any target law, restriction to a root-plus-orbit submagma gives necessary
local constraints. If `b` local parameters pass those constraints, encoding
these local restrictions and the inter-orbit products is injective, giving a
target upper bound `b^m * (2h+1)^(m*(m-1))`. No gluing theorem for target models
is needed. A strict gap `0 < b < a` suffices for the compactness contradiction.
The exported targets use at most three variables; the executable target test
checks all assignments of those variables. Only necessity of the test is used
in the general theorem.

The source representatives used here are E11, E56, E108, E440, E643, E1049, and
E1252. E846 also produces gaps in the scan, but its resulting arrows are
consequences of the retained ones. The selected certificates use 22 C2 gaps,
67 C3 gaps, and 50 C4 gaps. The Klein four group gives no additional gaps in
this pass.

## Proof checking and reproduction

The [general Lean argument](../equational_theories/Definability/PointedIdentityCounting.lean)
proves the source construction, the target encoding, both cardinality bounds,
and the compactness contradiction symbolically. Its axiom guard allows only
`propext`, `Classical.choice`, and `Quot.sound`.

The local arithmetic is in `PointedIdentityCountsC2.lean`,
`PointedIdentityCountsC3.lean`, and `PointedIdentityCountsC4.lean`. The C2 counts
use `decide +kernel`, and all 22 C2 conclusions have standard-axiom guards.
The C3 and C4 counts use `native_decide`, so those conclusions also depend on
Lean's native-evaluation axioms. There are no sorries or external SAT/LRAT
certificates in this batch. The largest enumeration has 15,625 local choices;
the arbitrarily large block constructions are not enumerated.

The [saved data](../data/definability_pointed_identity_counts.json) records the
139 independent certificates and the starting source fingerprint. Run:

```sh
OPENBLAS_NUM_THREADS=1 python3 scripts/definability_pointed_identity_counts.py
lake build equational_theories.Definability
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --verify-closure --date 2026-10-13
```

The Python checker independently enumerates all local operations and all target
assignments. Its output is not used as a proof oracle. `--emit-lean` reproduces
the three local-count modules and the catalogue; `--scan` searches the current
open board, which will naturally yield fewer results after this update.
The board parser explicitly treats this compactness helper as unrestricted,
so a finite local group cannot accidentally turn a counting argument into a
finite-carrier refutation.

## Other investigations in this pass

Finite-field symmetry searches did not find new finite FO-definability or
finite FO-structural negatives. The searched operations have the form
`f(x,y) = x + c([y-x])*(y-x)`, where `[y-x]` is a multiplicative subgroup coset.
Translations and that subgroup act by automorphisms. A source with a compatible
model and a target with none would give a one-way obstruction; a scalar
symmetry pattern occurring for the source but absent for the target would give
a structural obstruction. Neither occurred in the completed tests.

The two-coset survey covered odd primes from 5 through 251. The three-coset
survey covered eligible primes through 61, and the four-coset survey covered
eligible primes through 37 on the smaller finite-FO endpoint list. The broader
structural endpoint survey checked only laws with at most two variables;
three-variable laws were included on the smaller finite-FO list. The broader
four-coset scalar-period survey was completed through 29; the run was then stopped before
finishing 37. These bounded negative search results add no board facts.

For infinite term-structural equivalence, all 28 remaining possible class
mergers are already equivalences on finite carriers. Further finite witnesses
cannot separate these pairs. The existing finite parastrophe constructions and
one-sided infinite models remain the relevant next tools; this pass did not
establish a new positive infinite term-structural arrow.

## Audited impact

The exhaustive audit confirms the following change from the checkpoint after
the finite noninvertible-map pass:

| Measure | Before | After | Resolved |
|---|---:|---:|---:|
| Open unrestricted FO-structural raw arrows | 440,583 | 436,615 | 3,968 |
| Open arrows between current FO-structural classes | 59,684 | 58,993 | 691 |
| Possible FO-structural equivalence-class mergers | 853 | 707 | 146 |

The 139 explicit negatives are deduplicated before propagation. There are still
737 proved FO-structural classes: this pass separates possible mergers rather
than proving new positive equivalences. The other nine relation boards are
unchanged. In particular, all 139 corresponding finite FO-structural arrows
remain open, and this pass adds no infinite term-structural facts beyond those
already known.

The source audit checked all ten quotient propagations against the independent
full-matrix propagation. It also confirms that none of the 139 declarations was
misclassified as a finite-carrier refutation. The four generated Lean files
reproduce byte-for-byte from the saved counts. The five new Lean files total
78,574 bytes, with no external certificate payload.

Source fingerprint: `0dd94483420a6d4daa48503117a5809da6a54ae2ef1ac09de9662aea1ebd6204`
(15,930 Lean source files).

The complete `lake build equational_theories.Definability` passed (17,278 jobs),
as did all kernel-only axiom guards. With dependencies already built, the local
C2, C3, and C4 modules took approximately 15, 16, and 149 seconds respectively;
the general argument took about 5 seconds. The C3/C4 timings include the native
checks and do not represent kernel-only evaluation.

Both the [FO-structural priorities](definability_structural_equivalence_gaps.md)
and the [term-structural inventory](definability_term_structural_equivalence_gaps.md)
were regenerated against that fingerprint. The finite FO-structural inventory
still has 1,047 possible mergers; the unrestricted term-structural inventory
still has 28, and the finite term-structural classes remain completely separated.
