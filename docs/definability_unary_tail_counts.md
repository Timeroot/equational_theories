# Noninvertible maps and finite term recovery

13 October 2026. This follow-up to the
[block-symmetry counts](definability_block_symmetry_counting.md) gives **31 new
explicit finite term-structural negatives**, formalized in Lean. These also
refute unrestricted term structurality. Two larger count gaps are saved as
research candidates, without adding them to the proved board.

After duality and closure, these resolve **136 raw equation arrows / 31 class
arrows** in each term-structural board. The other eight boards are unchanged.

| Board | Raw open before → after | Class arrows open before → after |
|---|---:|---:|
| Term-structural, finite | 19,707 → 19,571 | 3,998 → 3,967 |
| Term-structural, unrestricted | 21,577 → 21,441 | 4,466 → 4,435 |

No equivalence-class count changes: these settle directed arrows between
already separated classes. The full `Definability` build and all ten audit
closure comparisons passed.

The baseline is the snapshot with fingerprint
`44a9aeb7ab167b2bef517b04435edf82de1ff7235d9725e9374fd846d96349d9`.
All arrows below are **source → target**.

## The useful strengthening

A term operation preserves every endomorphism of its source magma, including
noninvertible ones. Fix a finite set X and a map u : X → X. The binary operations
f satisfying

```
f(u(x), u(y)) = u(f(x,y))
```

contain both projections and are closed under composition. Suppose this family
contains s source-law operations and at most t target-law operations, with s>t.
Take the finite product of the s source magmas. A proposed defining term for the
target acts separately on each coordinate, producing a compatible target
operation there. Two source coordinates must receive the same target operation.
A recovery term then gives the same original operation in those two coordinates,
contradicting their distinctness.

This is the existing finite clone-family argument, so **no compactness or
uniform bound on formula length is needed**. Model-dependent choices of the two
terms do not evade the obstruction: the product is itself a single finite source
model. The new ingredient is using maps with trees feeding into cycles, instead
of only permutations or their group actions.

For example, the four-point predecessor map
`[0,0,1,2]`, meaning `3 → 2 → 1 → 0 → 0`, has 1,024 commuting binary operations.
Exactly 20 satisfy E1252, while only 18 satisfy each of E835, E842, E1637, and
E3729. This refutes all four finite term-structural arrows. The same construction
on five points supplies further obstructions that the four-point counts miss.

## Formalized arrows

The map column lists `[u(0),…,u(n−1)]`. Counts concern the complete compatible
family, rather than all magmas of that order. When several source or target laws
share a row, the displayed count applies to each one individually. Python
reproduces the exact family counts; Lean proves the sufficient lower bound
on source operations and upper bound on target operations using the lists.

| Map | Source | Targets | Source count | Target count |
|---|---|---|---:|---:|
| `[0,0,1,2]` | E1252 | E835, E842, E1637, E3729 | 20 | 18 |
| `[0,0,1,3]` | E844, E1042 | E847 | 21 | 19 |
| `[0,0,3,2]` | E1263 | E1249 | 34 | 30 |
| `[0,2,1,1]` | E1050 | E1435, E1638 | 2 | 1 |
| `[1,0,0,1]` | E443 | E1253, E1255 | 14 | 13 |
| `[1,0,0,1]` | E1052 | E843 | 25 | 17 |
| `[1,0,0,1]` | E1056 | E109, E1253, E1255, E1263 | 17 | 13 |
| `[1,0,0,2]` | E844, E1042 | E1250 | 5 | 3 |
| `[1,2,0,0]` | E1029 | E1632 | 11 | 8 |
| `[0,0,1,2,3]` | E108 | E835, E842, E1637, E3729 | 85 | 67 |
| `[0,0,1,2,3]` | E108 | E3323 | 85 | 84 |
| `[0,0,1,2,3]` | E108 | E3537 | 85 | 71 |
| `[0,0,1,2,3]` | E1252 | E3323, E3537 | 94 | 84, 71 |
| `[0,2,3,1,1]` | E626 | E1478, E1630, E1681 | 25 | 23 |
| `[1,2,3,0,0]` | E826 | E1632 | 30 | 27 |

The smallest example has two compatible E1050 operations but just one E1435
operation, the left projection. Thus even a product of two four-element source
models gives the counting obstruction; a huge explicit model certificate is
unnecessary.

The generating declarations are imported by
[UnaryTailCountingCatalogue.lean](../equational_theories/Definability/UnaryTailCountingCatalogue.lean).
Their names have the form
`Equation<Target>_not_termStructuralFromFin_Equation<Source>_unaryTail`.

## Lean checks and certificate size

[FiniteEndomorphismCover.lean](../equational_theories/Definability/FiniteEndomorphismCover.lean)
proves the reusable `Magma.UnaryMap.not_termStructuralFromFin_of_cover` theorem.
It only needs an injective list of source operations and a shorter list covering
all compatible target operations. It does not compute the cardinality of the
entire commuting family. The general theorem and the table-encoding lemmas use
only ordinary Lean axioms.

The concrete modules check source laws, endomorphism preservation, and distinctness
with `decide +kernel`. Target-list completeness is a finite propositional theorem
checked by standard `bv_decide`, using its compiled LRAT checker. Explicit axiom
guards record those checker axioms. There are no new `sorry` obligations, solver
assumptions, or unchecked Python certificates.

A four-point table occupies 32 bits; a five-point table occupies 75 bits. In the
latter encoding Lean proves that all entries lie among the five legitimate
values, so the three unused three-bit values cannot introduce spurious models.
The largest formalized source list has 94 tables; the largest target list has
84. The ten generated Lean files total about 208 KiB. No external LRAT bundle is
required. In the initial builds, individual four-point modules took 7–27 seconds;
the largest five-point module, containing eight arrows, took 87 seconds. These
are local observations, not a CI performance guarantee.

## What did not upgrade to finite FO structure or one-way definitions

The previous block-counting pass's 79 explicit unrestricted FO-structural
negatives were already negative in the finite term-structural board. Thus merely
applying the product theorem to those same counts would add no facts.

Finite FO structure requires the same automorphism group, not a bound on the
number of tables having that group. Searching all automorphism patterns in the
pointed C4 and V4 families on five points, and the regular S3 family on six
points, supplied no missing target pattern for those 79 arrows. This rules out
those particular finite witnesses, not finite FO separation in general.
Intersecting each pointed four-group family with every noninvertible unary map
also supplied no new finite term-structural arrow. The independent maps with
tails above were the productive step.

Noninvertible endomorphisms need not be preserved by arbitrary FO definitions,
so the new tail obstructions do **not** prove FO-structural negatives. Every
target in this pass, including the two research candidates below, admits either
the left or right projection. Its one-way term and FO definability arrows are
therefore positive already; no one-way negative upgrade is possible.

## Survey boundary and remaining candidates

The search considered unary maps on four and five points up to relabeling,
omitting permutations and constant maps. It completed ten map families of each
size. It skipped three four-point and 29 five-point map types when an intermediate
enumeration exceeded 150,000 partial tables. This is not an exhaustive search
of all such families below a bound on their final size.

Two additional Python count gaps have not been given Lean certificates here:

| Source → target | Map | Source count | Target count |
|---|---|---:|---:|
| E846 → E3315 | `[0,0,1,1]` | 2,065 | 1,890 |
| E1262 → E1254 | `[1,2,0,0,1]` | 566 | 540 |

Adding a second unary map, tested over every possible map on the same carrier,
did not shrink either of these count gaps to a smaller compatible family.
A better target characterization or another closed operation family could make
these two proofs more economical.

The [survey data](../data/definability_unary_tail_counts.json) records every
completed and skipped map type and distinguishes `lean` from `research` entries.
The saved counts and all generated Lean files can be reproduced with:

```sh
OPENBLAS_NUM_THREADS=1 python3 scripts/definability_unary_tail_counts.py
lake build equational_theories.Definability
```

Use `--write` to regenerate the Lean files. Use
`--scan /tmp/unary-tail-survey.json` to repeat the search against the current
open-arrow snapshot. That search never changes the saved proof catalogue.
