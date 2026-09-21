# Equivalence priorities: infinite term recovery and FO structure

Date: 2026-09-20; follow-ups through 2026-09-21.

**Current status:** the finite term-structural classification is complete; the
unrestricted variant has 28 unresolved class pairs. The
[FO counting follow-up](definability_fo_compactness_counting.md) supplies 35
negative generators and completes the unrestricted E1 source row, reducing the
unrestricted FO inventory from 1,094 to 1,001 unresolved class pairs. The sections
below preserve the earlier milestones; use the linked inventories for current
counts.

**E1133 → E1096 and E1167 → E1096 are now refuted for unrestricted
term-structural interpretation.** Both finite equivalences remain proved.
These are the two largest remaining unrestricted equivalence questions by
raw equation-pair count: each separates a four-equation class from the
18-equation E1096 class.

The [term-structural inventory](definability_term_structural_equivalence_gaps.md)
therefore falls from 36 to **34 unresolved class pairs**, and from 304 to
**160 raw unordered equation pairs**. Propagation adds 144 negative directed
cells, all in TS/all. There are still 739 currently proved unrestricted
classes and exactly 716 finite classes. The E1133/E1167 comparison remains open.

## The unary-permutation obstruction

[UnaryPermutationRecovery.lean](../equational_theories/Definability/UnaryPermutationRecovery.lean)
proves that every one-variable term operation in an E1202 magma is bijective.
E1202 belongs to the E1096 ordinary equivalence class and says

```text
x = y * ((z * (w * y)) * x).
```

Write `L_a(x) = a*x`. This equation implies

```text
L_a² = identity,
L_(a*(b*x)) = L_x.
```

Define `S(x) = x*x` and `T(x) = (x*x)*x`. The row identities give
`S(T(x)) = x` and `T(S(x)) = x`, so both are bijections.

For each unary term `u`, its row and its square's row are either
`(L_x, L_S(x))` or `(L_S(x), L_x)`, with the choice depending only on the term.
For unary terms `u,v`, these two possibilities imply that
`u(x)*v(x)` is either `S(v(x))` or `T(v(x))`. Induction therefore shows that
every unary term acts bijectively. The Lean proof expresses this as a clone
invariant on diagonals of binary terms.

Consequently, an operation whose square map is not bijective cannot be
recovered by terms from any E1096 companion. The forward defining term is
not needed for this obstruction.

[UnaryPermutationSeparations.lean](../equational_theories/Definability/UnaryPermutationSeparations.lean)
applies it to two infinite models:

* For E1167, use the natural numbers with
  `x*y = y+1` if `x,y` have the same parity, and `y-1` otherwise, with
  truncated subtraction. Its square map is `n ↦ n+1`, which is not surjective.
* For E1133, the September 21 follow-up simplifies the witness to the
  predecessor ray: `x*y = y-1` for equal parities, and `y+1` otherwise.
  Its square map is truncated predecessor, which sends both `0` and `1` to `0`.
  This replaces the earlier proof through the opposite of the patched E1661 model.

Both conclusions have transitive axiom guards listing only `propext`,
`Classical.choice`, and `Quot.sound`. The full `Definability` build and the
reference closure audit pass. These arguments make no new FO-structural or
term-definable negative claim.

## Remaining term-structural targets

All 34 unresolved unrestricted pairs are already equivalent on finite
carriers. Their connected groups of possible class collapses are:

| Representatives | Unresolved class pairs |
|---|---:|
| 63, 73, 118, 125, 1692 | 10 |
| 464, 511, 714, 1289 | 6 |
| 504, 910, 1722 | 3 |
| 883, 1323, 1526 | 3 |
| 917, 1086, 1729 | 3 |
| 1133, 1167 | 1 |
| Eight separate two-class groups | 8 |

The last row consists of 65/1491, 115/880, 124/1648, 476/503, 477/1492,
481/1496, 680/1695, and 707/1316. The large five- and four-class groups offer
the broadest next targets. E1133/E1167 is the closest continuation of the
new unary argument, but neither of its model classes has the bijective-unary
property used to separate E1096.

The [September 21 follow-up](definability_three_row_tree.md) proves that the
two rays are FO interdefinable, and constructs an infinite three-row tree
refuting the proposed square-row term for E1133 → E1167. The unrestricted
class-pair count remains 34.

The subsequent [unary-cycle pass](definability_unary_cycles.md) refutes
E65 → E1491 and E1648 → E124, reducing that count to **32**. Their finite
equivalences remain proved; these results do not settle the FO questions.

The [confluence and endomorphism pass](definability_confluence_recovery.md)
further refutes E115 → E880, E477 → E1492, E680 → E1695, and E481 → E1496,
leaving **28** unrestricted equivalence questions / **136** raw unordered pairs.
It also closes E115, E477, E680, and E481 → E4273 and E481 → E1492; closure
adds E873 → E4273. These nine generators add 60 directed TS/all negatives.

## FO-structural follow-up: 21 September 2026

The [compactness counting pass](definability_fo_compactness_counting.md) now
settles all four original unrestricted priorities negatively: E8 → E3,
E11 → E109, E3253 → E326, and E3522 → E3715. The latter two follow by closure
from E8 → E326. It also separates many of the weak-law classes through exact
row counts and families of square maps. A final straight-line counting argument
closes the remaining nine unrestricted targets from E1.

These arguments use compactness to obtain a uniform finite cover by formula
pairs. They do **not** settle the finite FO versions of these questions.
The [current FO inventory](definability_structural_equivalence_gaps.md) gives
the remaining pairs and updated conditional priorities. The finite inventory
still has 1,049 unresolved class pairs across 712 proved classes.

The [cube-column construction](definability_cube_column_repair.md) separately
proves E3471, E317, E3283, E3270, and E3280 → E108, for arbitrary and finite
carriers. These settle implication directions without yet collapsing any
additional FO equivalence classes.

## An initial E8 → E3 probe

E8 is `x = x*(x*x)`. Swapping columns `x` and `x*x` within row `x` makes the
operation idempotent, but can destroy recovery. An exhaustive check of all
3,375 E8 tables of order three finds 278 where this construction gains extra
automorphisms. One example is

```text
source:       candidate:
0 0 0         0 0 0
0 1 0         0 1 0
2 0 0         0 0 2
```

The source is rigid; the candidate permits swapping 1 and 2. Hence the source
cannot be FO-defined back from this candidate. The probe alone refutes that particular
construction. The later compactness argument refutes E8 → E3 over arbitrary
carriers; its finite FO variant remains open.

The [probe](../scripts/definability_idempotent_swap_probe.py) regenerates the
[saved counts and example](../data/definability_idempotent_swap_probe.json).
The FO priority generator independently checks the leading balanced targets
using full Boolean matrix propagation on the quotient.
