# Equivalence priorities: infinite term recovery and FO structure

Date: 2026-09-20.

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

## FO-structural targets

The new [FO inventory and conditional impact tables](definability_structural_equivalence_gaps.md)
contain the complete unresolved pairs and their class memberships. There are
**1,049 finite** and **1,094 unrestricted** equivalence questions, across
712 and 737 currently proved classes respectively. No FO-structural pair was
settled in this pass.

A focused shortlist, ranked by usefulness of either outcome, is:

| Arrow | Finite gaps settled if positive / negative | Unrestricted gaps settled if positive / negative |
|---|---:|---:|
| E8 → E3 | 10 / 9 | 6 / 9 |
| E11 → E109 | 6 / 8 | 6 / 7 |
| E3253 → E326 | 10 / 6 | 10 / 6 |
| E3522 → E3715 | 10 / 8 | 6 / 8 |

For example, a finite positive E8 → E3 would merge the five classes
represented by 3, 8, 326, 3715, and 4470. E11 → E109 would merge four classes,
represented by 11, 109, 844, and 1256. These counts overlap and must not be added.
The counts in each column concern a result in that variant; a finite negative
also gives the unrestricted negative, while a finite positive need not.

The universal idempotent-encoding question **E1 → E3** has larger conditional
impact: a positive result would merge 23 classes and settle 253 equivalence
pairs in either variant. This is a broad construction problem, not a reason to
expect an easy proof. For negative searches, **E3471 → E108** would settle 66
finite or 60 unrestricted class-pair questions if refuted.

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
cannot be FO-defined back from this candidate. This refutes that particular
construction, not E8 → E3 itself.

The [probe](../scripts/definability_idempotent_swap_probe.py) regenerates the
[saved counts and example](../data/definability_idempotent_swap_probe.json).
The FO priority generator independently checks the leading balanced targets
using full Boolean matrix propagation on the quotient.
