# An error in the published construction at order 90

**The sixteen-element singular product in Bennett's Lemma 5.46 cannot contain
its claimed five-element subquasigroup. This is now proved in Lean for every
choice of the specified factors.** Order 90 itself remains unresolved here:
this is an error in the proposed construction, not a nonexistence theorem.

## The exact claim and multiplication rule

F. E. Bennett, *Quasigroup Identities and Mendelsohn Designs*, Canadian Journal
of Mathematics 41 (1989), 341–368,
[DOI: 10.4153/CJM-1989-017-0](https://doi.org/10.4153/CJM-1989-017-0),
Lemma 5.46, p. 365, states:

> ... we obtain a model ... of order 16 = 5(4 − 1) + 1 which contains a
> subquasigroup of order 5, by using C₃-quasigroups of orders 3 and 4 and an
> idempotent ... quasigroup of order 5.

That subquasigroup is the shared five-point hole required by the subsequent
application of Theorem 3.13 to a `{7,8}`-GDD of type `11^7 8^1`.

Theorem 3.4 invokes Lindner's singular direct product. Its multiplication rules
are explicitly printed in C. C. Lindner, *The Generalized Singular Direct
Product for Quasigroups*, Canadian Mathematical Bulletin 14 (1971), 61–63,
[DOI: 10.4153/CMB-1971-011-0](https://doi.org/10.4153/CMB-1971-011-0),
p. 61, §2, rules (1)–(5). Lindner explicitly identifies the construction with
constant off-fiber operation as the ordinary singular direct product. Bennett's
reference [24], *Identities preserved by the singular direct product*,
[DOI: 10.1007/BF02944960](https://doi.org/10.1007/BF02944960), concerns preservation
of identities; its full text was not needed for the multiplication-rule check.

Write `V` for the five-point index factor, `Q` for the four-point C₃ factor,
and `P={c}` for the shared point. A C₃ quasigroup is commutative and satisfies
`L_x³ = id`, where `L_x(y)=x*y` (Bennett, p. 352, before Example 5.3).
The product has underlying set

```
S = {c} ∪ ((Q \ {c}) × V).
```

Rule (4) says that multiplication within any one fiber uses `Q`, including
its diagonal. Rules (2) and (3) say that multiplication by `c` also uses `Q`.
These are precisely the corresponding rules of the implementation
`Spectrum.E63.singularOp`, with the pair coordinates interchanged.

## Every allowed four-point factor has constant diagonal

This does not depend on choosing the particular table in Example 3.5.
Here is a short classification argument for any four-point C₃ quasigroup
with `c*c=c`.

Each `L_x` is a permutation whose cycles have length one or three. Since
`L_c` fixes `c`, it is either the identity or a three-cycle on the other points.
It cannot be the identity: for `a≠c`, the `L_a` orbit through `c` would be the
three-cycle `c → a → a*a → c`. The remaining point `d` would be fixed by
`L_a`, giving `a*d=d=c*d`, contrary to cancellation in column `d`.

Label the other points so that `L_c` is `(a b d)`. Thus `a*c=b` and `c*b=d`.
The value `a*b` cannot be `b` (row cancellation against `a*c`), cannot be `c`
(which would give a two-cycle `c ↔ b` in `L_a`), and cannot be `d` (column
cancellation against `c*b`). Hence `a*b=a`; the cubic law then gives `a*a=c`.
The same argument applies to `b` and `d`. The entire table is forced:

| `*` | c | a | b | d |
| --- | --- | --- | --- | --- |
| c | c | b | d | a |
| a | b | c | a | d |
| b | d | a | c | b |
| d | a | d | b | c |

In particular, **every square is `c`, and `c` is the only idempotent**.

## Why a five-point subquasigroup is impossible

Every square in the sixteen-point product is the shared point `c`, because
squares are evaluated inside their four-point fibers. Therefore every
nonempty closed subset contains `c`.

Multiplication by `c` cycles the three other points of each fiber. A closed
subset containing any one of them must contain all three. Consequently every
nonempty closed subset has size

```
1 + 3k,   with 0 ≤ k ≤ 5.
```

Five is impossible. This argument uses **no properties at all** of the
operations on the index factor or the three-point complement. Changing those
operations, relabeling the factors, or choosing a different allowed C₃ table
cannot repair this construction.

A likely source of the mistake is importing the usual direct-product intuition
that the index factor embeds. A section `{(a,v) : v∈V}` can inherit `V` when
both `a*a=a` in `Q` and `a⊗a=a` in the complement operation. Here the only
idempotent of `Q` is the point already removed into `P`. In fact the square
of every point of that proposed section lands at `c`, outside the section.
Confusing a Latin subsquare with a subquasigroup is another possible explanation:
the reconstructed table has two five-by-five Latin subsquares, but their row,
column, and symbol sets differ (see below). These are diagnoses of possible
reasoning errors, not claims about the author's intent.

## Lean verification and scope

The complete proofs are in
[`BennettObstruction.lean`](../equational_theories/Spectrum/Equation63/BennettObstruction.lean),
namespace `Spectrum.E63.BennettObstruction`:

- `c3_four_diagonal`: the four-point classification, for every operation on
  every four-element type with the stated hypotheses.
- `singular_closed_card_mod_three`: the orbit obstruction, for arbitrary
  finite index and complement types and arbitrary operations on them.
- `singular_no_five`: the contradiction for Bennett's sixteen-point product.
- `card_mod_three` and `closed_card_mod_three`: the more general observation
  that any finite constant-diagonal E229 quasigroup, and every nonempty closed
  subset of it, has order 1 modulo 3.

The proofs contain no `sorry`, native-computation axioms, or external SAT
refutations. The small four-point case analysis uses `grind`, which produces
an ordinary proof checked by Lean's kernel; the cardinality arguments use
three-cycle counting. They are included by the E63 spectrum entry point.

For the general E229 observation, write `R_x=L_x⁻²`. Then `L_x³(x)=x` and `x`
commutes with its square. If every square is `c`, this makes `L_c=R_c` a cubic
permutation. Its only fixed point is `c`: `c*x=x` would imply
`x=L_x³(x)=x*(x*c)=x*x=c`. Every nonempty closed subset contains `c`, so the
same count applies to it. E229 is the equivalent presentation
`(y*(y*x))*y=x`; the primary singular-product obstruction above works directly
with Bennett's multiplication and requires no change of presentation.

**What remains open:** another sixteen-element model with a five-element
subquasigroup could exist, and an entirely different construction at order 90
could exist. Neither is refuted by this result. The known local arguments leave
seven unsettled orders: `18,26,30,38,42,90,158`, in addition to the unformalized
exclusions at 10 and 14. The 2026-09-25 replacement searches below found no
positive certificate; their timeouts are not negative results.

## Checking whether isotopy repairs it

The sixteen-point singular product has exactly two Latin subsquares of order
five (row, column, and symbol sets need not coincide). They are, using the
generator's labels,

```
R = {1,4,7,10,13}, C = {3,6,9,12,15}, S = {3,6,9,12,15};
R = {3,6,9,12,15}, C = {1,4,7,10,13}, S = {3,6,9,12,15}.
```

They were enumerated by considering every five-element row set and grouping
columns by the set of symbols appearing in those rows.

Up to isomorphism, an arbitrary isotope of a table `T` has the form
`H⁻¹(T(x,G(y)))`, for two permutations `G,H`. A closed five-element set `R`
therefore requires a Latin subsquare `(R,C,S)` of `T`, with `G(R)=C` and
`H(R)=S`. CP-SAT searched both cases, imposing E229 on every pair, and
reported `INFEASIBLE` for each. These are solver results without independently
checked proof traces; they are not Lean exclusions. They concern isotopes
of this particular sixteen-point table, not all sixteen-point models.

## Independent routes to order 90

The following remain possible construction targets; no positive certificate
has yet been found.

1. A partial E229 table of order 13 with a two-point hole. Add two common
   points to TD(8,11), use this partial table on seven groups, and a full
   order-13 model on the last group.
2. A partial E229 table of order 15 with a four-point hole. Truncate the last
   group of TD(8,11) to nine points, add four common points, use the partial
   table on the seven full groups, and fill the last thirteen points.
3. A `{5,7,8}`-GDD of type `11^7 13^1`. Fill the groups with the known models
   of orders 11 and 13 and the blocks with the idempotent models of orders
   5, 7, and 8.

For the third route, there are compact cyclic difference-matrix searches.
Use eight coordinate groups over `Z/11Z`; the last coordinate group and two
additional points form the thirteen-point group. A row with two defined
coordinates must realize each of the eleven differences exactly once over
all rows. Rows assigned to the two additional points omit the last coordinate;
their seven-point translates become eight-point blocks after adjoining the
assigned point. The other rows are translated directly.

Let the seven four-subsets of the first seven coordinates be complements of
the lines of the Fano plane. Three tested row-support patterns are:

| Pattern | Rows containing the last coordinate | Rows omitting it |
| --- | --- | --- |
| A | Seven full eight-coordinate rows; seven Fano-complement rows of size five | Two full seven-coordinate rows, assigned to the additional points |
| B | One full row; seven rows of size seven, omitting each ordinary coordinate once; seven Fano-complement rows | Three full seven-coordinate rows, two assigned to the additional points |
| C | Three full rows; two copies of the seven Fano-complement rows | Four full seven-coordinate rows, two assigned to the additional points |

Each pattern has eleven occurrences of every coordinate pair. This checks
the support counts only; assigning values with all eleven distinct differences
is still required. A nonzero collision score is not a design certificate.

## A discarded smaller-design route

A `{5,7,8}`-GDD of type `3^9 2^1` on 29 points would also suffice: triple its
points, use product constructions on the blocks, and adjoin three common
points. The nine enlarged groups would have order 12 and a three-point
subquasigroup; the final group would have order 9. This would give 90 points.

However, that GDD cannot exist. For a block `B` of size `k` and a group `G`
not represented in `B`, choose `x` in `G`. The `k` pairs joining `x` to `B`
belong to distinct blocks. Each such block has at least three further points,
all outside `B ∪ G`, and those sets of further points are disjoint. Hence
`29 ≥ 4*k + |G|`. There are ten groups, so an unrepresented group always
exists when `k` is 7 or 8, and the inequality rules out both sizes. Blocks
of size five alone also fail: a point in a three-point group has 26 required
partners, which cannot be partitioned into sets of four. The searches for
this route were stopped after this counting obstruction was established.

## A useful constraint for the sixteen-point search

If `P` is a five-point subquasigroup and `x` lies outside it, the sets
`P`, `L_x(P)`, and `L_x²(P)` are disjoint. The third disjointness follows
from `R_x = L_x^(-2)` and closure of `P`; adjacent disjointness follows by
applying the permutation `L_x`. They occupy fifteen of the sixteen points.
In the cycles of `L_x`, successive visits to `P` are therefore separated
by at least three steps, with only one point left over in total.

Let `k` count the points of `P` not commuting with `x`. There is an
`ε ∈ {0,1}` such that the number of noncommuting partners outside `P` is
`2*k+ε`, and the number of fixed points of `L_x` is `1-ε`. The possible
`(k,ε)` pairs are

```
(0,0), (1,1), (2,0), (2,1), (3,0), (3,1), (4,0), (4,1), (5,0).
```

Indeed, a commuting point of `P` lies in a three-cycle, while a noncommuting
cycle containing `t` points of `P` has length `3*t` or `3*t+1`. There can
be only one extra point: either a fixed point in a cycle disjoint from `P`,
or the extra point of one noncommuting cycle. If the latter occurs, `x`
is not fixed and its own three-cycle contains a commuting point of `P`,
so `k≤4`. A noncommuting cycle of length three is impossible, which also
excludes `(1,0)`. The latest targeted search encodes these counts explicitly.
It fixes the first point of `P` to have outside cycles `1,1,3,3,3`; that
normalization selects a branch and does not cover all possible models.
Two additional runs use outside cycles `1^5 3^2` and `1^8 3`.

The [search report](../data/spectrum/63_order90_followup.json) records the
outcomes separately from the Lean spectrum. The small
[source and log archive](../data/spectrum/63_order90_followup_sources.tar.gz)
contains a README with replay commands, including the strengthened search
generator. It contains no independently checked refutation traces. No new
`sorry` or positive claim at order 90 has been added.
