# Eighteen tops cannot have eight degree-five elements with two small profiles

Research finite-assisted proof, 20 September 2026. This excludes the
order-forty case `m=8,h=18,a=8,q=2`, where `q` counts degree-five
elements with three top neighbors rather than four. The analytic
reduction ends in two normalized central grids and 200 complete
central rectangle fixtures. None admits even one three-element
first-output profile. No SAT solver is used. The analytic reduction,
normalization, exhaustive construction, and independent set-based
oracles have been audited, and the checker independently rerun.
It is not a Lean theorem.

## 1. Zero weighted defect determines all paired block types

Use `P,C,α,β` for a top's central block sizes and its successor
and predecessor counts in the degree-five class. The
[weighted central identity](1485_order_forty_eight_central_top_bound.md)
gives, with `v=7−2C−α`,

\[
 v\ge0,\quad v\ge1\text{ if }C=1,\qquad
 \sum(P-1)v=160-7h-4a-q=0.                              \tag{1}
\]

Thus a singleton `C` block has singleton `P`; the dual proves
the converse. Whenever `P>1`, (1) forces `α=f(C)`, with
`f(2)=3,f(3)=1`. The corresponding dual statement holds for `β`.

Write the paired block counts as `n11=x,n22=y,n23=n32=w,n33=t`.
The equality of the off-diagonal counts follows from `ΣP=ΣC=32`.
The remaining moments `Σ1=18,ΣPC=64` give

\[
                 x=8-t,\qquad w=4-2t,\qquad y=2+4t.
\]

A central row cannot have block pattern `2222`, since all four
tops would have `α=3`, but their sum must be eight. Its pattern
is therefore `3311` or `3221`. Every singleton-`C` top also has
singleton `P`, so occurs in exactly one central row. If `R` rows
have pattern `3311`, counting these singleton occurrences gives
`x=8+R`. Comparison with `x=8−t` forces `t=R=0`.

Consequently every central row and column has pattern `3221`, and

\[
\boxed{n11=8,\quad n22=2,\quad n23=n32=4,\quad n33=0.}   \tag{2}
\]

The singleton top in each row must have `α=1`; dually `β=1`.
The other types have `(α,β)=(3,3),(1,3),(3,1)` respectively.
These final neighbor counts are not needed by the finite check below.

### Common finite central-profile lemma

The following is the precise finite lemma proved in §§2–6; it does
**not** depend on `a=8,q=2` or on any `α,β` values.

Suppose eighteen central rectangles on eight labels have block-type
counts (2), partition `Z×Z`, have four tops in each central row
and column, and satisfy global orthogonality `|P_u∩C_v|≤1`.
Suppose each central row and column has block pattern `3221`, and
the two triple-block families satisfy the multiplicity and intersection
conditions (3). Then there are no three-element top sets `U,V`
such that `P_U,C_V` partition `Z` and their central intersection
matrix is a permutation matrix, as in (5).

For the original branch, §1 supplies its block profile and row patterns;
the existence of a small first output supplies (3). The
[one-small-profile reduction](1485_order_forty_eight_central_eighteen_one_small.md)
supplies the same hypotheses with different neighbor counts, and so
reuses this identical finite lemma. No code or case inventory depends
on which analytic reduction supplies the hypotheses.

## 2. The two double-partition grids

Index the four type-`(2,3)` tops by `i` and write their blocks as
`A_i,C_i`. Index the four type-`(3,2)` tops by `j` and write
their blocks as `P_j,B_j`. Because every central row has exactly
one triple successor block, the four two-sets `A_i` partition `Z`.
Dually the four two-sets `B_j` partition `Z`.

Central orthogonality gives `|A_i∩B_j|≤1`. Their incidence is
therefore a binary four-by-four matrix with every row and column sum
two. Viewed as a bipartite graph it is either a single eight-cycle
or two four-cycles. These are the complete two normal forms.

The checker labels `Z={0,…,7}` and sets `A_i={2i,2i+1}`. It
uses the following successor partitions:

| Normal form | The four `B_j` blocks |
| --- | --- |
| Eight-cycle | `{0,7}`, `{1,2}`, `{3,4}`, `{5,6}` |
| Two four-cycles | `{0,2}`, `{1,3}`, `{4,6}`, `{5,7}` |

Every grid is isomorphic to one of these by independently relabeling
the `A` and `B` blocks. Each central label is the unique point of
an occupied intersection, so such an isomorphism lifts to a relabeling
of `Z`. No normal form is imposed on the eight unit rectangles.
They will be recovered from the remaining cells.

Define

\[
             \varepsilon_{ij}=|P_j\cap A_i|,\qquad
             \delta_{ij}=|C_i\cap B_j|.
\]

The large rectangles `P_j×B_j` and `A_i×C_i` are disjoint, so
`εδ=0` in each grid cell. Each `ε` column sums to three and
each `δ` row sums to three, with entries at most two. Each has
at least two nonzero positions. The two supports are disjoint and
there are only sixteen cells, so all these bounds are exact:

- The supports partition the grid, with two positions per row and column.
- Each triple block has distribution `2+1` across the opposite
  double partition.

Every `P_j` also meets every `B_k` at most once, and every `C_i`
meets every `A_k` at most once. Thus each direction has exactly
sixteen candidate triples in either normal form: choose a full block
from one partition and a third point avoiding its two blocks in the
other partition.

## 3. The first small profile supplies stronger intersection conditions

Since `q=2`, at least one three-element first-output profile exists.
The [one-hole grid theorem](1485_one_hole_first_output_grid.md)
applies with four triple blocks in each direction. It proves

\[
 |P_j\cap C_i|=1\quad\text{for all }i,j,
 \qquad\lambda_z,\mu_z\le2,
 \qquad(2-\lambda_z)(2-\mu_z)=0,                        \tag{3}
\]

where `λ,μ` are the multiplicities in the two triple-block families.
The same argument applies whenever at least one small profile exists;
the number two is not used in the finite lemma.

Write `U_1,U_2` for the predecessor blocks of the two type-`(2,2)`
tops, and `V_1,V_2` for their successor blocks. Each central row
already contains one unit top and one type-`(2,3)` top. Therefore

\[
 2-\lambda_z=\mathbf1_{U_1}(z)+\mathbf1_{U_2}(z),
 \qquad
 2-\mu_z=\mathbf1_{V_1}(z)+\mathbf1_{V_2}(z).            \tag{4}
\]

In particular their two deficiency supports are disjoint. The two
`U` blocks themselves need not be disjoint or distinct, and neither
assumption is made about the two `V` blocks.

Every `C_i` meets each `U_l` exactly once. Indeed (3) gives

\[
 \sum_{z\in C_i}(2-\lambda_z)=6-4=2;
\]

by (4), this is `|C_i∩U_1|+|C_i∩U_2|`, with each summand
at most one. The dual proves `|P_j∩V_l|=1`.

## 4. A complete finite central-system check

The standalone standard-library checker is
[`1485_m8_eighteen_two_small_check.py`](../scripts/1485_m8_eighteen_two_small_check.py).
For each of the two normal forms it performs the following exhaustive
construction.

1. Choose the four `P_j` from their sixteen candidates. Impose the
   support conditions of §2. From their pointwise deficiencies,
   enumerate **all** unordered pairs of two-sets satisfying (4).
2. Choose each `C_i` from its sixteen candidates, imposing support
   disjointness and all the intersections in (3). Enumerate all dual
   two-set complements in (4). Check that the two deficiency supports
   are disjoint.
3. Impose the remaining orthogonality and exact intersections with
   `U_l,V_l`. Try both pairings of the two `U` blocks with the two
   `V` blocks to form the two double-double rectangles. Repeated
   blocks are allowed throughout; overlapping rectangles are rejected.
4. The eight large rectangles cover 48 of the 64 ordered central
   pairs, and the two double-double rectangles cover another eight.
   Their remainder must have exactly one cell in every row and
   column. These cells are precisely the eight unit rectangles.

There is no guessing or fixed labeling of the unit permutation. Any
valid central system with the stated hypotheses is included: its
triples occur in the candidate lists, its double blocks occur in the
complete complement lists, and its actual unit cells are the remainder.

The exact inventory is:

| Grid | Predecessor families after initial tests | Paired triple families | Complete central fixtures |
| --- | ---: | ---: | ---: |
| Eight-cycle | 4,488 | 1,432 | 40 |
| Two four-cycles | 7,344 | 4,224 | 160 |
| Total | 11,832 | 5,656 | **200** |

The complete fixtures in each case are distinct, and every displayed
count is asserted. They are valid necessary central incidence systems,
not asserted magma models.

## 5. None of the 200 fixtures admits a first-output profile

For an actual degree-five output with three top neighbors, the
[first-output profile theorem](1485_first_successor_degree_profiles.md)
provides two three-element sets of tops `U,V`. Their predecessor
blocks `P_U` and successor blocks `C_V` respectively partition `Z`.
After matching their indices, the central intersection matrix satisfies

\[
                        |C_u\cap P_v|=\mathbf1_{u=v}.   \tag{5}
\]

Each one-sided partition necessarily has sizes `332`. The checker
enumerates **all** three-subsets of the complete top set in each
direction, including double parts from either mixed type or from either
type-`(2,2)` top. It does not assume in advance that those double
parts must be of a particular type. The sets `U,V` may overlap.

Every one of the 200 fixtures has exactly two predecessor partitions
and two successor partitions. But none of its four combinations has
a permutation intersection matrix (5). The independently implemented
set-based oracle confirms both complete one-sided inventories and the
absence of a compatible pair. Thus none of the fixtures supports even
**one** small first-output profile, contradicting `q=2`.

Using (3), which follows from the supposed existence of such a profile,
is not circular: the argument constructs every central system with
these necessary consequences, then shows that none can have the
profile whose existence was assumed.

## 6. Controls, reproduction, and scope

Run:

```sh
python3 scripts/1485_m8_eighteen_two_small_check.py
```

Add `--verbose` to print all fixtures and their one-sided partitions.
The first production run, including independent audits, took 8.11
seconds. The controls include:

- All ninety labeled binary four-by-four matrices of row/column
  degree two: 72 lie in the eight-cycle orbit and eighteen in the
  two-four-cycle orbit.
- Recovery of every incidence vector of two two-sets, including
  repeated sets, by the complement constructor.
- A fixed complete central fixture, which must pass the literal
  central-system oracle and be found by the constructor. Removing
  one label from one of its blocks must be rejected.
- A separate six-top partial incidence fixture for which the two
  profile oracles must **accept** a compatible `332` profile pair.
  It is a profile-oracle control, not a complete central system or
  a magma construction.
- Independent literal-set validation of all 200 complete fixtures:
  exact rectangle coverage, four tops in every central row and
  column, global orthogonality, block-type counts, and (3).

The fast bit-mask profile computation and the independent set/matching
oracle agree on every fixture. Python's `-O` mode is refused, so
assertions cannot be silently disabled. No external package, helper
script, SAT solver, or unverified solver answer is a premise.

The result excludes this particular eighteen-top branch; other
eight-central degree splits require their separate arguments.
