# First-output gap with one extra central vertex

Research note, 19 September 2026. This is an analytic finite E1485
theorem, not yet formalized in Lean.

**Theorem.** Let the minimum degree be `r≥4`, and suppose there
are exactly `r+1` central vertices. If `p` is the least degree of
a noncentral product of two tops, then

\[
\boxed{r<p\le2r-2.}                              \tag{1}
\]

This includes the earlier minimum-four/five-central bound `p≤6`.
It does not exclude the entire `r+1`-central-vertex case.

The later [regular two-set bound](1485_linear_two_set_regular_bound.md)
also gives `p≤2r+1−ceil((r+1)/5)`. Taking the minimum with
(1) improves the bound further once `r≥15`.

## Central profile counts

Each central row partitions `r+1` central labels into `r`
nonempty successor blocks, and the dual assertion holds for columns.
Thus every top vertex's central predecessor and successor counts
are one or two. Write `N_ij` for the number with these counts
`i,j`, and put `m=r+1`.

The central incidence moments are

\[
\sum iN_{ij}=\sum jN_{ij}=rm,
\qquad \sum ijN_{ij}=m^2.
\]

Putting `d=N_22` gives

\[
N_{12}=N_{21}=m-2d,\qquad
N_{11}=m(r-3)+4d.                                \tag{2}
\]

In particular some top has central successor count one. The
[row-local degree bound](1485_first_top_output_fibers.md#5-a-row-local-degree-bound)
in such a row gives a noncentral top product of degree at most
`r+(r−1)=2r−1`. Thus `p≤2r−1`.

Suppose for contradiction that `p=2r−1`. Every top-top product of
that degree has equal top-profile sizes `t`, with `t≥p−r+1=r`,
by the [first-output fiber theorem](1485_first_top_output_fibers.md).
Its central-middle matrix is `(r−1)`-regular.

## Case 1: a top has central profile `(2,1)`

Suppose `N_21>0`, and choose such a top `w`. The row-local
bound supplies a degree-`p` output `a=w*v`. The predecessor
central blocks of `a` partition `r+1` labels and include the
two-element block of `w`. Hence `t≤r`, so `t=r`.

Its central-middle matrix is therefore `J_r` minus a permutation
matrix. After reindexing, this is the crown matrix `J_r−I_r`.
It is the intersection matrix of the sets `C_u` for top predecessors
`u` and `P_v` for top successors `v`, each of size at most two.
Since `r≥4`, the
[singleton crown lemma](1485_two_set_crown_bound.md#1-a-singleton-permits-at-most-three-pairs)
forces every one of these sets to have size two. But one of them
is the singleton `C_w`, a contradiction.

For even `r`, this case is automatic: (2) makes `N_21` a
nonnegative odd integer.

## Case 2: predecessor and successor sizes always agree

Suppose `N_21=0`. Then also `N_12=0`, and (2) gives
`N_11=m(r−1)>0`. Choose a top `w` of profile `(1,1)`.
Again the row-local bound gives a degree-`p` product in its row.
Its top-profile size satisfies `r≤t≤r+1`.

If `t=r`, the singleton crown lemma says that every top
predecessor has central successor count two. Since the two central
counts agree at every top, all their predecessor blocks also have
size two. They cannot partition `r+1` central labels into `r`
two-element blocks.

If `t=r+1`, every predecessor central block and every successor
central block is a singleton. By equality of the two central counts,
the opposite blocks are singletons as well. The central-middle
matrix is consequently an equality matrix

\[
K_{ij}=1_{f(i)=g(j)}.
\]

Its row and column sums are `r−1>0`. Thus `f` and `g` have
the same support, and each value in that support appears exactly
`r−1` times in each list. Consequently

\[
r-1\mid r+1,
\]

which would require `r−1` to divide two, impossible for `r≥4`.
This excludes the final case and proves (1).

The proof needs only the singleton part of the crown lemma. The
stronger sharp bound of five, including its pentagon equality case,
is a separate combinatorial result rather than an additional
dependency of this theorem.
