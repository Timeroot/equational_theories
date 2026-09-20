# Small central blocks exclude the boundary first-output degree

Research note, 20 September 2026. This is an analytic finite
E1485 theorem. No enumeration, solver result, or Lean declaration
is involved.

Let `r≥4` be the minimum translation degree, let `Z` have
size `m<2r`, and suppose every central predecessor and successor
block of a top vertex has size at most two. If a noncentral
product of two tops exists, let `p` be its least degree. Then

\[
\boxed{p\le2r-2.}
\]

## Proof

The central blocks in each central row partition `Z` into `r`
nonempty pieces. Since `m<2r`, some piece is a singleton.
Thus there is a top vertex `u` with `C_u={c}`. The
[row-local bound](1485_first_top_output_fibers.md#5-a-row-local-degree-bound)
gives `p≤2r−1`. Suppose equality holds.

The `r` central successor blocks of the tops in `Row(c)`
also partition `Z`. Choose a top `d∈Row(c)` whose successor
block `C_d` is a singleton. Choose its central successor
`z∈C_d`, and take a least noncentral output `a` in
`u*Col(z)`. Its degree is exactly `2r−1`, by the row-local
bound and the definition of `p`.

The [exact replacement argument](1485_maximal_central_block_first_output_gap.md#2-every-omitted-central-row-point-occurs)
does not require the maximal-block hypothesis of that note at
this step. It gives

\[
Row(a)=L_u^{-1}(a)\ \sqcup\ (Row(c)\setminus\{d\}).
\]

The top successor profile of `a` retains the other `r−1`
tops in `Row(c)`. The successor blocks of its new top inputs
partition the omitted block `C_d`. Since that block is a
singleton and each new block is nonempty, there is exactly one
new top. Thus `a` has exactly `r` top successors and, by the
first-output theorem, exactly `r` top predecessors.

Its central-middle matrix is `(p−r)=(r−1)`-regular of size
`r`, hence the crown `J_r−I_r` after reindexing. Both families
of sets defining the matrix have size at most two, and the row
at `u` is the singleton `C_u={c}`. The
[singleton crown lemma](1485_two_set_crown_bound.md#1-a-singleton-permits-at-most-three-pairs)
permits at most three rows, contradicting `r≥4`.

This excludes equality and proves the theorem.

## Consequences

At minimum degree four and central count six, a first noncentral
top-product degree of seven therefore requires a globally
occurring three-element central block. The case with all blocks
of size at most two is completely excluded, without splitting
the central-moment inventories or enumerating five-neighbor
profiles.

When `m=r+1`, the central partition bound already makes all
blocks have size at most two. For `r≥4`, the theorem thus
also gives a shorter proof of the
[one-extra-central-vertex bound](1485_one_extra_central_first_output_gap.md).

## At minimum degree at least six, the central-count hypothesis is unnecessary

Suppose `r≥6` and every central block has size at most two.
Then again **`p≤2r−2`**, without an additional hypothesis on `m`.
Indeed the central partitions give `m≤2r`, and the preceding
theorem handles strict inequality.

If `m=2r`, every central block has size exactly two. The central
blocks on the top predecessor or successor profile of any vertex
partition `Z`, so each such profile has size exactly `r`.
At a first noncentral top output, the first-output fiber theorem
therefore gives `p≤2r−1`. Equality would make its intersection
matrix a crown of size `r`, with both families consisting of
two-element sets. The [general two-set crown bound](1485_two_set_crown_bound.md)
permits at most five rows, contradicting `r≥6`.

The small exceptional minima have concrete local alternatives, not
asserted models: at `r=4,m=8`, the boundary crown has one of
[two pair-family types](1485_min_four_eight_central_pair_crowns.md);
at `r=5,m=10`, it must have the pentagon type from the same
general crown theorem. These cases are not excluded by this corollary.
