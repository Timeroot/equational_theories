# A uniform mixed-path capacity in the minimal-core four-degree family

Research note, 20 September 2026. This is an analytic necessary condition,
not a classification or an exclusion of the family. No finite search or
affine-profile assumption is used. It generalizes the
[order-forty mixed-return calculation](1485_order_forty_mixed_return_counts.md).

Assume a finite E1485 magma has central count `r` and exactly the degrees

\[
r<q=r+k<2r<2q,\qquad n=2rq.
\]

Write `Z,A,B,T` for these four degree classes. The
[minimal-core structure](1485_four_degree_minimal_core_returns.md) gives
`r` top predecessors and successors at every vertex. Thus a member of
`B` has `r` non-top neighbors in either direction. All edges between
`A` and `B` are sharp; `A` is independent, and there are no edges
between `Z` and `B`.

On `B`, let `D` be ordinary adjacency and let `C_bd` record whether
`b*d∈A`. Equivalently, `C_bd` counts sharp two-edge paths from `b`
to `d` through `A`; it is zero or one. Define

\[
G_{db}=\#\{(x,y)\in B^2:
dDxDyDb,\ C_{dy}=C_{xb}=0\},\qquad K=CD+DC+G.
\tag{1}
\]

The condition `C_xy=0` makes any existing two-edge path from `x` to
`y` through `B` good. A bad middle could only be replaced by a vertex
of `A`: strict degree descent excludes `B,T`, and a central middle
is impossible for these endpoints. Consequently `K_db` counts exactly
the good-good three-edge paths `d→x→y→b` with `x,y∈A∪B`.
The two mixed contributions are `CD` and `DC`; there is no `A×A`
contribution. For `k>1`, the row and column sums of `C` are `k j_b`,
not `j_b`; this does not affect the counting identity.

## Uniform upper bound

For every pair of vertices in `B`,

\[
\boxed{K_{db}\le r.} \tag{2}
\]

Put `e=b*d` and use the
[return matching](1485_general_return_matching.md)

\[
X=L_e^{-1}(d)\longrightarrow Y=R_e^{-1}(b),
\qquad x\longmapsto x*b.
\]

It has `n/d(e)` matched pairs, and `K_db` counts those with both
endpoints non-top. Neither fiber contains a central vertex.

If `e∈T`, there are only `r` matched pairs altogether, proving (2).
This case includes the pairs with neither an `A` middle nor an ordinary
two-step `B` path; it must not be omitted from an incidence checker.

If `e∈A`, sharpness gives `X=Row(d)` and `Y=Col(b)`. Both have
`r` top and `r` non-top members. The boundary matching identity gives
exactly `K_db` top-top matched pairs as well. Since their endpoints
lie in two `r`-element sets, `K_db≤r` again.

## Sharper bounds when the return lies in `B`

Suppose `e=b*d∈B`. Define the bad internal extension/predecessor counts

\[
\beta=\#\{x\in B:eCx,\ dDx\},\qquad
\eta=\#\{x\in B:xDb,\ xCe\}.
\]

The fiber `X` has `r−β` non-top members: the `r` non-top successors
of `d` are eligible except for the bad internal extensions of `e→d`.
Similarly `Y` has `r−η` non-top members. Their total sizes are `q`,
so their top counts are `k+β` and `k+η`. Boundary matching therefore
counts the top-top pairs by

\[
g_{TT}=q-(r-\beta)-(r-\eta)+K_{db}
=K_{db}-(r-k)+\beta+\eta.
\]

This is nonnegative and at most `min(k+β,k+η)`. Hence

\[
\boxed{r-k-\beta-\eta\le K_{db}
\le r-\max(\beta,\eta).} \tag{3}
\]

In particular (2) holds in this final case too. The alternative
`e∈Z` cannot occur, completing the proof.

At order forty, (3) reads `3−β−η≤K_db≤4−max(β,η)`.
At order forty-eight it reads `2−β−η≤K_db≤4−max(β,η)`.
These are additional necessary constraints, not evidence that a
matrix pair satisfying them extends to a magma.
